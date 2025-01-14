#![cfg(not(target_arch = "wasm32"))]
use crate::{
    core::{Invocation, InvocationResponse, WasmCloudEntity},
    Message, RpcError,
};
#[allow(unused_imports)]
use log::{debug, error, trace};
use ring::digest::{Context, SHA256};
use serde::{de::DeserializeOwned, Serialize};
use serde_json::Value as JsonValue;
use std::{
    convert::{TryFrom, TryInto},
    sync::Arc,
    time::Duration,
};

pub(crate) const DEFAULT_RPC_TIMEOUT_MILLIS: Duration = Duration::from_millis(2000);

/// Send wasmbus rpc messages
///
/// The primary use of RpcClient is providers sending to actors,
/// however providers don't need to construct this - one is created
/// by HostBridge, which providers create during initialization.
///
/// This class is also used by wash and test tools for sending
/// rpc messages to actors and providers. Note that sending to
/// a provider requires an existing link definition, _and_,
/// the message needs to be signed by a valid cluster key.
///
/// This RpcClient does not subscribe to rpc topics.
/// To subscribe, use the nats client api directly.
///
#[derive(Clone)]
pub struct RpcClient {
    /// sync or async nats client
    client: NatsClientType,
    /// lattice rpc prefix
    lattice_prefix: String,
    /// secrets for signing invocations
    key: Arc<wascap::prelude::KeyPair>,
    /// host id for invocations
    host_id: String,
    /// timeout for rpc messages
    timeout: Option<Duration>,
}

#[derive(Clone)]
pub(crate) enum NatsClientType {
    Async(crate::anats::Connection),
}

/// Returns the rpc topic (subject) name for sending to an actor or provider.
/// A provider entity must have the public_key and link_name fields filled in.
/// An actor entity must have a public_key and an empty link_name.
#[doc(hidden)]
pub fn rpc_topic(entity: &WasmCloudEntity, lattice_prefix: &str) -> String {
    if !entity.link_name.is_empty() {
        // provider target
        format!(
            "wasmbus.rpc.{}.{}.{}",
            lattice_prefix, entity.public_key, entity.link_name
        )
    } else {
        // actor target
        format!("wasmbus.rpc.{}.{}", lattice_prefix, entity.public_key)
    }
}

impl RpcClient {
    /// Constructs a new RpcClient for the async nats connection.
    /// parameters: async nats client, lattice rpc prefix (usually "default"),
    /// secret key for signing messages, and host_id
    pub fn new(
        nats: crate::anats::Connection,
        lattice_prefix: &str,
        key: wascap::prelude::KeyPair,
        host_id: String,
        timeout: Option<Duration>,
    ) -> Self {
        RpcClient {
            client: NatsClientType::Async(nats),
            lattice_prefix: lattice_prefix.to_string(),
            key: Arc::new(key),
            host_id,
            timeout,
        }
    }

    /// convenience method for returning async client
    /// If the client is not the correct type, returns None
    pub fn get_async(&self) -> Option<crate::anats::Connection> {
        use std::borrow::Borrow;
        match self.client.borrow() {
            NatsClientType::Async(nats) => Some(nats.clone()),
        }
    }

    /// Replace the default timeout with the specified value.
    /// If the parameter is None, unsets the default timeout
    pub fn set_timeout(&mut self, timeout: Option<Duration>) {
        self.timeout = timeout;
    }

    /// Send an rpc message using json-encoded data
    pub async fn send_json<Target, Arg, Resp>(
        &self,
        origin: WasmCloudEntity,
        target: Target,
        method: &str,
        data: JsonValue,
    ) -> Result<JsonValue, RpcError>
    where
        Arg: DeserializeOwned + Serialize,
        Resp: DeserializeOwned + Serialize,
        Target: Into<WasmCloudEntity>,
    {
        let msg = JsonMessage(method, data).try_into()?;
        let bytes = self.send(origin, target, msg).await?;
        let resp = response_to_json::<Resp>(&bytes)?;
        Ok(resp)
    }

    /// Send a wasmbus rpc message by wrapping with an Invocation before sending over nats.
    /// 'target' may be &str or String for sending to an actor, or a WasmCloudEntity (for actor or provider)
    /// If nats client is sync, this can block the current thread.
    /// If a response is not received within the default timeout, the Error RpcError::Timeout is returned.
    /// If the client timeout has been set, this call is equivalent to send_timeout passing in the
    /// default timeout.
    pub async fn send<Target>(
        &self,
        origin: WasmCloudEntity,
        target: Target,
        message: Message<'_>,
    ) -> Result<Vec<u8>, RpcError>
    where
        Target: Into<WasmCloudEntity>,
    {
        self.inner_rpc(origin, target, message, true, self.timeout)
            .await
    }

    /// Send a wasmbus rpc message, with a timeout.
    /// The rpc message is wrapped with an Invocation before sending over nats.
    /// 'target' may be &str or String for sending to an actor, or a WasmCloudEntity (for actor or provider)
    /// If nats client is sync, this can block the current thread until either the response is received,
    /// or the timeout expires. If the timeout expires before the response is received,
    /// this returns Error RpcError::Timeout.
    pub async fn send_timeout<Target>(
        &self,
        origin: WasmCloudEntity,
        target: Target,
        message: Message<'_>,
        timeout: Duration,
    ) -> Result<Vec<u8>, RpcError>
    where
        Target: Into<WasmCloudEntity>,
    {
        self.inner_rpc(origin, target, message, true, Some(timeout))
            .await
    }

    /// Send a wasmbus rpc message without waiting for response.
    /// This has somewhat limited utility and is only useful if
    /// the message is declared to return no args, or if the caller
    /// doesn't care about the response.
    /// 'target' may be &str or String for sending to an actor,
    /// or a WasmCloudEntity (for actor or provider)
    #[doc(hidden)]
    pub async fn post<Target>(
        &self,
        origin: WasmCloudEntity,
        target: Target,
        message: Message<'_>,
    ) -> Result<(), RpcError>
    where
        Target: Into<WasmCloudEntity>,
    {
        let _ = self.inner_rpc(origin, target, message, false, None).await?;
        Ok(())
    }

    /// request or publish an rpc invocation
    async fn inner_rpc<Target>(
        &self,
        origin: WasmCloudEntity,
        target: Target,
        message: Message<'_>,
        expect_response: bool,
        timeout: Option<Duration>,
    ) -> Result<Vec<u8>, RpcError>
    where
        Target: Into<WasmCloudEntity>,
    {
        let target = target.into();
        let origin_url = origin.url();
        let subject = make_uuid();
        let issuer = &self.key.public_key();
        let target_url = format!("{}/{}", target.url(), &message.method);
        debug!("rpc_client sending to {}", &target_url);
        let claims = wascap::prelude::Claims::<wascap::prelude::Invocation>::new(
            issuer.clone(),
            subject.clone(),
            &target_url,
            &origin_url,
            &invocation_hash(&target_url, &origin_url, message.method, &message.arg),
        );

        let topic = rpc_topic(&target, &self.lattice_prefix);
        let method = message.method.to_string();
        let invocation = Invocation {
            origin,
            target,
            operation: method.clone(),
            msg: message.arg.into_owned(),
            id: subject,
            encoded_claims: claims.encode(&self.key).unwrap(),
            host_id: self.host_id.clone(),
        };
        trace!("rpc send {}", &target_url);

        let nats_body = crate::serialize(&invocation)?;
        if expect_response {
            let payload = if let Some(timeout) = timeout {
                match tokio::time::timeout(timeout, self.request(&topic, &nats_body)).await {
                    Ok(Ok(result)) => Ok(result),
                    Ok(Err(rpc_err)) => Err(RpcError::Nats(format!(
                        "rpc send error: {}: {}",
                        target_url, rpc_err
                    ))),
                    Err(timeout_err) => {
                        error!("rpc timeout: sending to {}: {}", &target_url, timeout_err);
                        Err(RpcError::Timeout(format!(
                            "sending to {}: {}",
                            &target_url, timeout_err
                        )))
                    }
                }
            } else {
                // no timeout, wait indefinitely or until host times out
                self.request(&topic, &nats_body)
                    .await
                    .map_err(|e| RpcError::Nats(format!("rpc send error: {}: {}", target_url, e)))
            }?;

            let inv_response = crate::deserialize::<InvocationResponse>(&payload).map_err(|e| {
                RpcError::Deser(format!("response to {}: {}", &method, &e.to_string()))
            })?;
            match inv_response.error {
                None => {
                    trace!("rpc ok response from {}", &target_url);
                    Ok(inv_response.msg)
                }
                Some(err) => {
                    // if error is Some(_), we must ignore the msg field
                    error!("rpc error response from {}: {}", &target_url, &err);
                    Err(RpcError::Rpc(err))
                }
            }
        } else {
            self.publish(&topic, &nats_body)
                .await
                .map_err(|e| RpcError::Nats(format!("rpc send error: {}: {}", target_url, e)))?;
            Ok(Vec::new())
        }
    }

    /// Send a nats message and wait for the response.
    /// This can be used for general nats messages, not just wasmbus actor/provider messages.
    /// If this client has a default timeout, and a response is not received within
    /// the appropriate time, an error will be returned.
    pub async fn request(&self, subject: &str, data: &[u8]) -> Result<Vec<u8>, RpcError> {
        use std::borrow::Borrow as _;

        let bytes = match self.client.borrow() {
            NatsClientType::Async(ref nats) => {
                let resp = if let Some(timeout) = self.timeout {
                    nats.request_timeout(subject, data, timeout)
                        .await
                        .map_err(|e| RpcError::Nats(e.to_string()))?
                } else {
                    nats.request(subject, data)
                        .await
                        .map_err(|e| RpcError::Nats(e.to_string()))?
                };
                resp.data
            }
        };
        Ok(bytes)
    }

    /// Send a nats message with no reply-to. Do not wait for a response.
    /// This can be used for general nats messages, not just wasmbus actor/provider messages.
    pub async fn publish(&self, subject: &str, data: &[u8]) -> Result<(), RpcError> {
        use std::borrow::Borrow as _;

        match self.client.borrow() {
            NatsClientType::Async(nats) => nats
                .publish(subject, data)
                .await
                .map_err(|e| RpcError::Nats(e.to_string()))?,
        }
        Ok(())
    }
}

pub(crate) fn invocation_hash(
    target_url: &str,
    origin_url: &str,
    method: &str,
    args: &[u8],
) -> String {
    let mut context = Context::new(&SHA256);
    context.update(origin_url.as_bytes());
    context.update(target_url.as_bytes());
    context.update(method.as_bytes());
    context.update(args);
    let digest = context.finish();
    data_encoding::HEXUPPER.encode(digest.as_ref())
}

/// Create a new random uuid for invocations.
/// Internally this (currently) uses the uuid crate, which uses 'getrandom',
/// which uses the operating system's random number generator.
/// See https://docs.rs/getrandom/0.2.3/getrandom/ for details
#[doc(hidden)]
pub fn make_uuid() -> String {
    use uuid::Uuid;
    // uuid uses getrandom, which uses the operating system's RNG
    // as the source of random numbers.
    Uuid::new_v4()
        .to_simple()
        .encode_lower(&mut Uuid::encode_buffer())
        .to_string()
}

/// A Json message (method, args)
struct JsonMessage<'m>(&'m str, JsonValue);

impl<'m> TryFrom<JsonMessage<'m>> for Message<'m> {
    type Error = RpcError;

    /// convert json message to rpc message (msgpack)
    fn try_from(jm: JsonMessage<'m>) -> Result<Message<'m>, Self::Error> {
        let arg = json_to_args::<JsonValue>(jm.1)?;
        Ok(Message {
            method: jm.0,
            arg: std::borrow::Cow::Owned(arg),
        })
    }
}

/// convert json args to msgpack
fn json_to_args<T>(v: JsonValue) -> Result<Vec<u8>, RpcError>
where
    T: Serialize,
    T: DeserializeOwned,
{
    crate::serialize(
        &serde_json::from_value::<T>(v)
            .map_err(|e| RpcError::Deser(format!("invalid params: {}.", e)))?,
    )
}

/// convert message response to json
fn response_to_json<T>(msg: &[u8]) -> Result<JsonValue, RpcError>
where
    T: Serialize,
    T: DeserializeOwned,
{
    serde_json::to_value(crate::deserialize::<T>(msg)?)
        .map_err(|e| RpcError::Ser(format!("response serialization : {}.", e)))
}
