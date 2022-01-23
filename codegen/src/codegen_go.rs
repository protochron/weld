//! Go language code-generator
//!
#[cfg(feature = "wasmbus")]
use crate::wasmbus_model::Wasmbus;
use crate::{
    config::{LanguageConfig, OutputLanguage},
    error::{print_warning, Error, Result},
    gen::{CodeGen, SourceFormatter},
    model::{
        get_operation, get_sorted_fields, get_trait, has_default, is_opt_namespace,
        serialization_trait, value_to_json, wasmcloud_model_namespace, CommentKind, PackageName,
        Ty,
    },
    render::Renderer,
    wasmbus_model::{CodegenRust, Serialization},
    writer::Writer,
    BytesMut, JsonValue, ParamMap,
};
use atelier_core::model::shapes::ShapeKind;
use atelier_core::{
    model::{
        shapes::{
            AppliedTraits, HasTraits, ListOrSet, Map as MapShape, MemberShape, Operation, Service,
            Simple, StructureOrUnion,
        },
        values::Value,
        HasIdentity, Identifier, Model, NamespaceID, ShapeID,
    },
    prelude::{
        prelude_namespace_id, prelude_shape_named, PRELUDE_NAMESPACE, SHAPE_BIGDECIMAL,
        SHAPE_BIGINTEGER, SHAPE_BLOB, SHAPE_BOOLEAN, SHAPE_BYTE, SHAPE_DOCUMENT, SHAPE_DOUBLE,
        SHAPE_FLOAT, SHAPE_INTEGER, SHAPE_LONG, SHAPE_PRIMITIVEBOOLEAN, SHAPE_PRIMITIVEBYTE,
        SHAPE_PRIMITIVEDOUBLE, SHAPE_PRIMITIVEFLOAT, SHAPE_PRIMITIVEINTEGER, SHAPE_PRIMITIVELONG,
        SHAPE_PRIMITIVESHORT, SHAPE_SHORT, SHAPE_STRING, SHAPE_TIMESTAMP, TRAIT_DEPRECATED,
        TRAIT_DOCUMENTATION, TRAIT_TRAIT, TRAIT_UNSTABLE,
    },
};
use std::{collections::HashMap, path::Path, str::FromStr, string::ToString};
//
const WASMBUS_RPC_PKG: &str = "wasmbus_rpc";

//const DEFAULT_SET_TYPE: &str = "std::collections::BTreeSet";
//const DEFAULT_DOCUMENT_TYPE: &str = "Vec<u8>";
//
#[derive(Default)]
pub struct GoCodeGen<'model> {
    /// if set, limits declaration output to this namespace only
    pub(crate) namespace: Option<NamespaceID>,
    pub(crate) packages: HashMap<String, PackageName>,
    pub(crate) import_core: String,
    pub(crate) model: Option<&'model Model>,
}

impl<'model> GoCodeGen<'model> {
    pub fn new(model: Option<&'model Model>) -> Self {
        Self {
            model,
            namespace: None,
            packages: HashMap::default(),
            import_core: String::default(),
        }
    }

    /// field type, wrapped with Option if field is not required
    pub(crate) fn field_type_string(&self, field: &MemberShape) -> Result<String> {
        self.type_string(if is_optional_type(field) {
            Ty::Opt(field.target())
        } else {
            Ty::Shape(field.target())
        })
    }

    /// Write a type name, a primitive or defined type, with or without deref('&') and with or without Option<>
    pub(crate) fn type_string(&self, ty: Ty<'_>) -> Result<String> {
        let mut s = String::new();
        match ty {
            Ty::Opt(id) => {
                //s.push_str("Option<");
                //s.push_str(&self.type_string(Ty::Shape(id))?);
                //s.push('>');
            }
            Ty::Ref(id) => {
                s.push('&');
                s.push_str(&self.type_string(Ty::Shape(id))?);
            }
            Ty::Shape(id) => {
                let name = id.shape_name().to_string();
                if id.namespace() == prelude_namespace_id() {
                    let ty = match name.as_ref() {
                        // Document are  Blob
                        SHAPE_BLOB => "[]byte",
                        SHAPE_BOOLEAN | SHAPE_PRIMITIVEBOOLEAN => "bool",
                        SHAPE_STRING => "string",
                        SHAPE_BYTE | SHAPE_PRIMITIVEBYTE => "int8",
                        SHAPE_SHORT | SHAPE_PRIMITIVESHORT => "int16",
                        SHAPE_INTEGER | SHAPE_PRIMITIVEINTEGER => "int32",
                        SHAPE_LONG | SHAPE_PRIMITIVELONG => "int64",
                        SHAPE_FLOAT | SHAPE_PRIMITIVEFLOAT => "float32",
                        SHAPE_DOUBLE | SHAPE_PRIMITIVEDOUBLE => "float64",
                        // if declared as members (of a struct, list, or map), we don't have trait data here to write
                        // as anything other than a blob. Instead, a type should be created for the Document that can have traits,
                        // and that type used for the member. This should probably be a lint rule.
                        SHAPE_DOCUMENT => "[]byte", // FIXME
                        SHAPE_TIMESTAMP => "time.Time",
                        SHAPE_BIGINTEGER => {
                            // FIXME: NOT IMPLEMENTED
                            return Err(Error::UnsupportedBigInteger);
                        }
                        SHAPE_BIGDECIMAL => {
                            // FIXME: NOT IMPLEMENTED
                            return Err(Error::UnsupportedBigDecimal);
                        }
                        _ => return Err(Error::UnsupportedType(name)),
                    };
                    s.push_str(ty);
                } else if id.namespace() == wasmcloud_model_namespace() {
                    match name.as_bytes() {
                        b"U64" | b"U32" | b"U16" | b"U8" => {
                            s.push_str("uint");
                            s.push_str(&name)
                        }
                        b"I64" | b"I32" | b"I16" | b"I8" => {
                            s.push_str("int");
                            s.push_str(&name)
                        }
                        _ => {
                            if self.namespace.is_none()
                                || self.namespace.as_ref().unwrap() != wasmcloud_model_namespace()
                            {
                                s.push_str(&self.import_core);
                                s.push_str(".model.");
                            }
                            s.push_str(&self.to_type_name(&name));
                        }
                    };
                } else if self.namespace.is_some()
                    && id.namespace() == self.namespace.as_ref().unwrap()
                {
                    // we are in the same namespace so we don't need to specify namespace
                    s.push_str(&self.to_type_name(&id.shape_name().to_string()));
                } else {
                    match self.packages.get(&id.namespace().to_string()) {
                        Some(PackageName {
                            crate_name: Some(crate_name),
                            ..
                        }) => {
                            // the crate name should be valid rust syntax. If not, they'll get an error with rustc
                            s.push_str(crate_name);
                            s.push_str("::");
                            s.push_str(&self.to_type_name(&id.shape_name().to_string()));
                        }
                        _ => {
                            return Err(Error::Model(format!("undefined crate for namespace {} for symbol {}. Make sure codegen.toml includes all dependent namespaces, and that the dependent .smithy file contains package metadata with crate: value",
                                                            &id.namespace(), &id)));
                        }
                    }
                }
            }
        }
        Ok(s)
    }
}

impl<'model> CodeGen for GoCodeGen<'model> {
    fn output_language(&self) -> OutputLanguage {
        OutputLanguage::Go
    }
    /// Initialize code generator and renderer for language output.j
    /// This hook is called before any code is generated and can be used to initialize code generator
    /// and/or perform additional processing before output files are created.
    fn init(
        &mut self,
        model: Option<&Model>,
        _lc: &LanguageConfig,
        _output_dir: &Path,
        _renderer: &mut Renderer,
    ) -> std::result::Result<(), Error> {
        self.namespace = None;
        //self.import_core = WASMBUS_RPC_CRATE.to_string();

        if let Some(model) = model {
            if let Some(packages) = model.metadata_value("package") {
                //let packages: Vec<PackageName> = serde_json::from_value(value_to_json(packages))
                //    .map_err(|e| Error::Model(format!("invalid metadata format for package, expecting format '[{{namespace:\"org.example\",crate:\"path::module\"}}]':  {}", e)))?;
                //for p in packages.iter() {
                //    self.packages.insert(p.namespace.to_string(), p.clone());
                //}
            }
        }
        Ok(())
    }

    fn source_formatter(&self) -> Result<Box<dyn SourceFormatter>> {
        Ok(Box::new(crate::format::GoSourceFormatter::default()))
    }

    /// Perform any initialization required prior to code generation for a file
    /// `model` may be used to check model metadata
    /// `id` is a tag from codegen.toml that indicates which source file is to be written
    /// `namespace` is the namespace in the model to generate
    #[allow(unused_variables)]
    fn init_file(
        &mut self,
        w: &mut Writer,
        model: &Model,
        file_config: &crate::config::OutputFile,
        params: &ParamMap,
    ) -> Result<()> {
        self.namespace = match &file_config.namespace {
            Some(ns) => Some(NamespaceID::from_str(ns)?),
            None => None,
        };
        if let Some(ref ns) = self.namespace {
            if self.packages.get(&ns.to_string()).is_none() {
                print_warning(&format!(
                    concat!(
                        "no package metadata defined for namespace {}.",
                        " Add a declaration like this at the top of fhe .smithy file: ",
                        " metadata package = [ {{ namespace: \"{}\", crate: \"crate_name\" }} ]"
                    ),
                    ns, ns
                ));
            }
        }
        //self.import_core = match params.get("crate") {
        //    Some(JsonValue::String(c)) if c == WASMBUS_RPC_CRATE => "crate".to_string(),
        //    _ => WASMBUS_RPC_CRATE.to_string(),
        //};
        Ok(())
    }

    fn write_source_file_header(
        &mut self,
        w: &mut Writer,
        model: &Model,
        _params: &ParamMap,
    ) -> Result<()> {
        //cfg_if::cfg_if! {
        //    if #[cfg(feature = "cbor")] {
        //        let import_cbor = "minicbor,";
        //    }  else {
        //        let import_cbor = "";
        //    }
        //}
        w.write(
            r#"// This file is generated automatically using wasmcloud/weld-codegen and smithy model definitions
               //
            "#);
        match &self.namespace {
            Some(n) if n == wasmcloud_model_namespace() => {
                // the base model has minimal dependencies
                //   w.write(
                //       r#"
                //   #![allow(dead_code, unused_imports, clippy::ptr_arg, clippy::needless_lifetimes)]
                //   use serde::{{Deserialize, Serialize}};
                //"#,
                //   );
            }
            _ => {
                // all others use standard frontmatter

                // special case for imports:
                // if the crate we are generating is "wasmbus_rpc" then we have to import it with "crate::".
                //w.write(&format!(
                //    r#"
                //#![allow(unused_imports, clippy::ptr_arg, clippy::needless_lifetimes)]
                //use {}::{{
                //    Context, deserialize, serialize, MessageDispatch, RpcError, RpcResult,
                //    Timestamp, Transport, Message, SendOpts, {}
                //}};
                //use serde::{{Deserialize, Serialize}};
                //use async_trait::async_trait;
                //use std::{{borrow::Cow, io::Write, string::ToString}};
                //"#,
                //    &self.import_core, import_cbor,
                //));
            }
        }
        w.write(
            r#"
package lib

import "time"

import "github.com/vmihailenco/msgpack/v5"
             "#,
        );
        w.write(&format!(
            "\nconst SMITHY_VERSION = \"{}\"\n\n",
            model.smithy_version(),
        ));
        //w.write(&format!(
        //    "\npub const SMITHY_VERSION : &str = \"{}\";\n\n",
        //    model.smithy_version()
        //));
        Ok(())
    }

    //fn declare_types(&mut self, w: &mut Writer, model: &Model, _params: &ParamMap) -> Result<()> {
    //    let ns = self.namespace.clone();

    //    let mut shapes = model
    //        .shapes()
    //        .filter(|s| is_opt_namespace(s.id(), &ns))
    //        .map(|s| (s.id(), s.traits(), s.body()))
    //        .collect::<ShapeList>();
    //    // sort shapes (they are all in the same namespace if ns.is_some(), which is usually true)
    //    shapes.sort_by_key(|v| v.0);

    //    for (id, traits, shape) in shapes.into_iter() {
    //        match shape {
    //            ShapeKind::Simple(simple) => {
    //                self.declare_simple_shape(w, id.shape_name(), traits, simple)?;
    //            }
    //            ShapeKind::Map(map) => {
    //                self.declare_map_shape(w, id.shape_name(), traits, map)?;
    //            }
    //            ShapeKind::List(list) => {
    //                self.declare_list_or_set_shape(
    //                    w,
    //                    id.shape_name(),
    //                    traits,
    //                    list,
    //                    DEFAULT_LIST_TYPE,
    //                )?;
    //            }
    //            ShapeKind::Set(set) => {
    //                self.declare_list_or_set_shape(
    //                    w,
    //                    id.shape_name(),
    //                    traits,
    //                    set,
    //                    DEFAULT_SET_TYPE,
    //                )?;
    //            }
    //            ShapeKind::Structure(strukt) => {
    //                self.declare_structure_shape(w, id.shape_name(), traits, strukt)?;
    //            }
    //            ShapeKind::Operation(_)
    //            | ShapeKind::Resource(_)
    //            | ShapeKind::Service(_)
    //            | ShapeKind::Union(_)
    //            | ShapeKind::Unresolved => {}
    //        }
    //        cfg_if::cfg_if! {
    //            if #[cfg(feature = "cbor")] {
    //                if !traits.contains_key(&prelude_shape_named(TRAIT_TRAIT).unwrap()) {
    //                    self.declare_shape_encoder(w, id, shape)?;
    //                    self.declare_shape_decoder(w, id, shape)?;
    //                }
    //            }
    //        }
    //    }
    //    Ok(())
    //}

    //fn write_services(&mut self, w: &mut Writer, model: &Model, _params: &ParamMap) -> Result<()> {
    //    let ns = self.namespace.clone();
    //    for (id, traits, shape) in model
    //        .shapes()
    //        .filter(|s| is_opt_namespace(s.id(), &ns))
    //        .map(|s| (s.id(), s.traits(), s.body()))
    //    {
    //        if let ShapeKind::Service(service) = shape {
    //            self.write_service_interface(w, model, id.shape_name(), traits, service)?;
    //            self.write_service_receiver(w, model, id.shape_name(), traits, service)?;
    //            self.write_service_sender(w, model, id.shape_name(), traits, service)?;
    //        }
    //    }
    //    Ok(())
    //}

    /// Write a single-line comment
    fn write_comment(&mut self, w: &mut Writer, kind: CommentKind, line: &str) {
        w.write(match kind {
            CommentKind::Documentation => "// ",
            CommentKind::Inner => "// ",
            CommentKind::InQuote => "// ",
        });
        w.write(line);
        w.write(b"\n");
    }

    /// returns Go source file extension "go"
    fn get_file_extension(&self) -> &'static str {
        "go"
    }
}

/// returns true if the file path ends in ".go"
#[allow(clippy::ptr_arg)]
pub(crate) fn is_go_source(path: &Path) -> bool {
    match path.extension() {
        Some(s) => s.to_string_lossy().as_ref() == "go",
        _ => false,
    }
}

/// is_optional_type determines whether the field should be wrapped in Option<>
/// the value is true if it has an explicit `box` trait, or if it's
/// un-annotated and not one of (boolean, byte, short, integer, long, float, double)
pub(crate) fn is_optional_type(field: &MemberShape) -> bool {
    field.is_boxed()
        || (!field.is_required()
            && ![
                "Boolean", "Byte", "Short", "Integer", "Long", "Float", "Double",
            ]
            .contains(&field.target().shape_name().to_string().as_str()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() -> Result<()> {
        let model = r#"
namespace example.weather

/// Provides weather forecasts.
@paginated(inputToken: "nextToken", outputToken: "nextToken",
           pageSize: "pageSize")
service Weather {
    version: "2006-03-01",
    resources: [City],
    operations: [GetCurrentTime]
}

resource City {
    identifiers: { cityId: CityId },
    read: GetCity,
    list: ListCities,
    resources: [Forecast],
}

resource Forecast {
    identifiers: { cityId: CityId },
    read: GetForecast,
}

// "pattern" is a trait.
@pattern("^[A-Za-z0-9 ]+$")
string CityId

@readonly
operation GetCity {
    input: GetCityInput,
    output: GetCityOutput,
    errors: [NoSuchResource]
}

@input
structure GetCityInput {
    // "cityId" provides the identifier for the resource and
    // has to be marked as required.
    @required
    cityId: CityId
}

@output
structure GetCityOutput {
    // "required" is used on output to indicate if the service
    // will always provide a value for the member.
    @required
    name: String,

    @required
    coordinates: CityCoordinates,
}

// This structure is nested within GetCityOutput.
structure CityCoordinates {
    @required
    latitude: Float,

    @required
    longitude: Float,
}

// "error" is a trait that is used to specialize
// a structure as an error.
@error("client")
structure NoSuchResource {
    @required
    resourceType: String
}

// The paginated trait indicates that the operation may
// return truncated results.
@readonly
@paginated(items: "items")
operation ListCities {
    input: ListCitiesInput,
    output: ListCitiesOutput
}

@input
structure ListCitiesInput {
    nextToken: String,
    pageSize: Integer
}

@output
structure ListCitiesOutput {
    nextToken: String,

    @required
    items: CitySummaries,
}

// CitySummaries is a list of CitySummary structures.
list CitySummaries {
    member: CitySummary
}

// CitySummary contains a reference to a City.
@references([{resource: City}])
structure CitySummary {
    @required
    cityId: CityId,

    @required
    name: String,
}

@readonly
operation GetCurrentTime {
    input: GetCurrentTimeInput,
    output: GetCurrentTimeOutput
}

@input
structure GetCurrentTimeInput {}

@output
structure GetCurrentTimeOutput {
    @required
    time: Timestamp
}

@readonly
operation GetForecast {
    input: GetForecastInput,
    output: GetForecastOutput
}

// "cityId" provides the only identifier for the resource since
// a Forecast doesn't have its own.
@input
structure GetForecastInput {
    @required
    cityId: CityId,
}

@output
structure GetForecastOutput {
    chanceOfRain: Float
}
    "#;
        use std::collections::BTreeMap;
        use std::fs;
        use std::path::PathBuf;

        let mut assembler = atelier_assembler::ModelAssembler::default();

        fs::write("/tmp/model", model).expect("unable to write file");
        assembler.push(Path::new("/tmp/model"));
        let smithy: Model = assembler
            .try_into()
            .map_err(|e| Error::Model(format!("assembling model: {:#?}", e)))?;
        let mut go_gen = GoCodeGen::default();
        let params = BTreeMap::new();
        let out = go_gen.generate_file(
            &smithy,
            &crate::config::OutputFile {
                create_only: false,
                namespace: None,
                hbs: None,
                path: PathBuf::from(r"/tmp/gen.go"),
                params: params,
            },
            &crate::ParamMap::new(),
        )?;
        fs::write("/tmp/gen.go", out);

        Ok(())
    }
}
