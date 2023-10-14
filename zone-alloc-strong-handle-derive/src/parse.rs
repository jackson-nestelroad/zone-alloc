use proc_macro2::{
    Ident,
    Span,
};
use syn::{
    parse::{
        Parse,
        ParseStream,
    },
    Data,
    DeriveInput,
    Error,
    Fields,
    Result,
};

pub struct Input {
    pub ident: Ident,
}

impl Parse for Input {
    fn parse(input: ParseStream) -> Result<Self> {
        let call_site = Span::call_site();
        let derive_input = DeriveInput::parse(input)?;
        let data = match derive_input.data {
            Data::Struct(data) => data,
            _ => return Err(Error::new(call_site, "input must be a struct")),
        };

        let fields = match data.fields {
            Fields::Unnamed(fields) => fields.unnamed,
            _ => {
                return Err(Error::new(
                    call_site,
                    "input must be a tuple struct with unnamed fields",
                ))
            }
        };
        if fields.is_empty() || fields.len() > 1 {
            return Err(Error::new(
                call_site,
                "input must have exactly one unnamed field",
            ));
        }

        Ok(Input {
            ident: derive_input.ident,
        })
    }
}
