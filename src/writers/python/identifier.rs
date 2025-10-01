use core::fmt::Display;

macro_rules! ident_type {
    ($name:ident, $format:literal) => {
        pub(crate) struct $name<'a>(pub(crate) &'a str);
        impl<'a> Display for $name<'a> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                let Self(name) = self;
                write!(f, $format, name)
            }
        }
        impl<'a> $name<'a> {
            pub(crate) fn name(self) -> &'a str {
                self.0
            }
        }
    };
}

ident_type!(PackageStateTypeName, "PackageState_{}");
ident_type!(PackageStateFieldName, "{}");
