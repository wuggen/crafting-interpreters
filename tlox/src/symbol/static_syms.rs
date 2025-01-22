use super::Symbol;

macro_rules! static_syms {
    ($($NAME:ident => $sym:expr,)*) => {
        static_syms!(@consts $($NAME => $sym,)*);

        impl Symbol<'_> {
            pub fn resolve_static_sym(sym: &str) -> Option<Symbol<'static>> {
                static_syms! {
                    @match sym {
                        $($NAME => $sym,)*
                    }
                }
            }
        }

        static_syms!(@test $($NAME => $sym,)*);
    };

    (@consts $($NAME:ident => $sym:expr,)*) => {
        $(pub static $NAME: Symbol<'static> = Symbol::mk_static($sym);)*
    };

    (@match $var:ident { $($NAME:ident => $sym:expr,)* }) => {
        match $var {
            $(
                $sym =>  Some($NAME),
            )*
            _ => None,
        }
    };

    (@test $($NAME:ident => $sym:expr,)*) => {
        #[cfg(test)]
        mod test {
            use super::*;
            use crate::sym;
            use crate::session::Session;

            #[test]
            fn static_syms() {
                Session::with_default(|key| {
                    $(assert_eq!($NAME, sym!(key, $sym));)*
                })
            }
        }
    };
}

static_syms! {
    SYM_CLOCK => "clock",
    SYM_THIS => "this",
    SYM_INIT => "init",
}
