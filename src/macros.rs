/// Define a trait as usual, and a macro with the same name that can be used to
/// expose some internal methods on an opaque wrapping object.
///
/// The methods that are exposed are marked with `@expose` in the trait definition.
macro_rules! exposable_trait {
    ($(#[$doc:meta])* pub trait $name:ident $(<$($generics:tt $(= $generic_val:tt)?),*>)? $(where $($where:ident : $where_args:tt),* $(,)?)? { $($methods:tt)* }) => {

        // This is where the trait definition is reproduced by the macro.
        // It makes the source links point to this place!
        //
        // I'm sorry, you'll have to find the source by looking at the
        // source of the module the trait is defined in.
        //
        // We use this nifty macro so that we can automatically generate
        // delegation trait impls and implement the graph traits for more
        // types and combinators.

        use crate::macros::remove_tags;

        $(#[$doc])*
        pub trait $name $(<$($generics $(= $generic_val)?),*>)? $(where $($where : $where_args),*)? {
            remove_tags! { [] $($methods)* }
        }

        // After it we define a `$trait!` macro that can be used to expose the trait
        // methods on a non-transparent wrapper.

        macro_rules! $name {
            ($extra:tt) => {
                expose_methods! {
                    $extra
                    $($methods)*
                }
            }
        }
    }
}
pub(crate) use exposable_trait;

macro_rules! remove_tags {
    ([$($stack:tt)*]) => {
        $($stack)*;
    };
    ([$($stack:tt)*] @expose $($tail:tt)*) => {
        remove_tags!([$($stack)*] $($tail)*);
    };
    ([$($stack:tt)*] $t:tt $($tail:tt)*) => {
        remove_tags!([$($stack)* $t] $($tail)*);
    };
}
pub(crate) use remove_tags;

/// Implement a trait by delegation. By default as if we are delegating
/// from &G to G.
macro_rules! expose_methods {
    ([$trait_assoc_type:ident, $trait_getter:ident]) => {};
    ([$trait_assoc_type:ident, $trait_getter:ident]
        // Associated types. Not forwarded.
        $(
        [type $assoc_name_ext:ident]
        // Associated types. Forwarded.
        )*
        // Non-forwarded methods. Forwarded. Using $self_map!(self) around the self argument.
        // Methods must use receiver `self` or explicit type like `self: &Self`
        // &self and &mut self are _not_ supported.
        $(
            $(#[$_method_attr:meta])*
            fn $_method_name:ident($($_arg:ident : $_arg_ty:ty),*) $(-> $_ret:ty)? $({$($_body:tt)*})?;
        )?
        // Non-forwarded methods. Forwarded. Using $self_map!(self) around the self argument.
        // Methods must use receiver `self` or explicit type like `self: &Self`
        // &self and &mut self are _not_ supported.
        $(
            @expose
            $(#[$method_attr:meta])*
            fn $method_name:ident($($arg:ident : $arg_ty:ty),*) $(-> $ret:ty)? $({$($body:tt)*})?;
        )?
        // Tail recursion
        $($tail:tt)*
    ) => {
        // Only define the exposed methods, and ignore the rest.
        $(
            $(#[$_method_attr:meta])*
            #[inline(always)]
            fn $method_name($($arg:ident : $arg_ty:ty),*) $(-> $ret)? {
                self.$trait_getter!().$method_name($($arg),*)
            }
        )*
        // Continue with the rest of the trait.
        expose_methods! { [$trait_assoc_type, $trait_getter] $($tail)* }
    };
}
