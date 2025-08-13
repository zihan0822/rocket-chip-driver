#[macro_export]
macro_rules! declare_module {
    (
        #[in(bundle = $in_bundle:path)]
        #[out(bundle = $out_bundle:path)]
        struct $name:ident  {
            $(
                #[in<$in_width:literal> = $btor_in_port:literal, bundle_field = $in_bundle_field:ident]
                $in_field:ident,
            )*
            $(
                #[out = $btor_out_port:literal, bundle_field = $out_bundle_field:ident]
                $out_field:ident,
            )*
        }
    ) => {
        $crate::declare_module!(
            @__emit_ctor
            struct $name{
                $(
                    #[in<$in_width> = $btor_in_port]
                    $in_field,
                )*
                $(
                    #[out = $btor_out_port]
                    $out_field,
                )*
            }
        );

        impl $name {
            #[allow(dead_code)]
            fn set_input(&self, backend: &mut $crate::SimBackend, input: $in_bundle) {
                $(
                    backend.set(
                        self.$in_field,
                        (&baa::BitVecValue::from_u64(input.$in_bundle_field as _, $in_width)).into()
                    );
                )*
            }

            #[allow(dead_code)]
            fn get_output(&self, backend: &$crate::SimBackend) -> $out_bundle {
                $out_bundle {
                    $($out_bundle_field: backend.get(self.$out_field).try_into_u64().unwrap() as _,)*
                }
            }
        }
    };

    (
        struct $name:ident  {
            $(
                #[in<$in_width:literal> = $btor_in_port:literal, c_type = $in_c_type:ty]
                $in_field:ident,
            )*
            $(
                #[out = $btor_out_port:literal, c_type = $out_c_type:ty]
                $out_field:ident,
            )*
        }
    ) => {
        $crate::declare_module!(
            @__emit_ctor
            struct $name {
                $(
                    #[in<$in_width> = $btor_in_port]
                    $in_field,
                )*
                $(
                    #[out = $btor_out_port]
                    $out_field,
                )*
            }
        );

        impl $name {
            $(
               paste::paste! {
                    #[allow(dead_code)]
                    fn [<set_ $in_field>](&self, backend: &mut $crate::SimBackend, input: $in_c_type) {
                         backend.set(
                             self.$in_field,
                             (&baa::BitVecValue::from_u64(input as _, $in_width)).into()
                         );
                    }
               }
            )*
            $(
                paste::paste! {
                    #[allow(dead_code)]
                    fn [<get_ $out_field>](&self, backend: &$crate::SimBackend) -> $out_c_type {
                        backend.get(self.$out_field).try_into_u64().unwrap() as _
                    }
                }
            )*
        }
    };

    (@__find_state $lookup_method:ident, $port_name:literal, $ctx:ident, $sys:ident) => {
        $sys.$lookup_method($ctx, $port_name)
            .unwrap_or_else(
                || panic!(concat!("unable to find port with name: ", $port_name))
            )
    };

    (@__emit_ctor
        struct $name:ident  {
            $(
                #[in<$in_width:literal> = $btor_in_port:literal]
                $in_field:ident,
            )*
            $(
                #[out = $btor_out_port:literal]
                $out_field:ident,
            )*
        }
    ) => {
        struct $name {
            $($in_field: patronus::expr::ExprRef,)*
            $($out_field: patronus::expr::ExprRef,)*
        }
        impl $name {
            fn from_context_and_system(
                ctx: &patronus::expr::Context,
                sys: &patronus::system::TransitionSystem,
            ) -> Self {
                Self {
                    $($in_field: $crate::declare_module!(@__find_state lookup_input, $btor_in_port, ctx, sys),)*
                    $($out_field: $crate::declare_module!(@__find_state lookup_output, $btor_out_port, ctx, sys),)*
                }
            }
        }
    }
}