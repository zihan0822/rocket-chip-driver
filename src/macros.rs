#[macro_export]
macro_rules! debug_module {
    (
        struct $name:ident  {
            $(
                #[in = $btor_in_port:ident, c_struct_field = $req_c_struct_field:ident]
                $in_field:ident,
            )*
            $(
                #[out = $btor_out_port:ident, c_struct_field = $resp_c_struct_field:ident]
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
                    $($in_field: $crate::debug_module!(@__find_state lookup_input, $btor_in_port, ctx, sys),)*
                    $($out_field: $crate::debug_module!(@__find_state lookup_output, $btor_out_port, ctx, sys),)*
                }
            }

            fn set_input(&self, backend: &mut $crate::SimBackend, request: $crate::ffi::req) {
                $(
                    backend.set(
                        self.$in_field,
                        (&baa::BitVecValue::from_u64(request.$req_c_struct_field as _, 32)).into()
                    );
                )*
            }

            fn get_output(&self, backend: &$crate::SimBackend) -> $crate::ffi::resp {
                $crate::ffi::resp {
                    $($resp_c_struct_field: backend.get(self.$out_field).try_into_u64().unwrap() as _,)*
                }
            }
        }
    };
    (@__find_state $lookup_method:ident, $port_name:ident, $ctx:ident, $sys:ident) => {
        $sys.$lookup_method($ctx, stringify!($port_name))
            .unwrap_or_else(
                || panic!(concat!("unable to find port with name: ", stringify!($port_name)))
            )
    }
}

#[macro_export]
macro_rules! rocket_chip_simulator {
    () => {
        $crate::ROCKET_CHIP_SIMULATOR
            .get()
            .expect("`bootstrap` has never been called")
            .lock()
            .unwrap()
    };
}
