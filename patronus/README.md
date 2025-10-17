#### Precompiled Cranelift IR Support
Patronus's `aot-clif` feature lets user inject their own JIT runtime implementation by providing pre-compiled CLIF IR in textual format.
One potential way to generate them is through Rust's CLIF backend and rustc's `--emit=llvm-ir` flag.
[baa-clif-gen](https://github.com/zihan0822/rocket-chip-driver/blob/main/baa-clif-gen) crate demonstrates one possible workflow.
User should guarantee that:
* Their runtime function has the correct signature and is a valid implementation of the original runtime function provided by [baa](https://github.com/zihan0822/rocket-chip-driver/blob/main/patronus/src/sim/jit/runtime.rs).
* Their runtime function has the same unmangled symbol name as the original runtime function for JIT to locate them.
* Their runtime function adheres to C's calling convention, which can be achieved by `extern "C"` in Rust.

Failure to meet any of these requirements can result in JIT fallbacking to its default runtime or incorrect runtime behavior in the jitted code. 

#### Limitation
Current pre-compiled CLIF support is still limited. User should try their best to write their code in a data-section free fashion, i.e avoid allocating const/static data.

#### How To Use
User can set `CLIF_DIRECTORY` env variable to point to the directory containing the `.clif` files of their implementation.
Let's take [baa-clif-gen](https://github.com/zihan0822/rocket-chip-driver/blob/main/baa-clif-gen) as an example.
```shell
# Inside baa-clif-gen crate
# You can't run `cargo build -p baa-clif-gen` from the workspace because it's excluded.
$ cargo build
# Generated clif files are usually under baa-clif-gen/target/debug/deps
$ export CLIF_DIRECTORY=/path/to/baa-clif-gen/target/debug/deps/<build-dependent-directory-name>
# Disable clif loading
$ unset CLIF_DIRECTORY
```

#### Cranelift Function Inlining
Patronus's `inline` feature further inlines user provided CLIF functions. The current policy is simple: inlining every call site recursively.
User can enable logging to inspect loaded and inlined functions by setting
```shell
$ export RUST_LOG=patronus=info
```
