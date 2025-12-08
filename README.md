### Patronus: a BTOR2 JIT compiler as a fast RTL Simulator
`Patronus` is a just-in-time (JIT) compiler that consumes BTOR2 inputs lowered from hardward description frontends, such as Verilog and FIRRTL emitted by Chisel,
and can serve as an alternative to existing RTL simulation tools. `Patronus` features fast compilation while preserving simulation speed within acceptable ranges.

#### Repository Layout
* `designs`: Pre-generated Verilog files for different rocket-chip configs
* `patronus`: `Patronus` Rust crate
* `resources`: Verilog resources used in `designs` and C++ resources for simulation 

#### Demo: Running Patronus on RocketChips
#### Prerequisites
* [riscv-toolchain](https://github.com/riscv-collab/riscv-gnu-toolchain/tree/b683d4dec3f6bb2d715e63d78a2a92862e551590): riscv cross-compiler and libc
* [riscv-tests](https://github.com/riscv-software-src/riscv-tests/tree/b5ba87097c42aa41c56657e0ae049c2996e8d8d8): test and benchmark program
* yosys: used to translate Verilog into Btor. Please build it from our [forked version](https://github.com/zihan0822/yosys/tree/btor-fix), 
which includes a few extensions to support translation of large chip designs. 
* git-lfs: used to download large precompiled Verilog and BTOR files for uploaded chip designs. 

```
$ make all
$ ./resources/emulator <rocket-chip-btor-file> <test-elf>
```
* `make all` generates btor file from rocket-chip's Verilog, compiles `Patronus` as a shared library
and links it against the top test driver compiled from `resources/cxx/emulator.cc`.
* `<rocket-chip-btor-file>` can be found in `designs/<config>/TestHarness.btor`.
* `<test-elf>` is compiled from [riscv-tests](https://github.com/riscv-software-src/riscv-tests/tree/b5ba87097c42aa41c56657e0ae049c2996e8d8d8).
  
We recommend starting with tests under `riscv-tests/isa` for a quick demonstration of `Patronus`.
User may also try out bench programs under `riscv-tests/benchmarks`, which might take several minutes to finish.

**Example run**:
```
$ ./resources/emulator -c designs/rocket20/TestHarness.btor $RISCV_TESTS/isa/rv64ui-p-add
```
By default, `Patronus` uses the JIT backend. It also provides an interpreter backend, which can be configured by setting `RUST_DRIVER_FEATURE = interpreter` in `Makefile`,
but it is somewhat discouraged for RocketChip due to its slow speed. 

#### Benchmarking
For a more comprehensive comparison between `Patronus` and other existing RLT simulation tools over multiple metrics, including simulator generation, simulator compilation time and simulation performance, please check out our [benchmarking repo](https://github.com/zihan0822/rtl-sim-bench)!



