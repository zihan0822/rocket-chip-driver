### Patronus Interpreter/JIT Test & Benchmark
We use `Patronus` to simulate [rocket-chip](https://github.com/chipsalliance/rocket-chip) that is able to run RISC-V test and benchmark elfs.

#### Repository Layout
* `designs`: Pre-generated Verilog files for different rocket-chip configs
* `patronus`: Rust crate implementing `Patronus` simulator
* `resources`: Verilog resources used in `designs` and C++ resources for simulation 

#### Prerequisites
* [riscv-toolchain](https://github.com/riscv-collab/riscv-gnu-toolchain/tree/b683d4dec3f6bb2d715e63d78a2a92862e551590): riscv cross-compiler and libc
* [riscv-tests](https://github.com/riscv-software-src/riscv-tests/tree/b5ba87097c42aa41c56657e0ae049c2996e8d8d8): test and benchmark program
* yosys: used to translate Verilog into Btor. Please build it from our [forked version](https://github.com/zihan0822/yosys/tree/btor-fix), 
which includes a few extensions to support translation of large chip designs. 

#### Running Patronus
```
$ make all
$ ./resources/emulator <rocket-chip-btor-file> <test-elf>
```
* `make all` generates btor file from rocket-chip's Verilog, compiles `Patronus` simulator as a shared library
and links it against the top test driver compiled from `resources/cxx/emulator.cc`.
* `<rocket-chip-btor-file>` can be found in `designs/<config>/TestHarness.btor`.
* `<test-elf>` is compiled from [riscv-tests](https://github.com/riscv-software-src/riscv-tests/tree/b5ba87097c42aa41c56657e0ae049c2996e8d8d8).
  
We recommend starting with tests under `riscv-tests/isa` for a quick demonstration of `Patronus` simulator.
User may also try out bench programs under `riscv-tests/benchmarks`, which might take several minutes to finish.

**Example run**:
```
$ ./resources/emulator -c designs/rocket-latest-1GB-RAM/TestHarness.btor $RISCV_TESTS/isa/rv64ui-p-add
```
By default, `Patronus` uses the JIT backend. Interpreter backend can be configured by setting `RUST_DRIVER_FEATURE = interpreter` in `Makefile`,
but it is somewhat discouraged for rocket-chip due to its slow speed. 

#### Running Verilator
We compare `Patronus` against a verilator-based emulator available in our [rocket-chip fork](https://github.com/zihan0822/rocket-chip/tree/verilator-bench).
After finishing rocket-chip specific setup, from the cloned rocket-chip repository:
```
$ make verilog
$ ROCKET_CHIP_DRIVER=<path-to-this-rocket-chip-driver-repo> make emulator
```
* Env variable `ROCKET_CHIP_DRIVER` should be set to point to this repository so both emulators share the same simulation libraries. 
* Compiled emulator elf can be found in `out/emulator/<design>/verilator/elf.dest/emulator`.
* Note that `designs/rocket-latest/TestHarness.sv` is directly adapted from `make verilog` output, with minor modifications to wire up the debug module to accommondate test driver used for `Patronus`.


