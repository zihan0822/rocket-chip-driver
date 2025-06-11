# Patronus


[![Crates.io Version](https://img.shields.io/crates/v/patronus)](https://crates.io/crates/patronus)
[![docs.rs](https://img.shields.io/docsrs/patronus)](https://docs.rs/patronus)
[![GitHub License](https://img.shields.io/github/license/ekiwi/patronus)](LICENSE)



### TODO

Some things we will hopefully get to one day.

- simulator
  - JIT based implementation
  - better debugging, add option to print expressions with trace
  - waveform generation
  - quickly update only parts of the circuit


#### API Changes

- `patronus::btor2::parse_file` should take in a `Context` instead of producing one
- `Context` should use `RefCell` to allow expressions to be built with a immutable reference