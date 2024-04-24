# Arithmetic Circuits

A Haskell library for building ZK programs

## Contents
- High level expression language DSL for writing ZK programs
- Low level arithmetic circuit DSL
- Efficient constraint solver for arbitrary circuits
- Binary codecs for core types (R1CS, witness, etc) which are compatible with the Circom toolchain
- Witness generator which is WASM compatible with Circom witness generator binaries.

## Examples
There are examples in `test` directory. See the sudoky verifier for the most complete example.

### Note about WASM target
Circom is a language/compiler which has been widely adopted by developers building ZK programs. As such, many proving frameworks (e.g. arkworks, snarkjs, nova) have integrations with Circom that expect a certain binary serialization format for the r1cs and witness data. The Circom compiler also emits a witness calculator in the form of a WASM binary, which is meant to be embedded in a host environment (e.g. the browser, a rust program, etc). In the `circom-compat` library in this repo, we give the scaffolding that you need in order to produce this binary via GHC's WASM backend. You can see an example of how to use it [here](https://github.com/l-adic/factors) 


### Attributions
This work started as a fork from the original [arithmetic-circuits](https://github.com/sdiehl/arithmetic-circuits) library which is no longer developed. Since there is currently no hope for merging changes upstream and GitHub forks have limited PM functionality, this repo has been severed. All good ideas surrounding the low-level circuit DSL come from those effors, and the supporting libs created by those original authors (e.g. galois-fields lib) are heavily used. You can find their original README in the `docs` folder. Much credit goes to them, in the event they revive the original libraries then PRs will be made.
