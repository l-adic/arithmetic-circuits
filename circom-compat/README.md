## circom-compat

This library provides a compatibility layer between the `arithmetic-circuits` library/DSL and the [circom](https://docs.circom.io/) toolchain. Specifically it provides:
  1. Binary codecs for the core circom type (e.g. R1CS and Witness files)
  2. A method to generate circom-compatible witness solvers (e.g. native executables and wasm binaries).

This allows you to take advantage of any proving system that was designed to work with circom. To see an example of how this can be used, check out the [arkworks-demo](https://github.com/l-adic/arkworks-demo) or the [factors](https://github.com/l-adic/factors) sample application.
