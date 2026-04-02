# Sail Tiny x86

A very simple x86 model

## Repository overview

Generated files
- snapshot/ -> contains Rocq files generated from the Sail specification
- coq-sail-tiny-x86.opam -> generated Opam package definition file

Sail specification
- prelude.sail -> contains general configurations and function definitions
- registers.sail -> contains types, declarations and helper functions for registers
- interface.sail -> functions to request memory effects, using Sail's concurrency interface
- operands.sail -> contains types and helper functions for operands (immediate, register, or memory values)
- decode.sail -> contains the AST, decode types, and most of the decode logic
- tiny-x86.sail -> contains the outer fetch-execute function, and instruction-specific decode and execute definitions
- tests.sail -> contains tests for the decode and execute definitions


## To build
### Installing dependencies
Opam must be installed.
Add the Rocq opam repository to be able to install certain packages:
```
opam repo add rocq-released --set-default https://rocq-prover.org/opam/released
```
Then run
```
opam install .
```

### Building
`make` or `make rocq` generates Rocq files from the Sail specification
`make rocq-snapshot` generates the Rocq files then updates the snapshots to match
`make type-check` checks that the Sail specification type-checks
`make test` generates C code from the Sail specification, including tests.sail, and runs the tests generated from tests.sail