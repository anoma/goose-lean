# GOOSE - Good Object Oriented System Experience

This repository contains GOOSE specification in Lean 4. GOOSE provides an object-oriented abstraction on top of the Anoma Resource Machine.

GOOSE consists of three layers:
1. Surface syntax for defining classes, methods, and other object-oriented constructs. The syntax is implemented using Lean 4's macro system and it desugars to the Anoma Virtual Machine (AVM) object structures.
2. Anoma Virtual Machine object structures (`AVM` directory) provide representations of objects, methods, classes, etc. These constitute the AVM object model and are translated to the Anoma Resource Machine structures.
3. Anoma Resource Machine structures (`Anoma` directory).

## Building documentation

1. `cd docbuild`
2. `lake update doc-gen4`
3. `lake build AVM:docs`

After executing the above commands, the documentation will be available in `docbuild/.lake/build/doc`. To view it, change into the `docbuild/.lake/build/doc` directory and run `python3 -m http.server`.
