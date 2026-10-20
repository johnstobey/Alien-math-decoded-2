# Independent Duodenary Mathematics

An independent Lean 4 project about finite residue rings and binary vectors.
No predecessor project is a source or dependency.

## Mathematical scope

- `ModularCore`: reduction into `ZMod 12` and `ZMod 144`, addition preservation
  and closure, residue identities, station-11 predecessor identities, and
  explicit nonzero zero-divisors.
- `BinaryStructure`: vectors `Fin 12 → ZMod 2`, Hamming weight, the bound 12,
  maximum weight exactly when every coordinate is 1, and the general layer
  cardinality `Nat.choose 12 k` (including weights 0, 1, and 12).
- `MappingBoundary`: an explicit internal map from natural addition to modular
  addition; a general image-closure theorem **assuming** operation preservation;
  and a level-return statement **assuming** the stated level and step values.

No external paper-to-model map is defined or claimed. Establishing one would
require precise source operations, an explicit map, and a preservation proof.
The conditional theorems do not establish those hypotheses for any external source.

## Reproduce

Install [elan](https://github.com/leanprover/elan), then from this directory:

```sh
lake update
lake exe cache get
lake build
python3 scripts/audit.py
```

`lean-toolchain` pins Lean 4.14.0. `lake-manifest.json` locks mathlib v4.14.0
at `4bbdccd9c5f862bf90ff12f0a9e2c8be032b9a84` and all transitive Git dependencies.
For routine builds, use the committed manifest without running `lake update`.
The cache accelerates dependency compilation; if unavailable, `lake build`
compiles dependencies from their locked sources.

The audit inventories all project theorem declarations, prints their exact
elaborated statements, proof terms, direct dependencies, and transitive axioms,
and fails on placeholders or unexpected axioms. Only `propext`, `Classical.choice`,
and `Quot.sound` are permitted. No project proof uses native evaluation.

GitHub Actions builds and audits on pushes and pull requests. Local and remote
verification outcomes are recorded in `verification/STATUS.md`; a configured
workflow alone is not evidence of a successful remote run.
