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
- `BinaryBridge`: explicit additive binary-to-residue maps, exact two-element
  images, injectivity conditions, and obstructions to surjective additive maps
  and unital ring maps. See [the bridge scope](verification/BRIDGE_SCOPE.md).
- `SourceKeys`, `SourceReduction`, `SourceProjection`, `SourceFactorization`:
  exact-key translation, canonical representatives, homogeneous permitted
  projections, support factorization and uniqueness, folding, and key sharing.
  See [the pinned source and proof scope](verification/SOURCE_MODEL.md).
- `MappingBoundary`: an explicit internal map from natural addition to modular
  addition; a general image-closure theorem **assuming** operation preservation;
  and a level-return statement **assuming** the stated level and step values.

The cited source section now has an explicit coefficient model with proved
projection, reduction, folding, and key-sharing identities. The full paper
construction and its Unique Games result are not formalized. Residue-valued
observables require a chosen functional and labeling; no full ring identification
is claimed. Conditional level assumptions are not established for an external source.

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
