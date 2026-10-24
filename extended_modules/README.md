# Incremental duodenary extensions

This library contains 10,000 uniquely named parameterized specializations of ten
existing theorem families. Unlike `z12z_generated`, its modules share imported
definitions and can all be imported together:

```lean
import extended_modules
```

The generator indexes 447 main-library and 16 experimental declarations using
tracked project sources. It excludes dependency caches and both generated trees.
The ten selected dependency theorems are in `ModularCore` and `BinaryBridge`;
the indexed experimental declarations are not used as dependencies.

Instances vary actual natural-number shifts or binary-vector dimensions. They
cover addition preservation, additive closure, coordinate bridge ranges, and
binary-to-residue surjectivity obstructions. They are specializations of existing
results, not 10,000 independent discoveries or new external-source equivalences.

From the repository root, generate, build, and audit with:

```sh
python3 scripts/generate_incremental_proofs.py --check
```

The default is 10,000 declarations in 100 batches. `--count` and `--batch-size`
also support nonmultiples of 100. The generator refuses to overwrite Lean files
without its ownership header and refuses configuration changes that would leave
stale batches. Without `--check`, validation flags remain false.

`lake build` includes this library as a default target. The aggregate module
imports every batch, so duplicate names or incompatible declarations fail the
build. The checker then inspects every proof's direct constants for its declared
baseline theorem, and audits transitive axioms. Only `propext`, `Classical.choice`,
and `Quot.sound` are permitted. Missing declarations, dependencies, or audit
results fail the run. The successful manifest records source hashes, dependency
provenance, counts, and validation flags. Detailed audit output stays outside
the publication tree in `.lake/incremental-proof-audit.log`.
