# Independent Duodenary Mathematics

An independent Lean 4 project about finite residue rings and binary vectors.
No predecessor project is a source or dependency.

[Proof dependency map and next obligation](verification/PROOF_DEPENDENCY_MAP.md)
connects the supplied claims to the checked results and identifies the remaining gaps.

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
- `TwelveStateStructure`, `AffineStations`, `EncodingIntegrity`: CRT with an
  explicit inverse, the complete cyclic-isometry classification, the 48-element
  affine permutation group, exact-decoding capacity, and a concrete single-error
  correcting repetition codec. See [the structural ledger](verification/STRUCTURAL_LEDGER.md).
- `StationGrammar`, `StationCodec`: a typed operation language with complete
  permutation semantics, exact encoding/decoding on semantic classes, wire
  composition and inverse, and bounded-error recovery. See the
  [worked grammar and codec](verification/STATION_CODEC.md).
- `CipherValidator`: exact arithmetic semantics for the supplied Mod-144
  calculator, periodicity and information-loss proofs, and protected result
  transport. See [source rules and proof boundaries](verification/CIPHER_VALIDATOR.md).
- `SourceKeyRepresentation`: a chosen binary-coordinate cycle of exact order
  twelve, a lossless framed full-key codec, malformed-word rejection, and
  compatible translated-word operations. See [exact scope](verification/KEY_DIRECTIVES.md).
- `RegisterDynamics`, `RegisterBridge`: product operators, subsystem
  projections, exact orbit bounds, and inductive transport of metadata and
  modular relative-phase invariants. See [formal boundaries and dependencies](verification/REGISTER_BRIDGE.md).
- `RegisterNaturality`, `CanonicalArchitecture`: a common naturality interface,
  canonical full-state representation, master invariant induction and bounded-error
  recovery of final and original states. See [exact scope and dependencies](verification/CANONICAL_ENVELOPE.md).
- `PipelineSynthesis`, `PipelineHarness`: arbitrary validated station-program
  composition, exact recovery of initial states, and executable boundary checks.
  See [deployment harness](verification/PIPELINE_DEPLOYMENT.md).
- `MappingBoundary`: an explicit internal map from natural addition to modular
  addition; a general image-closure theorem **assuming** operation preservation;
  and a level-return statement **assuming** the stated level and step values.

The cited source section now has an explicit coefficient model with proved
projection, reduction, folding, and key-sharing identities. The full paper
construction and its Unique Games result are not formalized. Residue-valued
observables require a chosen functional and labeling; no full ring identification
is claimed. Conditional level assumptions are not established for an external source.

## Verification executable

```sh
lake build
lake exe verifyPipeline
```

The executable runs thirteen end-to-end boundary checks and exits nonzero on
failure. See [composition proofs, integration and exact scope](verification/PIPELINE_DEPLOYMENT.md).

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

[Formal alignment and reproducible audit bundles](verification/MILLENNIUM_BRIDGE.md)
state the finite bounds, unproved complexity obligation and release procedure.

The [LaTeX translation monograph](MillenniumPrizeTranslation.tex) and
`scripts/perfect_claim_bundle.sh` provide a PDF audit archive with a complete
theorem index. This does not certify or file a Millennium Prize claim.

[Administrative dossier index](claim_manifest.json),
[cover letter](administrative/COVER_LETTER.md) and
[intake summary](administrative/INTAKE_SUMMARY.md) record the audited baseline
and unresolved prize and legal obligations. Generate a self-contained enclosure
packet with `python3 scripts/build_intake_bundle.py` when the indexed release
assets are present in `dist/`. Verify an extracted packet with the same script's
`--verify-only` option. Large archives remain ignored by Git; a repository clone
alone does not contain those binary enclosures. No institutional filing is made.

[Search-boundary research report](verification/SEARCH_BOUNDARY.md) records the
new reachability decision and global orbit-cover lower bound. The 350-theorem
`claim_manifest.json` and administrative packet remain a historical dossier for
commit `65e0db1`, not an index of subsequent research. Rebuild that historical
packet from its archived revision; current research has its own audit index.

[Atomic bridge specification](verification/ATOMIC_BRIDGE_SPECIFICATION.md)
expands the four missing complexity bridges into 77 explicit obligations and
an acyclic dependency graph. Five initial encoding facts are checked as unnamed
Lean examples. Nineteen named parser and halting theorems additionally close
obligations 1.10–1.12; the library now has 373 named declarations. Eight of 77
atomic obligations are discharged, with 69 open. See the
[parser and halting report](verification/COMPLEXITY_ENCODING.md). The general SAT reduction
and polynomial-time machine proof remain absent.
