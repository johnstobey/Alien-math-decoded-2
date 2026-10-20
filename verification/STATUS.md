# Verification evidence

- Lean: 4.14.0, compiler commit `410fab728470` (Linux release).
- mathlib: v4.14.0, Git commit `4bbdccd9c5f862bf90ff12f0a9e2c8be032b9a84`.
- Project library: eighteen modules; 297 theorem declarations.
- `lake build`: passed, exit status 0; see `local-build.txt`.
- `python3 scripts/audit.py`: passed, exit status 0; see
  `axioms-and-proofs.txt` and the per-theorem index `THEOREMS.md`.
- Axiom union: `propext`, `Classical.choice`, `Quot.sound`; no custom axioms,
  placeholders, or native evaluation. `conditional_closure` and
  `number_372_multiple` have no axioms.
- The full local build, theorem audit and codec walkthrough were executed
  successfully. The reusable setup instructions activate the retained toolchain
  and run the build/audit workflow. No application services or credentials are needed.
- `lake update` succeeded with the supported
  `MATHLIB_NO_CACHE_ON_UPDATE=1` setting. The independent `lake exe cache get`
  attempt failed because the environment proxy returned HTTP 403 for the cache.
  Dependencies were successfully compiled from locked sources instead.

## Remote verification

The committed workflow runs the library build, theorem/axiom audit, and lockfile
stability check on pushes and pull requests. Remote results must be checked
against the exact pushed commit at
<https://github.com/johnstobey/Alien-math-decoded-2/actions>.
A workflow file or a successful local build alone is not CI certification.

## Mathematical scope and remaining obligations

The source coefficient model now proves support factorization and uniqueness,
permitted-projection key compatibility, the free translation action, canonical
representatives, folding, and key sharing. See `SOURCE_MODEL.md` for the exact
primary-source pin, assumptions, and theorem inventory. The restricted binary
bridges and their non-surjectivity obstruction remain proved (`BRIDGE_SCOPE.md`).

The complete Unique Games construction and its theorem remain outside this
formalization. A faithful or surjective map to the full residue rings is not
established; a surjective additive map from an exponent-two source is ruled out.
The level-return theorem still assumes the supplied level and step values.
There are no incomplete obligations inside the 297 stated Lean theorems.

The independent structural ledger is now formalized as described in
`STRUCTURAL_LEDGER.md`, including cyclic/affine symmetries and exact/robust
encoding results. The constructed station-operation grammar now has a complete semantics and
codec, including bounded-error recovery (`STATION_CODEC.md`). A source-specific
natural-language interpretation still requires a proved rule mapping.

The executable station-code walkthrough passed all five guards. It is run by
CI in addition to the build and theorem audit; local output is preserved in
`station-walkthrough.txt`.

The supplied Mod-144 calculator now has an exact positive-rational arithmetic
model, normalized implementation proof, five source fixtures, a noninjectivity
proof, and a lossless protected result codec. See `CIPHER_VALIDATOR.md` for the
source hash, rule mapping and numerical/interpretive boundaries. Both the Lean
cipher walkthrough (nine guards) and five isolated JavaScript fixtures passed.

The [proof dependency map](PROOF_DEPENDENCY_MAP.md) separates the proved
restricted correspondence from the obstructed fixed-fold/twelve-cycle proposal,
the unidentified alternative source operator, and the unformulated external
theorem implication. Its subsequent finite-instance extension supplies lossless structured key
encoding. The original map-only milestone added no Lean declarations.

`SourceKeyRepresentation` adds 34 theorems for the chosen finite key carrier.
Its coordinate permutation has exact global period twelve, with a station
label on a one-hot orbit; it is not identified as an external-source operator.
The framed full-key codec has both round-trip and parse-soundness proofs,
malformed-word rejection, and transported binary translation. See
[exact statements](KEY_DIRECTIVES.md). CI separately requires the new module
to elaborate without diagnostics and checks twelve executable guards. Local
build, all 245 theorem audits, warning-free module elaboration and all twelve
guards passed.

`RegisterDynamics` and `RegisterBridge` add 52 theorems: exact product
operator periods, subsystem compatibility, regular-orbit phase preservation,
noncollapse bounds, product codecs and an inductive modular-invariant bridge.
The external comparator is explicitly equality of relative phases; it is not
a full-key equivalence or an unspecified external theorem. See
[definitions, boundary conditions and dependencies](REGISTER_BRIDGE.md).

For this extension, the local full build and all 297 theorem audits passed.
Both new modules elaborated with zero diagnostics; all twelve register
walkthrough guards passed. The CI workflow repeats the warning-free checks
and walkthrough on the pushed revision.
