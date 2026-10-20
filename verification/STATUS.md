# Verification evidence

- Lean: 4.14.0, compiler commit `410fab728470` (Linux release).
- mathlib: v4.14.0, Git commit `4bbdccd9c5f862bf90ff12f0a9e2c8be032b9a84`.
- Project library: twenty-eight modules; 430 theorem declarations.
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
There are no incomplete obligations inside the 430 stated Lean theorems.

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

`RegisterNaturality` and `CanonicalArchitecture` add 37 declarations. Four
existing projection proofs now use the common naturality interface. The
canonical full-state codec, coefficient view and dynamics are injective; the
phase projection alone is proved noninjective. The single canonical file
proves a master invariant and the bounded-error channel envelope, including
original-state recovery by inverse dynamics. See [scope](CANONICAL_ENVELOPE.md).

`PipelineSynthesis` adds eight theorems for arbitrary finite validated station
programs, exact original-state recovery and injectivity. `PipelineHarness`
provides thirteen executable boundary checks, with the native `verifyPipeline`
launcher included in default build targets. See
[integration and closure boundaries](PIPELINE_DEPLOYMENT.md). The local full
build, warning-free checks, fifteen canonical guards, synthesis guards and all
thirteen executable checks passed. The executable output is retained in
`pipeline-execution.txt`.

Final local audit: all 430 theorem declarations passed, permitting only the
standard Lean axiom union already listed. The placeholder scan also covers
the native launcher and example sources. All newly added modules, the
refactored dynamics module and both runners elaborate without diagnostics.

## Q/R packaging boundary

The new bridge and boundary fixture type-check with zero diagnostics. The full
build succeeds but replays existing Mathlib docPrime documentation warnings;
it is not a zero-warning dependency build. See `MILLENNIUM_BRIDGE.md` and
`../packaging/problem_alignment.json` for the unproved complexity obligation.

## S/T translation and archival audit

`protocol_reachability_iff_bounded_search` proves the precise twelve-candidate
reachability equivalence for the fixed structural operator. It does not relate
arbitrary certificate-verifiable languages to this protocol. The LaTeX monograph
includes every declaration and makes the missing complexity bridge explicit.
`scripts/perfect_claim_bundle.sh` adds the compiled PDF, generated theorem
appendix, LaTeX logs and hashes to the existing verified export. It performs no
institutional filing and asserts no CMI compliance. Standard classical axioms
remain in the audited library; constructive-only foundations are not claimed.

## Search-boundary research extension

Four additional declarations establish a Boolean reachability decision and the
lower bound `49152^r ≤ 12 * seeds.card` on complete fixed-operator orbit covers.
That extension brought the library to 354 named declarations. This is not a general
computational lower bound or a prize solution. The administrative dossier at
65e0db1 remains historical; current source and audit evidence are indexed by
`THEOREMS.md` and `SEARCH_BOUNDARY.md`.

## Total parsers and halted-run persistence

Nineteen new declarations close atomic obligations 1.10, 1.11 and 1.12.
See [COMPLEXITY_ENCODING.md](COMPLEXITY_ENCODING.md). At that revision eight of 77 atomic
obligations were discharged; 69 remained open. This does not establish the
general SAT reduction, machine simulation or a Millennium Prize result.

## Reference-machine syntax and complexity definitions

`ReferenceMachines.lean` implements obligations 1.01–1.04 with 13 supporting
theorems. That revision brought the library to 386 named declarations. The register has five
completed example obligations, three proved parser/halting obligations and four
implemented definition obligations: 12 completed, 65 open. Reference P/NP are
explicit definitions, not equivalences with the Prize classes. Full individual
status for all 69 entries open at the start of this execution is retained in
[CLOSURE_EXECUTION.md](CLOSURE_EXECUTION.md).

## Guarded Fulgurite SAT experiment

The new semantic prototype adds 22 theorems: lossless Boolean phase encoding,
formula interpretation and exact AST-size preservation, satisfiability
equivalence, certified bounded rewrite execution and its preservation theorem,
and a no-affine-AND result for the chosen 0/6 encoding. The current count is 408.
All 65 registered open obligations remain open; the target is circuit SAT with
conditional gates, not fixed-operator reachability. See [FULGURITE_SAT.md](FULGURITE_SAT.md).

## Anchored phase-alignment experiment

`examples/PhaseAlignmentBridge.lean` adds 16 experimental declarations checked
separately by `scripts/audit_phase_alignment.py`. They do not change the 408
library inventory or the 65-open obligation count. The code proves rotation
invariance, an anchored sum criterion for AND, conditional-free 0/1 ring
semantics for arbitrary Boolean formulas, both directions of satisfiability
equivalence, lossless assignment encoding and exact cardinality 2^n.
See [PHASE_ALIGNMENT.md](PHASE_ALIGNMENT.md) for the precise scope.

## Acceptance normalization: sequential batch 1.13

Twenty-two new library declarations provide a complete finite local table for
state-output/head-output convention conversion, forward and reverse run
classification, language preservation in each direction and exact one-transition
overhead. Input-independent polynomial witnesses increase c to c+1 and retain d.
The current library count is 430; 13 atomic obligations are completed and 64
remain open. This does not supply the next four-symbol TM0 compiler (1.14).
See [ACCEPTANCE_NORMALIZATION.md](ACCEPTANCE_NORMALIZATION.md).
