# Compositional closure and executable verification package

## O: exact theorem scope

The top-level synthesis module is
[PipelineSynthesis.lean](../IndependentDuodenary/PipelineSynthesis.lean).
It imports the preceding algebraic, source-coefficient, canonical-state and
channel layers. All states and operators retain their existing mathematical
definitions; no biological intelligence predicate is introduced.

For any finite list of validated grammar operations:
\[
\operatorname{compile}([])=\operatorname{id},\qquad
\operatorname{compile}(e::es)=\operatorname{compile}(es)\circ e.
\]

`station_program_compilation` proves equality between sequential execution and
execution of the compiled expression. `stationProgramEquiv` gives an actual
bijection on register words, with the inverse station permutation as inverse.
The input language admits only the existing `StationExpr` constructors, including
unit scaling. Arbitrary noninvertible functions are not silently validated.

For known h, n, and program ops, define
\[
\operatorname{Transmit}(x)=\operatorname{run}(ops,\widehat S_h^{\,n}(E(x))).
\]

`pipeline_master_composition` proves
\[
\operatorname{RegisterNoiseBound}(\operatorname{Transmit}(x),R)
\Longrightarrow
\operatorname{recoverInitial}(h,n,\operatorname{compile}(ops),R)
=\operatorname{some}(x).
\]

The conclusion is exact equality of the recovered original full canonical
state, not merely equality of a phase observation. No regularity hypothesis is
required for this recovery theorem. Initial regularity remains necessary for
the separate phase-evolution laws in the canonical master invariant.

The noise bound pairs each sent symbol with an aligned received triple and
allows at most one substituted symbol in that triple. Register count, triple
alignment, h, n and the program are known protocol parameters. These are
operational boundaries, not unproved decoder-success assumptions.

`pipeline_noiseless_closure` and `pipeline_successor_channel_closure` discharge
the noise premise for repetition transmission and the concrete channel changing
the first position of every triple. `pipeline_transmission_injective` derives
injectivity from the proved left inverse. `pipeline_recovered_state_unique`
proves uniqueness of the recovered canonical state.

`pipeline_empty_transmission_rejected` proves that an empty received row in the
one-register case decodes to none. Since none differs from some(x), an
unconditional recovery statement for every possible received word is false.
The noise/alignment requirement cannot be deleted as a redundant assumption.

## Structural dependencies

```
RegisterNaturality
  → RegisterDynamics → RegisterBridge
  → CanonicalArchitecture
      exact encoding + master induction + station inverse
      + majority channel recovery + inverse structural dynamics
  → PipelineSynthesis
      arbitrary finite station program + exact initial-state closure
  → PipelineHarness
      thirteen concrete executable boundary checks
  → examples/PipelineRunner.lean
      nonzero exit on any failed check
  → PipelineMain.lean / verifyPipeline
      native launcher propagating the Lean runner's output and exit status
```

The general proof terms and transitive axiom lists are in
[axioms-and-proofs.txt](axioms-and-proofs.txt). The executable checks are validation
fixtures; they do not replace the universal kernel-checked theorems.

## P: reproducible build and execution

From the repository root with the pinned Lean toolchain active:

```sh
lake build
python3 scripts/audit.py
lake env lean examples/CanonicalDirectives.lean
lake env lean examples/PipelineDirectives.lean
lake exe verifyPipeline
```

`lakefile.toml` includes the native `verifyPipeline` executable in default build
targets. The library build compiles the synthesis and fixture modules. The native
launcher invokes the Lean runtime for `examples/PipelineRunner.lean`; the runner
executes every Boolean boundary check, prints a PASS line for each success and
raises an error on a failure. The launcher forwards the exact exit code, stdout
and stderr. It avoids requiring native compilation of the entire mathlib proof
library merely to run fixtures. Both launch and execution require the pinned
Lean/Lake installation and the built repository; this is not a toolchain-free
standalone deployment.

The fixture program contains shift, reflection, unit scaling and inverse shift.
Checks cover empty programs, compiled/sequential order, inverse execution,
noiseless transmission, one substitution in every triple, recovery of all key
fields, final phases, protected block count, rejected empty/truncated inputs,
a two-header-errors rejection case, an empty product and an irregular initial
state. The latter checks that full-state recovery does not silently depend on
the phase-regularity hypothesis.

Exact execution output is preserved in
[pipeline-execution.txt](pipeline-execution.txt). The canonical fifteen-guard
harness additionally checks framing restoration and recovery of final and
initial states. CI runs both harnesses and separately requires zero diagnostics
for the new canonical/synthesis modules and native launcher.

## Defined closure boundary

The package proves closure of this finite algebraic protocol under its validated
station programs and specified channel. Phase projection remains explicitly
noninjective. Arbitrary source coefficient tables keep their separate types and
are not automatically encoded into the fixed-key metadata space. No broader
native-intelligence, historical interpretation, or external Millennium theorem
is a consequence asserted by this package.
