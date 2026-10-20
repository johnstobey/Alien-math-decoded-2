# Obligation 1.14: checked compiler component

Complete code: `IndependentDuodenary/PostMicrocode.lean`.
Boundary checks: `examples/PostMicrocodeBoundary.lean`.
This adds 17 named library declarations, for a total of 447. The general
obligation 1.14 is still open, with its original acceptance criterion unchanged.

## Concrete source and target machines

The source `WriteMoveMachine s` is a single-tape, four-symbol transition table
with s+1 states and initial state zero. A transition reads the current symbol,
then either halts or supplies a new state, symbol to write, and left/stay/right
movement. Writing occurs before movement. The tape is Mathlib's unbounded
`Turing.Tape (Fin 4)`, with the same initial input placement as the target.

The target is the actual existing type `PrizeMachine (4*s+3)`, containing
4*(s+1) control states and four tape symbols. A computable finite equivalence
maps the pair of source-state and phase to these Fin labels. The initial pair
maps to the default initial label, so there is no extra initialization step.

Phase zero fetches an instruction and writes its symbol. Phase one implements
stay by writing the already-current symbol; phase two moves left; phase three
moves right. Each finishing phase returns to phase zero in the new source
state. Only phase zero can halt. The table explicitly defines every state/symbol
case; no target transition is left unspecified.

## Statements and verification

`post_micro_instruction` and `post_micro_actual_step` establish the two-step
simulation of a source instruction, including an explicit intermediate target
configuration. `post_micro_actual_run` and `post_compiler_actual_run` lift a run
of n actual source transitions to 2*n actual target transitions. Thus the cost
factor does not count padded iterations after halting as executed instructions.

`post_micro_prize_step`, `post_micro_prize_tick` and the iteration lemma justify
the finite control relabeling. `post_compiler_run` proves, for every table M,
input word and natural n:

    prizeRun (compileWriteMove M) input (2*n)
      = microPrizeConfiguration (microLift (writeMoveRun M input n)).

This saturated-iterator theorem also covers initially halted inputs. At those
macrostep boundaries, `post_compiler_accepts` preserves the head-symbol
acceptance condition and `post_compiler_halts` preserves halting. Pending phases
cannot halt, as separately proved in `post_micro_pending_not_halted`.

`post_compiler_polynomial_bound` doubles the coefficient and leaves the exponent
unchanged: t <= c(N+1)^d implies 2*t <= (2*c)(N+1)^d.

Boundary examples exercise all three moves, writing before movement, blank
extension, preservation of an adjacent symbol, no premature halt after writing
an accepting symbol, immediate halting and zero-time initialization.

## Exact remaining scope

This is a complete compiler for the explicitly defined single-tape four-symbol
source. It is only a component of the registered compiler from the multi-tape
`ReferenceDeterministicMachine`. It does not yet supply:

- a tape-block encoding for arbitrary `Fin (a+3)` source alphabets;
- a single-tape encoding of all source tapes, head markers and control;
- an initialization algorithm and simulation relation for those layouts;
- the choice-certificate-controlled branch implementation;
- polynomial resource bounds for those additional constructions.

No ring or phase interpretation is assumed to provide these missing algorithms.
Acceptance normalization from 1.13 remains available for the eventual compiler,
but its configuration type is not silently identified with this source model.
The general SAT-to-protocol reduction is also still absent. All 64 registered
open entries retain their original status and acceptance criteria.

## Reproduce

    lake build
    lake env lean IndependentDuodenary/PostMicrocode.lean
    lake env lean examples/PostMicrocodeBoundary.lean
    python3 scripts/audit.py

The theorem audit prints exact elaborated propositions, proof terms and direct
dependencies. Exported bundles include strict source and boundary checks; the
fresh-build verifier also runs the new boundary file.
