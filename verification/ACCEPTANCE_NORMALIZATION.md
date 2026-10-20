# Sequential batch: acceptance-convention normalization (1.13)

Complete code: `IndependentDuodenary/AcceptanceNormalization.lean`.
Boundary checks: `examples/AcceptanceNormalizationBoundary.lean`.
This batch adds 22 named library declarations. The library now has 430; the
separate phase investigation still has 16 experimental declarations.

## Complete finite-control construction

The converted machine retains the original tapes and heads. Its finite control
is the product `Fin (s+2) × Bool`, with exactly `2*(s+2)` states. The Boolean field
records whether the final output-convention transition has executed. Its initial
value is false, independently of the input. `normalizationTable` is a complete
local transition function depending only on that finite control and the finite
tuple of head symbols. It does not inspect global tape contents or query a
language oracle.

While the original state is nonterminal, it executes exactly the original write,
move and state-change instruction. On reaching an original terminal state, it
performs one finishing instruction and sets the flag true. A true flag has no
outgoing transition. The model is a concrete finite-control multi-tape machine;
compilation of this table into the particular four-symbol `PrizeMachine` is
separately required by 1.14. The convention conversion does not claim that
compiler has been constructed.

### State acceptance to halted head output

The finishing instruction writes 1 at the current head of tape zero for an
accepting source state, and writes 2 for a rejecting source state. It keeps all
heads stationary. At every other head it writes the symbol already present.
The output is always Boolean. The acceptance and rejection equivalences are
proved, using the existing assumption that a halted source state is 0 or 1.

### Halted head output to state acceptance

The finishing instruction reads the head of tape zero and enters accepting
state 0 exactly for symbol 1; otherwise it enters rejecting state 1. It leaves
the entire tape contents and all head positions unchanged. On Boolean source
outputs (symbols 1 or 2), both acceptance and rejection correspond exactly.
Invalid output symbols are explicitly classified as reject, not accepted by
an unspecified branch.

## Proof obligations discharged

- `normalization_halted_iff_done`: the computed step is absent exactly when
  the finishing flag is true, so the flag matches actual machine halting.
- `normalization_forward_run`: each source finite run lifts at the same length.
- `normalization_finished_run`: a halted run of t source steps has a completed
  converted run of exactly t+1 steps.
- `normalization_reverse_run`: every converted run is either an unfinished
  lifted source prefix or precisely one source prefix followed by its finishing
  instruction. There are no additional accepted computations.
- `normalization_exact_overhead`: every completed converted run has length
  exactly t+1 for a corresponding halted source run of length t.
- `normalization_state_to_head_language` and
  `normalization_head_to_state_language`: both directions of language
  preservation, with existence quantified over complete actual-transition runs.
- `normalization_polynomial_overhead`: t <= c(N+1)^d implies
  t+1 <= (c+1)(N+1)^d. The new coefficient and unchanged exponent are fixed,
  independent of the input. The result includes N=0, c=0 and d=0.
- `normalization_empty_input`: an initially halted machine on empty input
  completes convention conversion in exactly one transition. More generally,
  the run and language theorems cover any initial configuration, including
  `referenceInitial M.initial []`.

The remaining declarations establish the finite control count, local transition
semantics, stopping, head/tape preservation and output classification used by
those composition proofs. The source file contains every declaration and proof.

## Concrete checks

Examples cover immediate accept/reject on empty input, head-based classification
independent of the old terminal-state label, a stopped converted machine,
a genuine nonterminal source transition, a finishing write after a right move,
and the zero-length, zero-coefficient polynomial boundary.

## Dependency and structural scope

This batch uses the actual `ReferenceRun`, `referenceApply`, terminal convention
and finite-control definitions supplied in 1.01–1.04. It changes no register
operator, phase encoding or ring arithmetic. Those structures are not premises
that stand in for a compiler proof. The construction normalizes the acceptance
interface that the future register-machine simulation must preserve.

The register now has 13 completed entries and 64 open. The next open entry is
1.14: the uniform transition-table compiler with alphabet encoding, initialization
and run simulation. No general SAT reduction or prize conjecture is proved by
normalizing output conventions.
