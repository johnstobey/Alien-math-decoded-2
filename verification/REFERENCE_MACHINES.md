# Explicit reference machines: obligations 1.01–1.04

The complete implementation is `IndependentDuodenary/ReferenceMachines.lean`.
The fixture file is `examples/ReferenceMachinesBoundary.lean`.

## Exact conventions

A machine has k+1 two-way tapes, an alphabet `Fin (a+3)` and states `Fin (s+2)`.
Blank is 0, false/true symbols are 1/2, accepting state is 0, rejecting state is 1.
Its initial state is supplied explicitly and may already be terminal. Every
head starts at zero. The whole input occupies nonnegative positions of tape 0;
all other cells start blank, including the cells after the input terminates.

One instruction simultaneously reads all current head symbols, writes one
symbol at each head, moves each head left/stay/right, and updates the state.
Both terminal states have no outgoing edges. A deterministic table chooses one
instruction at each nonterminal local situation. A nondeterministic table
supplies a first instruction and a finite list of additional choices; nonterminal
deadlock is impossible. The state and read-symbol domains of the tables are
finite. Reachable configurations may use unbounded tape space.

`ReferenceRun edge t q q'` is an inductive relation containing exactly t genuine
edges, with no padded steps at a halt. The supporting proofs establish single
successor uniqueness, finite branching, no successors from terminal states,
nonterminal progress, input blank conventions and single-cell write behavior.
The branch-bound theorem shows that a run reaching the universal time bound must
be terminal: otherwise an additional transition would violate that bound.

`ReferenceP L` requires one fixed deterministic machine and fixed natural c,d
such that every binary word has a terminal run of at most c(|x|+1)^d actual
transitions, with accepting state exactly for membership in L.

`ReferenceNP L` requires one fixed finite-branching nondeterministic machine and
fixed natural c,d bounding every finite branch prefix on every binary word.
Together with nonterminal progress, this excludes infinite branches and ensures
termination within the bound. Membership is equivalent to an accepting branch.
The bound covers rejecting branches too; constants do not depend on the input.

## Proof status and structural traceability

These are the actual reference definitions requested by 1.01–1.04, accompanied by
13 checked foundational theorems. They do not prove reference-class equivalence
with the head-output `PrizeMachine` definitions. In particular, accept/reject
normalization (1.13), compilers (1.14–1.15), overhead (1.16) and class bridges
(1.17–1.20) remain open.

The shared interface is the existing binary-word type and polynomial-bound
function from `MillenniumBridge.lean`. No configuration encoding of the Mod-144
calculator or `RegisterState r` is supplied by this module. Exact ring/register
simulation and its cost remain separate obligations. The full per-entry ledger
is `CLOSURE_EXECUTION.md`; it retains all 69 initially open entries without
changing any acceptance criterion. Four definitions are now implemented; 65
entries are still open. No SAT reduction or Millennium Prize solution is claimed.
