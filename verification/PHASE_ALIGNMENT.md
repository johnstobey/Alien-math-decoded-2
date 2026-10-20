# Phase-alignment and conditional-free SAT investigation

Complete code: `examples/PhaseAlignmentBridge.lean`.
Independent experimental audit: `scripts/audit_phase_alignment.py`.
The namespace is `IndependentDuodenary.PhaseAlignmentInvestigation`.
There are 16 checked experimental theorem declarations. They are separate from
the 408 named library declarations. No registered obligation changes status.

## Preserve the distinction between geometric relations and Boolean semantics

Alignment means `y - x = 0` in ZMod 12. Lean proves this is equality and that
simultaneously rotating both coordinates preserves it. On a two-point encoding,
pairwise alignment means Boolean equality: both false inputs align, just as both
true inputs align. Therefore this relation alone does not implement Boolean AND.
This does not invalidate geometric conjunction; it identifies the missing logical
correspondence when using conjunction to decide Boolean satisfiability.

## An explicit spatial criterion

Choose false=0 and true=1. For any common origin t, define the encoded input
coordinate as t+bit(b). Then Lean proves, for all t,a,b:

    aligned ((t+bit(a)) + (t+bit(b))) ((t+1)+(t+1))
      iff (a AND b) = true.

There is no conditional gate in this relation. False/false and mixed inputs fail;
true/true succeeds. The origin is arbitrary and transported consistently. This
is a criterion for satisfaction, not an algorithm for finding satisfying values.
Testing the criterion is not the same task as constructing a satisfying input.

## Conditional-free semantics for complete formulas

The experiment uses the existing arbitrary finite `DiscoveryFormula n`, with
these ring expressions:

    NOT x = 1-x
    AND(x,y) = x*y
    OR(x,y) = x+y-x*y.

Each identity is proved for encoded Boolean operands. Structural induction then
proves correctness for every finite formula and every assignment. Decoding is a
mutual inverse on valid phase vectors, and both directions of the equivalence

    exists Boolean assignment satisfying f
      iff exists valid phase assignment p with aligned(arithmeticEval(p,f),1)

are proved. The constructor/evaluator never receives a satisfying assignment as
advice. The anchored phase test uses equality only at its final constraint.

This re-encoding genuinely removes the previous conditional gate. It does not
contradict `fulgurite_meet_not_affine`: that theorem concerns an affine expression
on the different 0/6 encoding. The new AND uses multiplication on 0/1 values.
Multiplication is ring arithmetic; it is not one of the independent fixed
rotations merely because both are described on a twelve-position carrier.
A machine implementation and cost for these operations are still needed.

## Exact connection to existing source registers

`represented_register_phase_roundtrip` embeds the new assignment phases using
`phaseRegisterState`, then recovers them with `registerPhases`. This is a checked
connection to the represented-key registers, with their one-hot complements.
It does not equate formula evaluation with iterations of `registerStep`, or
transfer ring arithmetic into the Mod-144 calculator's execution model. Those
simulation claims need their own constructors, invariants and cost proofs.

## What this experiment does not assert

The valid phase assignment space has exactly 2^n elements. This is a lossless
encoding theorem, not a proof of an exponential runtime lower bound. No bound
for solving the resulting constraint system has been proved, and no uniform
SAT-to-fixed-register-reachability reduction has been constructed.

A twelve-element ring by itself does not specify a continuous one-manifold,
a simplicial complex or a homology computation. Narrative topology labels are
not premises of any declaration in this experiment. A claimed Betti number
would require explicit construction and an independently checked calculation.

The next sequential registered entry, 1.13, still requires accept/reject
normalization with language preservation and a time bound. This phase encoding
is not that compiler. Entries 1.13–1.21, the general reduction and the resource
proofs remain open. The registry remains 12 completed and 65 open.

## Reproduce

    lake build
    lake env lean examples/PhaseAlignmentBridge.lean
    python3 scripts/audit_phase_alignment.py

The separate audit prints every experimental proposition, proof term and
transitive foundational usage, and permits only the same standard Lean axioms
as the library audit. Exported bundles run both audits; `verify_bundle.py --all`
repeats both after a fresh build. No biological or identity assertions are used.
