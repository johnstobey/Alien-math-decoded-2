# Combining the proposed calculus with the P-versus-NP investigation

Complete source: `IndependentDuodenary/FulguriteSAT.lean`.
Boundary examples: `examples/FulguriteSATBoundary.lean`.
This is a proposed semantic core inspired by the uploaded discussion, not an
implementation of the complete Obsidian or 31-glyph Fulgurite specifications.
No claims about the historical source or physical reality are used as premises.

## The experiment

`DiscoveryFormula n` permits arbitrary finite expressions over n variables using
NOT, AND and OR. The compiler inspects syntax recursively; it neither receives a
satisfying assignment nor tests satisfiability. The target `FulguriteCircuit n`
contains reads, half-turns and conditional meet/join gates.

False and true are encoded as positions 0 and 6 in ZMod 12. The proposed
Obsidian bit law restricts each input to those positions. A half-turn is exactly
x + 6, which implements Boolean NOT on valid bits. Reflection is not substituted
for it. Meet is `if x = 6 then y else 0`; join is `if x = 6 then 6 else y`.
These conditional, two-input operations are explicit experimental additions.
The attachments do not establish that the existing source opcodes implement
them, and the fixed independent-register cycle does not supply them merely by
changing notation.

## What Lean proves

- Encoding and decoding assignments are mutual inverses on valid phase vectors.
- There are exactly 2^n valid encoded assignments, including the n=0 case.
- Compilation preserves the AST node count exactly. This counts constructors,
  not serialized bits, variable-index encoding or Turing-machine instructions.
- Evaluating a compiled expression on an encoded assignment yields exactly the
  encoding of its Boolean result, for every n, formula and assignment.
- A formula is satisfiable iff its compiled circuit has a valid phase vector
  yielding 6. Both directions are proved; this is not fixed-protocol reachability.
- The phase vectors embed into the existing `phaseRegisterState` one-hot keys;
  projecting with `registerPhases` recovers the vector exactly.
- No affine expression A*x+B*y+C over ZMod 12 represents AND on the chosen bit
  encoding. Four Boolean inputs suffice for the contradiction. This result is
  about that encoding and affine expression, not all possible encodings or
  algorithms, and is not a complexity lower bound.
- Double half-turn elimination and guarded meet/join commutation preserve
  evaluation. Finite traces preserve both evaluation and satisfiability.
- A small executable proposer emits these rules with certificates. Bounded
  execution returns a certified trace. Commutation can cycle, so a fuel limit
  bounds execution; neither normalization nor proof-search completeness follows.

## Concrete boundary checks

The example `(x0 OR x1) AND NOT x0` succeeds on false/true. The contradiction
`x0 AND NOT x0` has no valid satisfying phase vector. The examples check one-step
double-turn elimination, one-step commutation and a two-step commutation cycle.
They also demonstrate why the bit law is required: meet(6,1) differs from
meet(1,6). Multiplying the two encoded true values does not implement AND.

## Relation to the prize bridge

This is an exact representation of Boolean formula satisfiability inside a
richer, guarded circuit language. It does not remove the existential search for
an assignment. A new representation alone supplies neither a polynomial SAT
algorithm nor a reduction to the already-audited twelve-candidate protocol.
The 2^n cardinality theorem also does not prove that enumerating all assignments
is necessary: a different algorithm might avoid enumeration.

A candidate future advance must provide either a justified satisfiability
algorithm with uniform resource bounds, or a uniform reduction into the exact
existing protocol. It must account for these added binary gates and preserve
all quantifiers. Existing obligations 2.21–2.25, Item 3 and 4.01–4.19 are not
closed by this experiment. The registered count remains 12 completed, 65 open.
There is no claim that this familiar Boolean encoding constitutes a novel
complexity result. Its purpose is to test the proposed discovery-to-certification
workflow on a precise mathematical task and expose the remaining interface.
