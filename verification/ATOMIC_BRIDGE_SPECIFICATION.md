# Atomic specification of the four missing bridges

This expands the annotated statements about the missing prize bridge and the
incompleteness of packaging as mathematical proof. It is an obligation register,
not a completed P-versus-NP proof. The baseline library has 354 named theorem
declarations; the parser and halting extension adds 19, for 373 declarations. The reference-machine extension adds 13, for 386 declarations. The experimental guarded Fulgurite SAT module adds 22, for 408 declarations. Acceptance normalization adds 22, for 430 declarations. The four-symbol single-tape microcode component adds 17, for 447 current declarations; the general compiler entry 1.14 remains open. This does not close a registered compiler or fixed-protocol reduction obligation. Five additional unnamed encoding examples are checked separately;
they do not increase that library count.

This is one concrete equality-route specification; alternative encodings and
reference models are possible. Many open entries are standard known mathematics
not yet formalized for these exact interfaces. The absent general reduction is
a substantive research gap, not merely missing theorem transcription.

Each numbered atom below has one inspectable construction or proof acceptance
criterion and explicit prerequisites. `open` means that the stated construction
or proof is not supplied. No open item is added to Lean as an assumed theorem.
Definitions and theorems must be distinguished: naming a proposition does not
prove it. Some compiler/loop atoms require further transition-level expansion
once an actual implementation exists; no transition table is claimed for the
currently unconstructed SAT-to-protocol reduction.

## Scope of the annotations

The annotated claim was that the repository's finite results do not yet establish
a prize result. Its exact content is: the existing orbit decision is correct
for the constructed fixed operator, but no general-problem reduction, resource
proof or equivalence with conventional P and NP has been established. The
historical administrative dossier proves none of those missing implications.
The concrete missing links are the four groups below.

## Fixed notation and quantifiers

- A binary input is a finite list of Bool; N is its encoded bit length, not the
  number of abstract registers or clauses.
- A polynomial bound has the form c(N+1)^d, with fixed natural c,d. The constants
  may depend on a fixed machine or reduction but never on its particular input.
- P_ref and NP_ref are proposed conventional multi-tape, accept-state reference
  classes. Their exact formal definitions are still owed in 1.01–1.04. They are
  not existing Lean declarations asserted by this document.
- The repository classes and finite TM0 model are actual definitions in
  `IndependentDuodenary/MillenniumBridge.lean`. Its input alphabet is Fin 4:
  blank 0; binary symbols 1 and 2; pair separator 3.
- SAT_u and Q below are proposed languages with specified encodings. Their
  machine implementations and language-class theorems are not supplied.

## Concrete source-language design

For this specification choose `u(n) = true^n ++ [false]`, a unary count code.
A literal is `(negated : Bool, variable : Nat)` with code `negated :: u(variable)`.
A clause is `u(number of literals)` followed by its literal codes; a formula
is `u(number of clauses)` followed by its clause codes. All input must be
consumed. True negates a literal; false leaves it positive. Literal evaluation
is the assignment bit, or its Boolean negation. Clauses use disjunction,
formulas conjunction. An empty clause is false; an empty formula is true.

For m clauses, L total literals and variable indices i_j, the specified encoder
would have the exact length

    |encode(F)| = 1 + 2m + 3L + sum_j i_j.

Derivation: the formula count contributes m+1 bits; every clause contributes
one count terminator plus its literal count; every literal contributes one
sign bit and i_j+1 count bits. Summing yields the formula above. This is a
mathematical design calculation; there is no implemented formula encoder or
Lean length theorem yet. Unary indices make raw index size visible in input
length. Translating other SAT formats still requires compact renaming and a
polynomial-size proof. SAT completeness must be proved for this exact language,
not imported from a differently encoded problem without a bridge.

## Concrete target-language design

A protocol instance is `(r,h,q,x)` with one fixed step `registerStep h`.
Use canonical coordinate order. The proposed direct binary key format contains
2 metadata bits (00,01,10; reject 11), 2 binary-intercept bits, and 12 complement
bits: 16 bits per key. h requires 2 bits per register. Put a unary r header
before h, q and x. The proposed instance length is

    (r+1) + 2r + 16r + 16r = 35r+1.

This is a design specification, not an implemented or proved binary codec.
It is separate from the already-proved 17-symbol ZMod-12 frame and its noisy
transmission codec. The additional protocol binary codec and its parser are
explicit obligations 2.18–2.19. Q must reject invalid encodings and otherwise
decide reachability of the full target state. No noise, extra station program
or oracle parameter is hidden in Q.

## Required reduction statements

One total machine-computable bit-word function f must satisfy

    for every binary word y: SAT_u(y) iff Q(f(y)),
    |f(y)| <= c_S (|y|+1)^d_S,
    time_G(y) <= c_R (|y|+1)^d_R.

Writing `if SAT_u(y) then yesInstance else noInstance` is not an efficient
construction unless a polynomial SAT decider has already been independently
proved and implemented. It would hide precisely the problem being reduced.
A noncomputable selection, supplied satisfying assignment, arbitrary finite
table indexed by all inputs, or instance-dependent advice is insufficient.

## Required machine-time composition

Suppose the missing implementations eventually establish

    time_G(N) <= a(N+1)^b,
    |f(y)| <= c(N+1)^d,
    time_Q(M) <= e(M+1)^k,
    transfer(N) <= g(N+1)^h.

Then, since N+1 >= 1 and c(N+1)^d+1 <= (c+1)(N+1)^d,

    total_time(N)
      <= [a + e(c+1)^k + g] (N+1)^max(b, d*k, h).

This algebra composes already-proved cost bounds; it does not establish any of
the missing machine constructions or their local costs. All preprocessing and
rejection paths must be counted. The existing twelve-candidate theorem bounds
a number of candidates, not the cost of constructing and comparing them.

## Consequence and direction

Completing all four groups, including the actual general reduction and its
polynomial machine bounds, would support P = NP through SAT completeness.
The existing `PVersusNPConjecture` instead asserts inequality. Such an equality
result would contradict that defined proposition; it would not prove it.
No equality, inequality, conventional-model equivalence or prize resolution is
currently established. A separation route would require a different universal
lower-bound argument; the bound on explicit orbit covers is not one.

## Dependency and status interpretation

The machine-readable companion is `packaging/atomic_bridge_obligations.json`.
Dependencies refer to the numbered atoms, not to assumed Lean facts. Five proved entries identify checked unnamed Lean examples; three additional
entries identify named parser and halting theorems in the library. The acceptance-convention entry 1.13 now has a finite-control compiler, two-way
run and language proofs, and exact one-transition overhead. Four further
entries supply the requested reference-machine and class definitions; these are
marked `defined_in_library`, not equivalence or simulation theorems. Existing library
reachability correctness and cover bounds are separately listed as verified
baseline evidence. The dependency graph has no cycles; the absent reduction
2.21 remains a genuine missing construction rather than a renamed hypothesis.

**Register totals:** 77 atoms; 13 completed obligations; 64 open obligations. These totals are not library theorem counts.

## Item 1: Standard-model correspondence

### 1.01 — Reference machine syntax

Define a conventional finite multi-tape deterministic Turing machine and a finitely branching nondeterministic counterpart: finite alphabets, blank, states, initial state, accepting/rejecting states and one-transition semantics.

Status: **defined_in_library**.

Prerequisites: none.

Declarations: `ReferenceMove`, `ReferenceConfiguration`, `ReferenceInstruction`, `ReferenceDeterministicMachine`, `ReferenceNondeterministicMachine`, `referenceApply`, `referenceDStep`, `referenceNSuccessors`.

Evidence: `IndependentDuodenary/ReferenceMachines.lean`.

### 1.02 — Reference runs and time

Define configurations, initial input placement, finite runs, halting and acceptance. Count one actual reference-machine transition as one time step; specify whether all nondeterministic branches must halt within the bound.

Status: **defined_in_library**.

Prerequisites: 1.01.

Declarations: `referenceTerminal`, `referenceRead`, `referenceInitial`, `referenceDEdge`, `referenceNEdge`, `ReferenceRun`.

Evidence: `IndependentDuodenary/ReferenceMachines.lean`.

### 1.03 — Reference P

Define P_ref(L): one fixed deterministic reference machine decides every binary input x within a polynomial in |x|, with constants independent of x. Invalid encodings remain inputs and require a total answer.

Status: **defined_in_library**.

Prerequisites: 1.02.

Declarations: `ReferenceP`.

Evidence: `IndependentDuodenary/ReferenceMachines.lean`.

### 1.04 — Reference NP

Define NP_ref(L): one fixed nondeterministic reference machine has an accepting branch exactly for x in L and all branches obey a polynomial transition bound.

Status: **defined_in_library**.

Prerequisites: 1.02.

Declarations: `ReferenceNP`.

Evidence: `IndependentDuodenary/ReferenceMachines.lean`.

### 1.05 — Existing word length

Prove |prizeEncodeWord(x)| = |x|.

Status: **proved_in_Lean_example**.

Prerequisites: none.

Evidence: `examples/ComplexityEncodingBoundary.lean`.

### 1.06 — Existing pair length

Prove |prizeEncodePair(x,w)| = |x| + |w| + 1.

Status: **proved_in_Lean_example**.

Prerequisites: 1.05.

Evidence: `examples/ComplexityEncodingBoundary.lean`.

### 1.07 — Bit-symbol distinction

Prove that the map false -> 1 and true -> 2 in Fin 4 is injective.

Status: **proved_in_Lean_example**.

Prerequisites: none.

Evidence: `examples/ComplexityEncodingBoundary.lean`.

### 1.08 — Blank exclusion

Prove symbol 0 never occurs in prizeEncodeWord(x).

Status: **proved_in_Lean_example**.

Prerequisites: none.

Evidence: `examples/ComplexityEncodingBoundary.lean`.

### 1.09 — Separator exclusion

Prove symbol 3 never occurs in prizeEncodeWord(x).

Status: **proved_in_Lean_example**.

Prerequisites: none.

Evidence: `examples/ComplexityEncodingBoundary.lean`.

### 1.10 — Word decoder

Supply a total partial decoder on Fin-4 words, prove decode(encode(x)) = some x and uniqueness, and reject symbols outside {1,2}. A left inverse only on words actually in the image is insufficient for malformed-input handling.

Status: **proved_in_library**.

Prerequisites: 1.07, 1.08, 1.09.

Evidence: `IndependentDuodenary/ComplexityEncoding.lean`.

### 1.11 — Pair decoder

Supply a total pair parser. Prove its left inverse, uniqueness of the separator split, rejection of absent/multiple separators and invalid bit symbols, and no ignored trailing data.

Status: **proved_in_library**.

Prerequisites: 1.10, 1.09.

Evidence: `IndependentDuodenary/ComplexityEncoding.lean`.

### 1.12 — Halted-run persistence

Prove the repository saturated iterator freezes configurations after halting: halted at t implies same configuration, halting status and output at every t+s. This connects checking at the exact polynomial bound to halting by that bound.

Status: **proved_in_library**.

Prerequisites: none.

Evidence: `IndependentDuodenary/ComplexityEncoding.lean`.

### 1.13 — Acceptance convention conversion

Convert accept/reject control states to halted head symbols 1/2 and back. Prove language preservation, correct handling of empty input, and an explicit time overhead independent of the particular input.

Status: **proved_in_library**.

Prerequisites: 1.02, 1.12.

Evidence: `IndependentDuodenary/AcceptanceNormalization.lean`.

### 1.14 — Reference-to-repository simulator

For deterministic reference machines, including a single nondeterministic branch controlled by a supplied choice certificate, construct a uniform finite transition-table compiler into PrizeMachine. Encode every tape, head marker and state over four symbols. Prove initialization, one-step simulation and finite-run simulation by induction with acceptance preservation. This must not assume a polynomial deterministic simulation of all nondeterministic branches.

Status: **open**.

Prerequisites: 1.01, 1.02, 1.10, 1.13.

### 1.15 — Repository-to-reference simulator

Construct the reverse compiler for any finite PrizeMachine. Prove configuration decoding, initialization, step simulation and acceptance/rejection preservation, with an explicit polynomial time overhead.

Status: **open**.

Prerequisites: 1.01, 1.02, 1.12, 1.13.

### 1.16 — Simulation polynomial closure

For each fixed source machine, exhibit natural coefficient/exponent constants for the whole simulation. Prove overhead remains polynomial after input encoding, tape growth, step simulation and output normalization. Constants may depend on the machine, not on x or w.

Status: **open**.

Prerequisites: 1.05, 1.06, 1.14, 1.15.

### 1.17 — Deterministic class equality

Prove for every language L: P_ref(L) iff PrizeDeterministicPolynomial(L), using the actual compilers and their cost proofs rather than declaring the classes equivalent by definition.

Status: **open**.

Prerequisites: 1.03, 1.16.

### 1.18 — Nondeterministic run to certificate

Encode a bounded accepting branch as a polynomial-length choice word. Construct a deterministic verifier that checks each actual branch choice and simulates that branch; prove both accepting-run completeness and rejection of invalid certificates, with a uniform polynomial bound for every x,w.

Status: **open**.

Prerequisites: 1.04, 1.11, 1.16.

### 1.19 — Certificate to nondeterministic run

Construct a machine that guesses a certificate of length at most the stated polynomial and executes the verifier. Prove all branches halt in polynomial time and an accepting branch exists exactly when a valid witness exists, including the empty witness.

Status: **open**.

Prerequisites: 1.04, 1.06, 1.16.

### 1.20 — Nondeterministic class equality

Prove for every language L: NP_ref(L) iff PrizeCertificatePolynomial(L), tracking both certificate-length and verifier-time bounds through the compilers.

Status: **open**.

Prerequisites: 1.18, 1.19.

### 1.21 — P inclusion in NP

Construct a total pair-input verifier that ignores the certificate, simulates a deterministic decider and accepts the empty certificate exactly for positive instances. Prove PrizeDeterministicPolynomial(L) implies PrizeCertificatePolynomial(L).

Status: **open**.

Prerequisites: 1.11, 1.12, 1.16.

## Item 2: General-problem reduction and its source/target languages

### 2.01 — CNF syntax

Define Literal = variable index plus negation bit, Clause = finite list of literals, and Formula = finite list of clauses. Choose the exact unary-count binary serialization described in this specification.

Status: **open**.

Prerequisites: none.

### 2.02 — Unary-count parser

Implement u(n) = true^n ++ [false] and a total parser consuming a prefix. Prove round trip, uniqueness, exact consumption, and termination/rejection when the terminating false bit is absent.

Status: **open**.

Prerequisites: 2.01.

### 2.03 — Formula codec

Implement length-prefixed literal/clause/formula parsing. Prove parse(encode(F)) = some F, exact input consumption and rejection of trailing or truncated data. Prove the exact encoded length 1 + 2m + 3L + sum(variable indices).

Status: **open**.

Prerequisites: 2.02.

### 2.04 — Variable indexing bounds

Prove every unary-coded variable index is at most input length. When translating other SAT encodings, construct a polynomial-time renaming to compact indices and prove satisfiability is preserved in both directions. Do not expand an enormous binary index without this bound.

Status: **open**.

Prerequisites: 2.03.

### 2.05 — Boolean semantics

Define literal evaluation, disjunction for clauses and conjunction for formulas. Prove empty clause is false, empty formula is true, and specify repeated literals, negation and out-of-range certificate access.

Status: **open**.

Prerequisites: 2.01.

### 2.06 — Finite assignment domain

Restrict assignments to the occurring or maximum-index variable domain and prove extension/restriction preserves formula evaluation. This connects finite certificate words to ordinary variable assignments.

Status: **open**.

Prerequisites: 2.04, 2.05.

### 2.07 — Binary SAT language

Define SAT_u(x): x parses as F and F has a satisfying assignment. Prove every malformed binary input is outside the language.

Status: **open**.

Prerequisites: 2.03, 2.06.

### 2.08 — SAT verification machine

Construct a deterministic TM certificate verifier for SAT_u, prove correctness for every x,w and a polynomial certificate bound and transition bound. Include malformed formulas and short/invalid witnesses in the total behavior.

Status: **open**.

Prerequisites: 1.11, 1.16, 2.07.

### 2.09 — Clocked source computation

For an arbitrary fixed NP_ref machine with polynomial time bound T(n), derive a polynomial tape window and normalize accepting computations so that accepting early can be padded safely to T(n).

Status: **open**.

Prerequisites: 1.04.

### 2.10 — Tableau variables

Explicitly allocate Boolean variables for every needed time, cell, symbol, head and control-state position in the bounded computation tableau. Prove allocation is collision-free and polynomially bounded.

Status: **open**.

Prerequisites: 2.09.

### 2.11 — Initial and well-formed tableau clauses

Generate clauses for the encoded input row, blank boundaries, legal state/head positions and exactly-one symbol/state constraints. Prove each constraint family has its stated semantics and polynomial size.

Status: **open**.

Prerequisites: 2.10.

### 2.12 — Transition clauses

Generate bounded-locality clauses enforcing precisely one legal source transition between consecutive tableau rows, including nondeterministic choices. Prove local clauses are equivalent to the intended step relation under the well-formedness conditions.

Status: **open**.

Prerequisites: 2.11.

### 2.13 — Acceptance clauses

Generate and prove the accepting condition on the padded tableau. Ensure early acceptance, rejecting halts and clock exhaustion have the intended distinct meanings.

Status: **open**.

Prerequisites: 2.09, 2.12.

### 2.14 — Run-to-assignment proof

From any accepting clocked computation, construct a satisfying assignment of the generated CNF and prove every clause family true.

Status: **open**.

Prerequisites: 2.11, 2.12, 2.13.

### 2.15 — Assignment-to-run proof

From any satisfying assignment, reconstruct a legal accepting source computation. Prove uniqueness/consistency of each decoded row and validity of every transition.

Status: **open**.

Prerequisites: 2.11, 2.12, 2.13.

### 2.16 — Tableau generator resource proof

Implement the tableau-to-unary-CNF generator as a uniform machine and prove polynomial output length and transition count, including the unary encoding of allocated variable indices. Combine the preceding directions to establish SAT_u completeness for NP_ref.

Status: **open**.

Prerequisites: 2.03, 2.10, 2.14, 2.15.

### 2.17 — Protocol instance domain

Define a dependent instance (r,h,q,x), with h : RegisterTranslation r and q,x : RegisterState r. Fix the operator to registerStep h. No unencoded extra operation, oracle, noise advice or hidden phase is allowed.

Status: **open**.

Prerequisites: none.

### 2.18 — Protocol binary encoder

Implement the proposed canonical coefficient encoding: two metadata bits, two binary-intercept bits and twelve complement bits per key; two bits per register for h; unary r header. Prove encoder determinism and canonical coordinate ordering.

Status: **open**.

Prerequisites: 2.17.

### 2.19 — Protocol decoder and exact length

Implement a total decoder; reject metadata code 11 and malformed lengths. Prove decoder left inverse, soundness, unique full consumption and total length 35r+1 for this proposed direct-coefficient format. This format is separate from the existing 17-symbol framed channel codec.

Status: **open**.

Prerequisites: 2.02, 2.18.

### 2.20 — Protocol binary language

Define Q(x) to reject malformed protocol encodings and otherwise return protocolReachabilityCheck h q x_target. Connect its Boolean result to existence of a natural iterate using the existing correctness theorem.

Status: **open**.

Prerequisites: 2.19.

### 2.21 — Actual SAT-to-protocol construction

Construct a single total effective function f on binary words whose output is a protocol instance encoding. This is the missing mathematical reduction, not an assumption or a function supplied with a SAT-answer oracle. No such f is currently implemented.

Status: **open**.

Prerequisites: 2.07, 2.20.

### 2.22 — Reduction forward direction

For every satisfiable well-formed F, prove that f(encode(F)) decodes to a protocol instance with a reachable target. The witness construction must use the actual f, not redefine f from satisfiability.

Status: **open**.

Prerequisites: 2.21.

### 2.23 — Reduction reverse direction

For every well-formed F, prove that target reachability for f(encode(F)) yields a satisfying assignment of F. This must exclude all false positive protocol instances.

Status: **open**.

Prerequisites: 2.21.

### 2.24 — Malformed source behavior

Prove malformed formula strings map to a fixed valid rejecting protocol instance, or another explicitly proved rejecting output. A one-register zero state and a target with different metadata supply a possible rejecting-instance design.

Status: **open**.

Prerequisites: 2.07, 2.20, 2.21.

### 2.25 — Complete many-one reduction

Combine correctness on well-formed and malformed words with the actual generator and resource proofs to obtain, for every binary x, SAT_u(x) iff Q(f(x)), with polynomial generation time and polynomial output length.

Status: **open**.

Prerequisites: 2.22, 2.23, 2.24, 3.11, 3.12.

## Item 3: Efficient and non-circular instance construction

### 3.01 — Uniform generator

Supply one finite machine G independent of the input, implementing the reduction. A separate hard-coded answer or machine for each formula is not a uniform algorithm.

Status: **open**.

Prerequisites: 2.21.

### 3.02 — Parsing cost

Bound the transition count for reading, validating and parsing an input of N bits, including rejection paths and end-of-input checks.

Status: **open**.

Prerequisites: 2.03, 3.01.

### 3.03 — Register-count computation

Give the actual computation of r from the formula syntax. Prove termination and correctness of that computation without using a satisfiability decision as a primitive.

Status: **open**.

Prerequisites: 3.01, 3.02.

### 3.04 — Translation construction

Give the algorithm producing every bit of h from the parsed input and prove each produced bit equals the intended construction. Count all tape scans and writes.

Status: **open**.

Prerequisites: 3.03.

### 3.05 — Initial-state construction

Give the algorithm producing metadata and all fourteen binary coefficients of every q register. Prove its output does not presuppose an unknown satisfying assignment.

Status: **open**.

Prerequisites: 3.03.

### 3.06 — Target-state construction

Give the analogous algorithm for x_target, with a proof connecting its fields to the actual reduction rather than a precomputed SAT truth value.

Status: **open**.

Prerequisites: 3.03.

### 3.07 — Register bound

Prove r(F) <= c_r (N+1)^d_r for explicit constants independent of F, and combine it with the fixed-width coordinate format to bound output length. A bound on r alone is insufficient if any field silently carries an unbounded integer.

Status: **open**.

Prerequisites: 2.19, 3.03, 3.04, 3.05, 3.06.

### 3.08 — Intermediate-value sizes

Bound the bit lengths of counters, indices, addresses and arithmetic intermediates. Prove that operations on these values have their stated machine costs rather than unit-cost arithmetic on unbounded integers.

Status: **open**.

Prerequisites: 3.02, 3.07.

### 3.09 — Total generation

Prove every source input produces an answer within a finite bound, including invalid formulas. Prove any exceptional branch produces the specified rejecting encoding.

Status: **open**.

Prerequisites: 2.24, 3.04, 3.05, 3.06.

### 3.10 — Generator instruction accounting

Implement all loops, scans, copies, index calculations and output writes in the chosen machine model. Prove local loop invariants and costs; sum them without assuming syntax-level operations take one transition.

Status: **open**.

Prerequisites: 1.14, 1.16, 3.08, 3.09.

### 3.11 — Exact generator realization

Prove that the halted machine output is precisely the bit word f(x), including the complete header and every field, and that no unread or unvalidated data changes its meaning.

Status: **open**.

Prerequisites: 3.10.

### 3.12 — Generator polynomial witnesses

Exhibit fixed c_R,d_R with T_R(N) <= c_R (N+1)^d_R for every input. Separately prove the encoded output bound; time alone bounds length only after the output/write model has been justified.

Status: **open**.

Prerequisites: 3.07, 3.11.

## Item 4: Protocol Turing-machine implementation and final time composition

### 4.01 — Protocol parsing machine

Implement the protocol decoder in the machine model and prove its relation to the mathematical decoder, including rejection and a transition bound on all input strings.

Status: **open**.

Prerequisites: 1.14, 2.19.

### 4.02 — Machine storage representation

Specify exactly how the unary header, h bits, current state, target state, scratch area and counters are laid out on tapes. Prove that the encoding relation is unambiguous.

Status: **open**.

Prerequisites: 4.01.

### 4.03 — Rotation implementation

Implement complement-coordinate rotation in the fixed 12-coordinate order, using scratch space or another proved method that does not overwrite unread source bits.

Status: **open**.

Prerequisites: 4.02.

### 4.04 — XOR implementation

Implement addition in ZMod 2 as a finite transition routine and prove its four input cases, including correct h-coordinate lookup.

Status: **open**.

Prerequisites: 4.02.

### 4.05 — Metadata copying

Implement and prove preservation of each two-bit metadata field and preservation of register count and key-field boundaries.

Status: **open**.

Prerequisites: 4.02.

### 4.06 — One-step simulation

Prove that the combined rotation, XOR and metadata routines transform a well-encoded q to a well-encoded registerStep h q, with an explicit transition cost bound and unchanged h and target buffers.

Status: **open**.

Prerequisites: 4.03, 4.04, 4.05.

### 4.07 — Loop initialization

Prove that the current-state buffer initially contains q, the phase counter is zero and every fixed buffer remains valid.

Status: **open**.

Prerequisites: 4.02.

### 4.08 — Full equality routine

Implement comparison of all metadata, binary-intercept and complement bits against the target. Prove true iff equality of full RegisterState values; phase equality alone is insufficient.

Status: **open**.

Prerequisites: 4.02.

### 4.09 — Phase-loop invariant

Prove that at loop entry k the current buffer represents (registerStep h)^k(q), h and the target remain unchanged, and 0 <= k < 12.

Status: **open**.

Prerequisites: 4.06, 4.07.

### 4.10 — Successful comparison correctness

Prove any accepting comparison produces a genuine finite-index witness of target reachability.

Status: **open**.

Prerequisites: 4.08, 4.09.

### 4.11 — Twelve-failure correctness

Prove that rejecting after all twelve comparisons means no natural iterate reaches the target, using the period theorem and the existing Boolean rejection theorem.

Status: **open**.

Prerequisites: 4.08, 4.09.

### 4.12 — Loop termination and count

Prove the phase counter advances, cannot overflow its intended representation, and makes at most twelve comparisons and at most eleven necessary step updates. Count initialization, updates and final exit.

Status: **open**.

Prerequisites: 4.09.

### 4.13 — Malformed-input rejection

Prove all malformed binary instance strings terminate and reject, and cannot accidentally reach the successful-comparison branch.

Status: **open**.

Prerequisites: 4.01.

### 4.14 — Output and halting convention

Implement and prove halted symbol 1 for acceptance and 2 for rejection at the observed head position, matching prizeAccepts and prizeBooleanOutput exactly.

Status: **open**.

Prerequisites: 1.12, 1.13, 4.10, 4.11, 4.13.

### 4.15 — Protocol-machine polynomial witnesses

Exhibit fixed c_Q,d_Q with T_Q(M) <= c_Q (M+1)^d_Q for every M-bit input. Include parsing, repeated comparisons, scans, copies, at most twelve candidates and all failure branches.

Status: **open**.

Prerequisites: 4.06, 4.08, 4.12, 4.14.

### 4.16 — Generator/decider composition

Construct an actual finite machine running G, preparing its output as the input to Q, and then running Q. Prove state-renaming, head positioning, delimiter handling and buffer transfer, with an explicit communication cost.

Status: **open**.

Prerequisites: 1.14, 3.11, 4.14.

### 4.17 — Composed decision correctness

Prove the composed machine accepts exactly SAT_u on every binary input, by the reduction equivalence and the protocol-machine correctness, and rejects otherwise.

Status: **open**.

Prerequisites: 2.25, 4.10, 4.11, 4.13, 4.16.

### 4.18 — Composed polynomial time

Substitute the output-length polynomial into T_Q and add generation and communication costs. Exhibit one coefficient and exponent independent of the input, as detailed in the composition formula in this specification.

Status: **open**.

Prerequisites: 3.12, 4.15, 4.16.

### 4.19 — Class-equality consequence

Use SAT_u completeness and closure of polynomial reductions to give a polynomial decider for every NP_ref language; combine with P inclusion in NP and model correspondence to obtain class equality. This would oppose the existing inequality conjecture; no such equality is currently proved.

Status: **open**.

Prerequisites: 1.17, 1.20, 1.21, 2.16, 4.17, 4.18.
