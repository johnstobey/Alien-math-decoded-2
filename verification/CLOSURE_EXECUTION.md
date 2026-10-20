# Historical closure execution ledger

This records the reference-machine batch at e50b45c. The later normalization
batch closes 1.13; current statuses are in `packaging/atomic_bridge_obligations.json`.
The historical entries below are retained rather than rewritten.

This ledger lists individually all 69 entries that were open at the start of this execution. Four definition obligations are now implemented; 65 remain open. It does not certify zero-open closure. Complete code is in the cited source file, not abbreviated here. Every original acceptance criterion is preserved below.

## Structural traceability

The existing duodenary carrier is `ZMod 12`; the calculator carrier is `ZMod 144`. The actual source-register operator is `registerStep`, whose twelve-phase bound is proved in `MillenniumBridge.lean`. These are ring and finite-state results. No topological equivalence with SAT or a reference Turing machine is proved.

The new reference machines share `PrizeBinaryWord` and `prizePolynomialBound` with the existing complexity interface. This is an input-and-bound interface, not an operator simulation. The missing operator bridge is assigned to 1.14–1.20 and 4.01–4.15. Protocol encodings are assigned to 2.17–2.20; the SAT bridge is 2.21–2.25; constructor costs are Item 3; composition and the resulting class statement are 4.16–4.19. None is implied by a ring cardinality or an orbit bound.

## Central unresolved construction

No uniform SAT-to-protocol constructor with the specified correctness and polynomial machine bound has been supplied. Selecting a yes/no protocol instance by first evaluating satisfiability would merely hide the SAT decision and would not meet the obligation. Failure to construct this reduction does not prove that it is impossible. The compiler obligations beginning at 1.13 are also not discharged by the new machine definitions.

## 1.01 — Reference machine syntax

**Acceptance criterion:** Define a conventional finite multi-tape deterministic Turing machine and a finitely branching nondeterministic counterpart: finite alphabets, blank, states, initial state, accepting/rejecting states and one-transition semantics.

**Status:** `defined_in_library`.

**Prerequisites:** none.

**Implementation:** `IndependentDuodenary/ReferenceMachines.lean`.

**Declarations:** `ReferenceMove`, `ReferenceConfiguration`, `ReferenceInstruction`, `ReferenceDeterministicMachine`, `ReferenceNondeterministicMachine`, `referenceApply`, `referenceDStep`, `referenceNSuccessors`.

**Validation:** strict Lean elaboration, source-derived axiom audit, and `examples/ReferenceMachinesBoundary.lean`. Definitions of P/NP are not proofs of equality or equivalence to the existing Prize classes.

## 1.02 — Reference runs and time

**Acceptance criterion:** Define configurations, initial input placement, finite runs, halting and acceptance. Count one actual reference-machine transition as one time step; specify whether all nondeterministic branches must halt within the bound.

**Status:** `defined_in_library`.

**Prerequisites:** 1.01.

**Implementation:** `IndependentDuodenary/ReferenceMachines.lean`.

**Declarations:** `referenceTerminal`, `referenceRead`, `referenceInitial`, `referenceDEdge`, `referenceNEdge`, `ReferenceRun`.

**Validation:** strict Lean elaboration, source-derived axiom audit, and `examples/ReferenceMachinesBoundary.lean`. Definitions of P/NP are not proofs of equality or equivalence to the existing Prize classes.

## 1.03 — Reference P

**Acceptance criterion:** Define P_ref(L): one fixed deterministic reference machine decides every binary input x within a polynomial in |x|, with constants independent of x. Invalid encodings remain inputs and require a total answer.

**Status:** `defined_in_library`.

**Prerequisites:** 1.02.

**Implementation:** `IndependentDuodenary/ReferenceMachines.lean`.

**Declarations:** `ReferenceP`.

**Validation:** strict Lean elaboration, source-derived axiom audit, and `examples/ReferenceMachinesBoundary.lean`. Definitions of P/NP are not proofs of equality or equivalence to the existing Prize classes.

## 1.04 — Reference NP

**Acceptance criterion:** Define NP_ref(L): one fixed nondeterministic reference machine has an accepting branch exactly for x in L and all branches obey a polynomial transition bound.

**Status:** `defined_in_library`.

**Prerequisites:** 1.02.

**Implementation:** `IndependentDuodenary/ReferenceMachines.lean`.

**Declarations:** `ReferenceNP`.

**Validation:** strict Lean elaboration, source-derived axiom audit, and `examples/ReferenceMachinesBoundary.lean`. Definitions of P/NP are not proofs of equality or equivalence to the existing Prize classes.

## 1.13 — Acceptance convention conversion

**Acceptance criterion:** Convert accept/reject control states to halted head symbols 1/2 and back. Prove language preservation, correct handling of empty input, and an explicit time overhead independent of the particular input.

**Status:** `open`.

**Prerequisites:** 1.02, 1.12.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 1.14 — Reference-to-repository simulator

**Acceptance criterion:** For deterministic reference machines, including a single nondeterministic branch controlled by a supplied choice certificate, construct a uniform finite transition-table compiler into PrizeMachine. Encode every tape, head marker and state over four symbols. Prove initialization, one-step simulation and finite-run simulation by induction with acceptance preservation. This must not assume a polynomial deterministic simulation of all nondeterministic branches.

**Status:** `open`.

**Prerequisites:** 1.01, 1.02, 1.10, 1.13.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 1.15 — Repository-to-reference simulator

**Acceptance criterion:** Construct the reverse compiler for any finite PrizeMachine. Prove configuration decoding, initialization, step simulation and acceptance/rejection preservation, with an explicit polynomial time overhead.

**Status:** `open`.

**Prerequisites:** 1.01, 1.02, 1.12, 1.13.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 1.16 — Simulation polynomial closure

**Acceptance criterion:** For each fixed source machine, exhibit natural coefficient/exponent constants for the whole simulation. Prove overhead remains polynomial after input encoding, tape growth, step simulation and output normalization. Constants may depend on the machine, not on x or w.

**Status:** `open`.

**Prerequisites:** 1.05, 1.06, 1.14, 1.15.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 1.17 — Deterministic class equality

**Acceptance criterion:** Prove for every language L: P_ref(L) iff PrizeDeterministicPolynomial(L), using the actual compilers and their cost proofs rather than declaring the classes equivalent by definition.

**Status:** `open`.

**Prerequisites:** 1.03, 1.16.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 1.18 — Nondeterministic run to certificate

**Acceptance criterion:** Encode a bounded accepting branch as a polynomial-length choice word. Construct a deterministic verifier that checks each actual branch choice and simulates that branch; prove both accepting-run completeness and rejection of invalid certificates, with a uniform polynomial bound for every x,w.

**Status:** `open`.

**Prerequisites:** 1.04, 1.11, 1.16.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 1.19 — Certificate to nondeterministic run

**Acceptance criterion:** Construct a machine that guesses a certificate of length at most the stated polynomial and executes the verifier. Prove all branches halt in polynomial time and an accepting branch exists exactly when a valid witness exists, including the empty witness.

**Status:** `open`.

**Prerequisites:** 1.04, 1.06, 1.16.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 1.20 — Nondeterministic class equality

**Acceptance criterion:** Prove for every language L: NP_ref(L) iff PrizeCertificatePolynomial(L), tracking both certificate-length and verifier-time bounds through the compilers.

**Status:** `open`.

**Prerequisites:** 1.18, 1.19.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 1.21 — P inclusion in NP

**Acceptance criterion:** Construct a total pair-input verifier that ignores the certificate, simulates a deterministic decider and accepts the empty certificate exactly for positive instances. Prove PrizeDeterministicPolynomial(L) implies PrizeCertificatePolynomial(L).

**Status:** `open`.

**Prerequisites:** 1.11, 1.12, 1.16.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 2.01 — CNF syntax

**Acceptance criterion:** Define Literal = variable index plus negation bit, Clause = finite list of literals, and Formula = finite list of clauses. Choose the exact unary-count binary serialization described in this specification.

**Status:** `open`.

**Prerequisites:** none.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 2.02 — Unary-count parser

**Acceptance criterion:** Implement u(n) = true^n ++ [false] and a total parser consuming a prefix. Prove round trip, uniqueness, exact consumption, and termination/rejection when the terminating false bit is absent.

**Status:** `open`.

**Prerequisites:** 2.01.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 2.03 — Formula codec

**Acceptance criterion:** Implement length-prefixed literal/clause/formula parsing. Prove parse(encode(F)) = some F, exact input consumption and rejection of trailing or truncated data. Prove the exact encoded length 1 + 2m + 3L + sum(variable indices).

**Status:** `open`.

**Prerequisites:** 2.02.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 2.04 — Variable indexing bounds

**Acceptance criterion:** Prove every unary-coded variable index is at most input length. When translating other SAT encodings, construct a polynomial-time renaming to compact indices and prove satisfiability is preserved in both directions. Do not expand an enormous binary index without this bound.

**Status:** `open`.

**Prerequisites:** 2.03.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 2.05 — Boolean semantics

**Acceptance criterion:** Define literal evaluation, disjunction for clauses and conjunction for formulas. Prove empty clause is false, empty formula is true, and specify repeated literals, negation and out-of-range certificate access.

**Status:** `open`.

**Prerequisites:** 2.01.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 2.06 — Finite assignment domain

**Acceptance criterion:** Restrict assignments to the occurring or maximum-index variable domain and prove extension/restriction preserves formula evaluation. This connects finite certificate words to ordinary variable assignments.

**Status:** `open`.

**Prerequisites:** 2.04, 2.05.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 2.07 — Binary SAT language

**Acceptance criterion:** Define SAT_u(x): x parses as F and F has a satisfying assignment. Prove every malformed binary input is outside the language.

**Status:** `open`.

**Prerequisites:** 2.03, 2.06.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 2.08 — SAT verification machine

**Acceptance criterion:** Construct a deterministic TM certificate verifier for SAT_u, prove correctness for every x,w and a polynomial certificate bound and transition bound. Include malformed formulas and short/invalid witnesses in the total behavior.

**Status:** `open`.

**Prerequisites:** 1.11, 1.16, 2.07.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 2.09 — Clocked source computation

**Acceptance criterion:** For an arbitrary fixed NP_ref machine with polynomial time bound T(n), derive a polynomial tape window and normalize accepting computations so that accepting early can be padded safely to T(n).

**Status:** `open`.

**Prerequisites:** 1.04.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 2.10 — Tableau variables

**Acceptance criterion:** Explicitly allocate Boolean variables for every needed time, cell, symbol, head and control-state position in the bounded computation tableau. Prove allocation is collision-free and polynomially bounded.

**Status:** `open`.

**Prerequisites:** 2.09.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 2.11 — Initial and well-formed tableau clauses

**Acceptance criterion:** Generate clauses for the encoded input row, blank boundaries, legal state/head positions and exactly-one symbol/state constraints. Prove each constraint family has its stated semantics and polynomial size.

**Status:** `open`.

**Prerequisites:** 2.10.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 2.12 — Transition clauses

**Acceptance criterion:** Generate bounded-locality clauses enforcing precisely one legal source transition between consecutive tableau rows, including nondeterministic choices. Prove local clauses are equivalent to the intended step relation under the well-formedness conditions.

**Status:** `open`.

**Prerequisites:** 2.11.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 2.13 — Acceptance clauses

**Acceptance criterion:** Generate and prove the accepting condition on the padded tableau. Ensure early acceptance, rejecting halts and clock exhaustion have the intended distinct meanings.

**Status:** `open`.

**Prerequisites:** 2.09, 2.12.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 2.14 — Run-to-assignment proof

**Acceptance criterion:** From any accepting clocked computation, construct a satisfying assignment of the generated CNF and prove every clause family true.

**Status:** `open`.

**Prerequisites:** 2.11, 2.12, 2.13.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 2.15 — Assignment-to-run proof

**Acceptance criterion:** From any satisfying assignment, reconstruct a legal accepting source computation. Prove uniqueness/consistency of each decoded row and validity of every transition.

**Status:** `open`.

**Prerequisites:** 2.11, 2.12, 2.13.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 2.16 — Tableau generator resource proof

**Acceptance criterion:** Implement the tableau-to-unary-CNF generator as a uniform machine and prove polynomial output length and transition count, including the unary encoding of allocated variable indices. Combine the preceding directions to establish SAT_u completeness for NP_ref.

**Status:** `open`.

**Prerequisites:** 2.03, 2.10, 2.14, 2.15.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 2.17 — Protocol instance domain

**Acceptance criterion:** Define a dependent instance (r,h,q,x), with h : RegisterTranslation r and q,x : RegisterState r. Fix the operator to registerStep h. No unencoded extra operation, oracle, noise advice or hidden phase is allowed.

**Status:** `open`.

**Prerequisites:** none.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 2.18 — Protocol binary encoder

**Acceptance criterion:** Implement the proposed canonical coefficient encoding: two metadata bits, two binary-intercept bits and twelve complement bits per key; two bits per register for h; unary r header. Prove encoder determinism and canonical coordinate ordering.

**Status:** `open`.

**Prerequisites:** 2.17.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 2.19 — Protocol decoder and exact length

**Acceptance criterion:** Implement a total decoder; reject metadata code 11 and malformed lengths. Prove decoder left inverse, soundness, unique full consumption and total length 35r+1 for this proposed direct-coefficient format. This format is separate from the existing 17-symbol framed channel codec.

**Status:** `open`.

**Prerequisites:** 2.02, 2.18.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 2.20 — Protocol binary language

**Acceptance criterion:** Define Q(x) to reject malformed protocol encodings and otherwise return protocolReachabilityCheck h q x_target. Connect its Boolean result to existence of a natural iterate using the existing correctness theorem.

**Status:** `open`.

**Prerequisites:** 2.19.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 2.21 — Actual SAT-to-protocol construction

**Acceptance criterion:** Construct a single total effective function f on binary words whose output is a protocol instance encoding. This is the missing mathematical reduction, not an assumption or a function supplied with a SAT-answer oracle. No such f is currently implemented.

**Status:** `open`.

**Prerequisites:** 2.07, 2.20.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 2.22 — Reduction forward direction

**Acceptance criterion:** For every satisfiable well-formed F, prove that f(encode(F)) decodes to a protocol instance with a reachable target. The witness construction must use the actual f, not redefine f from satisfiability.

**Status:** `open`.

**Prerequisites:** 2.21.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 2.23 — Reduction reverse direction

**Acceptance criterion:** For every well-formed F, prove that target reachability for f(encode(F)) yields a satisfying assignment of F. This must exclude all false positive protocol instances.

**Status:** `open`.

**Prerequisites:** 2.21.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 2.24 — Malformed source behavior

**Acceptance criterion:** Prove malformed formula strings map to a fixed valid rejecting protocol instance, or another explicitly proved rejecting output. A one-register zero state and a target with different metadata supply a possible rejecting-instance design.

**Status:** `open`.

**Prerequisites:** 2.07, 2.20, 2.21.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 2.25 — Complete many-one reduction

**Acceptance criterion:** Combine correctness on well-formed and malformed words with the actual generator and resource proofs to obtain, for every binary x, SAT_u(x) iff Q(f(x)), with polynomial generation time and polynomial output length.

**Status:** `open`.

**Prerequisites:** 2.22, 2.23, 2.24, 3.11, 3.12.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 3.01 — Uniform generator

**Acceptance criterion:** Supply one finite machine G independent of the input, implementing the reduction. A separate hard-coded answer or machine for each formula is not a uniform algorithm.

**Status:** `open`.

**Prerequisites:** 2.21.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 3.02 — Parsing cost

**Acceptance criterion:** Bound the transition count for reading, validating and parsing an input of N bits, including rejection paths and end-of-input checks.

**Status:** `open`.

**Prerequisites:** 2.03, 3.01.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 3.03 — Register-count computation

**Acceptance criterion:** Give the actual computation of r from the formula syntax. Prove termination and correctness of that computation without using a satisfiability decision as a primitive.

**Status:** `open`.

**Prerequisites:** 3.01, 3.02.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 3.04 — Translation construction

**Acceptance criterion:** Give the algorithm producing every bit of h from the parsed input and prove each produced bit equals the intended construction. Count all tape scans and writes.

**Status:** `open`.

**Prerequisites:** 3.03.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 3.05 — Initial-state construction

**Acceptance criterion:** Give the algorithm producing metadata and all fourteen binary coefficients of every q register. Prove its output does not presuppose an unknown satisfying assignment.

**Status:** `open`.

**Prerequisites:** 3.03.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 3.06 — Target-state construction

**Acceptance criterion:** Give the analogous algorithm for x_target, with a proof connecting its fields to the actual reduction rather than a precomputed SAT truth value.

**Status:** `open`.

**Prerequisites:** 3.03.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 3.07 — Register bound

**Acceptance criterion:** Prove r(F) <= c_r (N+1)^d_r for explicit constants independent of F, and combine it with the fixed-width coordinate format to bound output length. A bound on r alone is insufficient if any field silently carries an unbounded integer.

**Status:** `open`.

**Prerequisites:** 2.19, 3.03, 3.04, 3.05, 3.06.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 3.08 — Intermediate-value sizes

**Acceptance criterion:** Bound the bit lengths of counters, indices, addresses and arithmetic intermediates. Prove that operations on these values have their stated machine costs rather than unit-cost arithmetic on unbounded integers.

**Status:** `open`.

**Prerequisites:** 3.02, 3.07.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 3.09 — Total generation

**Acceptance criterion:** Prove every source input produces an answer within a finite bound, including invalid formulas. Prove any exceptional branch produces the specified rejecting encoding.

**Status:** `open`.

**Prerequisites:** 2.24, 3.04, 3.05, 3.06.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 3.10 — Generator instruction accounting

**Acceptance criterion:** Implement all loops, scans, copies, index calculations and output writes in the chosen machine model. Prove local loop invariants and costs; sum them without assuming syntax-level operations take one transition.

**Status:** `open`.

**Prerequisites:** 1.14, 1.16, 3.08, 3.09.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 3.11 — Exact generator realization

**Acceptance criterion:** Prove that the halted machine output is precisely the bit word f(x), including the complete header and every field, and that no unread or unvalidated data changes its meaning.

**Status:** `open`.

**Prerequisites:** 3.10.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 3.12 — Generator polynomial witnesses

**Acceptance criterion:** Exhibit fixed c_R,d_R with T_R(N) <= c_R (N+1)^d_R for every input. Separately prove the encoded output bound; time alone bounds length only after the output/write model has been justified.

**Status:** `open`.

**Prerequisites:** 3.07, 3.11.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 4.01 — Protocol parsing machine

**Acceptance criterion:** Implement the protocol decoder in the machine model and prove its relation to the mathematical decoder, including rejection and a transition bound on all input strings.

**Status:** `open`.

**Prerequisites:** 1.14, 2.19.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 4.02 — Machine storage representation

**Acceptance criterion:** Specify exactly how the unary header, h bits, current state, target state, scratch area and counters are laid out on tapes. Prove that the encoding relation is unambiguous.

**Status:** `open`.

**Prerequisites:** 4.01.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 4.03 — Rotation implementation

**Acceptance criterion:** Implement complement-coordinate rotation in the fixed 12-coordinate order, using scratch space or another proved method that does not overwrite unread source bits.

**Status:** `open`.

**Prerequisites:** 4.02.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 4.04 — XOR implementation

**Acceptance criterion:** Implement addition in ZMod 2 as a finite transition routine and prove its four input cases, including correct h-coordinate lookup.

**Status:** `open`.

**Prerequisites:** 4.02.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 4.05 — Metadata copying

**Acceptance criterion:** Implement and prove preservation of each two-bit metadata field and preservation of register count and key-field boundaries.

**Status:** `open`.

**Prerequisites:** 4.02.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 4.06 — One-step simulation

**Acceptance criterion:** Prove that the combined rotation, XOR and metadata routines transform a well-encoded q to a well-encoded registerStep h q, with an explicit transition cost bound and unchanged h and target buffers.

**Status:** `open`.

**Prerequisites:** 4.03, 4.04, 4.05.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 4.07 — Loop initialization

**Acceptance criterion:** Prove that the current-state buffer initially contains q, the phase counter is zero and every fixed buffer remains valid.

**Status:** `open`.

**Prerequisites:** 4.02.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 4.08 — Full equality routine

**Acceptance criterion:** Implement comparison of all metadata, binary-intercept and complement bits against the target. Prove true iff equality of full RegisterState values; phase equality alone is insufficient.

**Status:** `open`.

**Prerequisites:** 4.02.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 4.09 — Phase-loop invariant

**Acceptance criterion:** Prove that at loop entry k the current buffer represents (registerStep h)^k(q), h and the target remain unchanged, and 0 <= k < 12.

**Status:** `open`.

**Prerequisites:** 4.06, 4.07.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 4.10 — Successful comparison correctness

**Acceptance criterion:** Prove any accepting comparison produces a genuine finite-index witness of target reachability.

**Status:** `open`.

**Prerequisites:** 4.08, 4.09.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 4.11 — Twelve-failure correctness

**Acceptance criterion:** Prove that rejecting after all twelve comparisons means no natural iterate reaches the target, using the period theorem and the existing Boolean rejection theorem.

**Status:** `open`.

**Prerequisites:** 4.08, 4.09.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 4.12 — Loop termination and count

**Acceptance criterion:** Prove the phase counter advances, cannot overflow its intended representation, and makes at most twelve comparisons and at most eleven necessary step updates. Count initialization, updates and final exit.

**Status:** `open`.

**Prerequisites:** 4.09.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 4.13 — Malformed-input rejection

**Acceptance criterion:** Prove all malformed binary instance strings terminate and reject, and cannot accidentally reach the successful-comparison branch.

**Status:** `open`.

**Prerequisites:** 4.01.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 4.14 — Output and halting convention

**Acceptance criterion:** Implement and prove halted symbol 1 for acceptance and 2 for rejection at the observed head position, matching prizeAccepts and prizeBooleanOutput exactly.

**Status:** `open`.

**Prerequisites:** 1.12, 1.13, 4.10, 4.11, 4.13.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 4.15 — Protocol-machine polynomial witnesses

**Acceptance criterion:** Exhibit fixed c_Q,d_Q with T_Q(M) <= c_Q (M+1)^d_Q for every M-bit input. Include parsing, repeated comparisons, scans, copies, at most twelve candidates and all failure branches.

**Status:** `open`.

**Prerequisites:** 4.06, 4.08, 4.12, 4.14.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 4.16 — Generator/decider composition

**Acceptance criterion:** Construct an actual finite machine running G, preparing its output as the input to Q, and then running Q. Prove state-renaming, head positioning, delimiter handling and buffer transfer, with an explicit communication cost.

**Status:** `open`.

**Prerequisites:** 1.14, 3.11, 4.14.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 4.17 — Composed decision correctness

**Acceptance criterion:** Prove the composed machine accepts exactly SAT_u on every binary input, by the reduction equivalence and the protocol-machine correctness, and rejects otherwise.

**Status:** `open`.

**Prerequisites:** 2.25, 4.10, 4.11, 4.13, 4.16.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 4.18 — Composed polynomial time

**Acceptance criterion:** Substitute the output-length polynomial into T_Q and add generation and communication costs. Exhibit one coefficient and exponent independent of the input, as detailed in the composition formula in this specification.

**Status:** `open`.

**Prerequisites:** 3.12, 4.15, 4.16.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.

## 4.19 — Class-equality consequence

**Acceptance criterion:** Use SAT_u completeness and closure of polynomial reductions to give a polynomial decider for every NP_ref language; combine with P inclusion in NP and model correspondence to obtain class equality. This would oppose the existing inequality conjecture; no such equality is currently proved.

**Status:** `open`.

**Prerequisites:** 1.17, 1.20, 1.21, 2.16, 4.17, 4.18.

**Outstanding implementation/proof:** the acceptance criterion above is not established by this execution. There is no new theorem or implementation claimed for this entry. Its prerequisites must be supplied, followed by the specified construction or proof; none is inserted into Lean as a hypothesis standing in for the result.
