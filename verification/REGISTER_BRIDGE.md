# Product dynamics and the initial modular implication bridge

## Structural dependencies

```
SourceKeyRepresentation
  ├─ key_cycle_period_iff, key_cycle_iterate, translateKey_add
  ├─ exact_key_decode_encode, exact_key_parse_sound
  └─ binary_vector_double_zero
       ↓
RegisterDynamics
  ├─ projection/translation commutation
  ├─ PhaseRegular preservation and phase iteration
  ├─ exact operator periods and noncollapsing regular orbits
  └─ relativePhases classification and aggregate-collapse witness
       ↓
RegisterBridge
  ├─ product codec left inverse and parse soundness
  ├─ inductive exact transport and equality reflection
  └─ concrete metadata and modular relative-phase implications
```

These are mathematical dependency summaries. Exact direct dependencies and
proof terms are in [axioms-and-proofs.txt](axioms-and-proofs.txt).
Definitions and proofs:
[RegisterDynamics.lean](../IndependentDuodenary/RegisterDynamics.lean),
[RegisterBridge.lean](../IndependentDuodenary/RegisterBridge.lean).
Compiled statement checks and twelve guards:
[RegisterDirectives.lean](../examples/RegisterDirectives.lean).

## J: product carrier and transformations

\[
Q_r=\operatorname{Fin}(r)\to\operatorname{RepresentedKey},\quad
H_r=\operatorname{Fin}(r)\to\operatorname{KeyBinary},\quad
A_r=\operatorname{Fin}(r)\to\mathbb Z_{12}.
\]

\[
(Cq)_i=T(q_i),\quad (\tau_hq)_i=\operatorname{translateKey}(h_i,q_i),\quad
S_h=\tau_h\circ C,\quad (\pi_\sigma q)_i=q_{\sigma(i)}.
\]

The selectors \(\sigma:\operatorname{Fin}(s)\to\operatorname{Fin}(r)\)
need not be injective. All three transformation/projection equations are proved:
\[
\pi_\sigma C=C\pi_\sigma,\quad
\pi_\sigma\tau_h=\tau_{h\circ\sigma}\pi_\sigma,\quad
\pi_\sigma S_h^n=S_{h\circ\sigma}^n\pi_\sigma.
\]

`register_cycle_commutes_translation` proves \(C\tau_h=\tau_hC\).
Translation leaves each vertex and its phase label unchanged.
`register_step_iterate_formula` proves
\[
(S_h^nq)_i=\operatorname{translateKey}(n\mathbin{\bullet}h_i,T^n(q_i)).
\]

`register_step_period_twelve` proves \(S_h^{12}q=q\) for every q, including
states outside the one-hot domain. For \(r>0\),
`register_cycle_period_iff` and `register_step_period_iff` prove
\[
(\forall q,\ C^nq=q)\iff12\mid n,\qquad
(\forall q,\ S_h^nq=q)\iff12\mid n.
\]

The empty product has a unique state, so every n is a period
(`register_empty_cycle_period`). Nonemptiness cannot be omitted from an
exact-period assertion.

## Boundary and phase invariants

\[
\operatorname{PhaseRegular}(q)\iff
\forall i,\ \exists a_i\in\mathbb Z_{12},\quad (q_i).w=\operatorname{keyOneHot}(a_i).
\]

This predicate is preserved under C, every translation, S_h, subsystem
projection, and every iterate of S_h. The constructor `phaseRegisterState a`
satisfies it with no assumed regularity hypothesis and has phase vector a.

For \(\Phi(q)_i=\operatorname{keyPhaseLabel}(v(q_i))\),
`register_step_phase_iterate` proves on this domain
\[
\Phi(S_h^nq)_i=\Phi(q)_i+n\pmod{12}.
\]

With \(\Delta(a)_{ij}=a_j-a_i\),
`register_step_relative_invariant` therefore proves
\[
\Delta(\Phi(S_h^nq))=\Delta(\Phi(q)).
\]

For a retained index \(b:\operatorname{Fin}(r)\),
`register_regular_orbit_no_collapse` proves
\[
S_h^nq=S_h^mq\Longrightarrow n=m\pmod{12}.
\]

`register_regular_orbit_injective` supplies an injection of the twelve residue
positions into the orbit. This assertion needs the one-hot boundary and a
nonempty product; arbitrary keys may have smaller orbits.

A scalar aggregate has a different guarantee:
\[
\sum_i\Phi(S_h^nq)_i=\sum_i\Phi(q)_i+r n\pmod{12}.
\]

`two_register_sum_collapse` proves that the distinct vectors (0,0) and (6,6)
have the same sum. The executable checks instantiate this collision at orbit
times 0 and 6 of a two-register regular state. Thus vector retention avoids
this collision; scalar summation does not.

## L: typed representation bridge

\[
W_r=\operatorname{Fin}(r)\to\operatorname{List}(\mathbb Z_{12}),\qquad
E_r(q)_i=\operatorname{encodeExactKey}(q_i).
\]

The register count r is part of the type. This is a product of individually
framed words, not an unframed concatenation with an inferred register count.
`decodeRegisterWords` parses every register and fails if any one fails.

`register_decode_encode`, `register_parse_sound`, and
`register_reject_malformed` prove
\[
D_r(E_r(q))=\operatorname{some}(q),\qquad
D_r(w)=\operatorname{some}(q)\Longrightarrow w=E_r(q),
\]
\[
(\forall q,\ w\ne E_r(q))\Longrightarrow D_r(w)=\operatorname{none}.
\]

For any explicitly supplied state transformation A, define
\[
\widehat A(w)=\begin{cases}E_r(Aq)&D_r(w)=\operatorname{some}(q),\\
(i\mapsto[])&D_r(w)=\operatorname{none}.
\end{cases}
\]

The foundational inductive lemma is `register_transport_iterate`:
\[
\forall n,q,\qquad \widehat A^{\,n}(E_r(q))=E_r(A^nq).
\]

Its base case is reflexivity. Its successor case uses the induction hypothesis
and `register_transport_encode`. The resulting decoder and equality-reflection
statements are also proved:
\[
D_r(\widehat A^{\,n}(E_r(q)))=\operatorname{some}(A^nq),
\]
\[
\widehat A^{\,n}(E_r(q))=\widehat B^{\,m}(E_r(p))
\iff A^nq=B^mp.
\]

Thus exact transport adds no state collisions beyond those of the specified
transformations. No arbitrary malformed word is assumed to be a representation.

## Explicit modular comparator and discharged instances

The external modular carrier in this comparison is exactly A_r, with relation
\[
\operatorname{ExternalRelativeEquivalent}(a,b)\iff\forall i,j,\ \Delta(b)_{ij}=\Delta(a)_{ij}.
\]

For a retained index b₀, `external_relative_equivalence_offset` proves
\[
\operatorname{ExternalRelativeEquivalent}(a,b)
\iff\exists c\in\mathbb Z_{12},\ \forall i,\ b_i=a_i+c.
\]

This is a defined modular relation. It is not an asserted equivalence of an
external paper or a named complexity/analysis theorem.

`register_word_modular_bridge_phase` discharges the concrete initial conditions:
for every a, h, and n, decoding
\(\widehat S_h^{\,n}(E_r(\operatorname{phaseRegisterState}(a)))\)
produces a regular state p satisfying
\(\operatorname{ExternalRelativeEquivalent}(a,\Phi(p))\).
There is no assumed preservation premise in this concrete theorem.

`register_word_metadata_bridge` proves metadata equality with the initial state
for every initial q, without a regularity premise. Projection of encoded
iterates commutes with the matching subsystem transformation
(`register_word_projection_bridge`). Encoded regular orbit positions are
injective (`register_word_regular_orbit_injective`).

The general lemma `register_inductive_invariant_transport` has the explicit
premise \(\forall q,\ P(q)\Rightarrow P(Aq)\). It is a conditional induction
principle, not a claim that arbitrary P is invariant. The concrete modular and
metadata instances above prove their required preservation facts.

Finally, `external_relative_equivalence_not_lossless` constructs distinct exact
representations whose phase vectors are relatively equivalent. This proves
that the modular comparator does not replace the lossless full-key codec.
The implications established here are precisely these typed representation
and modular-invariant results; no unspecified external theorem is inferred.
