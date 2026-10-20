# Operator and exact-key representation

Implementation: [`SourceKeyRepresentation.lean`](../IndependentDuodenary/SourceKeyRepresentation.lean).
Checked statements and executable guards: [`KeyDirectives.lean`](../examples/KeyDirectives.lean).

## Carrier and chosen operator

\[
M=\operatorname{Fin}(3),\qquad K=\operatorname{Fin}(2)\to\mathbb F_2,
\qquad W=(\mathbb Z/12\mathbb Z)\to\mathbb F_2,
\qquad Q=\operatorname{ExactKey}(M,K,W).
\]

\[
T(m,k,w)=(m,k,i\mapsto w(i+1)).
\]

The index set of W has twelve coordinates. This coordinate permutation is a
chosen operator on this finite instance of the current model. It is not asserted
to be an operator defined by the external paper. Thus the existence/periodicity
problem for this chosen carrier is resolved; external-source identification at
node J remains a separate proposition.

`key_cycle_iterate` proves, for every n and q,
\[
T^n(m,k,w)=(m,k,i\mapsto w(i+n)).
\]

`key_cycle_period_iff` proves
\[
(\forall q\in Q,\ T^n(q)=q)\iff12\mid n.
\]

`key_cycle_no_shorter_positive_period` proves that no positive n below twelve
is a period of the operator. `key_cycle_distinct_from_translation` proves
\[
\forall h\in K,\quad T\ne(q\mapsto\operatorname{translateKey}(h,q)).
\]

For \(w_a(i)=\mathbf1[i+a=0]\), let \(q_0=(0,0,w_0)\). The vertex
labeling is
\[
f(m,w)=\sum_{i\in\mathbb Z/12\mathbb Z}\begin{cases}-i&w(i)=1,\\0&w(i)\ne1.\end{cases}
\]

`key_one_hot_phase`, `key_cycle_witness_phase`, and
`key_cycle_orbit_equivariance` prove
\[
f(0,w_a)=a,\qquad f(v(T^nq_0))=n\pmod{12},\qquad
f(v(T(T^nq_0)))=f(v(T^nq_0))+1.
\]

`key_cycle_witness_period_iff` proves that this witness has least positive
period twelve. The global operator has order twelve; not every key has least
period twelve. In particular, constant complement vectors are fixed points.
`key_cycle_no_global_station_shift` proves
\[
\neg\exists g:Q\to\mathbb Z/12\mathbb Z,\quad
\forall q,\ g(Tq)=g(q)+1.
\]

The station-shift preservation equation above is therefore restricted to the
explicit one-hot orbit. The W-valued vertex observable preserves the coordinate
permutation on all Q (`key_cycle_vertex_observable`). The operator commutes with
binary intercept translation (`key_cycle_commutes_translation`).

## Framing and decoding

The word alphabet is \(\mathbb Z/12\mathbb Z\). Metadata is encoded by its
value 0, 1, or 2. Binary coefficients are encoded by digits 0 and 1. The fourteen
payload bits consist of two K coordinates followed by twelve W coordinates in
canonical residue order.

\[
E(q)=[11,\operatorname{metadata}(q)]\mathbin{+\!+}
\operatorname{bits}(q)\mathbin{+\!+}[10],\qquad |E(q)|=17.
\]

`decodeExactKey` is a total function
\[
D:\operatorname{List}(\mathbb Z/12\mathbb Z)\to\operatorname{Option}(Q).
\]

It checks the header, metadata range, exactly fourteen binary digits, and the
single final terminator. The following statements are kernel checked:

- `exact_key_decode_encode`: \(D(E(q))=\operatorname{some}(q)\).
- `exact_key_parse_sound`: \(D(xs)=\operatorname{some}(q)\Rightarrow xs=E(q)\).
- `exact_key_reject_malformed`: \((\forall q,\ xs\ne E(q))\Rightarrow D(xs)=\operatorname{none}\).
- `exact_key_encode_length`: \(|E(q)|=17\).
- `exact_key_reject_length`: \(|xs|\ne17\Rightarrow D(xs)=\operatorname{none}\).
- `exact_key_encode_injective`: \(E(q)=E(r)\Rightarrow q=r\).

Separate rejection statements cover an incorrect header, out-of-range metadata,
a nonbinary first payload digit, and any incorrect suffix after valid payload
bits. Parse soundness covers malformed digits at every payload position.

## Transported translation

\[
U_h(xs)=\begin{cases}
 E(\operatorname{translateKey}(h,q))&D(xs)=\operatorname{some}(q),\\
 []&D(xs)=\operatorname{none}.
\end{cases}
\]

`exact_key_word_translation` and `exact_key_word_translation_involution` prove
\[
U_h(E(q))=E(\operatorname{translateKey}(h,q)),\qquad U_h(U_h(E(q)))=E(q).
\]

`exact_key_word_translation_invalid` proves that invalid words map to the empty
word, which D rejects. No insertions/deletions or error-correction guarantee is
asserted for this framing. The decoder is lossless on the complete chosen key,
including metadata and both intercept components.
