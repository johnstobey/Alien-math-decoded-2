# Independent structural ledger: formal results

The user-supplied `Independent_Structural_Proof_Ledger.md` is used as a list
of mathematical problems. Its embedded workflow suggestions and repository
audit note are not treated as instructions or as an inventory of this checkout.
No predecessor project was accessed, imported, or synchronized.

This extension adds 58 theorem declarations in three modules. The project now
has twelve library modules (including the root import module) and 150 theorems.
Lean 4.14.0 and the existing mathlib revision are unchanged.

## Ledger-to-proof correspondence

| Ledger entry | Formal result |
| --- | --- |
| P1: Chinese remainder decomposition | `twelveCRT` is a ring equivalence `ZMod 12 ≃+* ZMod 4 × ZMod 3`. Its inverse is proved to be `9*a.val + 4*b.val` modulo 12. Both round trips are proved. |
| P2: Dihedral symmetries | Rotation has period 12 and no smaller positive period; reflection is an involution and conjugates rotation to its inverse. The dihedral action is a faithful homomorphism into permutations. Every map preserving the labelled cyclic distance is proved dihedral, and that complete isometry space has cardinality 24. |
| P3: Antipodal involution | Addition by 6 is a fixed-point-free involution. The six explicit two-element pairs cover all twelve labels and are pairwise disjoint. |
| P4: Difference and distance invariance | Directed differences and cyclic distance are translation invariant. Reflection preserves cyclic distance, and the full dihedral action preserves it. Distances are bounded by 6 and all values 0 through 6 occur. |
| P5: Exact reversible encoding | A semantic-class decoder forces colliding encodings to have equivalent meanings. Exact decoding implies injectivity and a finite cardinality bound; an infinite type cannot have an exact decoder through a finite state space. Length-n words over twelve labels have cardinality `12^n`. An explicit variable-length unary word encoding has a length decoder and is injective on all natural numbers. |
| P6: Bounded error correction | Hamming distance satisfies the triangle inequality. If distinct codewords are separated by at least d and `2*t < d`, two codewords within t errors of a received word must coincide. A concrete repetition code has separation n; for length 3, the explicit majority decoder recovers every payload symbol after at most one corrupt position. |
| P7: Affine permutations | The unit-affine maps form an actual subgroup of permutations. Composition is `(a,b)*(c,d)=(ac,ad+b)`, the parameterization is injective, and the group has cardinality 48. There are four units, with residues 1, 5, 7 and 11. Multiplication by 5 gives a checked affine permutation that changes cyclic distance. |

## Objects and hypotheses

The symmetry classification is a theorem about twelve labels with the explicit
metric `min((b-a).val, 12-(b-a).val)`. It does not introduce an embedding into
Euclidean space or identify this finite metric with a particular physical object.
The 24 isometries and 48 affine permutations are different precisely defined
families, rather than competing counts of the same family.

The semantic theorem uses an explicitly supplied `Setoid` on expressions and
a decoder into its quotient. It proves the collision condition without assuming
that an encoding automatically descends to the quotient. Such descent separately
requires the encoding to respect the supplied equivalence relation. For a codec
already defined on meanings, an exact left inverse proves injectivity directly.
No interpretation of natural-language meanings or particular historical texts
is supplied by these general statements.

The general error-correction theorem retains the code, its separation bound,
and the decoder's radius guarantee as explicit hypotheses. The concrete triple
repetition result supplies its encoder, its separation proof and its decoder;
it does not assume correctness of that decoder. The error model counts changed
positions and permits arbitrary replacement symbols. This is a substitution
model, without an assertion about insertions, deletions, or unlimited corruption.

The variable-length construction proves unbounded representational capacity by
an actual left inverse. It makes no efficiency claim: an integer n is encoded
as n zero symbols. Fixed-length capacity remains bounded by `12^n`.

## Next mathematical breadcrumb

The finite structure, exact-decoding conditions, and a concrete error-correcting
codec are now available. A source-specific relational grammar still requires
explicit expression constructors, a specified meaning space, actual encoding
and decoding maps, and proofs that the sourced rules preserve those meanings.
Those objects must be supplied or independently constructed from a definite
corpus; neither cyclic symmetry nor the generic codec establishes them.

The earlier coefficient model and binary-bridge obstruction remain proved.
This extension makes no new claim about the full Unique Games Theorem or a
Millennium Problem. Exact theorem statements, proof terms, direct dependencies,
and transitive axioms are recorded in `THEOREMS.md` and `axioms-and-proofs.txt`.

Input ledger SHA-256: `d8a7b10af301a90a7d5440a26e8be59185f0ed8ad60db4744ee601111afd645a`.
