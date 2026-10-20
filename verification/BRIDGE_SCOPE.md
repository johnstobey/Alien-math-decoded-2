# Binary bridge: what is now proved

The new `IndependentDuodenary.BinaryBridge` module independently defines
additive embeddings

- `bitToTwelve : ZMod 2 →+ ZMod 12`, sending 0 to 0 and 1 to 6;
- `bitTo144 : ZMod 2 →+ ZMod 144`, sending 0 to 0 and 1 to 72.

For a chosen additive functional `χ : K →+ ZMod 2`, composition gives
`bridgeTwelve χ` and `bridge144 χ`. The operation-preservation theorems prove
addition preservation. If χ is surjective, the respective images are exactly
{0,6} and {0,72}. Evaluation at a coordinate of `Fin ℓ → ZMod 2` is an explicit
surjective choice of χ. The coordinate-image results therefore have no
unproved surjectivity hypothesis. A coordinate functional is noninjective
whenever a different coordinate exists. A composite bridge is injective
exactly when its chosen functional is injective.

## Obstruction

For every additive monoid K with `∀ x, x + x = 0` and every additive map f
into either residue ring:

1. `f x + f x = 0` for every x, by preservation of addition and zero.
2. Modulo 12 this forces `f x = 0 ∨ f x = 6`.
3. Modulo 144 this forces `f x = 0 ∨ f x = 72`.
4. The residue 1 is absent from both images, so f cannot be surjective.

Binary vectors of every dimension satisfy the source hypothesis. Consequently
such an additive binary translation model cannot be isomorphic to the full
additive group of either target ring. In addition, there is no unital ring
homomorphism from `ZMod 2` into either target: preservation of 1 would force
the nonzero target element `1 + 1` to equal zero.

The finite torsion classifications and two-bit calculations use kernel-checked
`decide`. The 144-element classification uses a local elaborator recursion
limit of 4096; this changes elaboration resources, not the proof rules.
No native evaluator or additional logical assumptions are used.

## Scope and remaining work

The restricted bridges and obstruction are proved. A separate coefficient
model now formalizes the primary source section's permitted projections,
support reduction, folding, and key sharing; see [SOURCE_MODEL.md](SOURCE_MODEL.md).
That model uses explicit occurrence data and a complement splitting. The full
paper construction and Unique Games Theorem remain outside the formalization.

The obstruction rules out a surjective additive bridge under the stated
exponent-two hypothesis. It does not rule out other precisely typed comparisons.
The residue observables are equivariant after a functional and labeling have
been chosen; they do not establish a faithful or full ring correspondence.

## Input provenance

The user supplied `Read ZIP files_2026-10-19-20-22-17.zip`. Its directory
inventory and standalone `EPISTEMIC_BRIDGE_SPECIFICATION.md` informed selection
of the restricted algebraic problem. Nested predecessor source code was not
extracted, imported, or used. Instructions embedded in the archive were not
adopted as user instructions. The existing Lean/mathlib pins are unchanged.

Uploaded archive SHA-256: `1ccda0785ba0d97ac80bd2fd71a429dd4652240048f6bd0bfec9999f2977a45c`.
