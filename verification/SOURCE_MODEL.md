# Source coefficient model: proof scope and provenance

## Frozen primary source

Repository: <https://github.com/openai/math>.
Commit: `1581d4cbdd69a0faf34b2089614fe2a814316a6a`.
File: `preprints/The-Unique-Games-Theorem-September-23-2026/build/sections/03-game.tex`.

[Permitted projections, lines 130–163](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Unique-Games-Theorem-September-23-2026/build/sections/03-game.tex#L130),
[reduction and key compatibility, lines 165–255](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Unique-Games-Theorem-September-23-2026/build/sections/03-game.tex#L165),
and [intercept translation and answers, lines 259–289](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Unique-Games-Theorem-September-23-2026/build/sections/03-game.tex#L259)
were inspected directly. The source labels are `eq:outer-projection`,
`eq:reduced-table-intercept`, `eq:table-folding`, and `eq:key-sharing`.
This source pin identifies the examined definitions, not a certification of
all the paper's claims. No predecessor project was accessed or imported.

## Representation

`SourceEquation` records an occurrence ID, three variable IDs, and a parity bit.
`SourcePosition` selects a bit. A block is retained, projected to a singleton,
or omitted. `Fin k` indexes local blocks independently of their IDs, so repeated
IDs in different positions do not collapse local coordinates.

A coefficient table has a homogeneous intercept and two slopes per full
block. Projected coordinate types have exactly two local bits for retained
equations, one for singletons, and no local bits for omissions. A common
homogeneous bit is retained separately. True and false encode the two parity
bits. The third actual coordinate is `b*t₀ + x + y`.

Reduction distinguishes the zero, first-only, second-only, equal-nonzero,
and distinct-nonzero slope patterns. A third-position singleton adds the
parity-times-slope correction to the intercept. Distinct nonzero binary
slopes are proved to give an injective pair map; a nonzero singleton slope
also gives an injective map. These proofs justify the algebraic distinctions
used by the reduction without assuming numerical rank claims.

The reduced key records retained block metadata and all coefficients, plus
the entire corrected intercept. With an explicit splitting `V = K × W`,
its intercept is stored as its K and W components. Retained equation IDs
are interpreted relative to the caller's fixed occurrence data; constructing
a global parity-instance registry is outside this model.

## Machine-checked results

| Source obligation | Lean result |
| --- | --- |
| Actual-bit homogeneous projection is surjective | `sourceBlockProjection_lift`, `permittedProjection_surjective` |
| Homogeneous coordinate is preserved | `permittedProjection_preserves_homogeneous` |
| Coefficient pullback equals composition on table values | `source_block_pullback_evaluation`, `source_table_pullback_evaluation` |
| Explicit support reconstructs slopes and intercept | `sourceSupportBlock_pullback`, `sourceSupportBlock_correction`, `pullback_reducedSourceTable` |
| Original table factors through the support projection | `source_reduction_factorization` |
| Support projection is surjective and reduced function unique | `source_reduction_projection_surjective`, `source_reduction_unique` |
| Permitted pullback preserves the complete reduced key | `permitted_pullback_exact_key` |
| Third-position corrections cancel | `pullback_block_intercept`, `pullback_reduced_intercept` |
| Intercept translation is a free group action | `translateKey_zero`, `translateKey_add`, `translateKey_free` |
| Orbits and canonical representatives | `keyOrbit_iff_vertex_eq`, `canonicalKey_unique`, `canonicalKey_reconstruct` |
| Translated and canonical keys are represented by tables | `source_key_translation_representable`, `source_canonical_key_representable` |
| Restored-answer folding | `source_folding`, `source_table_folding` |
| Restored answers agree under permitted pullback | `source_key_sharing`, `binary_source_key_sharing` |
| Chosen residue observables are equivariant | `residue_folding_twelve`, `residue_folding_144` |

These equalities hold for all the quantified inputs, rather than sampled
instances. The generic key-sharing theorem explicitly requires exponent two;
`binary_source_key_sharing` discharges it for arbitrary finite-dimensional
binary K and W. The reduction-factorization and uniqueness results quantify
over modules over `ZMod 2`; `binary_module_double_zero` derives the needed
cancellation from that module structure. Key compatibility is proved from
the block rules, not supplied as an assumption.

## Boundaries

The 40 new results formalize this coefficient model of the cited source
section. They do not prove the Unique Games Theorem, the weighted parity gap,
the latent gadget, probability estimates, the matrix test, completeness,
soundness, or the reduction's polynomial running time. The caller supplies
occurrence data and an explicit complement splitting. No theorem here
constructs a global instance from SAT or packages the full paper construction
as a single Lean object. Homogeneous maps are represented by their coordinate
functions and evaluated coefficient expressions; general `LinearMap` packaging
and a formal end-to-end equivalence with every source definition are not asserted.

The residue-valued observables require an explicitly chosen binary functional
and vertex labeling. Their equivariance does not turn them into faithful or
surjective maps to the full residue rings. The previously proved exponent-two
obstruction remains in force. No twelve-step cycle or full ring identification
has been established.

Lean and mathlib pins are unchanged. All project theorems are included in the
build and in `verification/THEOREMS.md` and `axioms-and-proofs.txt`.

Examined primary-source file SHA-256: `5e721242c7a3ba038f6f571bbf8a03da412f4f21cc5b7e2188a61bdb2bd2fa4a`.
