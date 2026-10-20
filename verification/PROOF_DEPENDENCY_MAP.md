# Proof dependency map and next obligation

Evidence baseline: commit `08d2715a6e73e03374794d9e20522728c46e50d3`,
211 checked theorem declarations. This map adds no mathematical assumptions or
new Lean theorems. Node labels below describe research obligations; they are
not declaration names. The exact machine dependency inventory remains
[THEOREMS.md](THEOREMS.md) and [axioms-and-proofs.txt](axioms-and-proofs.txt).

## What the supplied materials actually claim

The supplied structural ledger states P1–P7: finite-ring decomposition,
symmetries, an antipodal involution, difference/distance invariance, conditions
for reversible encoding, conditions for error correction, and affine
permutations. These are now formalized. Its explicit boundaries say that they
do not establish a historical-text interpretation or imply the Riemann
hypothesis or Unique Games Conjecture. It supplies no theorem deriving a
Millennium Prize result from those seven statements.

The supplied bridge specification proposes a comparison between binary exact-key
folding and modular stations. It explicitly classifies the broad correspondence
as an analogy, while giving a restricted additive map to test. Its historical
inventory of predecessor declarations is not an inventory of this independent
checkout; no predecessor source was consulted for this map.

The supplied HTML defines an arithmetic calculator and makes stronger
interpretive assertions about astronomical assignments. Its arithmetic is now
modeled, but those assertions do not follow from the computed examples.

Accordingly, there is no single stated central theorem in these materials to
which all 211 results are premises. The main proposed connection we can make
precise is the **source-operation-to-station correspondence**. The table below
separates its proved restricted version from stronger versions.

## Claims, prerequisites, and evidence

| Node | Precise content | Required inputs | Status and evidence |
| --- | --- | --- | --- |
| A: twelve-state structure | CRT decomposition, 24 cyclic isometries, 48 affine permutations | Explicit `ZMod 12` state space and cyclic distance | Proved: `twelveCRT_bijective`, `cyclic_station_isometry_card`, `affine_station_group_card`; see [ledger correspondence](STRUCTURAL_LEDGER.md). |
| B: source coefficient model | Reduction factorization, uniqueness, permitted-projection compatibility, exact-key folding | Fixed occurrence data, binary coefficient spaces, specified complement splitting | Proved in the stated model: `source_reduction_factorization`, `source_reduction_unique`, `permitted_pullback_exact_key`, `source_folding`; see [source scope](SOURCE_MODEL.md). |
| C: restricted residue observable | `R(translateKey h q) = R(q) + bridgeTwelve χ h` | B's keys, an explicitly chosen additive functional χ and vertex labeling | Proved: `residue_folding_twelve`. The translation image is contained in `{0,6}`; see `image_in_two_stations`. |
| D: station operation semantics | Every grammar expression denotes a permutation; its compiled affine parameters determine its whole meaning | Explicit `StationExpr` constructors and semantics | Proved: `station_compile_correct`, `station_meaning_iff_compiled`. |
| E: restricted source-to-grammar action | Applying the grammar shift for χ,h to R(q) equals R(translateKey h q) | C and the grammar shift interpretation in D | Proved: `source_shift_observable_equivariance`. This transports the chosen observable, not the entire key. |
| F: exact/robust operation codec | Decode an encoded semantic class exactly; recover it after at most one substitution per triple | D's semantics and the specified repetition channel | Proved: `station_meaning_decode_encode`, `protected_station_semantic_recovery`. |
| G: calculator arithmetic | Exact positive-rational pipeline equals its normalized implementation | Positive numerator/denominator and a natural harmonic | Proved: `cipher_pipeline_correct`; source mapping in [calculator scope](CIPHER_VALIDATOR.md). |
| H: protected calculator result | Recover G's residue after at most one substitution per digit triple | G and the separate result-payload codec | Proved: `cipher_pipeline_protected_recovery`. It does not recover the period. |
| I: fixed binary fold as a one-station rotation | For a fixed binary h and nonempty key carrier, `f(translateKey h q) = f(q)+1` for every q | An unrestricted observable f with this preservation equation | Impossible: the source operation squares to identity, while the target shift by 1 does not. See the derivation below. |
| J: some other genuine source operator has exact period 12 | Identify a source-defined T and prove its twelve iterates return, with no shorter positive period, together with a compatible station map | A different explicitly sourced operator, its carrier, and a preservation equation | Unresolved: no such source operator is identified in the examined material. A's local rotation does not supply it. |
| K: lossless source-key representation | Encode complete keys into structured twelve-symbol words with a decoding left inverse and a compatible translated-word operation | Explicit encodings of metadata and both intercept components, framing, decoder | Not constructed. C and E are observables and do not provide a decoder for full keys. |
| L: stronger mathematical conclusion | A named external theorem follows from specified source/model properties | Its exact statement, source/model equivalence, and a sufficient implication | Not formulated or proved here. Neither modular closure nor the calculator's zero remainder supplies this implication. |

## Established connections and missing connections

```mermaid
flowchart TD
  B[Source coefficient model: proved] --> C[Chosen residue observable: proved]
  A[Twelve-state structure: proved] --> D[Station semantics: proved]
  C --> E[Restricted action transport: proved]
  D --> E
  D --> F[Operation codec and recovery: proved]
  G[Exact calculator: proved] --> H[Result codec and recovery: proved]
  B -. requires full encoders and decoder .-> K[Lossless key words: not constructed]
  B -. fixed translation cannot supply this .-> J[Different source operator of exact period 12: unidentified]
  J -. would still require a sufficient implication .-> L[External theorem: not formulated]
```

Arrows summarize mathematical prerequisites, not Lean import edges. In
particular, there is no established arrow from G or H to J or L, and no arrow
from error correction to truth of an interpretation.

## First missing implication: examine the operator before assuming a cycle

A candidate correspondence must first name a source carrier Q, a source
operation T, an observable f, and a preservation equation. For the fixed
binary translation already present in the source model, put

`T(q) = translateKey h q`, with `h+h=0`.

The existing `translateKey_add` and `translateKey_zero` give `T(T(q))=q`.
If one additionally asserted `f(T(q))=f(q)+1` in `ZMod 12`, applying that
assertion twice would give

`f(q) = f(T(T(q))) = f(q)+2`.

Cancellation would force `2=0` in `ZMod 12`, which is false. Thus this candidate
fails even without assuming that f is injective or surjective. This paragraph
is a mathematical derivation from checked results, not an additional separately
compiled Lean declaration. The existing checked theorem
`binary_map_not_surjective_twelve` independently rules out every surjective
additive bridge from an exponent-two source. These are specific obstructions;
they do not rule out all possible source structures or comparisons.

For the actually proved observable, the increment is `bridgeTwelve χ h`,
which is 0 or 6. Its period is therefore at most two, consistently with the
source translation. A global observable can take other labels on different
orbits through its supplied vertex labeling; the two-element restriction is
on translation increments and on each fixed orbit, not on all labels globally.

The first unresolved implication on the stronger twelve-cycle branch is
therefore J: **identify a different operator in the source and prove its
period and preservation law**. Assuming twelve levels in
`conditional_level_return` does not discharge that obligation. Reinterpreting
the same fixed binary translation as a twelve-step rotation cannot discharge it.

## Concrete continuation that the supplied model supports

The ledger's structured-sequence route offers a separate, well-defined next
construction: K, a lossless encoding of complete keys. This would preserve more
source information without claiming an exact twelve-cycle in the source.

1. Fix a finite binary dimension and metadata with an explicitly supplied
   encoding/decoder. Give encodings for both intercept components.
2. Define a framed word encoder `E : ExactKey M K W → List (ZMod 12)` and a
   total partial decoder `D : List (ZMod 12) → Option (ExactKey M K W)`.
3. Prove `D(E(q)) = some q` for every key. Reject malformed framing explicitly.
   Recover all metadata and both intercept components, not just R(q).
4. Define a translated-word operation U_h and prove
   `U_h(E(q)) = E(translateKey h q)`. Prove its two-step return for binary h.
5. If robustness is needed, state a framed-word error model and prove its
   recovery bound. Existing fixed-triple guarantees do not cover insertion,
   deletion, or framing loss automatically.

Completion criterion: a compiled left-inverse and source-action transport
proof for these actual structured keys. This would advance the ledger's
reversible-representation claim. It would not by itself prove J or L.

## Research end point and prize assessment

The supplied materials do not identify an exact Millennium Problem statement
proved by these constructions. Unique Games and P versus NP are different
statements; a local model of part of a Unique Games construction is not a
proof of either. A prize assessment requires first specifying an eligible
problem and completing a proof of its actual statement, followed by applicable
publication and independent-review requirements. No prize eligibility conclusion
is inferred from theorem counts or successful CI.

Sources: [structural ledger correspondence](STRUCTURAL_LEDGER.md),
[binary bridge and archive provenance](BRIDGE_SCOPE.md),
[pinned source model](SOURCE_MODEL.md),
[station semantics](STATION_CODEC.md), and
[calculator provenance and scope](CIPHER_VALIDATOR.md).
