# Geometric jigsaw and cipher conformance test specification (2026-11-25)

Canonical research: https://github.com/johnstobey/Ravenproofs/blob/main/research/GEOMETRIC_INTELLIGENCE_INNOVATION/TOBEY_OPERATOR_JIGSAW_2026-11-25.md

**This is a test handoff, not a claimed passing test suite.** Preserve existing `CPRX_OMEGA/OPERATOR_ALGEBRA.md`, `CPRX_OMEGA/SOURCE_OPERATOR_REGISTRY.md`, `IndependentDuodenary/CipherValidator.lean`, `IndependentDuodenary/FulguriteSAT.lean`, and verification fixtures.

## Arithmetic fixtures
- `T_i={i,i+4,i+8}`, i=0..3; `Q_j={j,j+3,j+6,j+9}`, j=0..2; intersection `(9*i+4*j)%12`.
- `J(k)=(k+6)%12` (opposition), `R(k)=(11-k)%12` (reverse-index reflection), `J²=R²=id`. They differ, e.g. J(0)=6 and R(0)=11.
- 12x12 index pairs yield 144 addresses. They are not the same as active relations or a product ring Z/144; preserve the types `Z12×Z12` versus `Z144`.
- Directed +120° from 6 is 10, not 2; glyph `♀♎ ☳ ☿♊` is a negative source-target fixture under that directed convention. Directed +0° from 0 is 0, not 1; `☉♈ ☌ ☽♉` is a negative fixture.
- Position (sign_index=7, offset_within_sign=0) represents longitude=210°. Reject (sign_index=7, offset_within_sign=210) as an invalid *within-sign* value.
- Seven unsigned angular distances in 30-degree multiples cover 0..180; signed 30-degree rotations have distinct 1..11 orientations.

## Composite harmonic cipher
Source attachment `harmonic cipher.md` records the schema
`x* = fix((⊕_{k in Z12} α_k(x) * β_{11-k}(x)) mod 144)`.
Require specification of α, β, ⊕, state type, group behavior, reduction placement, and stopping rule before treating this as a unique executable cipher. A deterministic map of a 144-state domain eventually repeats; repetition may be a period>1 cycle rather than fixed point. Tests must label each separately.

## Source/AST metamorphic control
- Copy an operator AST and alter only its English descriptive keywords; mathematical result and admission are invariant.
- Keep the English descriptive string and alter an aspect/target or node orientation in the AST; detect changed semantics.
- Feed forged source hash with appealing text; reject provenance.
- For a signed/course-related operator, compare the code to its *actual source witness*, including frame and direction, not to the keyword-favorable paraphrase.

The 89-character Dewey example uses Unicode Phi, which is not one UTF-8 byte. Character count and byte count need separate assertions. Recovered-native Machine history describes a former 91-character fixture repair; do not treat all v11.1 example strings as validated.

## Transfer gate
Use the existing FulguriteSAT/CipherValidator material to build negative controls and unit correspondence checks; do not copy its source authority into a new algebra unverified by executable provenance. Report actual run receipts, not projected pass status.
