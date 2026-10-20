# Worked grammar, meaning, codec, and recovery

## The selected example

The independent ledger supplies rotation, reflection, their conjugation law,
and unit-affine composition. We use that mathematical example as the first
small language. Its expressions are operations on twelve station labels.
Their meaning is the entire induced permutation, rather than an output at one
sample point or an assigned natural-language interpretation.

`StationExpr` has identity, shift, reflection, unit scaling, composition, and
inversion constructors. `compose outer inner` executes inner first. Every
constructor acts on `ZMod 12`, so every expression has a defined interpretation.

The worked expression is:

```lean
.compose .reflect (.compose (.shift 1) .reflect)
```

Execution is reflect, shift by one, reflect. It acts as `x ↦ x-1` and compiles
to the multiplier/offset pair `(1,11)`. Independently, scaling by 5 after a
shift by 3 compiles to `(5,3)`. Both send input 2 to output 1, but their whole
permutations are proved different. Matching one sample is insufficient to
establish semantic equivalence.

## Meaning and reversible representation

`stationMeaning` recursively evaluates expressions as permutations.
`compileStation` independently normalizes syntax to unit-affine parameters.
The induction theorem `station_compile_correct` proves the compiler agrees
with evaluation for every finite expression, including composition and inverse.

Two expressions are equivalent exactly when their entire permutations agree.
The compiler characterizes this equivalence and gives a proved decision
procedure (`sameStationMeaning`). Normalization preserves meaning and is
idempotent. The quotient of expressions by this equivalence is proved bijective
with the 48 affine parameter pairs.

The wire format contains two `ZMod 12` symbols: multiplier and offset. The parser
accepts only unit multipliers 1, 5, 7 and 11. `ValidStationCode` is the checked
subtype of accepted codes. A computable encoder and decoder form an equivalence
between meanings and valid codes. There are 48 valid codes inside the raw
144-code space. Codes such as `(2,0)` are rejected.

Decoding preserves meaning, not syntax history. For example, a nested expression
and its canonical shift/scale form deliberately have the same code. The theorem
`station_code_collision_iff` proves both directions: codes coincide exactly
when meanings coincide. This supplies the quotient-respecting condition that
was only an explicit requirement in the earlier generic encoding results.

## Operation preservation

`composeStationWire` parses both inputs, computes affine composition, and
returns a checked representation of the result. `invertStationWire` does the
same for inverse. `station_wire_composition` and `station_wire_inverse` prove
these procedures agree with the corresponding expression constructors.
No arbitrary invalid multiplier is silently treated as a reversible operation.

## Concrete corruption model and full recovery path

Each wire symbol is repeated three times. The protected representation contains
two triples, for six symbols total. The stated error model permits at most one
substitution in each triple. It therefore covers any single substitution overall,
and also two substitutions when they occur in different triples. It does not
claim recovery from arbitrary two substitutions, insertions, or deletions.

The receive side uses the already proved majority decoder on each triple,
reconstructs the wire code, parses it, and returns a semantic class.
`protected_station_semantic_recovery` proves that this whole path returns the
original meaning whenever the two explicit Hamming bounds hold.

The actual executable walkthrough produces:

```text
reflection code: (1,11)
reflection input/output: (0,11), (1,0), (2,1), (6,5), (11,10)
scale-after-shift code: (5,3)
received triples: [1,5,1] and [11,11,0]
recovered code: (1,11)
decoded operation applied to 2: 1
nonunit code (2,0): rejected
```

The concrete corruption bounds and recovered semantic class are also proved
in Lean. `examples/StationWalkthrough.lean` executes this trace and contains
five guards on the expected results. Run it with:

```sh
lake env lean examples/StationWalkthrough.lean
```

The CI workflow runs this walkthrough in addition to the full library build
and theorem/axiom audit. Actual local output is in `station-walkthrough.txt`.
Remote success must be checked on the exact pushed commit.

## Restricted source connection

`sourceShiftExpression` uses an explicitly chosen `χ : K →+ ZMod 2` and the
proved binary bridge to construct grammar shifts. Theorems prove that these
shifts preserve addition and that evaluating the grammar operation transports
the residue observable exactly as intercept translation acts on an exact key.
This is a typed action-equivariance result, using the previously proved source
folding model. The choice of χ and vertex labeling remains explicit. It does
not establish a canonical, faithful, or surjective map to the full residue ring;
the exponent-two obstruction still applies.

## Roadmap status and next scope

| Stage | Result in this prototype |
| --- | --- |
| Select a worked source example | The ledger's reflection/rotation conjugation law and affine composition. |
| Define grammar and meaning | A typed operation AST, permutation semantics, and semantic equivalence. |
| Construct actual E and D | Exact two-sided round trips between semantic classes and valid wire codes. |
| Prove operation preservation | Correct compilation, wire composition, inverse, and semantic collision equivalence. |
| Prove robustness | Concrete six-symbol protected encoding and a proved semantic recovery path. |
| Connect to the source model | Restricted equivariance for a chosen binary functional and observable. |
| Independent review | Automated build, audit, and walkthrough; outside mathematical/source review remains outstanding. |

This is a complete worked codec for the stated operation language. It does not
supply an English parser, a meaning assignment for a historical corpus, a
universal semantic codec, or a proof of the full paper theorem. Extending it to
a particular corpus requires a fixed set of sourced rules and a proved mapping
from those rules to the formal operations. Such a mapping must be established
rather than inferred from successful encoding of the constructed language.

The extension adds 41 theorem declarations. The project now contains 14 library
modules and 191 theorems; the standalone walkthrough is an additional elaborated
example file. Lean and mathlib pins remain unchanged.
