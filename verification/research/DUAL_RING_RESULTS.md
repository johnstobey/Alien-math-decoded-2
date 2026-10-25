# Dual-ring consistency and observation batch

Baseline: main `a10099f48349bb2d67e2ca06ecb6b57524c892fa`, 447 audited
main-library declarations. Dedicated branch: `research/dual-ring-invariant-program`.
Eight additions bring the audited library to 455; the existing 16 experimental
declarations and 10,000 generated specializations remain separately counted.

## Source-defined model

The complete source has been read and mapped in
[DUAL_RING_FORMAL_MAP.md](../DUAL_RING_FORMAL_MAP.md). It explicitly specifies a
shared state with two observation frames. `DualRingSourceState` stores revision,
winding, a family of antipodally closed constraints, and a tagged event sequence.
The pointer is derived as winding plus revision. Admissibility is derived as
intersection of the active family. Events carry a closed constraint mask and
the source's four domain/two partition tags.

This is the consistent state portion of the specification, not an invented
implementation of its undefined classifier, authorization predicate, shadow
operator, collapse-speed threshold, or continuous-score conversion.

## Exact results and gate classifications

The full quantified Lean statements are in the linked modules and the updated
[theorem index](../THEOREMS.md); elaborated statements and proof terms are in
[the audit artifact](../axioms-and-proofs.txt).

| Declaration | Mathematical content | Classification |
|---|---|---|
| `observation_dynamics_iff_kernel_stable` | An observation O supports U with O∘T=U∘O iff equal observations have equal next observations | VERIFIED supporting formalization of standard factorization |
| `observation_trace_universal` | Equality of complete future observation traces is stable and contains every stable relation that respects the observation | VERIFIED standard observational-equivalence characterization |
| `observation_trace_reconstruction_iff` | An Option-valued decoder recovers every initial state from its complete trace iff the trace map is injective, including empty carriers | VERIFIED supporting reconstruction formalization |
| `dual_ring_admissible_closed` | The active-family intersection is antipodally closed | VERIFIED source invariant |
| `clearing_pointer_reset_classification` | In any additive group, 0=n+r iff r=-n, and 0=n+0 iff n=0 | VERIFIED classification; refutes unrestricted zero-offset clearing with retained winding |
| `quincunx_midpoint_obstruction` | No m in ZMod 12 satisfies m+m=5 | VERIFIED counterexample to a universally ring-valued quincunx midpoint |
| `dual_ring_common_anchor_insufficient` | Two closed sets may share zero and still differ | VERIFIED counterexample to deriving synchronized views from common anchor and closure alone |
| `dual_view_integration_iff` | For closed A,B and map a, A∩B={z,a(z)} iff both retain z and every outside point is excluded by at least one view | VERIFIED exact condition supplementing anchor membership |

Modules:
[ObservationReconstruction.lean](../../IndependentDuodenary/ObservationReconstruction.lean),
[DualRingConsistency.lean](../../IndependentDuodenary/DualRingConsistency.lean).

The last criterion works on arbitrary carriers and maps with the stated closure
hypotheses; no finite or involution hypothesis is hidden. Its ZMod 12 instance
uses the source antipode and anchor zero. It makes explicit the exclusion
condition absent from an anchor-only Integration criterion.

## Falsification and proof iterations

D1/D3 first candidate: unrestricted source clearing preserves k=n+r. Witness:
n=1,r=0,k=1 before clearing; specified output k'=0,r'=0,n'=1 violates it.
Three distinct repairs are separated: restrict original clearing to n=0;
retain n but compensate r'=-n; reset n as well (which abandons winding retention).
Only their exact algebraic classification is proved; none silently replaces
the source law.

Other counterexamples: sectors 0 and 5 have no midpoint in ZMod 12; the sets
univ and {0,6} share anchor and closure without equality. Constant observations
of a toggling Boolean system have autonomous observed dynamics but cannot
recover initial states. Identity observation with identity target does not
intertwine Boolean negation. Modulo three a midpoint can exist, so the ZMod 12
obstruction is not generalized to every modulus.

Eight unnamed Lean examples in
[DualRingBoundary.lean](../../examples/DualRingBoundary.lean) check these
boundaries plus empty and singleton carriers. They are not counted as named
discoveries. One initial proof elaboration failed because a local equality
was rewritten in the evidence but not the goal; explicit equality substitution
repaired it without changing the proposition. Both gate logs are retained.

## Dependencies, novelty, and significance

Dependency DAG:

```text
Mathlib.Logic.Function.Iterate → ObservationReconstruction
TwelveStateStructure → DualRingConsistency
ObservationReconstruction + DualRingConsistency → root library + boundary examples
```

D2 review inspected existing reconstruction, naturality and phase-loss results
and mathlib's `Function.FactorsThrough`, `Function.extend`, and
`Function.Semiconj.iterate_right`. The general principles already belong to
standard factorization and observability theory. These results supply missing
formal interfaces and source-specific consistency checks, not an independently
established original mathematical discovery. Independent external literature
review remains outstanding. Their significance is exact specification repair
and reconstruction boundaries; no scientific claim about model internals
follows from these propositions.

## Validation and release boundary

Baseline build, 447-declaration audit, 13 pipeline checks and five JavaScript
fixtures passed before proof edits. Integration build, 455-declaration audit,
eight adversarial examples, 16-declaration phase audit, 10,000-specialization
dependency/axiom audit and the pipeline checks passed. Only `propext`,
`Classical.choice`, and `Quot.sound` are permitted by the audits. Exact receipts
and full local logs remain in ignored `.lake/research-logs/`.

The generated Lean files are unchanged; their manifest now inventories the
additional source files and declarations. Lean and mathlib pins are unchanged.
No existing theorem or hypothesis was altered. Original PDFs, transcripts,
credentials, and personal material are excluded from the release.

Remote CI and PR creation are separate from these local results. GitHub API
access returned Forbidden during preparation; native Git read access works.
Publication status and exact committed revision must be read from the release
receipts, not inferred from this document.

## Open obligations and next operation

Source-dependent update composition remains OPEN until precise compatibility,
authorization, shadow and terminal-speed rules are supplied and the clearing
and midpoint conflicts are resolved explicitly. Equal initial views receiving
identical constraints can be synchronized by construction; shared anchor alone
does not provide that hypothesis. Monotonic intersection alone does not ensure
strict progress or eventual Integration.

Programs C, D, E1 and E2 remain open research programs. No compiler, SAT reduction,
complexity separation/equality, continuous-dynamics or subjective-consciousness
result is inferred from this batch. The existing general multi-tape compiler
obligation 1.14 is unchanged.

Next eligible source-independent operation: formulate finite-window observation
stabilization with an explicit horizon and a tight distinguishability condition,
check existing automata/observability literature, and run the candidate gates.
Source-dependent alternative: specify an authorized reset law consistent with
the retained winding before implementing the full transition operator.
