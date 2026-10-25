# Dual-ring source map and consistency audit

Source: *THE MATHEMATICAL SPECIFICATIONS OF TWO z/12z PROCESSES AS RINGS*.
SHA-256: `aadb500dee5b2996bb01ad9eecc48ccd8961ebbf0df9a71b59e33f977432faaf`.
The complete extracted document was read, including both Clearing v3 and
Alignment v4, Parts I–X and their formal completion summaries. Section locators
below apply to both specifications unless stated otherwise. The original PDF
is retained outside the checkout and is not authorized for publication.

## Baseline

Baseline main: `a10099f48349bb2d67e2ca06ecb6b57524c892fa`.
Initial checkout branch: `work`, clean. Dedicated branch:
`research/dual-ring-invariant-program`, created from local main at origin/main.
The build configuration is `lakefile.lean`; `lakefile.toml` does not exist.
Lean: `leanprover/lean4:v4.14.0`. Locked mathlib:
`4bbdccd9c5f862bf90ff12f0a9e2c8be032b9a84`.
Source inventory: 447 named main-library declarations, 16 separately audited
experimental declarations, and 10,000 generated specializations. Counts are
not evidence that the current baseline has passed its executable audit.

Existing topics: ModularCore/TwelveStateStructure (finite rings and cycles),
BinaryBridge/SourceKeys (binary actions), EncodingIntegrity/SourceKeyRepresentation
(encoding and inversion), RegisterNaturality/CanonicalArchitecture (naturality,
observations and recovery), FulguriteSAT (circuit SAT), and
ReferenceMachines/AcceptanceNormalization/PostMicrocode (machine definitions
and partial compiler). The current atomic ledger is
`packaging/atomic_bridge_obligations.json`; 1.14 remains open.

## Typed source inventory

Write R = ZMod 12, a(k) = k+6, and C = {s : Set R | ∀k, k∈s ↔ a(k)∈s}.
Use a family P : Set C, not a subset of R. Let S(P) = ⋂ p∈P, p.val.
An event ledger is a finite sequence with explicit order and partition tags.

| ID | Exact locator | Typed mathematical definition | Existing equivalent / missing obligation |
|---|---|---|---|
| S01 | I.1 | R with anchor 0 | ZMod 12 exists throughout baseline |
| S02 | I.4 | element(k)=k.val mod 4; four fibers of size 3 | Tables specify steps of 4 (120 degrees), whereas prose says 90 degrees; preserve distinction |
| S03 | I.5 | modality(k)=k.val mod 3; three fibers of size 4 | Tables specify steps of 3 (90 degrees), whereas prose says 120 degrees |
| S04 | I.6 | undirected distance min(d,12-d), d=(y-x).val, values 0…6 | Seven named aspects; this is not a complete directed relational vocabulary |
| S05 | I.7; III.4, III.6 | logging n↦n+1; revision r↦r+δ | Listed element subsequences use step 4, distinct from logging step 1 |
| S06 | I.2 | common reference 0:R | Common reference alone does not force equal sets or terminal signals |
| S07 | I.8; II.3 | a:R→R; C as above | Closure is a set property; reachability additionally needs a transition relation |
| S08 | preambles; II.1 | two observations of one shared X | Source explicitly chooses a shared state, not two independent ring carriers |
| S09 | III.3 | (A,B,π)↦(A∩π,B∩π), canonical S=A∩B | Equality of views is preserved if initially equal; not implied merely by common anchor |
| S10 | II.1–2 | k,r,n:R with consistency k=n+r | Baseline register phase is a different defined operator; no identification assumed |
| S11 | III.1–8 | K,U,L,T,G composition | K compatibility, exact recognition, authority and jurisdiction predicates unspecified |
| S12 | II.3–4; III.3, III.5 | intersections in C; T restricted to S×S | Closure and monotonicity are precise obligations |
| S13 | V.2–3 | Integration iff S={0,6}; Refusal for another pair; empty-set cases depend on collapse speed | Fast/slow threshold unspecified; anchor membership alone does not imply a minimal pair |
| S14 | IV.2–4; V.4 | revision, counters and clearing | Clearing (k,r,n)↦(0,0,n) preserves k=n+r iff n=0; general clearing law inconsistent |

Topology interpretation: shared state with two views, following II.1 explicitly.
Treating AW and FE as literal disjoint unions of the elemental fibers would make
their intersection empty. Treating each as a full copy of R instead requires
explicit view maps. Neither alternative is silently substituted for the source.

## Operation obligations

| Locator / operation | Domain → codomain; preconditions | Claimed invariant | Counterexample criterion / missing proof |
|---|---|---|---|
| III.2 K | Input→R×Element×Modality×Aspect; classifier supplied | source-compatible classification | Compatibility predicate and exact-match criterion absent; source-dependent implementation blocked |
| III.3 U | Set C × C → Set C; P↦P∪{π} | S shrinks; antipodal closure | A counterexample violates closure or intersection identity; prove independently of K |
| III.3 views | Set R × Set R × C → Set R × Set R | common intersection; synchronized equality if initialized equally | A={0,6}, B=univ share anchor and closure but differ; missing synchronization hypothesis |
| III.4 L | X×Event→X; append event, n↦n+1, recompute k=n+r | ordered history prefix; bounded residues | Set union is not sequence append; unchanged k would break pointer equation |
| III.5 T | Set(R×R)×Set R→Set(R×R) | T'⊆T and endpoints in S' | Reachability may be lost; no universal reachability follows from set closure |
| III.6 G | X×R→X under supplied authorization predicate | n unchanged; k recomputed | Grace score codomain and conversion to a residue require definition |
| IV.2.1 square | constraints→partitioned constraints | coexistence | routing and admissibility semantics absent |
| IV.2.2 midpoint | R×R→R purportedly with 2m=x+y | arbiter at midpoint | For x=0,y=5 no solution; 2 is not invertible in R |
| IV.2.3 shadow | C→C purported inverse relation | reversible structural memory | Shadow unspecified; antipodal translation fixes every element of C, so cannot distinguish old/new constraints |
| IV.4 counter | counters×pair→counters | bounded revision attempts | c_max, reset policy and scheduling required to prove termination |
| V.3 signal | Set R×Speed→Signal with nonterminal case | unified signal on common canonical S | independent view signals require equal sets or another proved compatibility condition |
| V.4 clear | X→X, k'=0,r'=0,n'=n | pointer consistency and retained ledger | choose n=1: 0≠1+0; exact admissibility also requires 0∈S |

No baseline theorem supplies the missing classifier, midpoint inverse, shadow
function, or general clearing invariant. The repository's canonical codecs and
natural maps preserve their original types and hypotheses.

## First candidate and falsification

D1 candidate: the V.4 clearing update preserves II.2 for every consistent state.
Exact proposed proposition: ∀ n : ZMod 12, (0 : ZMod 12) = n + 0.
D3 minimal witness: n=1, r=0, k=1 before clearing; after clearing k'=r'=0,
n'=1. The proposition is false. Preserve this refutation rather than weakening
the source claim silently.

Next eligible obligation, program A: characterize when an observation supports
well-defined evolution and reconstruction on arbitrary carriers. Equal observed
states must have equal next observations; complete trajectory reconstruction
additionally requires distinguishability of initial states. Standard factorization
and observability results are supporting infrastructure, not original discoveries.
Program B continues with explicit source-consistency obstructions above.

## Unresolved source details

The constraint family has 64 possible closed masks, so arbitrary P needs 64
membership bits, not the 12-bit mask stated for P in II.6. A 12-bit mask does
suffice for S. A bound of six on committed constraints needs an explicit policy.
Intersection can stabilize above a pair forever; finite monotonic contraction
alone supplies no strict-progress or eventual-Integration theorem. Continuous
grace scores need a specified conversion into R. The supplied attention-space
and empirical claims are separate from the finite-ring propositions and are not
established by modular closure.
