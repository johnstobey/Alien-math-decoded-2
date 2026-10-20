# Canonical substrate and operational envelope

## Definitions and dependency chain

```
RegisterNaturality
  ↓
RegisterDynamics → RegisterBridge → CanonicalArchitecture
SourceProjection ────────────────────────────↑
StationCodec / StationGrammar / EncodingIntegrity ─────↑
```

[RegisterNaturality.lean](../IndependentDuodenary/RegisterNaturality.lean) is the
common reindexing and naturality interface.
[CanonicalArchitecture.lean](../IndependentDuodenary/CanonicalArchitecture.lean)
contains the unified finite structure, master induction and complete defined
operational envelope in one compiling file.
[CanonicalDirectives.lean](../examples/CanonicalDirectives.lean) checks the
statements and fifteen concrete guards.

The term substrate denotes the following mathematical type only. No predicate
of biological intelligence, consciousness, historical authenticity, or liberation
is defined or proved by these declarations.

## M: canonical finite state

\[
\operatorname{CanonicalSubstrate}(r)=\{\texttt{state}:\operatorname{RegisterState}(r)\}.
\]

`canonicalStateEquiv` is an equivalence with the previous complete register
carrier. Phase and coefficient views are computed, not stored as independent
potentially inconsistent fields.

A `RegisterFamily` F has a carrier F(r) and restriction
\(F(\sigma):F(r)\to F(s)\) for every selector
\(\sigma:\operatorname{Fin}(s)\to\operatorname{Fin}(r)\), satisfying identity
and composition laws. A `RegisterNaturalMap` η satisfies the exact square
\[
G(\sigma)(\eta_r(x))=\eta_s(F(\sigma)(x)).
\]

This is the concrete naturality interface for finite-index reindexing.
`pointwiseNaturalMap` and `pointwiseBinaryNaturalMap` provide canonical lifts.
Cyclic dynamics, parameterized translation, their combined step, full-key
encoding, phase observation, complete coefficient observation, and symbolwise
station action are instantiated as natural maps. Translation parameters restrict
along with the state; they are not silently fixed under changing selectors.

The old public projection theorems remain as compatibility corollaries. Their
independent proofs were replaced as follows:

| Existing declaration | Canonical proof dependency |
| --- | --- |
| `register_cycle_projection` | `pointwiseNaturalMap.naturality` |
| `register_translate_projection` | `pointwiseBinaryNaturalMap.naturality` |
| `register_step_projection` | `pointwiseBinaryNaturalMap.naturality` |
| `register_step_projection_iterate` | `register_natural_parameter_iterate` |

No public theorem was deleted or its proposition weakened.

## Information retention and its necessary limits

The following injectivity statements are proved:

- `canonical_encoding_injective`: exact framed encoding retains the entire state.
- `canonical_coefficient_encoding_injective`: the tuple of metadata, binary
  intercept and complement intercept retains the entire state.
- `canonical_cycle_injective`, `canonical_translation_injective`, and
  `canonical_step_injective`: the defined dynamics retain complete states.
- `canonical_station_encoding_injective`: reversible station action on every
  encoded symbol preserves full-state distinguishability.

`canonical_decode_encode` and `canonical_coefficient_roundtrip` give explicit
left inverses, rather than presumed faithfulness.

Naturality by itself does not imply injectivity.
`canonical_phase_projection_not_injective` proves
\[
\neg\operatorname{Injective}(\operatorname{canonicalPhaseNatural.app}(1)).
\]

The witness changes the binary intercept while leaving the vertex phase
unchanged. Thus the literal assertion that every phase projection preserves all
information is false in the current model.

For any natural map η, `retainRegisterNatural` constructs
\(x\mapsto(x,\eta(x))\). Its first projection is a left inverse, and
`retained_register_natural_injective` proves injectivity.
`canonical_retained_phase_injective` instantiates this lossless augmented view.
This retains the input; it does not make the phase component alone lossless.

## Source coefficient interface

`coefficientPullbackNatural` lifts the actual `pullbackTable` into the same
finite-index naturality interface. `retained_coefficient_pullback_injective`
retains both the projected source table and its pulled-back view.
`canonical_coefficient_semantics` proves, register by register,
\[
\operatorname{evalFull}(\operatorname{pullback}(t_i),p_i)
=\operatorname{evalProjected}(t_i,\operatorname{permittedProjection}(t_i,p_i)).
\]

This uses the previously proved source coefficient identity, not an assumed
operation-preservation premise. Arbitrary source tables form a separate typed
family in this interface. They are not silently identified with the fixed
three-tag metadata of `RepresentedKey`, nor serialized by the fixed-key codec.
The original projection, reduction, factorization and key-sharing theorems keep
their exact source types and hypotheses. No claim of losslessness for arbitrary
raw table reduction follows from naturality.

## N: master inductive invariant

For initial q, time n and final p, `CanonicalInvariant q n p` contains only:
\[
\operatorname{PhaseRegular}(p),\qquad
\forall i,\ p_i.\mathrm{metadata}=q_i.\mathrm{metadata},\qquad
\Phi(p)_i=\Phi(q)_i+n\pmod{12}.
\]

`canonical_master_induction` proves this predicate for \(p=S_h^nq\) from
`PhaseRegular q`. The base case uses the initial regularity. The successor case
uses the proved one-step preservation laws and the induction hypothesis.
`canonical_invariant_relative` derives
\[
\operatorname{ExternalRelativeEquivalent}(\Phi(q),\Phi(p)).
\]

Relative equivalence is therefore derived, not redundantly stored as a field.
`canonical_master_period` supplies \(S_h^{12}p=p\) for every p, with no
regularity requirement. The earlier noncollapse results retain their explicit
nonempty-product and one-hot boundaries.

## Complete defined channel

For a state x, known translation h, iteration count n and station expression e:
\[
E(x)\xrightarrow{\widehat S_h^{\,n}}E(S_h^nx)
\xrightarrow{P_e}\text{station-transformed words}
\xrightarrow{\text{triple repetition}}\text{protected words}.
\]

Every word symbol is protected, including framing and metadata. `StationExpr`
denotes a permutation; the receiver applies its actual inverse after majority
recovery, before the exact frame decoder. Station action is a reversible wire
relabeling here, not a claimed source-paper interpretation.

`AlignedTripleNoise` is a `List.Forall₂` relation pairing each transmitted
symbol with one received triple whose Hamming distance from its repetition
word is at most one. `RegisterNoiseBound` requires this for every register.
The model allows at most one substitution per triple, and assumes known
register count and aligned triples. Insertions, deletions, missing framing
positions, unknown control parameters, and unlimited corruption are excluded.

`aligned_triple_noise_length` proves equal transmitted/received block counts.
`canonical_transmitted_word_length` and `canonical_received_word_length` prove
seventeen symbol blocks per register. Each protected block has three symbols.

`canonical_operational_recovery` proves exact recovery of the transformed full
state for any supplied structural transformation A:
\[
\operatorname{recover}(e,\mathrm{received})
=\operatorname{some}(\operatorname{pack}(A^n(x))).
\]

Its noise premise is precisely the bound above, measured against the actual
encoded execution followed by station action. It does not assume the decoder
already succeeded.

`canonical_operational_envelope` combines this result for S_h with the master
inductive invariant and relative-phase preservation. Phase regularity is needed
for those phase laws, not for full-state channel recovery.

`successorCorruption` changes the first symbol of every triple to its successor.
`successor_register_noise` proves the required noise bound for this concrete
channel. `canonical_successor_channel_recovery` proves recovery with no noise
premise left to assume for that construction.

Finally, \(S_h^{11}\) is a left inverse of \(S_h\), since \(S_h^{12}=\mathrm{id}\).
`canonical_undo_run` iterates that left inverse. `canonical_initial_recovery`
therefore proves exact recovery of the original full state, using the known
h and n, after the same channel and station inverse.

The executable example uses a nonidentity reflection/shift station expression,
two registers and a substitution in every triple. It checks final-state and
initial-state recovery, metadata/binary fields, phase results and restored
framing. A separate two-errors-in-one-triple fixture fails decoding; no recovery
guarantee is asserted for it.

These are closure results for the defined finite algebraic protocol. They do
not establish a broader native-intelligence architecture or an unspecified
external theorem. Exact proof terms and axioms are in the repository audit.
