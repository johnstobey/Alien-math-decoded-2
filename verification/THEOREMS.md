# Theorem-by-theorem audit

All names below are in namespace `IndependentDuodenary`. All 408 declarations compiled and passed the axiom audit. Exact elaborated propositions, proof terms, and direct dependency lists are in [axioms-and-proofs.txt](axioms-and-proofs.txt), under the matching theorem name and `DIRECT DEPENDENCIES` record. The Lean source propositions are reproduced below. Standard library infrastructure dependencies are included in that machine-generated record.

## `affine_station_composition`

Source: `IndependentDuodenary/AffineStations.lean`. Compilation: **passed**.

```lean
theorem affine_station_composition (p q : AffineStationParameter) (x : ZMod 12) :
    affineStationApply (affineStationCompose p q) x =
      affineStationApply p (affineStationApply q x)
```

Proof method: Expand the unit-affine formulas and normalize ring expressions.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES affine_station_composition` and the printed proof in the machine-generated audit.

## `affine_station_permutation_injective`

Source: `IndependentDuodenary/AffineStations.lean`. Compilation: **passed**.

```lean
theorem affine_station_permutation_injective : Function.Injective affineStationPermutation
```

Proof method: Evaluation at 0 identifies offsets; evaluation at 1 and cancellation identify units.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES affine_station_permutation_injective` and the printed proof in the machine-generated audit.

## `twelve_unit_count`

Source: `IndependentDuodenary/AffineStations.lean`. Compilation: **passed**.

```lean
theorem twelve_unit_count : Fintype.card (ZMod 12)ˣ = 4
```

Proof method: The units/coprime-residue equivalence and finite computation.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES twelve_unit_count` and the printed proof in the machine-generated audit.

## `twelve_unit_residues`

Source: `IndependentDuodenary/AffineStations.lean`. Compilation: **passed**.

```lean
theorem twelve_unit_residues : ∀ u : (ZMod 12)ˣ,
    (u : ZMod 12) = 1 ∨ (u : ZMod 12) = 5 ∨
      (u : ZMod 12) = 7 ∨ (u : ZMod 12) = 11
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES twelve_unit_residues` and the printed proof in the machine-generated audit.

## `affine_station_parameter_card`

Source: `IndependentDuodenary/AffineStations.lean`. Compilation: **passed**.

```lean
theorem affine_station_parameter_card : Fintype.card AffineStationParameter = 48
```

Proof method: Product cardinality with twelve_unit_count.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES affine_station_parameter_card` and the printed proof in the machine-generated audit.

## `affine_station_group_card`

Source: `IndependentDuodenary/AffineStations.lean`. Compilation: **passed**.

```lean
theorem affine_station_group_card : Nat.card affineStationSubgroup = 48
```

Proof method: The proved equivalence between parameters and the actual affine permutation subgroup.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES affine_station_group_card` and the printed proof in the machine-generated audit.

## `affine_five_changes_cyclic_distance`

Source: `IndependentDuodenary/AffineStations.lean`. Compilation: **passed**.

```lean
theorem affine_five_changes_cyclic_distance :
    cyclicDistance (affineStationApply multiplyFiveParameter 0)
      (affineStationApply multiplyFiveParameter 1) ≠ cyclicDistance 0 1
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES affine_five_changes_cyclic_distance` and the printed proof in the machine-generated audit.

## `bitToTwelve_values`

Source: `IndependentDuodenary/BinaryBridge.lean`. Compilation: **passed**.

```lean
theorem bitToTwelve_values : bitToTwelve 0 = 0 ∧ bitToTwelve 1 = 6
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES bitToTwelve_values` and the printed proof in the machine-generated audit.

## `bitTo144_values`

Source: `IndependentDuodenary/BinaryBridge.lean`. Compilation: **passed**.

```lean
theorem bitTo144_values : bitTo144 0 = 0 ∧ bitTo144 1 = 72
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES bitTo144_values` and the printed proof in the machine-generated audit.

## `bitToTwelve_injective`

Source: `IndependentDuodenary/BinaryBridge.lean`. Compilation: **passed**.

```lean
theorem bitToTwelve_injective : Function.Injective bitToTwelve
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES bitToTwelve_injective` and the printed proof in the machine-generated audit.

## `bitTo144_injective`

Source: `IndependentDuodenary/BinaryBridge.lean`. Compilation: **passed**.

```lean
theorem bitTo144_injective : Function.Injective bitTo144
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES bitTo144_injective` and the printed proof in the machine-generated audit.

## `binary_double_zero`

Source: `IndependentDuodenary/BinaryBridge.lean`. Compilation: **passed**.

```lean
theorem binary_double_zero : ∀ x : ZMod 2, x + x = 0
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES binary_double_zero` and the printed proof in the machine-generated audit.

## `twelve_two_torsion`

Source: `IndependentDuodenary/BinaryBridge.lean`. Compilation: **passed**.

```lean
theorem twelve_two_torsion :
    ∀ x : ZMod 12, x + x = 0 ↔ x = 0 ∨ x = 6
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES twelve_two_torsion` and the printed proof in the machine-generated audit.

## `mod144_two_torsion`

Source: `IndependentDuodenary/BinaryBridge.lean`. Compilation: **passed**.

```lean
theorem mod144_two_torsion :
    ∀ x : ZMod 144, x + x = 0 ↔ x = 0 ∨ x = 72
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES mod144_two_torsion` and the printed proof in the machine-generated audit.

## `binary_vector_double_zero`

Source: `IndependentDuodenary/BinaryBridge.lean`. Compilation: **passed**.

```lean
theorem binary_vector_double_zero {ℓ : ℕ} (v : Fin ℓ → ZMod 2) : v + v = 0
```

Proof method: Function extensionality and binary_double_zero at each coordinate.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES binary_vector_double_zero` and the printed proof in the machine-generated audit.

## `image_double_zero`

Source: `IndependentDuodenary/BinaryBridge.lean`. Compilation: **passed**.

```lean
theorem image_double_zero {K B : Type*} [AddMonoid K] [AddMonoid B]
    (hK : ∀ x : K, x + x = 0) (f : K →+ B) (x : K) : f x + f x = 0
```

Proof method: Preservation of addition and zero; the explicit source exponent-two hypothesis.

Axioms: `none`.

Dependencies: see `DIRECT DEPENDENCIES image_double_zero` and the printed proof in the machine-generated audit.

## `image_in_two_stations`

Source: `IndependentDuodenary/BinaryBridge.lean`. Compilation: **passed**.

```lean
theorem image_in_two_stations {K : Type*} [AddMonoid K]
    (hK : ∀ x : K, x + x = 0) (f : K →+ ZMod 12) (x : K) :
    f x = 0 ∨ f x = 6
```

Proof method: image_double_zero followed by twelve_two_torsion.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES image_in_two_stations` and the printed proof in the machine-generated audit.

## `image_in_two_superstations`

Source: `IndependentDuodenary/BinaryBridge.lean`. Compilation: **passed**.

```lean
theorem image_in_two_superstations {K : Type*} [AddMonoid K]
    (hK : ∀ x : K, x + x = 0) (f : K →+ ZMod 144) (x : K) :
    f x = 0 ∨ f x = 72
```

Proof method: image_double_zero followed by mod144_two_torsion.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES image_in_two_superstations` and the printed proof in the machine-generated audit.

## `binary_map_not_surjective_twelve`

Source: `IndependentDuodenary/BinaryBridge.lean`. Compilation: **passed**.

```lean
theorem binary_map_not_surjective_twelve {K : Type*} [AddMonoid K]
    (hK : ∀ x : K, x + x = 0) (f : K →+ ZMod 12) :
    ¬ Function.Surjective f
```

Proof method: A hypothetical preimage of 1 contradicts image_in_two_stations.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES binary_map_not_surjective_twelve` and the printed proof in the machine-generated audit.

## `binary_map_not_surjective_144`

Source: `IndependentDuodenary/BinaryBridge.lean`. Compilation: **passed**.

```lean
theorem binary_map_not_surjective_144 {K : Type*} [AddMonoid K]
    (hK : ∀ x : K, x + x = 0) (f : K →+ ZMod 144) :
    ¬ Function.Surjective f
```

Proof method: A hypothetical preimage of 1 contradicts image_in_two_superstations.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES binary_map_not_surjective_144` and the printed proof in the machine-generated audit.

## `binaryCoordinate_surjective`

Source: `IndependentDuodenary/BinaryBridge.lean`. Compilation: **passed**.

```lean
theorem binaryCoordinate_surjective {ℓ : ℕ} (i : Fin ℓ) :
    Function.Surjective (binaryCoordinate i)
```

Proof method: The constant vector with value b is a preimage of every b.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES binaryCoordinate_surjective` and the printed proof in the machine-generated audit.

## `binaryCoordinate_not_injective`

Source: `IndependentDuodenary/BinaryBridge.lean`. Compilation: **passed**.

```lean
theorem binaryCoordinate_not_injective {ℓ : ℕ} (i j : Fin ℓ) (hij : i ≠ j) :
    ¬ Function.Injective (binaryCoordinate i)
```

Proof method: A nonzero vector supported on a different coordinate maps to zero.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES binaryCoordinate_not_injective` and the printed proof in the machine-generated audit.

## `bridgeTwelve_preserves_addition`

Source: `IndependentDuodenary/BinaryBridge.lean`. Compilation: **passed**.

```lean
theorem bridgeTwelve_preserves_addition {K : Type*} [AddMonoid K]
    (χ : K →+ ZMod 2) :
    PreservesOperation (fun x y : K => x + y)
      (fun x y : ZMod 12 => x + y) (bridgeTwelve χ)
```

Proof method: Addition law of the composite AddMonoidHom.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES bridgeTwelve_preserves_addition` and the printed proof in the machine-generated audit.

## `bridge144_preserves_addition`

Source: `IndependentDuodenary/BinaryBridge.lean`. Compilation: **passed**.

```lean
theorem bridge144_preserves_addition {K : Type*} [AddMonoid K]
    (χ : K →+ ZMod 2) :
    PreservesOperation (fun x y : K => x + y)
      (fun x y : ZMod 144 => x + y) (bridge144 χ)
```

Proof method: Addition law of the composite AddMonoidHom.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES bridge144_preserves_addition` and the printed proof in the machine-generated audit.

## `bridgeTwelve_range`

Source: `IndependentDuodenary/BinaryBridge.lean`. Compilation: **passed**.

```lean
theorem bridgeTwelve_range {K : Type*} [AddMonoid K]
    (χ : K →+ ZMod 2) (hχ : Function.Surjective χ) (y : ZMod 12) :
    (∃ x, bridgeTwelve χ x = y) ↔ y = 0 ∨ y = 6
```

Proof method: Binary image classification and preimages supplied by the explicit surjectivity hypothesis.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES bridgeTwelve_range` and the printed proof in the machine-generated audit.

## `bridge144_range`

Source: `IndependentDuodenary/BinaryBridge.lean`. Compilation: **passed**.

```lean
theorem bridge144_range {K : Type*} [AddMonoid K]
    (χ : K →+ ZMod 2) (hχ : Function.Surjective χ) (y : ZMod 144) :
    (∃ x, bridge144 χ x = y) ↔ y = 0 ∨ y = 72
```

Proof method: Binary image classification and preimages supplied by the explicit surjectivity hypothesis.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES bridge144_range` and the printed proof in the machine-generated audit.

## `bridgeTwelve_injective_iff`

Source: `IndependentDuodenary/BinaryBridge.lean`. Compilation: **passed**.

```lean
theorem bridgeTwelve_injective_iff {K : Type*} [AddMonoid K]
    (χ : K →+ ZMod 2) :
    Function.Injective (bridgeTwelve χ) ↔ Function.Injective χ
```

Proof method: Injectivity of bitToTwelve and injectivity of function composition.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES bridgeTwelve_injective_iff` and the printed proof in the machine-generated audit.

## `bridge144_injective_iff`

Source: `IndependentDuodenary/BinaryBridge.lean`. Compilation: **passed**.

```lean
theorem bridge144_injective_iff {K : Type*} [AddMonoid K]
    (χ : K →+ ZMod 2) :
    Function.Injective (bridge144 χ) ↔ Function.Injective χ
```

Proof method: Injectivity of bitTo144 and injectivity of function composition.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES bridge144_injective_iff` and the printed proof in the machine-generated audit.

## `coordinate_bridgeTwelve_range`

Source: `IndependentDuodenary/BinaryBridge.lean`. Compilation: **passed**.

```lean
theorem coordinate_bridgeTwelve_range {ℓ : ℕ} (i : Fin ℓ) (y : ZMod 12) :
    (∃ v, bridgeTwelve (binaryCoordinate i) v = y) ↔ y = 0 ∨ y = 6
```

Proof method: bridgeTwelve_range with the proved binaryCoordinate_surjective.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES coordinate_bridgeTwelve_range` and the printed proof in the machine-generated audit.

## `coordinate_bridge144_range`

Source: `IndependentDuodenary/BinaryBridge.lean`. Compilation: **passed**.

```lean
theorem coordinate_bridge144_range {ℓ : ℕ} (i : Fin ℓ) (y : ZMod 144) :
    (∃ v, bridge144 (binaryCoordinate i) v = y) ↔ y = 0 ∨ y = 72
```

Proof method: bridge144_range with the proved binaryCoordinate_surjective.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES coordinate_bridge144_range` and the printed proof in the machine-generated audit.

## `no_binary_ring_hom_twelve`

Source: `IndependentDuodenary/BinaryBridge.lean`. Compilation: **passed**.

```lean
theorem no_binary_ring_hom_twelve : ¬ Nonempty (ZMod 2 →+* ZMod 12)
```

Proof method: Preservation of addition, 1 and 0 would force the nonzero target 1+1 to be zero.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES no_binary_ring_hom_twelve` and the printed proof in the machine-generated audit.

## `no_binary_ring_hom_144`

Source: `IndependentDuodenary/BinaryBridge.lean`. Compilation: **passed**.

```lean
theorem no_binary_ring_hom_144 : ¬ Nonempty (ZMod 2 →+* ZMod 144)
```

Proof method: Preservation of addition, 1 and 0 would force the nonzero target 1+1 to be zero.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES no_binary_ring_hom_144` and the printed proof in the machine-generated audit.

## `binary_nonzero_eq_one`

Source: `IndependentDuodenary/BinaryStructure.lean`. Compilation: **passed**.

```lean
theorem binary_nonzero_eq_one : ∀ x : ZMod 2, x ≠ 0 → x = 1
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES binary_nonzero_eq_one` and the printed proof in the machine-generated audit.

## `bitWeight_le`

Source: `IndependentDuodenary/BinaryStructure.lean`. Compilation: **passed**.

```lean
theorem bitWeight_le (v : BinaryVector) : bitWeight v ≤ 12
```

Proof method: Cardinality bound for subsets of Fin 12.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES bitWeight_le` and the printed proof in the machine-generated audit.

## `maximum_weight_iff`

Source: `IndependentDuodenary/BinaryStructure.lean`. Compilation: **passed**.

```lean
theorem maximum_weight_iff (v : BinaryVector) :
    bitWeight v = 12 ↔ ∀ i, v i = 1
```

Proof method: Equality in the finite-set cardinality bound and binary_nonzero_eq_one.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES maximum_weight_iff` and the printed proof in the machine-generated audit.

## `weightLayer_card`

Source: `IndependentDuodenary/BinaryStructure.lean`. Compilation: **passed**.

```lean
theorem weightLayer_card (k : ℕ) : (weightLayer k).card = Nat.choose 12 k
```

Proof method: Support-set bijection with k-element subsets; Finset.card_powersetCard.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES weightLayer_card` and the printed proof in the machine-generated audit.

## `single_bit_count`

Source: `IndependentDuodenary/BinaryStructure.lean`. Compilation: **passed**.

```lean
theorem single_bit_count : (weightLayer 1).card = 12
```

Proof method: Specialization of weightLayer_card and kernel-checked computation.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES single_bit_count` and the printed proof in the machine-generated audit.

## `all_bits_count`

Source: `IndependentDuodenary/BinaryStructure.lean`. Compilation: **passed**.

```lean
theorem all_bits_count : (weightLayer 12).card = 1
```

Proof method: Specialization of weightLayer_card and kernel-checked computation.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES all_bits_count` and the printed proof in the machine-generated audit.

## `zero_bits_count`

Source: `IndependentDuodenary/BinaryStructure.lean`. Compilation: **passed**.

```lean
theorem zero_bits_count : (weightLayer 0).card = 1
```

Proof method: Specialization of weightLayer_card and kernel-checked computation.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES zero_bits_count` and the printed proof in the machine-generated audit.

## `canonical_coefficient_roundtrip`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem canonical_coefficient_roundtrip {r : ℕ} (x : CanonicalSubstrate r) :
    canonicalFromCoefficients (canonicalCoefficientNatural.app r x) = x
```

Proof method: Kernel-checked tactic proof using cases. Exact terms and dependencies are in the audit.

Axioms: `none`.

Dependencies: see `DIRECT DEPENDENCIES canonical_coefficient_roundtrip` and the printed proof in the machine-generated audit.

## `canonical_coefficient_encoding_injective`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem canonical_coefficient_encoding_injective (r : ℕ) :
    Function.Injective (canonicalCoefficientNatural.app r)
```

Proof method: Kernel-checked tactic proof using simpa, intro. Exact terms and dependencies are in the audit.

Axioms: `none`.

Dependencies: see `DIRECT DEPENDENCIES canonical_coefficient_encoding_injective` and the printed proof in the machine-generated audit.

## `canonical_decode_encode`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem canonical_decode_encode {r : ℕ} (x : CanonicalSubstrate r) :
    canonicalDecode r (canonicalEncodingNatural.app r x) = some x
```

Proof method: Kernel-checked tactic proof using cases, simp. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES canonical_decode_encode` and the printed proof in the machine-generated audit.

## `canonical_encoding_injective`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem canonical_encoding_injective (r : ℕ) :
    Function.Injective (canonicalEncodingNatural.app r)
```

Proof method: Kernel-checked tactic proof using simpa, intro. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES canonical_encoding_injective` and the printed proof in the machine-generated audit.

## `canonical_cycle_translation_commute`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem canonical_cycle_translation_commute {r : ℕ} (h : RegisterTranslation r)
    (x : CanonicalSubstrate r) :
    canonicalCycleNatural.app r (canonicalTranslationNatural.app r (h, x)) =
      canonicalTranslationNatural.app r (h, canonicalCycleNatural.app r x)
```

Proof method: Kernel-checked tactic proof using exact. Exact terms and dependencies are in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES canonical_cycle_translation_commute` and the printed proof in the machine-generated audit.

## `canonical_cycle_injective`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem canonical_cycle_injective (r : ℕ) :
    Function.Injective (canonicalCycleNatural.app r)
```

Proof method: Kernel-checked tactic proof using funext, rw, exact, intro. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES canonical_cycle_injective` and the printed proof in the machine-generated audit.

## `canonical_translation_injective`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem canonical_translation_injective {r : ℕ} (h : RegisterTranslation r) :
    Function.Injective (fun x : CanonicalSubstrate r => canonicalTranslationNatural.app r (h, x))
```

Proof method: Kernel-checked tactic proof using funext, rw, exact, intro. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES canonical_translation_injective` and the printed proof in the machine-generated audit.

## `canonical_step_injective`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem canonical_step_injective {r : ℕ} (h : RegisterTranslation r) :
    Function.Injective (fun x : CanonicalSubstrate r => canonicalStepNatural.app r (h, x))
```

Proof method: Kernel-checked tactic proof using exact, intro. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES canonical_step_injective` and the printed proof in the machine-generated audit.

## `canonical_phase_translation_invariant`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem canonical_phase_translation_invariant {r : ℕ} (h : RegisterTranslation r)
    (x : CanonicalSubstrate r) :
    canonicalPhaseNatural.app r (canonicalTranslationNatural.app r (h, x)) =
      canonicalPhaseNatural.app r x
```

Proof method: Definitional equality.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES canonical_phase_translation_invariant` and the printed proof in the machine-generated audit.

## `canonical_phase_projection_not_injective`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem canonical_phase_projection_not_injective :
    ¬ Function.Injective (canonicalPhaseNatural.app 1)
```

Proof method: Kernel-checked tactic proof using exact, change, intro. Exact terms and dependencies are in the audit.

Axioms: `propext,
 Classical.choice,
 Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES canonical_phase_projection_not_injective` and the printed proof in the machine-generated audit.

## `canonical_retained_phase_injective`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem canonical_retained_phase_injective (r : ℕ) :
    Function.Injective ((retainRegisterNatural canonicalPhaseNatural).app r)
```

Proof method: Direct proof term applying the named previously checked declarations; see the printed proof and dependencies.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES canonical_retained_phase_injective` and the printed proof in the machine-generated audit.

## `retained_coefficient_pullback_injective`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem retained_coefficient_pullback_injective {k : ℕ} {E X V : Type}
    [AddCommMonoid V] (r : ℕ) :
    Function.Injective ((retainRegisterNatural
      (coefficientPullbackNatural (k
```

Proof method: Direct proof term applying the named previously checked declarations; see the printed proof and dependencies.

Axioms: `propext,
 Classical.choice,
 Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES retained_coefficient_pullback_injective` and the printed proof in the machine-generated audit.

## `canonical_coefficient_semantics`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem canonical_coefficient_semantics {k r : ℕ} {E X V : Type}
    [AddCommMonoid V] [Module (ZMod 2) V]
    (t : Fin r → ProjectedTable k E X V)
    (p : Fin r → ZMod 2 × (Fin k → ZMod 2 × ZMod 2)) :
    (fun i => evaluateFullTable (pullbackTable (t i)) (p i)) =
      fun i => evaluateProjectedTable (t i) (permittedProjection (t i) (p i))
```

Proof method: Kernel-checked tactic proof using funext, exact. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES canonical_coefficient_semantics` and the printed proof in the machine-generated audit.

## `canonical_master_induction`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem canonical_master_induction {r : ℕ} (h : RegisterTranslation r)
    (initial : RegisterState r) (hregular : PhaseRegular initial) (n : ℕ) :
    CanonicalInvariant initial n (((registerStep h)^[n]) initial)
```

Proof method: Kernel-checked tactic proof using induction, funext, rw, simp, refine, exact, intro. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES canonical_master_induction` and the printed proof in the machine-generated audit.

## `canonical_invariant_relative`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem canonical_invariant_relative {r n : ℕ} {initial final : RegisterState r}
    (h : CanonicalInvariant initial n final) :
    ExternalRelativeEquivalent (registerPhases initial) (registerPhases final)
```

Proof method: Kernel-checked tactic proof using rw, simp, intro. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES canonical_invariant_relative` and the printed proof in the machine-generated audit.

## `canonical_master_period`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem canonical_master_period {r : ℕ} (h : RegisterTranslation r)
    (initial : RegisterState r) : ((registerStep h)^[12]) initial = initial
```

Proof method: Direct proof term applying the named previously checked declarations; see the printed proof and dependencies.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES canonical_master_period` and the printed proof in the machine-generated audit.

## `aligned_triple_noise_recovery`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem aligned_triple_noise_recovery (word : List (ZMod 12))
    (received : List (Fin 3 → ZMod 12)) (h : AlignedTripleNoise word received) :
    received.map tripleMajority = word
```

Proof method: Kernel-checked tactic proof using induction, rw, change. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES aligned_triple_noise_recovery` and the printed proof in the machine-generated audit.

## `aligned_triple_noise_length`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem aligned_triple_noise_length (word : List (ZMod 12))
    (received : List (Fin 3 → ZMod 12)) (h : AlignedTripleNoise word received) :
    word.length = received.length
```

Proof method: Direct proof term applying the named previously checked declarations; see the printed proof and dependencies.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES aligned_triple_noise_length` and the printed proof in the machine-generated audit.

## `protected_register_words_recovery`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem protected_register_words_recovery {r : ℕ} (words : RegisterWords r)
    (received : ProtectedRegisterWords r) (h : RegisterNoiseBound words received) :
    recoverRegisterWords received = words
```

Proof method: Kernel-checked tactic proof using funext, exact. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES protected_register_words_recovery` and the printed proof in the machine-generated audit.

## `aligned_triple_noise_protect`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem aligned_triple_noise_protect (word : List (ZMod 12)) :
    AlignedTripleNoise word (word.map (repetitionWord 3))
```

Proof method: Kernel-checked tactic proof using induction, simp, exact. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES aligned_triple_noise_protect` and the printed proof in the machine-generated audit.

## `protected_register_noise_bound`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem protected_register_noise_bound {r : ℕ} (words : RegisterWords r) :
    RegisterNoiseBound words (protectRegisterWords words)
```

Proof method: Direct proof term applying the named previously checked declarations; see the printed proof and dependencies.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES protected_register_noise_bound` and the printed proof in the machine-generated audit.

## `station_word_action_inverse`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem station_word_action_inverse (e : StationExpr) {r : ℕ} (words : RegisterWords r) :
    undoStationWordAction e (stationWordAction e words) = words
```

Proof method: Kernel-checked tactic proof using funext, simp. Exact terms and dependencies are in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES station_word_action_inverse` and the printed proof in the machine-generated audit.

## `canonical_transmitted_word_length`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem canonical_transmitted_word_length {r : ℕ} (A : RegisterState r → RegisterState r)
    (n : ℕ) (e : StationExpr) (x : CanonicalSubstrate r) (i : Fin r) :
    (stationWordAction e (((transportRegisterWords A)^[n])
      (canonicalEncodingNatural.app r x)) i).length = 17
```

Proof method: Kernel-checked tactic proof using rw, simp, change. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES canonical_transmitted_word_length` and the printed proof in the machine-generated audit.

## `canonical_received_word_length`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem canonical_received_word_length {r : ℕ} (A : RegisterState r → RegisterState r)
    (n : ℕ) (e : StationExpr) (x : CanonicalSubstrate r) (received : ProtectedRegisterWords r)
    (hnoise : RegisterNoiseBound
      (stationWordAction e (((transportRegisterWords A)^[n]) (canonicalEncodingNatural.app r x))) received)
    (i : Fin r) : (received i).length = 17
```

Proof method: Kernel-checked tactic proof using rw, exact. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES canonical_received_word_length` and the printed proof in the machine-generated audit.

## `canonical_station_encoding_injective`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem canonical_station_encoding_injective (r : ℕ) (e : StationExpr) :
    Function.Injective (fun x : CanonicalSubstrate r =>
      stationWordAction e (canonicalEncodingNatural.app r x))
```

Proof method: Kernel-checked tactic proof using rw, exact, intro. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES canonical_station_encoding_injective` and the printed proof in the machine-generated audit.

## `successor_triple_noise`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem successor_triple_noise : ∀ a : ZMod 12,
    wordDistance (repetitionWord 3 a) ![a + 1, a, a] ≤ 1
```

Proof method: Kernel-checked finite decision procedure (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES successor_triple_noise` and the printed proof in the machine-generated audit.

## `successor_word_noise`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem successor_word_noise (word : List (ZMod 12)) :
    AlignedTripleNoise word (word.map (fun a => ![a + 1, a, a]))
```

Proof method: Kernel-checked tactic proof using induction, exact. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES successor_word_noise` and the printed proof in the machine-generated audit.

## `successor_register_noise`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem successor_register_noise {r : ℕ} (words : RegisterWords r) :
    RegisterNoiseBound words (successorCorruption words)
```

Proof method: Direct proof term applying the named previously checked declarations; see the printed proof and dependencies.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES successor_register_noise` and the printed proof in the machine-generated audit.

## `canonical_operational_recovery`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem canonical_operational_recovery {r : ℕ} (A : RegisterState r → RegisterState r)
    (n : ℕ) (e : StationExpr) (x : CanonicalSubstrate r) (received : ProtectedRegisterWords r)
    (hnoise : RegisterNoiseBound
      (stationWordAction e (((transportRegisterWords A)^[n]) (canonicalEncodingNatural.app r x))) received) :
    recoverCanonicalOperational e received = some (canonicalPack ((A^[n]) x.state))
```

Proof method: Kernel-checked tactic proof using rw, change, unfold. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES canonical_operational_recovery` and the printed proof in the machine-generated audit.

## `canonical_operational_envelope`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem canonical_operational_envelope {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (e : StationExpr) (x : CanonicalSubstrate r) (hregular : PhaseRegular x.state)
    (received : ProtectedRegisterWords r)
    (hnoise : RegisterNoiseBound
      (stationWordAction e (((transportRegisterWords (registerStep h))^[n])
        (canonicalEncodingNatural.app r x))) received) :
    recoverCanonicalOperational e received = some (canonicalPack (((registerStep h)^[n]) x.state)) ∧
    CanonicalInvariant x.state n (((registerStep h)^[n]) x.state) ∧
    ExternalRelativeEquivalent (registerPhases x.state)
      (registerPhases (((registerStep h)^[n]) x.state))
```

Proof method: Kernel-checked tactic proof using exact. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES canonical_operational_envelope` and the printed proof in the machine-generated audit.

## `canonical_successor_channel_recovery`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem canonical_successor_channel_recovery {r : ℕ} (A : RegisterState r → RegisterState r)
    (n : ℕ) (e : StationExpr) (x : CanonicalSubstrate r) :
    recoverCanonicalOperational e (successorCorruption (stationWordAction e
      (((transportRegisterWords A)^[n]) (canonicalEncodingNatural.app r x)))) =
      some (canonicalPack ((A^[n]) x.state))
```

Proof method: Direct proof term applying the named previously checked declarations; see the printed proof and dependencies.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES canonical_successor_channel_recovery` and the printed proof in the machine-generated audit.

## `canonical_undo_run`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem canonical_undo_run {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (x : CanonicalSubstrate r) :
    undoCanonicalDynamics h n (canonicalPack (((registerStep h)^[n]) x.state)) = x
```

Proof method: Kernel-checked tactic proof using exact, apply. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES canonical_undo_run` and the printed proof in the machine-generated audit.

## `canonical_initial_recovery`

Source: `IndependentDuodenary/CanonicalArchitecture.lean`. Compilation: **passed**.

```lean
theorem canonical_initial_recovery {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (e : StationExpr) (x : CanonicalSubstrate r) (received : ProtectedRegisterWords r)
    (hnoise : RegisterNoiseBound
      (stationWordAction e (((transportRegisterWords (registerStep h))^[n])
        (canonicalEncodingNatural.app r x))) received) :
    recoverCanonicalInitial h n e received = some x
```

Proof method: Kernel-checked tactic proof using change, calc. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES canonical_initial_recovery` and the printed proof in the machine-generated audit.

## `cipher_stage_normal_form`

Source: `IndependentDuodenary/CipherValidator.lean`. Compilation: **passed**.

```lean
theorem cipher_stage_normal_form (p : CipherPeriod) :
    cipherStage p = (12 * p.numerator / p.denominator) % 360
```

Proof method: Natural-number remainder/division identity Nat.mod_mul_left_div_self.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES cipher_stage_normal_form` and the printed proof in the machine-generated audit.

## `cipher_pipeline_correct`

Source: `IndependentDuodenary/CipherValidator.lean`. Compilation: **passed**.

```lean
theorem cipher_pipeline_correct (p : CipherPeriod) (h : ℕ) :
    cipherCalculate p h = cipherNormalized p h
```

Proof method: Substitute the proved stage normal form into both implementations.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES cipher_pipeline_correct` and the printed proof in the machine-generated audit.

## `cipher_stage_bound`

Source: `IndependentDuodenary/CipherValidator.lean`. Compilation: **passed**.

```lean
theorem cipher_stage_bound (p : CipherPeriod) : cipherStage p < 360
```

Proof method: Stage normal form and the strict natural remainder bound.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES cipher_stage_bound` and the printed proof in the machine-generated audit.

## `cipher_output_bound`

Source: `IndependentDuodenary/CipherValidator.lean`. Compilation: **passed**.

```lean
theorem cipher_output_bound (p : CipherPeriod) (h : ℕ) :
    cipherCalculate p h < 144
```

Proof method: Strict natural remainder bound modulo 144.

Axioms: `none`.

Dependencies: see `DIRECT DEPENDENCIES cipher_output_bound` and the printed proof in the machine-generated audit.

## `cipher_zero_iff_divides`

Source: `IndependentDuodenary/CipherValidator.lean`. Compilation: **passed**.

```lean
theorem cipher_zero_iff_divides (p : CipherPeriod) (h : ℕ) :
    cipherCalculate p h = 0 ↔ 144 ∣ cipherStage p * h
```

Proof method: Natural divisibility is equivalent to zero remainder.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES cipher_zero_iff_divides` and the printed proof in the machine-generated audit.

## `cipher_same_stage`

Source: `IndependentDuodenary/CipherValidator.lean`. Compilation: **passed**.

```lean
theorem cipher_same_stage (p q : CipherPeriod) (h : ℕ)
    (heq : cipherStage p = cipherStage q) :
    cipherCalculate p h = cipherCalculate q h
```

Proof method: Substitution into the calculation definition.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES cipher_same_stage` and the printed proof in the machine-generated audit.

## `cipher_shift_thirty_stage`

Source: `IndependentDuodenary/CipherValidator.lean`. Compilation: **passed**.

```lean
theorem cipher_shift_thirty_stage (p : CipherPeriod) :
    cipherStage (cipherShiftThirty p) = cipherStage p
```

Proof method: Distribute multiplication and remove one full remainder modulus.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES cipher_shift_thirty_stage` and the printed proof in the machine-generated audit.

## `cipher_shift_thirty_output`

Source: `IndependentDuodenary/CipherValidator.lean`. Compilation: **passed**.

```lean
theorem cipher_shift_thirty_output (p : CipherPeriod) (h : ℕ) :
    cipherCalculate (cipherShiftThirty p) h = cipherCalculate p h
```

Proof method: Apply cipher_same_stage to the thirty-year stage identity.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES cipher_shift_thirty_output` and the printed proof in the machine-generated audit.

## `cipher_shift_thirty_distinct`

Source: `IndependentDuodenary/CipherValidator.lean`. Compilation: **passed**.

```lean
theorem cipher_shift_thirty_distinct (p : CipherPeriod) :
    cipherShiftThirty p ≠ p
```

Proof method: Project to the numerator; positive denominator makes the increase nonzero.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES cipher_shift_thirty_distinct` and the printed proof in the machine-generated audit.

## `cipher_calculate_not_injective`

Source: `IndependentDuodenary/CipherValidator.lean`. Compilation: **passed**.

```lean
theorem cipher_calculate_not_injective (h : ℕ) :
    ¬ Function.Injective (fun p : CipherPeriod => cipherCalculate p h)
```

Proof method: The distinct thirty-year-shifted input has the same calculated output.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES cipher_calculate_not_injective` and the printed proof in the machine-generated audit.

## `cipher_result_roundtrip`

Source: `IndependentDuodenary/CipherValidator.lean`. Compilation: **passed**.

```lean
theorem cipher_result_roundtrip : ∀ r : ZMod 144,
    decodeCipherResult (encodeCipherResult r) = r
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES cipher_result_roundtrip` and the printed proof in the machine-generated audit.

## `cipher_payload_roundtrip`

Source: `IndependentDuodenary/CipherValidator.lean`. Compilation: **passed**.

```lean
theorem cipher_payload_roundtrip (c : CipherPayload) :
    encodeCipherResult (decodeCipherResult c) = c
```

Proof method: Destructure the payload and kernel-check all finite digit pairs.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES cipher_payload_roundtrip` and the printed proof in the machine-generated audit.

## `cipher_result_encoding_injective`

Source: `IndependentDuodenary/CipherValidator.lean`. Compilation: **passed**.

```lean
theorem cipher_result_encoding_injective : Function.Injective encodeCipherResult
```

Proof method: Injectivity of the explicitly proved payload equivalence.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES cipher_result_encoding_injective` and the printed proof in the machine-generated audit.

## `cipher_protected_result_recovery`

Source: `IndependentDuodenary/CipherValidator.lean`. Compilation: **passed**.

```lean
theorem cipher_protected_result_recovery (result : ZMod 144) (received : ProtectedStationCode)
    (hfirst : wordDistance (protectStationWire (cipherPayloadWire (encodeCipherResult result))).1
      received.1 ≤ 1)
    (hsecond : wordDistance (protectStationWire (cipherPayloadWire (encodeCipherResult result))).2
      received.2 ≤ 1) :
    cipherReceivedResult received = result
```

Proof method: Recover both repeated digits, then apply the result codec round trip.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES cipher_protected_result_recovery` and the printed proof in the machine-generated audit.

## `cipher_pipeline_protected_recovery`

Source: `IndependentDuodenary/CipherValidator.lean`. Compilation: **passed**.

```lean
theorem cipher_pipeline_protected_recovery (p : CipherPeriod) (h : ℕ)
    (received : ProtectedStationCode)
    (hfirst : wordDistance (protectStationWire (cipherPayloadWire
      (encodeCipherResult (cipherCalculate p h : ZMod 144)))).1 received.1 ≤ 1)
    (hsecond : wordDistance (protectStationWire (cipherPayloadWire
      (encodeCipherResult (cipherCalculate p h : ZMod 144)))).2 received.2 ≤ 1) :
    cipherReceivedResult received = (cipherNormalized p h : ZMod 144)
```

Proof method: Rewrite normalized output by pipeline correctness and apply protected result recovery.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES cipher_pipeline_protected_recovery` and the printed proof in the machine-generated audit.

## `cipher_eris_fixture`

Source: `IndependentDuodenary/CipherValidator.lean`. Compilation: **passed**.

```lean
theorem cipher_eris_fixture : cipherCalculate (cipherHundredths 55800 (by decide)) 12 = 0
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `none`.

Dependencies: see `DIRECT DEPENDENCIES cipher_eris_fixture` and the printed proof in the machine-generated audit.

## `cipher_haumea_fixture`

Source: `IndependentDuodenary/CipherValidator.lean`. Compilation: **passed**.

```lean
theorem cipher_haumea_fixture : cipherCalculate (cipherHundredths 28400 (by decide)) 5 = 120
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `none`.

Dependencies: see `DIRECT DEPENDENCIES cipher_haumea_fixture` and the printed proof in the machine-generated audit.

## `cipher_makemake_fixture`

Source: `IndependentDuodenary/CipherValidator.lean`. Compilation: **passed**.

```lean
theorem cipher_makemake_fixture : cipherCalculate (cipherHundredths 30604 (by decide)) 5 = 72
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `none`.

Dependencies: see `DIRECT DEPENDENCIES cipher_makemake_fixture` and the printed proof in the machine-generated audit.

## `cipher_gonggong_fixture`

Source: `IndependentDuodenary/CipherValidator.lean`. Compilation: **passed**.

```lean
theorem cipher_gonggong_fixture : cipherCalculate (cipherHundredths 55287 (by decide)) 5 = 50
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `none`.

Dependencies: see `DIRECT DEPENDENCIES cipher_gonggong_fixture` and the printed proof in the machine-generated audit.

## `cipher_orcus_fixture`

Source: `IndependentDuodenary/CipherValidator.lean`. Compilation: **passed**.

```lean
theorem cipher_orcus_fixture : cipherCalculate (cipherHundredths 24753 (by decide)) 5 = 18
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `none`.

Dependencies: see `DIRECT DEPENDENCIES cipher_orcus_fixture` and the printed proof in the machine-generated audit.

## `prize_word_decode_encode`

Source: `IndependentDuodenary/ComplexityEncoding.lean`. Compilation: **passed**.

```lean
theorem prize_word_decode_encode (x : PrizeBinaryWord) :
    prizeDecodeWord (prizeEncodeWord x) = some x
```

Proof method: Structural induction, finite alphabet case analysis, or rewriting by the parser and halted-run lemmas; see the exact proof term and direct dependencies below.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES prize_word_decode_encode` and the printed proof in the machine-generated audit.

## `prize_word_encode_decode`

Source: `IndependentDuodenary/ComplexityEncoding.lean`. Compilation: **passed**.

```lean
theorem prize_word_encode_decode (raw : List (Fin 4)) (x : PrizeBinaryWord)
    (h : prizeDecodeWord raw = some x) : prizeEncodeWord x = raw
```

Proof method: Structural induction, finite alphabet case analysis, or rewriting by the parser and halted-run lemmas; see the exact proof term and direct dependencies below.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES prize_word_encode_decode` and the printed proof in the machine-generated audit.

## `prize_word_encoding_injective`

Source: `IndependentDuodenary/ComplexityEncoding.lean`. Compilation: **passed**.

```lean
theorem prize_word_encoding_injective : Function.Injective prizeEncodeWord
```

Proof method: Structural induction, finite alphabet case analysis, or rewriting by the parser and halted-run lemmas; see the exact proof term and direct dependencies below.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES prize_word_encoding_injective` and the printed proof in the machine-generated audit.

## `prize_word_decode_blank_rejected`

Source: `IndependentDuodenary/ComplexityEncoding.lean`. Compilation: **passed**.

```lean
theorem prize_word_decode_blank_rejected (raw : List (Fin 4)) :
    prizeDecodeWord (0 :: raw) = none
```

Proof method: Structural induction, finite alphabet case analysis, or rewriting by the parser and halted-run lemmas; see the exact proof term and direct dependencies below.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES prize_word_decode_blank_rejected` and the printed proof in the machine-generated audit.

## `prize_word_decode_separator_rejected`

Source: `IndependentDuodenary/ComplexityEncoding.lean`. Compilation: **passed**.

```lean
theorem prize_word_decode_separator_rejected (raw : List (Fin 4)) :
    prizeDecodeWord (3 :: raw) = none
```

Proof method: Structural induction, finite alphabet case analysis, or rewriting by the parser and halted-run lemmas; see the exact proof term and direct dependencies below.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES prize_word_decode_separator_rejected` and the printed proof in the machine-generated audit.

## `prize_word_decode_prefix`

Source: `IndependentDuodenary/ComplexityEncoding.lean`. Compilation: **passed**.

```lean
theorem prize_word_decode_prefix (x : PrizeBinaryWord) (raw : List (Fin 4)) :
    prizeDecodeWord (prizeEncodeWord x ++ raw) =
      (fun y => x ++ y) <$> prizeDecodeWord raw
```

Proof method: Structural induction, finite alphabet case analysis, or rewriting by the parser and halted-run lemmas; see the exact proof term and direct dependencies below.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES prize_word_decode_prefix` and the printed proof in the machine-generated audit.

## `prize_pair_decode_prefix`

Source: `IndependentDuodenary/ComplexityEncoding.lean`. Compilation: **passed**.

```lean
theorem prize_pair_decode_prefix (x : PrizeBinaryWord) (raw : List (Fin 4)) :
    prizeDecodePair (prizeEncodeWord x ++ 3 :: raw) =
      (fun w => (x, w)) <$> prizeDecodeWord raw
```

Proof method: Structural induction, finite alphabet case analysis, or rewriting by the parser and halted-run lemmas; see the exact proof term and direct dependencies below.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES prize_pair_decode_prefix` and the printed proof in the machine-generated audit.

## `prize_pair_decode_encode`

Source: `IndependentDuodenary/ComplexityEncoding.lean`. Compilation: **passed**.

```lean
theorem prize_pair_decode_encode (x w : PrizeBinaryWord) :
    prizeDecodePair (prizeEncodePair x w) = some (x, w)
```

Proof method: Structural induction, finite alphabet case analysis, or rewriting by the parser and halted-run lemmas; see the exact proof term and direct dependencies below.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES prize_pair_decode_encode` and the printed proof in the machine-generated audit.

## `prize_pair_encode_decode`

Source: `IndependentDuodenary/ComplexityEncoding.lean`. Compilation: **passed**.

```lean
theorem prize_pair_encode_decode (raw : List (Fin 4)) (p : PrizeBinaryWord × PrizeBinaryWord)
    (h : prizeDecodePair raw = some p) : prizeEncodePair p.1 p.2 = raw
```

Proof method: Structural induction, finite alphabet case analysis, or rewriting by the parser and halted-run lemmas; see the exact proof term and direct dependencies below.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES prize_pair_encode_decode` and the printed proof in the machine-generated audit.

## `prize_pair_encoding_injective`

Source: `IndependentDuodenary/ComplexityEncoding.lean`. Compilation: **passed**.

```lean
theorem prize_pair_encoding_injective :
    Function.Injective (fun p : PrizeBinaryWord × PrizeBinaryWord => prizeEncodePair p.1 p.2)
```

Proof method: Structural induction, finite alphabet case analysis, or rewriting by the parser and halted-run lemmas; see the exact proof term and direct dependencies below.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES prize_pair_encoding_injective` and the printed proof in the machine-generated audit.

## `prize_pair_missing_separator_rejected`

Source: `IndependentDuodenary/ComplexityEncoding.lean`. Compilation: **passed**.

```lean
theorem prize_pair_missing_separator_rejected (x : PrizeBinaryWord) :
    prizeDecodePair (prizeEncodeWord x) = none
```

Proof method: Structural induction, finite alphabet case analysis, or rewriting by the parser and halted-run lemmas; see the exact proof term and direct dependencies below.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES prize_pair_missing_separator_rejected` and the printed proof in the machine-generated audit.

## `prize_pair_extra_separator_rejected`

Source: `IndependentDuodenary/ComplexityEncoding.lean`. Compilation: **passed**.

```lean
theorem prize_pair_extra_separator_rejected (x w : PrizeBinaryWord) (raw : List (Fin 4)) :
    prizeDecodePair (prizeEncodePair x w ++ 3 :: raw) = none
```

Proof method: Structural induction, finite alphabet case analysis, or rewriting by the parser and halted-run lemmas; see the exact proof term and direct dependencies below.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES prize_pair_extra_separator_rejected` and the printed proof in the machine-generated audit.

## `prize_pair_trailing_blank_rejected`

Source: `IndependentDuodenary/ComplexityEncoding.lean`. Compilation: **passed**.

```lean
theorem prize_pair_trailing_blank_rejected (x w : PrizeBinaryWord) (raw : List (Fin 4)) :
    prizeDecodePair (prizeEncodePair x w ++ 0 :: raw) = none
```

Proof method: Structural induction, finite alphabet case analysis, or rewriting by the parser and halted-run lemmas; see the exact proof term and direct dependencies below.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES prize_pair_trailing_blank_rejected` and the printed proof in the machine-generated audit.

## `prize_run_succ`

Source: `IndependentDuodenary/ComplexityEncoding.lean`. Compilation: **passed**.

```lean
theorem prize_run_succ {states : ℕ} (M : PrizeMachine states) (input : List (Fin 4)) (t : ℕ) :
    prizeRun M input (t + 1) =
      (Turing.TM0.step M (prizeRun M input t)).getD (prizeRun M input t)
```

Proof method: Structural induction, finite alphabet case analysis, or rewriting by the parser and halted-run lemmas; see the exact proof term and direct dependencies below.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES prize_run_succ` and the printed proof in the machine-generated audit.

## `prize_halted_run_stable`

Source: `IndependentDuodenary/ComplexityEncoding.lean`. Compilation: **passed**.

```lean
theorem prize_halted_run_stable {states : ℕ} (M : PrizeMachine states)
    (input : List (Fin 4)) (t : ℕ) (halt : prizeHalted M input t) (s : ℕ) :
    prizeRun M input (t + s) = prizeRun M input t
```

Proof method: Structural induction, finite alphabet case analysis, or rewriting by the parser and halted-run lemmas; see the exact proof term and direct dependencies below.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES prize_halted_run_stable` and the printed proof in the machine-generated audit.

## `prize_halted_status_stable`

Source: `IndependentDuodenary/ComplexityEncoding.lean`. Compilation: **passed**.

```lean
theorem prize_halted_status_stable {states : ℕ} (M : PrizeMachine states)
    (input : List (Fin 4)) (t : ℕ) (halt : prizeHalted M input t) (s : ℕ) :
    prizeHalted M input (t + s)
```

Proof method: Structural induction, finite alphabet case analysis, or rewriting by the parser and halted-run lemmas; see the exact proof term and direct dependencies below.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES prize_halted_status_stable` and the printed proof in the machine-generated audit.

## `prize_halted_acceptance_stable`

Source: `IndependentDuodenary/ComplexityEncoding.lean`. Compilation: **passed**.

```lean
theorem prize_halted_acceptance_stable {states : ℕ} (M : PrizeMachine states)
    (input : List (Fin 4)) (t : ℕ) (halt : prizeHalted M input t) (s : ℕ) :
    prizeAccepts M input (t + s) ↔ prizeAccepts M input t
```

Proof method: Structural induction, finite alphabet case analysis, or rewriting by the parser and halted-run lemmas; see the exact proof term and direct dependencies below.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES prize_halted_acceptance_stable` and the printed proof in the machine-generated audit.

## `prize_halted_boolean_output_stable`

Source: `IndependentDuodenary/ComplexityEncoding.lean`. Compilation: **passed**.

```lean
theorem prize_halted_boolean_output_stable {states : ℕ} (M : PrizeMachine states)
    (input : List (Fin 4)) (t : ℕ) (halt : prizeHalted M input t) (s : ℕ) :
    prizeBooleanOutput M input (t + s) ↔ prizeBooleanOutput M input t
```

Proof method: Structural induction, finite alphabet case analysis, or rewriting by the parser and halted-run lemmas; see the exact proof term and direct dependencies below.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES prize_halted_boolean_output_stable` and the printed proof in the machine-generated audit.

## `prize_accepts_by_bound_iff`

Source: `IndependentDuodenary/ComplexityEncoding.lean`. Compilation: **passed**.

```lean
theorem prize_accepts_by_bound_iff {states : ℕ} (M : PrizeMachine states)
    (input : List (Fin 4)) (bound : ℕ) :
    (prizeHalted M input bound ∧ prizeAccepts M input bound) ↔
      ∃ t ≤ bound, prizeHalted M input t ∧ prizeAccepts M input t
```

Proof method: Structural induction, finite alphabet case analysis, or rewriting by the parser and halted-run lemmas; see the exact proof term and direct dependencies below.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES prize_accepts_by_bound_iff` and the printed proof in the machine-generated audit.

## `semantic_decoder_no_collision`

Source: `IndependentDuodenary/EncodingIntegrity.lean`. Compilation: **passed**.

```lean
theorem semantic_decoder_no_collision {L S : Type*} (r : Setoid L)
    (encode : L → S) (decode : S → Quotient r)
    (h : ∀ x, decode (encode x) = Quotient.mk r x)
    (x y : L) (heq : encode x = encode y) : r.r x y
```

Proof method: Apply the class decoder to equal encodings, then Quotient.exact.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES semantic_decoder_no_collision` and the printed proof in the machine-generated audit.

## `exact_decoder_injective`

Source: `IndependentDuodenary/EncodingIntegrity.lean`. Compilation: **passed**.

```lean
theorem exact_decoder_injective {M S : Type*} (encode : M → S) (decode : S → M)
    (h : Function.LeftInverse decode encode) : Function.Injective encode
```

Proof method: Injectivity of a function with a left inverse.

Axioms: `none`.

Dependencies: see `DIRECT DEPENDENCIES exact_decoder_injective` and the printed proof in the machine-generated audit.

## `exact_decoder_capacity`

Source: `IndependentDuodenary/EncodingIntegrity.lean`. Compilation: **passed**.

```lean
theorem exact_decoder_capacity {M S : Type*} [Fintype M] [Fintype S]
    (encode : M → S) (decode : S → M) (h : Function.LeftInverse decode encode) :
    Fintype.card M ≤ Fintype.card S
```

Proof method: Finite cardinality inequality from the proved encoder injectivity.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES exact_decoder_capacity` and the printed proof in the machine-generated audit.

## `no_exact_decoder_over_capacity`

Source: `IndependentDuodenary/EncodingIntegrity.lean`. Compilation: **passed**.

```lean
theorem no_exact_decoder_over_capacity {M S : Type*} [Fintype M] [Fintype S]
    (hcard : Fintype.card S < Fintype.card M) (encode : M → S) (decode : S → M) :
    ¬ Function.LeftInverse decode encode
```

Proof method: Contradict the exact-decoder cardinality bound.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES no_exact_decoder_over_capacity` and the printed proof in the machine-generated audit.

## `no_infinite_exact_finite_decoder`

Source: `IndependentDuodenary/EncodingIntegrity.lean`. Compilation: **passed**.

```lean
theorem no_infinite_exact_finite_decoder {M S : Type*} [Infinite M] [Finite S]
    (encode : M → S) (decode : S → M) : ¬ Function.LeftInverse decode encode
```

Proof method: Infinite-to-finite pigeonhole theorem and left-inverse injectivity.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES no_infinite_exact_finite_decoder` and the printed proof in the machine-generated audit.

## `twelve_symbol_word_capacity`

Source: `IndependentDuodenary/EncodingIntegrity.lean`. Compilation: **passed**.

```lean
theorem twelve_symbol_word_capacity (n : ℕ) :
    Fintype.card (Fin n → ZMod 12) = 12 ^ n
```

Proof method: Cardinality of a function space with domain Fin n and codomain ZMod 12.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES twelve_symbol_word_capacity` and the printed proof in the machine-generated audit.

## `natural_word_length_left_inverse`

Source: `IndependentDuodenary/EncodingIntegrity.lean`. Compilation: **passed**.

```lean
theorem natural_word_length_left_inverse :
    Function.LeftInverse List.length encodeNaturalWord
```

Proof method: Length of List.replicate is the encoded natural number.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES natural_word_length_left_inverse` and the printed proof in the machine-generated audit.

## `natural_word_encoding_injective`

Source: `IndependentDuodenary/EncodingIntegrity.lean`. Compilation: **passed**.

```lean
theorem natural_word_encoding_injective : Function.Injective encodeNaturalWord
```

Proof method: Injectivity supplied by the length left inverse.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES natural_word_encoding_injective` and the printed proof in the machine-generated audit.

## `word_distance_self`

Source: `IndependentDuodenary/EncodingIntegrity.lean`. Compilation: **passed**.

```lean
theorem word_distance_self (x : ι → Alphabet) : wordDistance x x = 0
```

Proof method: The mismatch filter is empty.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES word_distance_self` and the printed proof in the machine-generated audit.

## `word_distance_comm`

Source: `IndependentDuodenary/EncodingIntegrity.lean`. Compilation: **passed**.

```lean
theorem word_distance_comm (x y : ι → Alphabet) : wordDistance x y = wordDistance y x
```

Proof method: Symmetry of inequality in the mismatch predicate.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES word_distance_comm` and the printed proof in the machine-generated audit.

## `word_distance_triangle`

Source: `IndependentDuodenary/EncodingIntegrity.lean`. Compilation: **passed**.

```lean
theorem word_distance_triangle (x y z : ι → Alphabet) :
    wordDistance x z ≤ wordDistance x y + wordDistance y z
```

Proof method: Every endpoint mismatch lies in the union of the two intermediate mismatch sets; cardinality bounds.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES word_distance_triangle` and the printed proof in the machine-generated audit.

## `bounded_error_unique`

Source: `IndependentDuodenary/EncodingIntegrity.lean`. Compilation: **passed**.

```lean
theorem bounded_error_unique (C : Set (ι → Alphabet)) (d t : ℕ)
    (hsep : ∀ a ∈ C, ∀ b ∈ C, a ≠ b → d ≤ wordDistance a b)
    (hbound : 2 * t < d) (a b received : ι → Alphabet)
    (ha : a ∈ C) (hb : b ∈ C)
    (hea : wordDistance a received ≤ t) (heb : wordDistance b received ≤ t) : a = b
```

Proof method: The proved Hamming triangle inequality contradicts the explicit separation and error-radius bounds.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES bounded_error_unique` and the printed proof in the machine-generated audit.

## `bounded_error_decoder_correct`

Source: `IndependentDuodenary/EncodingIntegrity.lean`. Compilation: **passed**.

```lean
theorem bounded_error_decoder_correct (C : Set (ι → Alphabet)) (d t : ℕ)
    (hsep : ∀ a ∈ C, ∀ b ∈ C, a ≠ b → d ≤ wordDistance a b)
    (hbound : 2 * t < d) (decode : (ι → Alphabet) → (ι → Alphabet))
    (received sent : ι → Alphabet) (hsent : sent ∈ C)
    (hnoise : wordDistance sent received ≤ t)
    (hdecode : decode received ∈ C)
    (hradius : wordDistance (decode received) received ≤ t) : decode received = sent
```

Proof method: Apply bounded_error_unique to the decoder output and transmitted codeword.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES bounded_error_decoder_correct` and the printed proof in the machine-generated audit.

## `repetition_word_distance`

Source: `IndependentDuodenary/EncodingIntegrity.lean`. Compilation: **passed**.

```lean
theorem repetition_word_distance (n : ℕ) (a b : Alphabet) :
    wordDistance (repetitionWord n a) (repetitionWord n b) = if a = b then 0 else n
```

Proof method: Equal/unequal payload cases make the mismatch set empty or all of Fin n.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES repetition_word_distance` and the printed proof in the machine-generated audit.

## `repetition_word_injective`

Source: `IndependentDuodenary/EncodingIntegrity.lean`. Compilation: **passed**.

```lean
theorem repetition_word_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (repetitionWord (Alphabet
```

Proof method: Evaluate an equality of repetition words at the first coordinate, supplied by n>0.

Axioms: `none`.

Dependencies: see `DIRECT DEPENDENCIES repetition_word_injective` and the printed proof in the machine-generated audit.

## `repetition_code_separation`

Source: `IndependentDuodenary/EncodingIntegrity.lean`. Compilation: **passed**.

```lean
theorem repetition_code_separation (n : ℕ) :
    ∀ a ∈ Set.range (repetitionWord (Alphabet
```

Proof method: Unpack both codewords from the range and use their explicit repetition-word distance.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES repetition_code_separation` and the printed proof in the machine-generated audit.

## `repetition_three_one_error_unique`

Source: `IndependentDuodenary/EncodingIntegrity.lean`. Compilation: **passed**.

```lean
theorem repetition_three_one_error_unique (a b : Alphabet) (received : Fin 3 → Alphabet)
    (ha : wordDistance (repetitionWord 3 a) received ≤ 1)
    (hb : wordDistance (repetitionWord 3 b) received ≤ 1) : a = b
```

Proof method: Specialize bounded_error_unique to the proved repetition separation and use encoder injectivity.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES repetition_three_one_error_unique` and the printed proof in the machine-generated audit.

## `two_errors_distance_lower`

Source: `IndependentDuodenary/EncodingIntegrity.lean`. Compilation: **passed**.

```lean
theorem two_errors_distance_lower (x y : ι → Alphabet) (i j : ι) (hij : i ≠ j)
    (hi : x i ≠ y i) (hj : x j ≠ y j) : 2 ≤ wordDistance x y
```

Proof method: The two distinct corrupted positions form a two-element subset of the mismatch set.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES two_errors_distance_lower` and the printed proof in the machine-generated audit.

## `at_most_one_error_pair`

Source: `IndependentDuodenary/EncodingIntegrity.lean`. Compilation: **passed**.

```lean
theorem at_most_one_error_pair (x y : ι → Alphabet) (i j : ι) (hij : i ≠ j)
    (hnoise : wordDistance x y ≤ 1) : x i = y i ∨ x j = y j
```

Proof method: Two errors would contradict the assumed distance at most one.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES at_most_one_error_pair` and the printed proof in the machine-generated audit.

## `repetition_majority_recovery`

Source: `IndependentDuodenary/EncodingIntegrity.lean`. Compilation: **passed**.

```lean
theorem repetition_majority_recovery (a : Alphabet) (received : Fin 3 → Alphabet)
    (hnoise : wordDistance (repetitionWord 3 a) received ≤ 1) :
    tripleMajority received = a
```

Proof method: The explicit majority decoder and the proved impossibility of two corrupted positions.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES repetition_majority_recovery` and the printed proof in the machine-generated audit.

## `fulgurite_zero_ne_six`

Source: `IndependentDuodenary/FulguriteSAT.lean`. Compilation: **passed**.

```lean
theorem fulgurite_zero_ne_six : (0 : ZMod 12) ≠ 6
```

Proof method: Structural induction, finite Boolean case analysis, phase-encoding equivalence, or composition of certified rewrites; exact proof terms and direct dependencies are retained in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES fulgurite_zero_ne_six` and the printed proof in the machine-generated audit.

## `fulgurite_half_turn_twice`

Source: `IndependentDuodenary/FulguriteSAT.lean`. Compilation: **passed**.

```lean
theorem fulgurite_half_turn_twice (x : ZMod 12) : x + 6 + 6 = x
```

Proof method: Structural induction, finite Boolean case analysis, phase-encoding equivalence, or composition of certified rewrites; exact proof terms and direct dependencies are retained in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES fulgurite_half_turn_twice` and the printed proof in the machine-generated audit.

## `fulgurite_bit_negation`

Source: `IndependentDuodenary/FulguriteSAT.lean`. Compilation: **passed**.

```lean
theorem fulgurite_bit_negation (b : Bool) :
    fulguriteBit (!b) = fulguriteBit b + 6
```

Proof method: Structural induction, finite Boolean case analysis, phase-encoding equivalence, or composition of certified rewrites; exact proof terms and direct dependencies are retained in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES fulgurite_bit_negation` and the printed proof in the machine-generated audit.

## `fulgurite_bit_conjunction`

Source: `IndependentDuodenary/FulguriteSAT.lean`. Compilation: **passed**.

```lean
theorem fulgurite_bit_conjunction (b c : Bool) :
    fulguriteMeet (fulguriteBit b) (fulguriteBit c) = fulguriteBit (b && c)
```

Proof method: Structural induction, finite Boolean case analysis, phase-encoding equivalence, or composition of certified rewrites; exact proof terms and direct dependencies are retained in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES fulgurite_bit_conjunction` and the printed proof in the machine-generated audit.

## `fulgurite_bit_disjunction`

Source: `IndependentDuodenary/FulguriteSAT.lean`. Compilation: **passed**.

```lean
theorem fulgurite_bit_disjunction (b c : Bool) :
    fulguriteJoin (fulguriteBit b) (fulguriteBit c) = fulguriteBit (b || c)
```

Proof method: Structural induction, finite Boolean case analysis, phase-encoding equivalence, or composition of certified rewrites; exact proof terms and direct dependencies are retained in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES fulgurite_bit_disjunction` and the printed proof in the machine-generated audit.

## `fulgurite_bit_injective`

Source: `IndependentDuodenary/FulguriteSAT.lean`. Compilation: **passed**.

```lean
theorem fulgurite_bit_injective : Function.Injective fulguriteBit
```

Proof method: Structural induction, finite Boolean case analysis, phase-encoding equivalence, or composition of certified rewrites; exact proof terms and direct dependencies are retained in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES fulgurite_bit_injective` and the printed proof in the machine-generated audit.

## `fulgurite_bit_law`

Source: `IndependentDuodenary/FulguriteSAT.lean`. Compilation: **passed**.

```lean
theorem fulgurite_bit_law (b : Bool) : obsidianBitLaw (fulguriteBit b)
```

Proof method: Structural induction, finite Boolean case analysis, phase-encoding equivalence, or composition of certified rewrites; exact proof terms and direct dependencies are retained in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES fulgurite_bit_law` and the printed proof in the machine-generated audit.

## `fulgurite_assignment_law`

Source: `IndependentDuodenary/FulguriteSAT.lean`. Compilation: **passed**.

```lean
theorem fulgurite_assignment_law {n : ℕ} (a : Fin n → Bool) :
    obsidianAssignmentLaw (fulguriteCompileAssignment a)
```

Proof method: Structural induction, finite Boolean case analysis, phase-encoding equivalence, or composition of certified rewrites; exact proof terms and direct dependencies are retained in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES fulgurite_assignment_law` and the printed proof in the machine-generated audit.

## `fulgurite_assignment_decode_encode`

Source: `IndependentDuodenary/FulguriteSAT.lean`. Compilation: **passed**.

```lean
theorem fulgurite_assignment_decode_encode {n : ℕ} (a : Fin n → Bool) :
    fulguriteDecodeAssignment (fulguriteCompileAssignment a) = a
```

Proof method: Structural induction, finite Boolean case analysis, phase-encoding equivalence, or composition of certified rewrites; exact proof terms and direct dependencies are retained in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES fulgurite_assignment_decode_encode` and the printed proof in the machine-generated audit.

## `fulgurite_assignment_encode_decode`

Source: `IndependentDuodenary/FulguriteSAT.lean`. Compilation: **passed**.

```lean
theorem fulgurite_assignment_encode_decode {n : ℕ} (p : RegisterPhase n)
    (valid : obsidianAssignmentLaw p) :
    fulguriteCompileAssignment (fulguriteDecodeAssignment p) = p
```

Proof method: Structural induction, finite Boolean case analysis, phase-encoding equivalence, or composition of certified rewrites; exact proof terms and direct dependencies are retained in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES fulgurite_assignment_encode_decode` and the printed proof in the machine-generated audit.

## `fulgurite_assignment_cardinality`

Source: `IndependentDuodenary/FulguriteSAT.lean`. Compilation: **passed**.

```lean
theorem fulgurite_assignment_cardinality (n : ℕ) :
    Nat.card { p : RegisterPhase n // obsidianAssignmentLaw p } = 2 ^ n
```

Proof method: Structural induction, finite Boolean case analysis, phase-encoding equivalence, or composition of certified rewrites; exact proof terms and direct dependencies are retained in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES fulgurite_assignment_cardinality` and the printed proof in the machine-generated audit.

## `fulgurite_compile_size`

Source: `IndependentDuodenary/FulguriteSAT.lean`. Compilation: **passed**.

```lean
theorem fulgurite_compile_size {n : ℕ} (f : DiscoveryFormula n) :
    fulguriteSize (discoveryCompile f) = discoverySize f
```

Proof method: Structural induction, finite Boolean case analysis, phase-encoding equivalence, or composition of certified rewrites; exact proof terms and direct dependencies are retained in the audit.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES fulgurite_compile_size` and the printed proof in the machine-generated audit.

## `fulgurite_compile_correct`

Source: `IndependentDuodenary/FulguriteSAT.lean`. Compilation: **passed**.

```lean
theorem fulgurite_compile_correct {n : ℕ} (f : DiscoveryFormula n) (a : Fin n → Bool) :
    fulguriteEval (fulguriteCompileAssignment a) (discoveryCompile f) =
      fulguriteBit (discoveryEval a f)
```

Proof method: Structural induction, finite Boolean case analysis, phase-encoding equivalence, or composition of certified rewrites; exact proof terms and direct dependencies are retained in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES fulgurite_compile_correct` and the printed proof in the machine-generated audit.

## `fulgurite_eval_preserves_law`

Source: `IndependentDuodenary/FulguriteSAT.lean`. Compilation: **passed**.

```lean
theorem fulgurite_eval_preserves_law {n : ℕ} (e : FulguriteCircuit n)
    (p : RegisterPhase n) (valid : obsidianAssignmentLaw p) :
    obsidianBitLaw (fulguriteEval p e)
```

Proof method: Structural induction, finite Boolean case analysis, phase-encoding equivalence, or composition of certified rewrites; exact proof terms and direct dependencies are retained in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES fulgurite_eval_preserves_law` and the printed proof in the machine-generated audit.

## `fulgurite_satisfiability_equivalence`

Source: `IndependentDuodenary/FulguriteSAT.lean`. Compilation: **passed**.

```lean
theorem fulgurite_satisfiability_equivalence {n : ℕ} (f : DiscoveryFormula n) :
    (∃ a : Fin n → Bool, discoveryEval a f = true) ↔
      ∃ p : RegisterPhase n, obsidianAssignmentLaw p ∧
        fulguriteEval p (discoveryCompile f) = 6
```

Proof method: Structural induction, finite Boolean case analysis, phase-encoding equivalence, or composition of certified rewrites; exact proof terms and direct dependencies are retained in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES fulgurite_satisfiability_equivalence` and the printed proof in the machine-generated audit.

## `fulgurite_register_phase_roundtrip`

Source: `IndependentDuodenary/FulguriteSAT.lean`. Compilation: **passed**.

```lean
theorem fulgurite_register_phase_roundtrip {n : ℕ} (a : Fin n → Bool) :
    registerPhases (phaseRegisterState (fulguriteCompileAssignment a)) =
      fulguriteCompileAssignment a
```

Proof method: Structural induction, finite Boolean case analysis, phase-encoding equivalence, or composition of certified rewrites; exact proof terms and direct dependencies are retained in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES fulgurite_register_phase_roundtrip` and the printed proof in the machine-generated audit.

## `fulgurite_meet_not_affine`

Source: `IndependentDuodenary/FulguriteSAT.lean`. Compilation: **passed**.

```lean
theorem fulgurite_meet_not_affine :
    ¬ ∃ A B C : ZMod 12, ∀ x y : Bool,
      A * fulguriteBit x + B * fulguriteBit y + C = fulguriteBit (x && y)
```

Proof method: Structural induction, finite Boolean case analysis, phase-encoding equivalence, or composition of certified rewrites; exact proof terms and direct dependencies are retained in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES fulgurite_meet_not_affine` and the printed proof in the machine-generated audit.

## `fulgurite_rewrite_sound`

Source: `IndependentDuodenary/FulguriteSAT.lean`. Compilation: **passed**.

```lean
theorem fulgurite_rewrite_sound {n : ℕ} {e f : FulguriteCircuit n}
    (rule : FulguriteRewrite e f) (p : RegisterPhase n)
    (valid : obsidianAssignmentLaw p) : fulguriteEval p e = fulguriteEval p f
```

Proof method: Structural induction, finite Boolean case analysis, phase-encoding equivalence, or composition of certified rewrites; exact proof terms and direct dependencies are retained in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES fulgurite_rewrite_sound` and the printed proof in the machine-generated audit.

## `fulgurite_trace_sound`

Source: `IndependentDuodenary/FulguriteSAT.lean`. Compilation: **passed**.

```lean
theorem fulgurite_trace_sound {n : ℕ} {e f : FulguriteCircuit n}
    (trace : FulguriteTrace e f) (p : RegisterPhase n)
    (valid : obsidianAssignmentLaw p) : fulguriteEval p e = fulguriteEval p f
```

Proof method: Structural induction, finite Boolean case analysis, phase-encoding equivalence, or composition of certified rewrites; exact proof terms and direct dependencies are retained in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES fulgurite_trace_sound` and the printed proof in the machine-generated audit.

## `fulgurite_trace_preserves_satisfiability`

Source: `IndependentDuodenary/FulguriteSAT.lean`. Compilation: **passed**.

```lean
theorem fulgurite_trace_preserves_satisfiability {n : ℕ} {e f : FulguriteCircuit n}
    (trace : FulguriteTrace e f) :
    (∃ p : RegisterPhase n, obsidianAssignmentLaw p ∧ fulguriteEval p e = 6) ↔
      ∃ p : RegisterPhase n, obsidianAssignmentLaw p ∧ fulguriteEval p f = 6
```

Proof method: Structural induction, finite Boolean case analysis, phase-encoding equivalence, or composition of certified rewrites; exact proof terms and direct dependencies are retained in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES fulgurite_trace_preserves_satisfiability` and the printed proof in the machine-generated audit.

## `fulgurite_trace_trans`

Source: `IndependentDuodenary/FulguriteSAT.lean`. Compilation: **passed**.

```lean
theorem fulgurite_trace_trans {n : ℕ} {e f g : FulguriteCircuit n}
    (first : FulguriteTrace e f) (second : FulguriteTrace f g) : FulguriteTrace e g
```

Proof method: Structural induction, finite Boolean case analysis, phase-encoding equivalence, or composition of certified rewrites; exact proof terms and direct dependencies are retained in the audit.

Axioms: `none`.

Dependencies: see `DIRECT DEPENDENCIES fulgurite_trace_trans` and the printed proof in the machine-generated audit.

## `fulgurite_discovery_preserves_satisfiability`

Source: `IndependentDuodenary/FulguriteSAT.lean`. Compilation: **passed**.

```lean
theorem fulgurite_discovery_preserves_satisfiability {n : ℕ}
    (fuel : ℕ) (e : FulguriteCircuit n) :
    (∃ p : RegisterPhase n, obsidianAssignmentLaw p ∧ fulguriteEval p e = 6) ↔
      ∃ p : RegisterPhase n, obsidianAssignmentLaw p ∧
        fulguriteEval p (fulguriteDiscover fuel e).val = 6
```

Proof method: Structural induction, finite Boolean case analysis, phase-encoding equivalence, or composition of certified rewrites; exact proof terms and direct dependencies are retained in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES fulgurite_discovery_preserves_satisfiability` and the printed proof in the machine-generated audit.

## `conditional_level_return`

Source: `IndependentDuodenary/MappingBoundary.lean`. Compilation: **passed**.

```lean
theorem conditional_level_return
    (levels step : ℕ) (hLevels : levels = 12) (hStep : step = 3) :
    station (step * levels) = 0
```

Proof method: Substitute the two stated hypotheses; three_times_twelve_returns.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES conditional_level_return` and the printed proof in the machine-generated audit.

## `stationMap_preserves_addition`

Source: `IndependentDuodenary/MappingBoundary.lean`. Compilation: **passed**.

```lean
theorem stationMap_preserves_addition :
    PreservesOperation Nat.add (fun x y : ZMod 12 => x + y) stationMap
```

Proof method: Unfold operation preservation and use station_add.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES stationMap_preserves_addition` and the printed proof in the machine-generated audit.

## `conditional_closure`

Source: `IndependentDuodenary/MappingBoundary.lean`. Compilation: **passed**.

```lean
theorem conditional_closure {A B : Type*}
    (sourceOp : A → A → A) (targetOp : B → B → B) (f : A → B)
    (S : Set A) (T : Set B)
    (hpres : PreservesOperation sourceOp targetOp f)
    (hclosed : ∀ x ∈ S, ∀ y ∈ S, sourceOp x y ∈ S)
    (himage : ∀ b, b ∈ T ↔ ∃ a ∈ S, f a = b) :
    ∀ x ∈ T, ∀ y ∈ T, targetOp x y ∈ T
```

Proof method: Choose source preimages, apply assumed source closure and operation preservation.

Axioms: `none`.

Dependencies: see `DIRECT DEPENDENCIES conditional_closure` and the printed proof in the machine-generated audit.

## `protocol_iterate_mod_twelve`

Source: `IndependentDuodenary/MillenniumBridge.lean`. Compilation: **passed**.

```lean
theorem protocol_iterate_mod_twelve {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (q : RegisterState r) :
    ((registerStep h)^[n]) q = ((registerStep h)^[n % 12]) q
```

Proof method: Divide the iteration count by twelve and use the established global period.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES protocol_iterate_mod_twelve` and the printed proof in the machine-generated audit.

## `protocol_orbit_candidate_bound`

Source: `IndependentDuodenary/MillenniumBridge.lean`. Compilation: **passed**.

```lean
theorem protocol_orbit_candidate_bound {r : ℕ} (h : RegisterTranslation r) (q : RegisterState r) :
    (protocolOrbitCandidates h q).card ≤ 12
```

Proof method: The cardinality of a finite image is at most its twelve-element domain.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES protocol_orbit_candidate_bound` and the printed proof in the machine-generated audit.

## `protocol_orbit_candidates_complete`

Source: `IndependentDuodenary/MillenniumBridge.lean`. Compilation: **passed**.

```lean
theorem protocol_orbit_candidates_complete {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (q : RegisterState r) : ((registerStep h)^[n]) q ∈ protocolOrbitCandidates h q
```

Proof method: Reduce the exponent modulo twelve and supply its Fin 12 witness.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES protocol_orbit_candidates_complete` and the printed proof in the machine-generated audit.

## `protocol_reachability_iff_bounded_search`

Source: `IndependentDuodenary/MillenniumBridge.lean`. Compilation: **passed**.

```lean
theorem protocol_reachability_iff_bounded_search {r : ℕ} (h : RegisterTranslation r)
    (q x : RegisterState r) :
    (∃ n : ℕ, ((registerStep h)^[n]) q = x) ↔
      ∃ k : Fin 12, ((registerStep h)^[k.val]) q = x
```

Proof method: Reduce an arbitrary iterate modulo twelve for the forward implication; use the finite witness value for the reverse implication.

Axioms: `propext,
 Classical.choice,
 Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES protocol_reachability_iff_bounded_search` and the printed proof in the machine-generated audit.

## `complete_key_cardinality`

Source: `IndependentDuodenary/MillenniumBridge.lean`. Compilation: **passed**.

```lean
theorem complete_key_cardinality : Nat.card RepresentedKey = 49152
```

Proof method: Explicit coefficient equivalence and finite product/function cardinalities.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES complete_key_cardinality` and the printed proof in the machine-generated audit.

## `complete_register_cardinality`

Source: `IndependentDuodenary/MillenniumBridge.lean`. Compilation: **passed**.

```lean
theorem complete_register_cardinality (r : ℕ) : Nat.card (RegisterState r) = 49152 ^ r
```

Proof method: Function-space cardinality and the proved full key cardinality.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES complete_register_cardinality` and the printed proof in the machine-generated audit.

## `majority_symbol_budget_linear`

Source: `IndependentDuodenary/MillenniumBridge.lean`. Compilation: **passed**.

```lean
theorem majority_symbol_budget_linear (r : ℕ) : majoritySymbolBudget r = 3 * (17 * r)
```

Proof method: Natural arithmetic on the defined symbol-position budget.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES majority_symbol_budget_linear` and the printed proof in the machine-generated audit.

## `protected_frame_width`

Source: `IndependentDuodenary/MillenniumBridge.lean`. Compilation: **passed**.

```lean
theorem protected_frame_width {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (ops : List StationExpr) (x : CanonicalSubstrate r) (i : Fin r) :
    (pipelineTransmit h n ops x i).length = 17
```

Proof method: Compilation equality and the established canonical transmitted length.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES protected_frame_width` and the printed proof in the machine-generated audit.

## `twelve_returns`

Source: `IndependentDuodenary/ModularCore.lean`. Compilation: **passed**.

```lean
theorem twelve_returns : station 12 = 0
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES twelve_returns` and the printed proof in the machine-generated audit.

## `predecessor_is_nonzero`

Source: `IndependentDuodenary/ModularCore.lean`. Compilation: **passed**.

```lean
theorem predecessor_is_nonzero : station 11 ≠ 0
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES predecessor_is_nonzero` and the printed proof in the machine-generated audit.

## `predecessor_successor_returns`

Source: `IndependentDuodenary/ModularCore.lean`. Compilation: **passed**.

```lean
theorem predecessor_successor_returns : station (11 + 1) = 0
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES predecessor_successor_returns` and the printed proof in the machine-generated audit.

## `three_times_twelve_returns`

Source: `IndependentDuodenary/ModularCore.lean`. Compilation: **passed**.

```lean
theorem three_times_twelve_returns : station (3 * 12) = 0
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES three_times_twelve_returns` and the printed proof in the machine-generated audit.

## `twelve_squared_returns`

Source: `IndependentDuodenary/ModularCore.lean`. Compilation: **passed**.

```lean
theorem twelve_squared_returns : superstation (12 * 12) = 0
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES twelve_squared_returns` and the printed proof in the machine-generated audit.

## `twelve_nonzero_mod_144`

Source: `IndependentDuodenary/ModularCore.lean`. Compilation: **passed**.

```lean
theorem twelve_nonzero_mod_144 : superstation 12 ≠ 0
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES twelve_nonzero_mod_144` and the printed proof in the machine-generated audit.

## `number_372_multiple`

Source: `IndependentDuodenary/ModularCore.lean`. Compilation: **passed**.

```lean
theorem number_372_multiple : 372 = 12 * 31
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `none`.

Dependencies: see `DIRECT DEPENDENCIES number_372_multiple` and the printed proof in the machine-generated audit.

## `number_719_predecessor`

Source: `IndependentDuodenary/ModularCore.lean`. Compilation: **passed**.

```lean
theorem number_719_predecessor : station 719 = 11
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES number_719_predecessor` and the printed proof in the machine-generated audit.

## `number_10800_multiple`

Source: `IndependentDuodenary/ModularCore.lean`. Compilation: **passed**.

```lean
theorem number_10800_multiple : superstation 10800 = 0
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES number_10800_multiple` and the printed proof in the machine-generated audit.

## `station_add`

Source: `IndependentDuodenary/ModularCore.lean`. Compilation: **passed**.

```lean
theorem station_add (m n : ℕ) : station (m + n) = station m + station n
```

Proof method: Natural-number cast addition law.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES station_add` and the printed proof in the machine-generated audit.

## `superstation_add`

Source: `IndependentDuodenary/ModularCore.lean`. Compilation: **passed**.

```lean
theorem superstation_add (m n : ℕ) : superstation (m + n) = superstation m + superstation n
```

Proof method: Natural-number cast addition law.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES superstation_add` and the printed proof in the machine-generated audit.

## `predecessor_add_one`

Source: `IndependentDuodenary/ModularCore.lean`. Compilation: **passed**.

```lean
theorem predecessor_add_one : (11 : ZMod 12) + 1 = 0
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES predecessor_add_one` and the printed proof in the machine-generated audit.

## `predecessor_eq_neg_one`

Source: `IndependentDuodenary/ModularCore.lean`. Compilation: **passed**.

```lean
theorem predecessor_eq_neg_one : (11 : ZMod 12) = -1
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES predecessor_eq_neg_one` and the printed proof in the machine-generated audit.

## `station_add_closed`

Source: `IndependentDuodenary/ModularCore.lean`. Compilation: **passed**.

```lean
theorem station_add_closed (m n : ℕ) :
    ∃ k : ℕ, station m + station n = station k
```

Proof method: Witness m+n using station_add.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES station_add_closed` and the printed proof in the machine-generated audit.

## `superstation_add_closed`

Source: `IndependentDuodenary/ModularCore.lean`. Compilation: **passed**.

```lean
theorem superstation_add_closed (m n : ℕ) :
    ∃ k : ℕ, superstation m + superstation n = superstation k
```

Proof method: Witness m+n using superstation_add.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES superstation_add_closed` and the printed proof in the machine-generated audit.

## `zero_divisors_mod_twelve`

Source: `IndependentDuodenary/ModularCore.lean`. Compilation: **passed**.

```lean
theorem zero_divisors_mod_twelve :
    (3 : ZMod 12) ≠ 0 ∧ (4 : ZMod 12) ≠ 0 ∧ (3 : ZMod 12) * 4 = 0
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES zero_divisors_mod_twelve` and the printed proof in the machine-generated audit.

## `zero_divisor_mod_144`

Source: `IndependentDuodenary/ModularCore.lean`. Compilation: **passed**.

```lean
theorem zero_divisor_mod_144 :
    (12 : ZMod 144) ≠ 0 ∧ (12 : ZMod 144) * 12 = 0
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES zero_divisor_mod_144` and the printed proof in the machine-generated audit.

## `station_word_action_composition`

Source: `IndependentDuodenary/PipelineSynthesis.lean`. Compilation: **passed**.

```lean
theorem station_word_action_composition (outer inner : StationExpr) {r : ℕ}
    (words : RegisterWords r) :
    stationWordAction (.compose outer inner) words =
      stationWordAction outer (stationWordAction inner words)
```

Proof method: Kernel-checked tactic proof using funext, simp. Exact terms and dependencies are in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES station_word_action_composition` and the printed proof in the machine-generated audit.

## `station_program_compilation`

Source: `IndependentDuodenary/PipelineSynthesis.lean`. Compilation: **passed**.

```lean
theorem station_program_compilation (ops : List StationExpr) {r : ℕ} (words : RegisterWords r) :
    runStationProgram ops words = stationWordAction (compileStationProgram ops) words
```

Proof method: Kernel-checked tactic proof using induction, funext, rw, simp. Exact terms and dependencies are in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES station_program_compilation` and the printed proof in the machine-generated audit.

## `pipeline_master_composition`

Source: `IndependentDuodenary/PipelineSynthesis.lean`. Compilation: **passed**.

```lean
theorem pipeline_master_composition {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (ops : List StationExpr) (x : CanonicalSubstrate r) (received : ProtectedRegisterWords r)
    (hnoise : RegisterNoiseBound (pipelineTransmit h n ops x) received) :
    recoverCanonicalInitial h n (compileStationProgram ops) received = some x
```

Proof method: Kernel-checked tactic proof using simpa, apply. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES pipeline_master_composition` and the printed proof in the machine-generated audit.

## `pipeline_noiseless_closure`

Source: `IndependentDuodenary/PipelineSynthesis.lean`. Compilation: **passed**.

```lean
theorem pipeline_noiseless_closure {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (ops : List StationExpr) (x : CanonicalSubstrate r) :
    recoverCanonicalInitial h n (compileStationProgram ops)
      (protectRegisterWords (pipelineTransmit h n ops x)) = some x
```

Proof method: Direct proof term applying the named previously checked declarations; see the printed proof and dependencies.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES pipeline_noiseless_closure` and the printed proof in the machine-generated audit.

## `pipeline_successor_channel_closure`

Source: `IndependentDuodenary/PipelineSynthesis.lean`. Compilation: **passed**.

```lean
theorem pipeline_successor_channel_closure {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (ops : List StationExpr) (x : CanonicalSubstrate r) :
    recoverCanonicalInitial h n (compileStationProgram ops)
      (successorCorruption (pipelineTransmit h n ops x)) = some x
```

Proof method: Direct proof term applying the named previously checked declarations; see the printed proof and dependencies.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES pipeline_successor_channel_closure` and the printed proof in the machine-generated audit.

## `pipeline_transmission_injective`

Source: `IndependentDuodenary/PipelineSynthesis.lean`. Compilation: **passed**.

```lean
theorem pipeline_transmission_injective {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (ops : List StationExpr) : Function.Injective (pipelineTransmit h n ops)
```

Proof method: Kernel-checked tactic proof using rw, exact, intro. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES pipeline_transmission_injective` and the printed proof in the machine-generated audit.

## `pipeline_recovered_state_unique`

Source: `IndependentDuodenary/PipelineSynthesis.lean`. Compilation: **passed**.

```lean
theorem pipeline_recovered_state_unique {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (ops : List StationExpr) (x y : CanonicalSubstrate r) (received : ProtectedRegisterWords r)
    (hnoise : RegisterNoiseBound (pipelineTransmit h n ops x) received)
    (hrecovered : recoverCanonicalInitial h n (compileStationProgram ops) received = some y) : y = x
```

Proof method: Kernel-checked tactic proof using rw, exact. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES pipeline_recovered_state_unique` and the printed proof in the machine-generated audit.

## `pipeline_empty_transmission_rejected`

Source: `IndependentDuodenary/PipelineSynthesis.lean`. Compilation: **passed**.

```lean
theorem pipeline_empty_transmission_rejected (h : RegisterTranslation 1) (n : ℕ)
    (ops : List StationExpr) :
    recoverCanonicalInitial h n (compileStationProgram ops) (fun _ => []) = none
```

Proof method: Definitional equality.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES pipeline_empty_transmission_rejected` and the printed proof in the machine-generated audit.

## `reference_accept_reject_distinct`

Source: `IndependentDuodenary/ReferenceMachines.lean`. Compilation: **passed**.

```lean
theorem reference_accept_reject_distinct {s : ℕ} : (0 : Fin (s + 2)) ≠ 1
```

Proof method: Unfold the explicit reference-machine semantics and use finite-state arithmetic, transition equality, or run extension; the exact elaborated proof term and dependencies are retained in the audit.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES reference_accept_reject_distinct` and the printed proof in the machine-generated audit.

## `reference_initial_heads`

Source: `IndependentDuodenary/ReferenceMachines.lean`. Compilation: **passed**.

```lean
theorem reference_initial_heads {a s k : ℕ} (state : Fin (s + 2))
    (x : PrizeBinaryWord) (i : Fin (k + 1)) :
    (referenceInitial (a
```

Proof method: Unfold the explicit reference-machine semantics and use finite-state arithmetic, transition equality, or run extension; the exact elaborated proof term and dependencies are retained in the audit.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES reference_initial_heads` and the printed proof in the machine-generated audit.

## `reference_initial_negative_blank`

Source: `IndependentDuodenary/ReferenceMachines.lean`. Compilation: **passed**.

```lean
theorem reference_initial_negative_blank {a s k : ℕ} (state : Fin (s + 2))
    (x : PrizeBinaryWord) (i : Fin (k + 1)) (j : ℤ) (hj : j < 0) :
    (referenceInitial (a
```

Proof method: Unfold the explicit reference-machine semantics and use finite-state arithmetic, transition equality, or run extension; the exact elaborated proof term and dependencies are retained in the audit.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES reference_initial_negative_blank` and the printed proof in the machine-generated audit.

## `reference_initial_other_tape_blank`

Source: `IndependentDuodenary/ReferenceMachines.lean`. Compilation: **passed**.

```lean
theorem reference_initial_other_tape_blank {a s k : ℕ} (state : Fin (s + 2))
    (x : PrizeBinaryWord) (i : Fin (k + 1)) (hi : i ≠ 0) (j : ℤ) :
    (referenceInitial (a
```

Proof method: Unfold the explicit reference-machine semantics and use finite-state arithmetic, transition equality, or run extension; the exact elaborated proof term and dependencies are retained in the audit.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES reference_initial_other_tape_blank` and the printed proof in the machine-generated audit.

## `reference_initial_empty_blank`

Source: `IndependentDuodenary/ReferenceMachines.lean`. Compilation: **passed**.

```lean
theorem reference_initial_empty_blank {a s k : ℕ} (state : Fin (s + 2))
    (i : Fin (k + 1)) (j : ℤ) :
    (referenceInitial (a
```

Proof method: Unfold the explicit reference-machine semantics and use finite-state arithmetic, transition equality, or run extension; the exact elaborated proof term and dependencies are retained in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES reference_initial_empty_blank` and the printed proof in the machine-generated audit.

## `reference_write_at_head`

Source: `IndependentDuodenary/ReferenceMachines.lean`. Compilation: **passed**.

```lean
theorem reference_write_at_head {a s k : ℕ} (q : ReferenceConfiguration a s k)
    (instruction : ReferenceInstruction a s k) (i : Fin (k + 1)) :
    (referenceApply q instruction).tape i (q.head i) = instruction.write i
```

Proof method: Unfold the explicit reference-machine semantics and use finite-state arithmetic, transition equality, or run extension; the exact elaborated proof term and dependencies are retained in the audit.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES reference_write_at_head` and the printed proof in the machine-generated audit.

## `reference_write_other_cell`

Source: `IndependentDuodenary/ReferenceMachines.lean`. Compilation: **passed**.

```lean
theorem reference_write_other_cell {a s k : ℕ} (q : ReferenceConfiguration a s k)
    (instruction : ReferenceInstruction a s k) (i : Fin (k + 1)) (j : ℤ)
    (hj : j ≠ q.head i) :
    (referenceApply q instruction).tape i j = q.tape i j
```

Proof method: Unfold the explicit reference-machine semantics and use finite-state arithmetic, transition equality, or run extension; the exact elaborated proof term and dependencies are retained in the audit.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES reference_write_other_cell` and the printed proof in the machine-generated audit.

## `reference_dstep_none_iff`

Source: `IndependentDuodenary/ReferenceMachines.lean`. Compilation: **passed**.

```lean
theorem reference_dstep_none_iff {a s k : ℕ} (M : ReferenceDeterministicMachine a s k)
    (q : ReferenceConfiguration a s k) : referenceDStep M q = none ↔ referenceTerminal q
```

Proof method: Unfold the explicit reference-machine semantics and use finite-state arithmetic, transition equality, or run extension; the exact elaborated proof term and dependencies are retained in the audit.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES reference_dstep_none_iff` and the printed proof in the machine-generated audit.

## `reference_deterministic_transition`

Source: `IndependentDuodenary/ReferenceMachines.lean`. Compilation: **passed**.

```lean
theorem reference_deterministic_transition {a s k : ℕ}
    (M : ReferenceDeterministicMachine a s k) (q q₁ q₂ : ReferenceConfiguration a s k)
    (h₁ : referenceDEdge M q q₁) (h₂ : referenceDEdge M q q₂) : q₁ = q₂
```

Proof method: Unfold the explicit reference-machine semantics and use finite-state arithmetic, transition equality, or run extension; the exact elaborated proof term and dependencies are retained in the audit.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES reference_deterministic_transition` and the printed proof in the machine-generated audit.

## `reference_nondeterministic_finite_branching`

Source: `IndependentDuodenary/ReferenceMachines.lean`. Compilation: **passed**.

```lean
theorem reference_nondeterministic_finite_branching {a s k : ℕ}
    (M : ReferenceNondeterministicMachine a s k) (q : ReferenceConfiguration a s k) :
    ∃ successors : List (ReferenceConfiguration a s k),
      ∀ q', referenceNEdge M q q' ↔ q' ∈ successors
```

Proof method: Unfold the explicit reference-machine semantics and use finite-state arithmetic, transition equality, or run extension; the exact elaborated proof term and dependencies are retained in the audit.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES reference_nondeterministic_finite_branching` and the printed proof in the machine-generated audit.

## `reference_terminal_no_nstep`

Source: `IndependentDuodenary/ReferenceMachines.lean`. Compilation: **passed**.

```lean
theorem reference_terminal_no_nstep {a s k : ℕ}
    (M : ReferenceNondeterministicMachine a s k) (q q' : ReferenceConfiguration a s k)
    (halt : referenceTerminal q) : ¬ referenceNEdge M q q'
```

Proof method: Unfold the explicit reference-machine semantics and use finite-state arithmetic, transition equality, or run extension; the exact elaborated proof term and dependencies are retained in the audit.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES reference_terminal_no_nstep` and the printed proof in the machine-generated audit.

## `reference_nonterminal_has_nstep`

Source: `IndependentDuodenary/ReferenceMachines.lean`. Compilation: **passed**.

```lean
theorem reference_nonterminal_has_nstep {a s k : ℕ}
    (M : ReferenceNondeterministicMachine a s k) (q : ReferenceConfiguration a s k)
    (halt : ¬ referenceTerminal q) : ∃ q', referenceNEdge M q q'
```

Proof method: Unfold the explicit reference-machine semantics and use finite-state arithmetic, transition equality, or run extension; the exact elaborated proof term and dependencies are retained in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES reference_nonterminal_has_nstep` and the printed proof in the machine-generated audit.

## `reference_nbranch_bound_forces_terminal`

Source: `IndependentDuodenary/ReferenceMachines.lean`. Compilation: **passed**.

```lean
theorem reference_nbranch_bound_forces_terminal {a s k : ℕ}
    (M : ReferenceNondeterministicMachine a s k) (initial : ReferenceConfiguration a s k)
    (bound : ℕ)
    (bounded : ∀ t q, ReferenceRun (referenceNEdge M) t initial q → t ≤ bound)
    (q : ReferenceConfiguration a s k)
    (run : ReferenceRun (referenceNEdge M) bound initial q) : referenceTerminal q
```

Proof method: Unfold the explicit reference-machine semantics and use finite-state arithmetic, transition equality, or run extension; the exact elaborated proof term and dependencies are retained in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES reference_nbranch_bound_forces_terminal` and the printed proof in the machine-generated audit.

## `register_decode_encode`

Source: `IndependentDuodenary/RegisterBridge.lean`. Compilation: **passed**.

```lean
theorem register_decode_encode (r : ℕ) (q : RegisterState r) :
    decodeRegisterWords r (encodeRegisterState q) = some q
```

Proof method: Kernel-checked tactic proof using induction, rw, simp, simpa, change. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_decode_encode` and the printed proof in the machine-generated audit.

## `register_parse_sound`

Source: `IndependentDuodenary/RegisterBridge.lean`. Compilation: **passed**.

```lean
theorem register_parse_sound (r : ℕ) (words : RegisterWords r) (q : RegisterState r)
    (h : decodeRegisterWords r words = some q) : words = encodeRegisterState q
```

Proof method: Kernel-checked tactic proof using induction, cases, funext, simp, simpa, refine, exact. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_parse_sound` and the printed proof in the machine-generated audit.

## `register_encoding_injective`

Source: `IndependentDuodenary/RegisterBridge.lean`. Compilation: **passed**.

```lean
theorem register_encoding_injective {r : ℕ} : Function.Injective (@encodeRegisterState r)
```

Proof method: Kernel-checked tactic proof using simpa, intro. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_encoding_injective` and the printed proof in the machine-generated audit.

## `register_reject_malformed`

Source: `IndependentDuodenary/RegisterBridge.lean`. Compilation: **passed**.

```lean
theorem register_reject_malformed {r : ℕ} (words : RegisterWords r)
    (h : ∀ q : RegisterState r, words ≠ encodeRegisterState q) : decodeRegisterWords r words = none
```

Proof method: Kernel-checked tactic proof using cases, exact. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_reject_malformed` and the printed proof in the machine-generated audit.

## `register_encoding_projection`

Source: `IndependentDuodenary/RegisterBridge.lean`. Compilation: **passed**.

```lean
theorem register_encoding_projection {r s : ℕ} (select : Fin s → Fin r) (q : RegisterState r) :
    projectRegisterWords select (encodeRegisterState q) =
      encodeRegisterState (projectRegisters select q)
```

Proof method: Definitional equality.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_encoding_projection` and the printed proof in the machine-generated audit.

## `register_transport_encode`

Source: `IndependentDuodenary/RegisterBridge.lean`. Compilation: **passed**.

```lean
theorem register_transport_encode {r : ℕ} (A : RegisterState r → RegisterState r)
    (q : RegisterState r) :
    transportRegisterWords A (encodeRegisterState q) = encodeRegisterState (A q)
```

Proof method: Kernel-checked tactic proof using simp. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_transport_encode` and the printed proof in the machine-generated audit.

## `register_transport_iterate`

Source: `IndependentDuodenary/RegisterBridge.lean`. Compilation: **passed**.

```lean
theorem register_transport_iterate {r : ℕ} (A : RegisterState r → RegisterState r)
    (n : ℕ) (q : RegisterState r) :
    ((transportRegisterWords A)^[n]) (encodeRegisterState q) = encodeRegisterState ((A^[n]) q)
```

Proof method: Kernel-checked tactic proof using induction, rw. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_transport_iterate` and the printed proof in the machine-generated audit.

## `register_decoded_transport_iterate`

Source: `IndependentDuodenary/RegisterBridge.lean`. Compilation: **passed**.

```lean
theorem register_decoded_transport_iterate {r : ℕ} (A : RegisterState r → RegisterState r)
    (n : ℕ) (q : RegisterState r) :
    decodeRegisterWords r (((transportRegisterWords A)^[n]) (encodeRegisterState q)) =
      some ((A^[n]) q)
```

Proof method: Kernel-checked tactic proof using rw. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_decoded_transport_iterate` and the printed proof in the machine-generated audit.

## `register_transport_reflects_equality`

Source: `IndependentDuodenary/RegisterBridge.lean`. Compilation: **passed**.

```lean
theorem register_transport_reflects_equality {r : ℕ}
    (A B : RegisterState r → RegisterState r) (n m : ℕ) (q p : RegisterState r) :
    ((transportRegisterWords A)^[n]) (encodeRegisterState q) =
      ((transportRegisterWords B)^[m]) (encodeRegisterState p) ↔ (A^[n]) q = (B^[m]) p
```

Proof method: Kernel-checked tactic proof using rw, exact. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_transport_reflects_equality` and the printed proof in the machine-generated audit.

## `decoded_register_property_encode`

Source: `IndependentDuodenary/RegisterBridge.lean`. Compilation: **passed**.

```lean
theorem decoded_register_property_encode {r : ℕ} (P : RegisterState r → Prop)
    (q : RegisterState r) : DecodedRegisterProperty P (encodeRegisterState q) ↔ P q
```

Proof method: Kernel-checked tactic proof using simp. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES decoded_register_property_encode` and the printed proof in the machine-generated audit.

## `register_inductive_invariant_transport`

Source: `IndependentDuodenary/RegisterBridge.lean`. Compilation: **passed**.

```lean
theorem register_inductive_invariant_transport {r : ℕ}
    (A : RegisterState r → RegisterState r) (P : RegisterState r → Prop)
    (hstep : ∀ q, P q → P (A q)) (n : ℕ) (q : RegisterState r) (hq : P q) :
    DecodedRegisterProperty P (((transportRegisterWords A)^[n]) (encodeRegisterState q))
```

Proof method: Kernel-checked tactic proof using induction, rw, exact. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_inductive_invariant_transport` and the printed proof in the machine-generated audit.

## `external_relative_equivalence_offset`

Source: `IndependentDuodenary/RegisterBridge.lean`. Compilation: **passed**.

```lean
theorem external_relative_equivalence_offset {r : ℕ} (base : Fin r) (a b : RegisterPhase r) :
    ExternalRelativeEquivalent a b ↔ ∃ c : ZMod 12, ∀ i, b i = a i + c
```

Proof method: Direct proof term applying the named previously checked declarations; see the printed proof and dependencies.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES external_relative_equivalence_offset` and the printed proof in the machine-generated audit.

## `external_relative_equivalence_step`

Source: `IndependentDuodenary/RegisterBridge.lean`. Compilation: **passed**.

```lean
theorem external_relative_equivalence_step {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (q : RegisterState r) (hq : PhaseRegular q) :
    ExternalRelativeEquivalent (registerPhases q) (registerPhases (((registerStep h)^[n]) q))
```

Proof method: Direct proof term applying the named previously checked declarations; see the printed proof and dependencies.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES external_relative_equivalence_step` and the printed proof in the machine-generated audit.

## `register_word_modular_bridge`

Source: `IndependentDuodenary/RegisterBridge.lean`. Compilation: **passed**.

```lean
theorem register_word_modular_bridge {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (q : RegisterState r) (hq : PhaseRegular q) :
    DecodedRegisterProperty (fun p => PhaseRegular p ∧
      ExternalRelativeEquivalent (registerPhases q) (registerPhases p))
      (((transportRegisterWords (registerStep h))^[n]) (encodeRegisterState q))
```

Proof method: Kernel-checked tactic proof using rw, exact. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_word_modular_bridge` and the printed proof in the machine-generated audit.

## `register_word_metadata_bridge`

Source: `IndependentDuodenary/RegisterBridge.lean`. Compilation: **passed**.

```lean
theorem register_word_metadata_bridge {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (q : RegisterState r) :
    DecodedRegisterProperty (fun p => ∀ i, (p i).metadata = (q i).metadata)
      (((transportRegisterWords (registerStep h))^[n]) (encodeRegisterState q))
```

Proof method: Kernel-checked tactic proof using rw, exact. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_word_metadata_bridge` and the printed proof in the machine-generated audit.

## `register_word_modular_bridge_phase`

Source: `IndependentDuodenary/RegisterBridge.lean`. Compilation: **passed**.

```lean
theorem register_word_modular_bridge_phase {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (a : RegisterPhase r) :
    DecodedRegisterProperty (fun p => PhaseRegular p ∧
      ExternalRelativeEquivalent a (registerPhases p))
      (((transportRegisterWords (registerStep h))^[n]) (encodeRegisterState (phaseRegisterState a)))
```

Proof method: Kernel-checked tactic proof using simpa. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_word_modular_bridge_phase` and the printed proof in the machine-generated audit.

## `register_word_projection_bridge`

Source: `IndependentDuodenary/RegisterBridge.lean`. Compilation: **passed**.

```lean
theorem register_word_projection_bridge {r s : ℕ} (select : Fin s → Fin r)
    (h : RegisterTranslation r) (n : ℕ) (q : RegisterState r) :
    projectRegisterWords select
      (((transportRegisterWords (registerStep h))^[n]) (encodeRegisterState q)) =
    (((transportRegisterWords (registerStep (fun i => h (select i))))^[n])
      (encodeRegisterState (projectRegisters select q)))
```

Proof method: Kernel-checked tactic proof using rw. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_word_projection_bridge` and the printed proof in the machine-generated audit.

## `register_word_regular_orbit_injective`

Source: `IndependentDuodenary/RegisterBridge.lean`. Compilation: **passed**.

```lean
theorem register_word_regular_orbit_injective {r : ℕ} (base : Fin r)
    (h : RegisterTranslation r) (q : RegisterState r) (hq : PhaseRegular q) :
    Function.Injective (fun n : Fin 12 =>
      ((transportRegisterWords (registerStep h))^[n.val]) (encodeRegisterState q))
```

Proof method: Kernel-checked tactic proof using rw, exact, change, intro. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_word_regular_orbit_injective` and the printed proof in the machine-generated audit.

## `external_relative_equivalence_not_lossless`

Source: `IndependentDuodenary/RegisterBridge.lean`. Compilation: **passed**.

```lean
theorem external_relative_equivalence_not_lossless :
    ∃ q p : RegisterState 1, ExternalRelativeEquivalent (registerPhases q) (registerPhases p) ∧
      encodeRegisterState q ≠ encodeRegisterState p
```

Proof method: Kernel-checked tactic proof using rw, refine, exact, change, intro. Exact terms and dependencies are in the audit.

Axioms: `propext,
 Classical.choice,
 Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES external_relative_equivalence_not_lossless` and the printed proof in the machine-generated audit.

## `register_cycle_projection`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_cycle_projection {r s : ℕ} (select : Fin s → Fin r) (q : RegisterState r) :
    projectRegisters select (registerCycle q) = registerCycle (projectRegisters select q)
```

Proof method: Compatibility corollary of pointwiseNaturalMap.naturality.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_cycle_projection` and the printed proof in the machine-generated audit.

## `register_translate_projection`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_translate_projection {r s : ℕ} (select : Fin s → Fin r)
    (h : RegisterTranslation r) (q : RegisterState r) :
    projectRegisters select (registerTranslate h q) =
      registerTranslate (fun i => h (select i)) (projectRegisters select q)
```

Proof method: Compatibility corollary of pointwiseBinaryNaturalMap.naturality.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_translate_projection` and the printed proof in the machine-generated audit.

## `register_step_projection`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_step_projection {r s : ℕ} (select : Fin s → Fin r)
    (h : RegisterTranslation r) (q : RegisterState r) :
    projectRegisters select (registerStep h q) =
      registerStep (fun i => h (select i)) (projectRegisters select q)
```

Proof method: Compatibility corollary of pointwiseBinaryNaturalMap.naturality.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_step_projection` and the printed proof in the machine-generated audit.

## `register_step_projection_iterate`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_step_projection_iterate {r s : ℕ} (select : Fin s → Fin r)
    (h : RegisterTranslation r) (n : ℕ) (q : RegisterState r) :
    projectRegisters select (((registerStep h)^[n]) q) =
      (((registerStep (fun i => h (select i)))^[n]) (projectRegisters select q))
```

Proof method: Instantiate the common register_natural_parameter_iterate theorem.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_step_projection_iterate` and the printed proof in the machine-generated audit.

## `register_relative_projection`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_relative_projection {r s : ℕ} (select : Fin s → Fin r)
    (q : RegisterState r) (i j : Fin s) :
    relativePhases (registerPhases (projectRegisters select q)) i j =
      relativePhases (registerPhases q) (select i) (select j)
```

Proof method: Definitional equality.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_relative_projection` and the printed proof in the machine-generated audit.

## `register_cycle_commutes_translation`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_cycle_commutes_translation {r : ℕ} (h : RegisterTranslation r)
    (q : RegisterState r) :
    registerCycle (registerTranslate h q) = registerTranslate h (registerCycle q)
```

Proof method: Kernel-checked tactic proof using funext, exact. Exact terms and dependencies are in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_cycle_commutes_translation` and the printed proof in the machine-generated audit.

## `register_translation_vertex_invariant`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_translation_vertex_invariant {r : ℕ} (h : RegisterTranslation r)
    (q : RegisterState r) (i : Fin r) :
    keyVertex (registerTranslate h q i) = keyVertex (q i)
```

Proof method: Definitional equality.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_translation_vertex_invariant` and the printed proof in the machine-generated audit.

## `register_translation_phase_invariant`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_translation_phase_invariant {r : ℕ} (h : RegisterTranslation r)
    (q : RegisterState r) : registerPhases (registerTranslate h q) = registerPhases q
```

Proof method: Definitional equality.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_translation_phase_invariant` and the printed proof in the machine-generated audit.

## `register_cycle_iterate`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_cycle_iterate {r : ℕ} (n : ℕ) (q : RegisterState r) (i : Fin r) :
    ((registerCycle^[n]) q) i = (keyCoordinateCycle^[n]) (q i)
```

Proof method: Kernel-checked tactic proof using induction, rw, exact. Exact terms and dependencies are in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_cycle_iterate` and the printed proof in the machine-generated audit.

## `register_cycle_period_iff`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_cycle_period_iff {r : ℕ} (hr : 0 < r) (n : ℕ) :
    (∀ q : RegisterState r, (registerCycle^[n]) q = q) ↔ 12 ∣ n
```

Proof method: Kernel-checked tactic proof using funext, rw, simpa, exact, apply, intro. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_cycle_period_iff` and the printed proof in the machine-generated audit.

## `register_empty_cycle_period`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_empty_cycle_period (n : ℕ) (q : RegisterState 0) :
    (registerCycle^[n]) q = q
```

Proof method: Direct proof term applying the named previously checked declarations; see the printed proof and dependencies.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_empty_cycle_period` and the printed proof in the machine-generated audit.

## `key_phase_from_one_hot`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem key_phase_from_one_hot (q : RepresentedKey) (a : ZMod 12)
    (ha : q.complementIntercept = keyOneHot a) : keyPhaseLabel (keyVertex q) = a
```

Proof method: Kernel-checked tactic proof using rw, exact, change. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES key_phase_from_one_hot` and the printed proof in the machine-generated audit.

## `key_cycle_one_hot`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem key_cycle_one_hot (q : RepresentedKey) (a : ZMod 12)
    (ha : q.complementIntercept = keyOneHot a) :
    (keyCoordinateCycle q).complementIntercept = keyOneHot (a + 1)
```

Proof method: Kernel-checked tactic proof using funext, simp. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES key_cycle_one_hot` and the printed proof in the machine-generated audit.

## `phase_register_regular`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem phase_register_regular {r : ℕ} (a : RegisterPhase r) : PhaseRegular (phaseRegisterState a)
```

Proof method: Direct proof term applying the named previously checked declarations; see the printed proof and dependencies.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES phase_register_regular` and the printed proof in the machine-generated audit.

## `phase_register_label`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem phase_register_label {r : ℕ} (a : RegisterPhase r) :
    registerPhases (phaseRegisterState a) = a
```

Proof method: Kernel-checked tactic proof using funext, exact. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES phase_register_label` and the printed proof in the machine-generated audit.

## `register_regular_cycle`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_regular_cycle {r : ℕ} (q : RegisterState r) (hq : PhaseRegular q) :
    PhaseRegular (registerCycle q)
```

Proof method: Kernel-checked tactic proof using exact, intro, obtain. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_regular_cycle` and the printed proof in the machine-generated audit.

## `register_regular_translation`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_regular_translation {r : ℕ} (h : RegisterTranslation r)
    (q : RegisterState r) (hq : PhaseRegular q) : PhaseRegular (registerTranslate h q)
```

Proof method: Direct proof term applying the named previously checked declarations; see the printed proof and dependencies.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_regular_translation` and the printed proof in the machine-generated audit.

## `register_regular_step`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_regular_step {r : ℕ} (h : RegisterTranslation r)
    (q : RegisterState r) (hq : PhaseRegular q) : PhaseRegular (registerStep h q)
```

Proof method: Direct proof term applying the named previously checked declarations; see the printed proof and dependencies.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_regular_step` and the printed proof in the machine-generated audit.

## `register_regular_projection`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_regular_projection {r s : ℕ} (select : Fin s → Fin r)
    (q : RegisterState r) (hq : PhaseRegular q) : PhaseRegular (projectRegisters select q)
```

Proof method: Direct proof term applying the named previously checked declarations; see the printed proof and dependencies.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_regular_projection` and the printed proof in the machine-generated audit.

## `register_cycle_phase`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_cycle_phase {r : ℕ} (q : RegisterState r) (hq : PhaseRegular q) :
    registerPhases (registerCycle q) = phaseAdvance (registerPhases q)
```

Proof method: Kernel-checked tactic proof using funext, rw, change, obtain. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_cycle_phase` and the printed proof in the machine-generated audit.

## `register_step_phase`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_step_phase {r : ℕ} (h : RegisterTranslation r)
    (q : RegisterState r) (hq : PhaseRegular q) :
    registerPhases (registerStep h q) = phaseAdvance (registerPhases q)
```

Proof method: Kernel-checked tactic proof using exact. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_step_phase` and the printed proof in the machine-generated audit.

## `register_step_regular_iterate`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_step_regular_iterate {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (q : RegisterState r) (hq : PhaseRegular q) : PhaseRegular (((registerStep h)^[n]) q)
```

Proof method: Kernel-checked tactic proof using induction, rw, exact. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_step_regular_iterate` and the printed proof in the machine-generated audit.

## `register_step_phase_iterate`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_step_phase_iterate {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (q : RegisterState r) (hq : PhaseRegular q) :
    registerPhases (((registerStep h)^[n]) q) = fun i => registerPhases q i + (n : ZMod 12)
```

Proof method: Kernel-checked tactic proof using induction, funext, rw, simp. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_step_phase_iterate` and the printed proof in the machine-generated audit.

## `register_step_relative_invariant`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_step_relative_invariant {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (q : RegisterState r) (hq : PhaseRegular q) (i j : Fin r) :
    relativePhases (registerPhases (((registerStep h)^[n]) q)) i j =
      relativePhases (registerPhases q) i j
```

Proof method: Kernel-checked tactic proof using rw, simp. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_step_relative_invariant` and the printed proof in the machine-generated audit.

## `register_step_iterate_formula`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_step_iterate_formula {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (q : RegisterState r) (i : Fin r) :
    (((registerStep h)^[n]) q) i = translateKey (n • h i) ((keyCoordinateCycle^[n]) (q i))
```

Proof method: Kernel-checked tactic proof using induction, rw, simp, change. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_step_iterate_formula` and the printed proof in the machine-generated audit.

## `register_step_metadata_invariant`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_step_metadata_invariant {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (q : RegisterState r) (i : Fin r) :
    (((registerStep h)^[n]) q i).metadata = (q i).metadata
```

Proof method: Kernel-checked tactic proof using rw. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_step_metadata_invariant` and the printed proof in the machine-generated audit.

## `register_step_period_twelve`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_step_period_twelve {r : ℕ} (h : RegisterTranslation r) (q : RegisterState r) :
    ((registerStep h)^[12]) q = q
```

Proof method: Kernel-checked tactic proof using funext, rw, exact, change. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_step_period_twelve` and the printed proof in the machine-generated audit.

## `register_regular_orbit_no_collapse`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_regular_orbit_no_collapse {r : ℕ} (base : Fin r)
    (h : RegisterTranslation r) (q : RegisterState r) (hq : PhaseRegular q) (n m : ℕ)
    (heq : ((registerStep h)^[n]) q = ((registerStep h)^[m]) q) :
    (n : ZMod 12) = (m : ZMod 12)
```

Proof method: Kernel-checked tactic proof using rw, exact. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_regular_orbit_no_collapse` and the printed proof in the machine-generated audit.

## `register_step_period_iff`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_step_period_iff {r : ℕ} (hr : 0 < r) (h : RegisterTranslation r) (n : ℕ) :
    (∀ q : RegisterState r, ((registerStep h)^[n]) q = q) ↔ 12 ∣ n
```

Proof method: Kernel-checked tactic proof using funext, rw, simp, simpa, exact, intro. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_step_period_iff` and the printed proof in the machine-generated audit.

## `register_regular_orbit_injective`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_regular_orbit_injective {r : ℕ} (base : Fin r)
    (h : RegisterTranslation r) (q : RegisterState r) (hq : PhaseRegular q) :
    Function.Injective (fun n : Fin 12 => ((registerStep h)^[n.val]) q)
```

Proof method: Kernel-checked tactic proof using simpa, apply, intro. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_regular_orbit_injective` and the printed proof in the machine-generated audit.

## `relative_phases_iff_common_offset`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem relative_phases_iff_common_offset {r : ℕ} (base : Fin r) (a b : RegisterPhase r) :
    (∀ i j, relativePhases b i j = relativePhases a i j) ↔
      ∃ c : ZMod 12, ∀ i, b i = a i + c
```

Proof method: Kernel-checked tactic proof using rw, simp, refine, abel, change, calc, intro. Exact terms and dependencies are in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES relative_phases_iff_common_offset` and the printed proof in the machine-generated audit.

## `register_aggregate_phase_formula`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem register_aggregate_phase_formula {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (q : RegisterState r) (hq : PhaseRegular q) :
    (∑ i : Fin r, registerPhases (((registerStep h)^[n]) q) i) =
      (∑ i : Fin r, registerPhases q i) + (r : ZMod 12) * (n : ZMod 12)
```

Proof method: Kernel-checked tactic proof using rw, simp. Exact terms and dependencies are in the audit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_aggregate_phase_formula` and the printed proof in the machine-generated audit.

## `two_register_sum_collapse`

Source: `IndependentDuodenary/RegisterDynamics.lean`. Compilation: **passed**.

```lean
theorem two_register_sum_collapse :
    (∑ i : Fin 2, (fun _ : Fin 2 => (6 : ZMod 12)) i) =
      (∑ i : Fin 2, (fun _ : Fin 2 => (0 : ZMod 12)) i) ∧
    (fun _ : Fin 2 => (6 : ZMod 12)) ≠ (fun _ : Fin 2 => (0 : ZMod 12))
```

Proof method: Kernel-checked finite decision procedure (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES two_register_sum_collapse` and the printed proof in the machine-generated audit.

## `retained_register_natural_injective`

Source: `IndependentDuodenary/RegisterNaturality.lean`. Compilation: **passed**.

```lean
theorem retained_register_natural_injective {F G : RegisterFamily}
    (f : RegisterNaturalMap F G) (r : ℕ) :
    Function.Injective ((retainRegisterNatural f).app r)
```

Proof method: Kernel-checked tactic proof using exact, intro. Exact terms and dependencies are in the audit.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES retained_register_natural_injective` and the printed proof in the machine-generated audit.

## `register_natural_parameter_iterate`

Source: `IndependentDuodenary/RegisterNaturality.lean`. Compilation: **passed**.

```lean
theorem register_natural_parameter_iterate {F H : RegisterFamily}
    (A : RegisterNaturalMap (productRegisterFamily H F) F)
    {r s : ℕ} (select : Fin s → Fin r) (h : H.Carrier r) (n : ℕ) (x : F.Carrier r) :
    F.restrict select (((fun y => A.app r (h, y))^[n]) x) =
      (((fun y => A.app s (H.restrict select h, y))^[n]) (F.restrict select x))
```

Proof method: Kernel-checked tactic proof using induction, rw, change. Exact terms and dependencies are in the audit.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES register_natural_parameter_iterate` and the printed proof in the machine-generated audit.

## `successor_period_left_inverse`

Source: `IndependentDuodenary/RegisterNaturality.lean`. Compilation: **passed**.

```lean
theorem successor_period_left_inverse {A : Type} (T : A → A) (n : ℕ)
    (hperiod : ∀ x, (T^[n + 1]) x = x) : Function.LeftInverse (T^[n]) T
```

Proof method: Kernel-checked tactic proof using rw, exact, intro. Exact terms and dependencies are in the audit.

Axioms: `none`.

Dependencies: see `DIRECT DEPENDENCIES successor_period_left_inverse` and the printed proof in the machine-generated audit.

## `successor_period_injective`

Source: `IndependentDuodenary/RegisterNaturality.lean`. Compilation: **passed**.

```lean
theorem successor_period_injective {A : Type} (T : A → A) (n : ℕ)
    (hperiod : ∀ x, (T^[n + 1]) x = x) : Function.Injective T
```

Proof method: Direct proof term applying the named previously checked declarations; see the printed proof and dependencies.

Axioms: `none`.

Dependencies: see `DIRECT DEPENDENCIES successor_period_injective` and the printed proof in the machine-generated audit.

## `protocol_reachability_check_correct`

Source: `IndependentDuodenary/SearchBoundary.lean`. Compilation: **passed**.

```lean
theorem protocol_reachability_check_correct {r : ℕ} (h : RegisterTranslation r)
    (q x : RegisterState r) :
    protocolReachabilityCheck h q x = true ↔ ∃ n : ℕ, ((registerStep h)^[n]) q = x
```

Proof method: List.any correctness, finite index membership and the proved bounded-search equivalence.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES protocol_reachability_check_correct` and the printed proof in the machine-generated audit.

## `protocol_reachability_check_rejects_iff`

Source: `IndependentDuodenary/SearchBoundary.lean`. Compilation: **passed**.

```lean
theorem protocol_reachability_check_rejects_iff {r : ℕ} (h : RegisterTranslation r)
    (q x : RegisterState r) :
    protocolReachabilityCheck h q x = false ↔ ¬ ∃ n : ℕ, ((registerStep h)^[n]) q = x
```

Proof method: Boolean case analysis and the exact positive correctness theorem.

Axioms: `propext,
 Classical.choice,
 Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES protocol_reachability_check_rejects_iff` and the printed proof in the machine-generated audit.

## `protocol_global_orbit_cover_bound`

Source: `IndependentDuodenary/SearchBoundary.lean`. Compilation: **passed**.

```lean
theorem protocol_global_orbit_cover_bound {r : ℕ} (h : RegisterTranslation r)
    (seeds : Finset (RegisterState r))
    (covers : ∀ x : RegisterState r, ∃ q ∈ seeds, x ∈ protocolOrbitCandidates h q) :
    49152 ^ r ≤ 12 * seeds.card
```

Proof method: Construct a surjection from seed-phase pairs onto all states and compare finite cardinalities.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES protocol_global_orbit_cover_bound` and the printed proof in the machine-generated audit.

## `protocol_one_register_cover_needs_4096`

Source: `IndependentDuodenary/SearchBoundary.lean`. Compilation: **passed**.

```lean
theorem protocol_one_register_cover_needs_4096 (h : RegisterTranslation 1)
    (seeds : Finset (RegisterState 1))
    (covers : ∀ x : RegisterState 1, ∃ q ∈ seeds, x ∈ protocolOrbitCandidates h q) :
    4096 ≤ seeds.card
```

Proof method: Specialize the cover bound to one register and discharge natural arithmetic.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES protocol_one_register_cover_needs_4096` and the printed proof in the machine-generated audit.

## `sourceSupportBlock_pullback`

Source: `IndependentDuodenary/SourceFactorization.lean`. Compilation: **passed**.

```lean
theorem sourceSupportBlock_pullback [Zero V] [DecidableEq V] (b : FullBlock E X V) :
    pullbackBlock (sourceSupportBlock b) = b
```

Proof method: Case analysis over zero and equal slopes reconstructs the original coefficient pair.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES sourceSupportBlock_pullback` and the printed proof in the machine-generated audit.

## `sourceSupportBlock_correction`

Source: `IndependentDuodenary/SourceFactorization.lean`. Compilation: **passed**.

```lean
theorem sourceSupportBlock_correction [Zero V] [DecidableEq V] (b : FullBlock E X V) :
    pullbackCorrection (sourceSupportBlock b) = (reduceFullBlock b).2
```

Proof method: Case analysis identifies the support projection correction with the reduced intercept correction.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES sourceSupportBlock_correction` and the printed proof in the machine-generated audit.

## `pullback_reducedSourceTable`

Source: `IndependentDuodenary/SourceFactorization.lean`. Compilation: **passed**.

```lean
theorem pullback_reducedSourceTable [AddCommMonoid V] [DecidableEq V]
    (hDouble : ∀ v : V, v + v = 0) (t : FullTable k E X V) :
    pullbackTable (reducedSourceTable t) = t
```

Proof method: Reconstruct block slopes; the exponent-two hypothesis cancels the duplicate sum of corrections.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES pullback_reducedSourceTable` and the printed proof in the machine-generated audit.

## `binary_module_double_zero`

Source: `IndependentDuodenary/SourceFactorization.lean`. Compilation: **passed**.

```lean
theorem binary_module_double_zero [AddCommMonoid V] [Module (ZMod 2) V] (v : V) :
    v + v = 0
```

Proof method: Rewrite self-addition as scalar multiplication by 1+1=0 in ZMod 2.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES binary_module_double_zero` and the printed proof in the machine-generated audit.

## `binary_module_add_eq_zero_iff`

Source: `IndependentDuodenary/SourceFactorization.lean`. Compilation: **passed**.

```lean
theorem binary_module_add_eq_zero_iff [AddCommMonoid V] [Module (ZMod 2) V]
    (a d : V) : a + d = 0 ↔ a = d
```

Proof method: Add the second summand and use binary_module_double_zero.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES binary_module_add_eq_zero_iff` and the printed proof in the machine-generated audit.

## `binary_single_slope_injective`

Source: `IndependentDuodenary/SourceFactorization.lean`. Compilation: **passed**.

```lean
theorem binary_single_slope_injective [AddCommMonoid V] [Module (ZMod 2) V]
    (a : V) (ha : a ≠ 0) : Function.Injective (fun z : ZMod 2 => z • a)
```

Proof method: Finite binary-scalar cases, with nonzero slope hypothesis.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES binary_single_slope_injective` and the printed proof in the machine-generated audit.

## `binary_pair_slopes_injective`

Source: `IndependentDuodenary/SourceFactorization.lean`. Compilation: **passed**.

```lean
theorem binary_pair_slopes_injective [AddCommMonoid V] [Module (ZMod 2) V]
    (a d : V) (ha : a ≠ 0) (hd : d ≠ 0) (had : a ≠ d) :
    Function.Injective (fun xy : ZMod 2 × ZMod 2 => xy.1 • a + xy.2 • d)
```

Proof method: Finite scalar kernel cases and characteristic-two cancellation establish injectivity.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES binary_pair_slopes_injective` and the printed proof in the machine-generated audit.

## `source_reduction_factorization`

Source: `IndependentDuodenary/SourceFactorization.lean`. Compilation: **passed**.

```lean
theorem source_reduction_factorization [AddCommMonoid V] [Module (ZMod 2) V]
    [DecidableEq V] (t : FullTable k E X V)
    (p : ZMod 2 × (Fin k → ZMod 2 × ZMod 2)) :
    evaluateFullTable t p = evaluateProjectedTable (reducedSourceTable t)
      (permittedProjection (reducedSourceTable t) p)
```

Proof method: source_table_pullback_evaluation and pullback_reducedSourceTable with module-derived cancellation.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES source_reduction_factorization` and the printed proof in the machine-generated audit.

## `source_reduction_projection_surjective`

Source: `IndependentDuodenary/SourceFactorization.lean`. Compilation: **passed**.

```lean
theorem source_reduction_projection_surjective [AddCommMonoid V] [DecidableEq V]
    (t : FullTable k E X V) :
    Function.Surjective (permittedProjection (reducedSourceTable t))
```

Proof method: Instantiate permittedProjection_surjective on the explicit support table.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES source_reduction_projection_surjective` and the printed proof in the machine-generated audit.

## `source_reduction_unique`

Source: `IndependentDuodenary/SourceFactorization.lean`. Compilation: **passed**.

```lean
theorem source_reduction_unique [AddCommMonoid V] [Module (ZMod 2) V]
    [DecidableEq V] (t : FullTable k E X V)
    (g : (ZMod 2 × ((i : Fin k) → ProjectedCoordinates ((reducedSourceTable t).blocks i))) → V)
    (hg : ∀ p, g (permittedProjection (reducedSourceTable t) p) = evaluateFullTable t p) :
    g = evaluateProjectedTable (reducedSourceTable t)
```

Proof method: Use a preimage of every support point; both functions agree by the factorization identities.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES source_reduction_unique` and the printed proof in the machine-generated audit.

## `key_cycle_vertex_observable`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem key_cycle_vertex_observable (q : RepresentedKey) :
    keyVertexObservable (keyVertex (keyCoordinateCycle q)) =
      fun i => keyVertexObservable (keyVertex q) (i + 1)
```

Proof method: Definitional equality of the rotated complement and the chosen vertex observable.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES key_cycle_vertex_observable` and the printed proof in the machine-generated audit.

## `key_cycle_iterate`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem key_cycle_iterate (n : ℕ) (q : RepresentedKey) :
    (keyCoordinateCycle^[n]) q =
      ⟨q.metadata, q.binaryIntercept, fun i => q.complementIntercept (i + (n : ZMod 12))⟩
```

Proof method: Induction on iteration count, then associativity and commutativity of residue addition.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES key_cycle_iterate` and the printed proof in the machine-generated audit.

## `key_one_hot_phase`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem key_one_hot_phase : ∀ a : ZMod 12,
    keyPhaseLabel (0, keyOneHot a) = a
```

Proof method: Simplify the one-hot predicate and its finite sum at the unique nonzero coordinate.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES key_one_hot_phase` and the printed proof in the machine-generated audit.

## `key_cycle_witness_phase`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem key_cycle_witness_phase (n : ℕ) :
    keyPhaseLabel (keyVertex ((keyCoordinateCycle^[n]) keyCycleWitness)) = (n : ZMod 12)
```

Proof method: Iteration formula, equality of the shifted one-hot vector, and key_one_hot_phase.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES key_cycle_witness_phase` and the printed proof in the machine-generated audit.

## `key_cycle_period_iff`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem key_cycle_period_iff (n : ℕ) :
    (∀ q : RepresentedKey, (keyCoordinateCycle^[n]) q = q) ↔ 12 ∣ n
```

Proof method: Necessity from the witness phase; sufficiency from the iterate formula and cast/divisibility equivalence.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES key_cycle_period_iff` and the printed proof in the machine-generated audit.

## `key_cycle_period_twelve`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem key_cycle_period_twelve :
    ∀ q : RepresentedKey, (keyCoordinateCycle^[12]) q = q
```

Proof method: Specialize key_cycle_period_iff to divisibility of 12 by itself.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES key_cycle_period_twelve` and the printed proof in the machine-generated audit.

## `key_cycle_witness_period_iff`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem key_cycle_witness_period_iff (n : ℕ) :
    (keyCoordinateCycle^[n]) keyCycleWitness = keyCycleWitness ↔ 12 ∣ n
```

Proof method: Witness phase yields the divisibility condition; the operator period theorem gives its converse.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES key_cycle_witness_period_iff` and the printed proof in the machine-generated audit.

## `key_cycle_orbit_equivariance`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem key_cycle_orbit_equivariance (n : ℕ) :
    keyPhaseLabel (keyVertex (keyCoordinateCycle ((keyCoordinateCycle^[n]) keyCycleWitness))) =
      keyPhaseLabel (keyVertex ((keyCoordinateCycle^[n]) keyCycleWitness)) + 1
```

Proof method: Relate the next orbit point to successor iteration, then use its phase formula.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES key_cycle_orbit_equivariance` and the printed proof in the machine-generated audit.

## `key_cycle_commutes_translation`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem key_cycle_commutes_translation (h : KeyBinary) (q : RepresentedKey) :
    keyCoordinateCycle (translateKey h q) = translateKey h (keyCoordinateCycle q)
```

Proof method: Definitional equality: the coordinate cycle and binary translation act on different fields.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES key_cycle_commutes_translation` and the printed proof in the machine-generated audit.

## `key_cycle_no_shorter_positive_period`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem key_cycle_no_shorter_positive_period (n : ℕ) (hn : 0 < n) (hlt : n < 12) :
    ¬ (∀ q : RepresentedKey, (keyCoordinateCycle^[n]) q = q)
```

Proof method: The period theorem and the lower bound for a positive multiple of 12.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES key_cycle_no_shorter_positive_period` and the printed proof in the machine-generated audit.

## `key_cycle_distinct_from_translation`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem key_cycle_distinct_from_translation (h : KeyBinary) :
    keyCoordinateCycle ≠ translateKey h
```

Proof method: Evaluate both candidate functions on the one-hot witness and its zero coordinate.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES key_cycle_distinct_from_translation` and the printed proof in the machine-generated audit.

## `key_cycle_no_global_station_shift`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem key_cycle_no_global_station_shift :
    ¬ ∃ f : RepresentedKey → ZMod 12, ∀ q, f (keyCoordinateCycle q) = f q + 1
```

Proof method: The all-zero key is fixed; additive cancellation contradicts the nonzero residue 1.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES key_cycle_no_global_station_shift` and the printed proof in the machine-generated audit.

## `key_metadata_roundtrip`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem key_metadata_roundtrip : ∀ m : KeyMetadata,
    decodeKeyMetadata (encodeKeyMetadata m) = some m
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES key_metadata_roundtrip` and the printed proof in the machine-generated audit.

## `key_metadata_parse_sound`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem key_metadata_parse_sound : ∀ x : ZMod 12, ∀ m : KeyMetadata,
    decodeKeyMetadata x = some m → encodeKeyMetadata m = x
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES key_metadata_parse_sound` and the printed proof in the machine-generated audit.

## `key_bit_roundtrip`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem key_bit_roundtrip : ∀ b : ZMod 2,
    decodeKeyBit (encodeKeyBit b) = some b
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES key_bit_roundtrip` and the printed proof in the machine-generated audit.

## `key_bit_parse_sound`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem key_bit_parse_sound : ∀ x : ZMod 12, ∀ b : ZMod 2,
    decodeKeyBit x = some b → encodeKeyBit b = x
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES key_bit_parse_sound` and the printed proof in the machine-generated audit.

## `framed_key_bits_suffix`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem framed_key_bits_suffix (n : ℕ) (b : Fin n → ZMod 2) (tail : List (ZMod 12)) :
    decodeFramedKeyBits n (encodeKeyBits b ++ tail) =
      if tail = [10] then some b else none
```

Proof method: Induction on binary dimension, the bit parser round trip and Fin.cons_self_tail.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES framed_key_bits_suffix` and the printed proof in the machine-generated audit.

## `framed_key_bits_roundtrip`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem framed_key_bits_roundtrip (n : ℕ) (b : Fin n → ZMod 2) :
    decodeFramedKeyBits n (encodeKeyBits b ++ [10]) = some b
```

Proof method: Specialize the suffix theorem to the sole terminator word.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES framed_key_bits_roundtrip` and the printed proof in the machine-generated audit.

## `framed_key_bits_parse_sound`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem framed_key_bits_parse_sound (n : ℕ) (xs : List (ZMod 12))
    (b : Fin n → ZMod 2) (h : decodeFramedKeyBits n xs = some b) :
    xs = encodeKeyBits b ++ [10]
```

Proof method: Induction on dimension and parser cases; reconstruct each digit from parser soundness.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES framed_key_bits_parse_sound` and the printed proof in the machine-generated audit.

## `key_bits_unpack_pack`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem key_bits_unpack_pack (q : RepresentedKey) :
    unpackKeyBits q.metadata (packKeyBits q) = q
```

Proof method: Record decomposition, the two Fin.append projection laws and residue value/cast round trip.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES key_bits_unpack_pack` and the printed proof in the machine-generated audit.

## `key_bits_pack_unpack`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem key_bits_pack_unpack (m : KeyMetadata) (b : Fin 14 → ZMod 2) :
    packKeyBits (unpackKeyBits m b) = b
```

Proof method: Split the fourteen indices into the two binary and twelve complement coordinates.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES key_bits_pack_unpack` and the printed proof in the machine-generated audit.

## `exact_key_decode_encode`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem exact_key_decode_encode (q : RepresentedKey) :
    decodeExactKey (encodeExactKey q) = some q
```

Proof method: Metadata and framed-bit round trips followed by full-record unpack/pack equality.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES exact_key_decode_encode` and the printed proof in the machine-generated audit.

## `exact_key_parse_sound`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem exact_key_parse_sound (xs : List (ZMod 12)) (q : RepresentedKey)
    (h : decodeExactKey xs = some q) : xs = encodeExactKey q
```

Proof method: Case analysis on framing and parsers, framed-bit soundness, and pack/unpack equality.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES exact_key_parse_sound` and the printed proof in the machine-generated audit.

## `exact_key_reject_malformed`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem exact_key_reject_malformed (xs : List (ZMod 12))
    (h : ∀ q : RepresentedKey, xs ≠ encodeExactKey q) : decodeExactKey xs = none
```

Proof method: A successful parse would reconstruct an encoded word, contradicting the hypothesis.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES exact_key_reject_malformed` and the printed proof in the machine-generated audit.

## `exact_key_encode_length`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem exact_key_encode_length (q : RepresentedKey) : (encodeExactKey q).length = 17
```

Proof method: Length of the fixed frame and List.ofFn payload.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES exact_key_encode_length` and the printed proof in the machine-generated audit.

## `exact_key_reject_length`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem exact_key_reject_length (xs : List (ZMod 12)) (h : xs.length ≠ 17) :
    decodeExactKey xs = none
```

Proof method: Parse soundness and the fixed encoded length rule out successful decoding.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES exact_key_reject_length` and the printed proof in the machine-generated audit.

## `exact_key_encode_injective`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem exact_key_encode_injective : Function.Injective encodeExactKey
```

Proof method: Apply the decoder to equal encoded words and use the proved left inverse.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES exact_key_encode_injective` and the printed proof in the machine-generated audit.

## `exact_key_reject_header`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem exact_key_reject_header (header metadata : ZMod 12) (body : List (ZMod 12))
    (h : header ≠ 11) : decodeExactKey (header :: metadata :: body) = none
```

Proof method: The header test fails under the explicit inequality.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES exact_key_reject_header` and the printed proof in the machine-generated audit.

## `exact_key_reject_metadata`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem exact_key_reject_metadata (metadata : ZMod 12) (body : List (ZMod 12))
    (h : ¬ metadata.val < 3) : decodeExactKey (11 :: metadata :: body) = none
```

Proof method: The metadata range test fails under the explicit bound.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES exact_key_reject_metadata` and the printed proof in the machine-generated audit.

## `exact_key_reject_suffix`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem exact_key_reject_suffix (q : RepresentedKey) (tail : List (ZMod 12))
    (h : tail ≠ [10]) :
    decodeExactKey (11 :: encodeKeyMetadata q.metadata ::
      (encodeKeyBits (packKeyBits q) ++ tail)) = none
```

Proof method: The framed-bit suffix theorem rejects every suffix other than the single terminator.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES exact_key_reject_suffix` and the printed proof in the machine-generated audit.

## `exact_key_reject_nonbinary_first`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem exact_key_reject_nonbinary_first (metadata x : ZMod 12) (xs : List (ZMod 12))
    (hzero : x ≠ 0) (hone : x ≠ 1) :
    decodeExactKey (11 :: metadata :: x :: xs) = none
```

Proof method: The first bit parser rejects a digit different from both zero and one.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES exact_key_reject_nonbinary_first` and the printed proof in the machine-generated audit.

## `exact_key_word_translation`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem exact_key_word_translation (h : KeyBinary) (q : RepresentedKey) :
    translateKeyWord h (encodeExactKey q) = encodeExactKey (translateKey h q)
```

Proof method: Decode the encoded key by the left inverse and evaluate the transported operation.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES exact_key_word_translation` and the printed proof in the machine-generated audit.

## `exact_key_word_translation_invalid`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem exact_key_word_translation_invalid (h : KeyBinary) (word : List (ZMod 12))
    (hinvalid : decodeExactKey word = none) : translateKeyWord h word = []
```

Proof method: Evaluate the transported operation at the explicitly failed parse.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES exact_key_word_translation_invalid` and the printed proof in the machine-generated audit.

## `exact_key_word_translation_involution`

Source: `IndependentDuodenary/SourceKeyRepresentation.lean`. Compilation: **passed**.

```lean
theorem exact_key_word_translation_involution (h : KeyBinary) (q : RepresentedKey) :
    translateKeyWord h (translateKeyWord h (encodeExactKey q)) = encodeExactKey q
```

Proof method: Apply transport twice, translation composition, binary exponent two and translation by zero.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES exact_key_word_translation_involution` and the printed proof in the machine-generated audit.

## `translateKey_zero`

Source: `IndependentDuodenary/SourceKeys.lean`. Compilation: **passed**.

```lean
theorem translateKey_zero [AddZeroClass K] (q : ExactKey M K W) :
    translateKey 0 q = q
```

Proof method: Unfold translation and use addition by zero.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES translateKey_zero` and the printed proof in the machine-generated audit.

## `translateKey_add`

Source: `IndependentDuodenary/SourceKeys.lean`. Compilation: **passed**.

```lean
theorem translateKey_add [AddSemigroup K] (h g : K) (q : ExactKey M K W) :
    translateKey g (translateKey h q) = translateKey (h + g) q
```

Proof method: Associativity of intercept addition.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES translateKey_add` and the printed proof in the machine-generated audit.

## `translateKey_free`

Source: `IndependentDuodenary/SourceKeys.lean`. Compilation: **passed**.

```lean
theorem translateKey_free [AddCancelMonoid K] (h g : K) (q : ExactKey M K W) :
    translateKey h q = translateKey g q ↔ h = g
```

Proof method: Project equality to the intercept and cancel its fixed left summand.

Axioms: `none`.

Dependencies: see `DIRECT DEPENDENCIES translateKey_free` and the printed proof in the machine-generated audit.

## `translateKey_vertex`

Source: `IndependentDuodenary/SourceKeys.lean`. Compilation: **passed**.

```lean
theorem translateKey_vertex [Add K] (h : K) (q : ExactKey M K W) :
    keyVertex (translateKey h q) = keyVertex q
```

Proof method: Definitional equality: translation leaves vertex fields unchanged.

Axioms: `none`.

Dependencies: see `DIRECT DEPENDENCIES translateKey_vertex` and the printed proof in the machine-generated audit.

## `canonicalKey_translate`

Source: `IndependentDuodenary/SourceKeys.lean`. Compilation: **passed**.

```lean
theorem canonicalKey_translate [AddZeroClass K] (h : K) (q : ExactKey M K W) :
    canonicalKey (translateKey h q) = canonicalKey q
```

Proof method: Definitional equality after discarding the translated intercept.

Axioms: `none`.

Dependencies: see `DIRECT DEPENDENCIES canonicalKey_translate` and the printed proof in the machine-generated audit.

## `canonicalKey_idempotent`

Source: `IndependentDuodenary/SourceKeys.lean`. Compilation: **passed**.

```lean
theorem canonicalKey_idempotent [Zero K] (q : ExactKey M K W) :
    canonicalKey (canonicalKey q) = canonicalKey q
```

Proof method: Definitional equality of zeroing the intercept twice.

Axioms: `none`.

Dependencies: see `DIRECT DEPENDENCIES canonicalKey_idempotent` and the printed proof in the machine-generated audit.

## `canonicalKey_reconstruct`

Source: `IndependentDuodenary/SourceKeys.lean`. Compilation: **passed**.

```lean
theorem canonicalKey_reconstruct [AddZeroClass K] (q : ExactKey M K W) :
    translateKey q.binaryIntercept (canonicalKey q) = q
```

Proof method: Add the removed intercept back to zero.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES canonicalKey_reconstruct` and the printed proof in the machine-generated audit.

## `keyOrbit_iff_vertex_eq`

Source: `IndependentDuodenary/SourceKeys.lean`. Compilation: **passed**.

```lean
theorem keyOrbit_iff_vertex_eq [AddGroup K] (q r : ExactKey M K W) :
    SameKeyOrbit q r ↔ keyVertex q = keyVertex r
```

Proof method: Project orbit equality to metadata; construct translation by minus the old intercept plus the new one.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES keyOrbit_iff_vertex_eq` and the printed proof in the machine-generated audit.

## `canonicalKey_unique`

Source: `IndependentDuodenary/SourceKeys.lean`. Compilation: **passed**.

```lean
theorem canonicalKey_unique [AddGroup K] (q r : ExactKey M K W)
    (horbit : SameKeyOrbit q r) (hz : r.binaryIntercept = 0) :
    r = canonicalKey q
```

Proof method: Orbit equality fixes metadata and complement; the stated zero intercept fixes the representative.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES canonicalKey_unique` and the printed proof in the machine-generated audit.

## `source_folding`

Source: `IndependentDuodenary/SourceKeys.lean`. Compilation: **passed**.

```lean
theorem source_folding [AddSemigroup K] (label : M × W → K)
    (h : K) (q : ExactKey M K W) :
    restoredAnswer label (translateKey h q) = restoredAnswer label q + h
```

Proof method: Associativity applied to the explicit restored-answer formula.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES source_folding` and the printed proof in the machine-generated audit.

## `exact_key_answers_equal`

Source: `IndependentDuodenary/SourceKeys.lean`. Compilation: **passed**.

```lean
theorem exact_key_answers_equal [Add K] (label : M × W → K)
    (q r : ExactKey M K W) (h : q = r) :
    restoredAnswer label q = restoredAnswer label r
```

Proof method: Congruence under the restored-answer function.

Axioms: `none`.

Dependencies: see `DIRECT DEPENDENCIES exact_key_answers_equal` and the printed proof in the machine-generated audit.

## `residue_folding_twelve`

Source: `IndependentDuodenary/SourceKeys.lean`. Compilation: **passed**.

```lean
theorem residue_folding_twelve [AddMonoid K] (χ : K →+ ZMod 2)
    (label : M × W → ZMod 12) (h : K) (q : ExactKey M K W) :
    residueAnswerTwelve χ label (translateKey h q) =
      residueAnswerTwelve χ label q + bridgeTwelve χ h
```

Proof method: Addition preservation of bridgeTwelve and associativity.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES residue_folding_twelve` and the printed proof in the machine-generated audit.

## `residue_folding_144`

Source: `IndependentDuodenary/SourceKeys.lean`. Compilation: **passed**.

```lean
theorem residue_folding_144 [AddMonoid K] (χ : K →+ ZMod 2)
    (label : M × W → ZMod 144) (h : K) (q : ExactKey M K W) :
    residueAnswer144 χ label (translateKey h q) =
      residueAnswer144 χ label q + bridge144 χ h
```

Proof method: Addition preservation of bridge144 and associativity.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES residue_folding_144` and the printed proof in the machine-generated audit.

## `sourceBlockProjection_lift`

Source: `IndependentDuodenary/SourceProjection.lean`. Compilation: **passed**.

```lean
theorem sourceBlockProjection_lift (b : ProjectedBlock E X V) (t₀ : ZMod 2)
    (z : ProjectedCoordinates b) :
    sourceBlockProjection b t₀ (sourceBlockLift b t₀ z) = z
```

Proof method: Explicit local right inverse for every block/position; third position subtracts the homogeneous correction.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES sourceBlockProjection_lift` and the printed proof in the machine-generated audit.

## `sourceBlockProjection_surjective`

Source: `IndependentDuodenary/SourceProjection.lean`. Compilation: **passed**.

```lean
theorem sourceBlockProjection_surjective (b : ProjectedBlock E X V) (t₀ : ZMod 2) :
    Function.Surjective (sourceBlockProjection b t₀)
```

Proof method: Use sourceBlockLift as a preimage.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES sourceBlockProjection_surjective` and the printed proof in the machine-generated audit.

## `permittedProjection_preserves_homogeneous`

Source: `IndependentDuodenary/SourceProjection.lean`. Compilation: **passed**.

```lean
theorem permittedProjection_preserves_homogeneous (t : ProjectedTable k E X V)
    (p : ZMod 2 × (Fin k → ZMod 2 × ZMod 2)) :
    (permittedProjection t p).1 = p.1
```

Proof method: Definitional equality of the homogeneous coordinate.

Axioms: `propext,
 Classical.choice,
 Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES permittedProjection_preserves_homogeneous` and the printed proof in the machine-generated audit.

## `permittedProjection_surjective`

Source: `IndependentDuodenary/SourceProjection.lean`. Compilation: **passed**.

```lean
theorem permittedProjection_surjective (t : ProjectedTable k E X V) :
    Function.Surjective (permittedProjection t)
```

Proof method: Choose each local right inverse independently and preserve the common homogeneous bit.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES permittedProjection_surjective` and the printed proof in the machine-generated audit.

## `source_block_pullback_evaluation`

Source: `IndependentDuodenary/SourceProjection.lean`. Compilation: **passed**.

```lean
theorem source_block_pullback_evaluation (b : ProjectedBlock E X V)
    (t₀ : ZMod 2) (xy : ZMod 2 × ZMod 2) :
    evaluateFullBlock (pullbackBlock b) xy + t₀ • pullbackCorrection b =
      evaluateProjectedBlock b (sourceBlockProjection b t₀ xy)
```

Proof method: Case analysis, distributivity of scalar multiplication, and the third-position correction.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES source_block_pullback_evaluation` and the printed proof in the machine-generated audit.

## `source_table_pullback_evaluation`

Source: `IndependentDuodenary/SourceProjection.lean`. Compilation: **passed**.

```lean
theorem source_table_pullback_evaluation (t : ProjectedTable k E X V)
    (p : ZMod 2 × (Fin k → ZMod 2 × ZMod 2)) :
    evaluateFullTable (pullbackTable t) p =
      evaluateProjectedTable t (permittedProjection t p)
```

Proof method: Distribute scalar multiplication and finite sums; apply the block evaluation identity.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES source_table_pullback_evaluation` and the printed proof in the machine-generated audit.

## `pullback_block_metadata`

Source: `IndependentDuodenary/SourceReduction.lean`. Compilation: **passed**.

```lean
theorem pullback_block_metadata [AddZeroClass V] [DecidableEq V]
    (b : ProjectedBlock E X V) :
    (reduceFullBlock (pullbackBlock b)).1 = (reduceProjectedBlock b).1
```

Proof method: Case analysis over block and position, then zero/nonzero slope simplification.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES pullback_block_metadata` and the printed proof in the machine-generated audit.

## `pullback_block_intercept`

Source: `IndependentDuodenary/SourceReduction.lean`. Compilation: **passed**.

```lean
theorem pullback_block_intercept [AddZeroClass V] [DecidableEq V]
    (hDouble : ∀ v : V, v + v = 0) (b : ProjectedBlock E X V) :
    pullbackCorrection b + (reduceFullBlock (pullbackBlock b)).2 =
      (reduceProjectedBlock b).2
```

Proof method: Case analysis; the explicit exponent-two hypothesis cancels duplicate third-position corrections.

Axioms: `propext`.

Dependencies: see `DIRECT DEPENDENCIES pullback_block_intercept` and the printed proof in the machine-generated audit.

## `pullback_reduced_intercept`

Source: `IndependentDuodenary/SourceReduction.lean`. Compilation: **passed**.

```lean
theorem pullback_reduced_intercept [AddCommMonoid V] [DecidableEq V]
    (hDouble : ∀ v : V, v + v = 0) (t : ProjectedTable k E X V) :
    fullReducedIntercept (pullbackTable t) = projectedReducedIntercept t
```

Proof method: Distribute the finite sum and apply pullback_block_intercept at each position.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES pullback_reduced_intercept` and the printed proof in the machine-generated audit.

## `permitted_pullback_exact_key`

Source: `IndependentDuodenary/SourceReduction.lean`. Compilation: **passed**.

```lean
theorem permitted_pullback_exact_key [AddCommMonoid K] [AddCommMonoid W]
    [DecidableEq K] [DecidableEq W] (hDouble : ∀ v : K × W, v + v = 0)
    (t : ProjectedTable k E X (K × W)) :
    fullExactKey (pullbackTable t) = projectedExactKey t
```

Proof method: Combine pullback_block_metadata and pullback_reduced_intercept.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES permitted_pullback_exact_key` and the printed proof in the machine-generated audit.

## `projected_exact_key_translate`

Source: `IndependentDuodenary/SourceReduction.lean`. Compilation: **passed**.

```lean
theorem projected_exact_key_translate [AddCommMonoid K] [AddCommMonoid W]
    [DecidableEq K] [DecidableEq W] (h : K) (t : ProjectedTable k E X (K × W)) :
    projectedExactKey (translateProjectedTable h t) = translateKey h (projectedExactKey t)
```

Proof method: Expand intercept sums and commute the added constant to the intercept component.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES projected_exact_key_translate` and the printed proof in the machine-generated audit.

## `source_key_translation_representable`

Source: `IndependentDuodenary/SourceReduction.lean`. Compilation: **passed**.

```lean
theorem source_key_translation_representable [AddCommMonoid K] [AddCommMonoid W]
    [DecidableEq K] [DecidableEq W] (h : K) (t : ProjectedTable k E X (K × W)) :
    ∃ s : ProjectedTable k E X (K × W),
      projectedExactKey s = translateKey h (projectedExactKey t)
```

Proof method: Witness the table with translated intercept; projected_exact_key_translate.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES source_key_translation_representable` and the printed proof in the machine-generated audit.

## `source_canonical_key_representable`

Source: `IndependentDuodenary/SourceReduction.lean`. Compilation: **passed**.

```lean
theorem source_canonical_key_representable [AddCommGroup K] [AddCommMonoid W]
    [DecidableEq K] [DecidableEq W] (t : ProjectedTable k E X (K × W)) :
    ∃ s : ProjectedTable k E X (K × W),
      projectedExactKey s = canonicalKey (projectedExactKey t)
```

Proof method: Translate the table by the negative removed intercept.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES source_canonical_key_representable` and the printed proof in the machine-generated audit.

## `source_table_folding`

Source: `IndependentDuodenary/SourceReduction.lean`. Compilation: **passed**.

```lean
theorem source_table_folding [AddCommMonoid K] [AddCommMonoid W]
    [DecidableEq K] [DecidableEq W]
    (label : (Fin k → ReducedBlock E X (K × W)) × W → K)
    (h : K) (t : ProjectedTable k E X (K × W)) :
    restoredAnswer label (projectedExactKey (translateProjectedTable h t)) =
      restoredAnswer label (projectedExactKey t) + h
```

Proof method: projected_exact_key_translate followed by source_folding.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES source_table_folding` and the printed proof in the machine-generated audit.

## `source_key_sharing`

Source: `IndependentDuodenary/SourceReduction.lean`. Compilation: **passed**.

```lean
theorem source_key_sharing [AddCommMonoid K] [AddCommMonoid W]
    [DecidableEq K] [DecidableEq W] (hDouble : ∀ v : K × W, v + v = 0)
    (label : (Fin k → ReducedBlock E X (K × W)) × W → K)
    (t : ProjectedTable k E X (K × W)) :
    restoredAnswer label (fullExactKey (pullbackTable t)) =
      restoredAnswer label (projectedExactKey t)
```

Proof method: Rewrite using the proved permitted_pullback_exact_key.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES source_key_sharing` and the printed proof in the machine-generated audit.

## `split_binary_double_zero`

Source: `IndependentDuodenary/SourceReduction.lean`. Compilation: **passed**.

```lean
theorem split_binary_double_zero {ℓ d : ℕ}
    (v : (Fin ℓ → ZMod 2) × (Fin d → ZMod 2)) : v + v = 0
```

Proof method: Product extensionality and coordinatewise binary_vector_double_zero.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES split_binary_double_zero` and the printed proof in the machine-generated audit.

## `binary_source_key_sharing`

Source: `IndependentDuodenary/SourceReduction.lean`. Compilation: **passed**.

```lean
theorem binary_source_key_sharing {ℓ d : ℕ}
    (label : (Fin k → ReducedBlock E X ((Fin ℓ → ZMod 2) × (Fin d → ZMod 2))) ×
      (Fin d → ZMod 2) → (Fin ℓ → ZMod 2))
    (t : ProjectedTable k E X ((Fin ℓ → ZMod 2) × (Fin d → ZMod 2))) :
    restoredAnswer label (fullExactKey (pullbackTable t)) =
      restoredAnswer label (projectedExactKey t)
```

Proof method: Discharge source_key_sharing cancellation with split_binary_double_zero.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES binary_source_key_sharing` and the printed proof in the machine-generated audit.

## `parse_station_unit_roundtrip`

Source: `IndependentDuodenary/StationCodec.lean`. Compilation: **passed**.

```lean
theorem parse_station_unit_roundtrip : ∀ u : (ZMod 12)ˣ,
    parseStationUnit (u : ZMod 12) = some u
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES parse_station_unit_roundtrip` and the printed proof in the machine-generated audit.

## `parse_station_unit_sound`

Source: `IndependentDuodenary/StationCodec.lean`. Compilation: **passed**.

```lean
theorem parse_station_unit_sound : ∀ x : ZMod 12, ∀ u : (ZMod 12)ˣ,
    parseStationUnit x = some u → (u : ZMod 12) = x
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES parse_station_unit_sound` and the printed proof in the machine-generated audit.

## `parse_station_parameter_roundtrip`

Source: `IndependentDuodenary/StationCodec.lean`. Compilation: **passed**.

```lean
theorem parse_station_parameter_roundtrip (p : AffineStationParameter) :
    parseStationParameter (encodeStationParameter p) = some p
```

Proof method: The finite unit parser round trip followed by pairing the unchanged offset.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES parse_station_parameter_roundtrip` and the printed proof in the machine-generated audit.

## `encode_parsed_station_parameter`

Source: `IndependentDuodenary/StationCodec.lean`. Compilation: **passed**.

```lean
theorem encode_parsed_station_parameter (c : StationWireCode) (p : AffineStationParameter)
    (h : parseStationParameter c = some p) : encodeStationParameter p = c
```

Proof method: Case analysis on the unit parser, its soundness theorem, and equality of the parsed pair.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES encode_parsed_station_parameter` and the printed proof in the machine-generated audit.

## `station_expression_decode_encode`

Source: `IndependentDuodenary/StationCodec.lean`. Compilation: **passed**.

```lean
theorem station_expression_decode_encode (e : StationExpr) :
    decodeStationExpression (encodeStationExpression e) = some (normalizeStation e)
```

Proof method: Parser round trip and the definition of canonical normalization.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES station_expression_decode_encode` and the printed proof in the machine-generated audit.

## `station_meaning_decode_encode`

Source: `IndependentDuodenary/StationCodec.lean`. Compilation: **passed**.

```lean
theorem station_meaning_decode_encode (q : StationMeaningClass) :
    decodeStationMeaning (encodeStationMeaning q) = some q
```

Proof method: Parser round trip and the semantic quotient round trip.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES station_meaning_decode_encode` and the printed proof in the machine-generated audit.

## `station_expression_semantic_roundtrip`

Source: `IndependentDuodenary/StationCodec.lean`. Compilation: **passed**.

```lean
theorem station_expression_semantic_roundtrip (e : StationExpr) :
    decodeStationMeaning (encodeStationExpression e) = some (Quotient.mk stationSemanticSetoid e)
```

Proof method: Instantiate station_meaning_decode_encode with the expression semantic class.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES station_expression_semantic_roundtrip` and the printed proof in the machine-generated audit.

## `station_parameter_encoding_injective`

Source: `IndependentDuodenary/StationCodec.lean`. Compilation: **passed**.

```lean
theorem station_parameter_encoding_injective : Function.Injective encodeStationParameter
```

Proof method: Project code equality to both fields and use Units.ext.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES station_parameter_encoding_injective` and the printed proof in the machine-generated audit.

## `station_code_collision_iff`

Source: `IndependentDuodenary/StationCodec.lean`. Compilation: **passed**.

```lean
theorem station_code_collision_iff (e f : StationExpr) :
    encodeStationExpression e = encodeStationExpression f ↔ stationMeaning e = stationMeaning f
```

Proof method: Injectivity of parameter encoding and the compiler characterization of meaning.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES station_code_collision_iff` and the printed proof in the machine-generated audit.

## `valid_station_decode_encode`

Source: `IndependentDuodenary/StationCodec.lean`. Compilation: **passed**.

```lean
theorem valid_station_decode_encode (q : StationMeaningClass) :
    decodeValidStationMeaning (encodeValidStationMeaning q) = q
```

Proof method: The unit parser round trip and parameter_meaning_roundtrip.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES valid_station_decode_encode` and the printed proof in the machine-generated audit.

## `valid_station_encode_decode`

Source: `IndependentDuodenary/StationCodec.lean`. Compilation: **passed**.

```lean
theorem valid_station_encode_decode (c : ValidStationCode) :
    encodeValidStationMeaning (decodeValidStationMeaning c) = c
```

Proof method: The semantic-parameter round trip and encode_parsed_station_parameter.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES valid_station_encode_decode` and the printed proof in the machine-generated audit.

## `valid_station_code_card`

Source: `IndependentDuodenary/StationCodec.lean`. Compilation: **passed**.

```lean
theorem valid_station_code_card : Nat.card ValidStationCode = 48
```

Proof method: The proved equivalence with semantic classes and station_meaning_class_card.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES valid_station_code_card` and the printed proof in the machine-generated audit.

## `raw_station_code_card`

Source: `IndependentDuodenary/StationCodec.lean`. Compilation: **passed**.

```lean
theorem raw_station_code_card : Fintype.card StationWireCode = 144
```

Proof method: Product cardinality of two twelve-element residue types.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES raw_station_code_card` and the printed proof in the machine-generated audit.

## `station_wire_composition`

Source: `IndependentDuodenary/StationCodec.lean`. Compilation: **passed**.

```lean
theorem station_wire_composition (outer inner : StationExpr) :
    composeStationWire (encodeStationExpression outer) (encodeStationExpression inner) =
      some (encodeStationExpression (.compose outer inner))
```

Proof method: Parse both encoded parameters and expand the composition compiler constructor.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES station_wire_composition` and the printed proof in the machine-generated audit.

## `station_wire_inverse`

Source: `IndependentDuodenary/StationCodec.lean`. Compilation: **passed**.

```lean
theorem station_wire_inverse (e : StationExpr) :
    invertStationWire (encodeStationExpression e) = some (encodeStationExpression (.invert e))
```

Proof method: Parse the encoded parameter and expand the inverse compiler constructor.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES station_wire_inverse` and the printed proof in the machine-generated audit.

## `reject_nonunit_station_code`

Source: `IndependentDuodenary/StationCodec.lean`. Compilation: **passed**.

```lean
theorem reject_nonunit_station_code : parseStationParameter (2, 0) = none
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES reject_nonunit_station_code` and the printed proof in the machine-generated audit.

## `reflection_example_wire`

Source: `IndependentDuodenary/StationCodec.lean`. Compilation: **passed**.

```lean
theorem reflection_example_wire : encodeStationExpression reflectionConjugationExample = (1, 11)
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES reflection_example_wire` and the printed proof in the machine-generated audit.

## `scale_shift_example_wire`

Source: `IndependentDuodenary/StationCodec.lean`. Compilation: **passed**.

```lean
theorem scale_shift_example_wire : encodeStationExpression scaleAfterShiftExample = (5, 3)
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES scale_shift_example_wire` and the printed proof in the machine-generated audit.

## `protected_station_wire_recovery`

Source: `IndependentDuodenary/StationCodec.lean`. Compilation: **passed**.

```lean
theorem protected_station_wire_recovery (c : StationWireCode) (received : ProtectedStationCode)
    (hfirst : wordDistance (protectStationWire c).1 received.1 ≤ 1)
    (hsecond : wordDistance (protectStationWire c).2 received.2 ≤ 1) :
    recoverStationWire received = c
```

Proof method: Apply the explicit repetition majority recovery theorem to both triples.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES protected_station_wire_recovery` and the printed proof in the machine-generated audit.

## `protected_station_semantic_recovery`

Source: `IndependentDuodenary/StationCodec.lean`. Compilation: **passed**.

```lean
theorem protected_station_semantic_recovery (e : StationExpr) (received : ProtectedStationCode)
    (hfirst : wordDistance (protectStationWire (encodeStationExpression e)).1 received.1 ≤ 1)
    (hsecond : wordDistance (protectStationWire (encodeStationExpression e)).2 received.2 ≤ 1) :
    decodeStationMeaning (recoverStationWire received) = some (Quotient.mk stationSemanticSetoid e)
```

Proof method: Recover the original wire pair, then apply station_expression_semantic_roundtrip.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES protected_station_semantic_recovery` and the printed proof in the machine-generated audit.

## `reflection_example_corruption_bound`

Source: `IndependentDuodenary/StationCodec.lean`. Compilation: **passed**.

```lean
theorem reflection_example_corruption_bound :
    wordDistance (protectStationWire (encodeStationExpression reflectionConjugationExample)).1
      reflectionExampleCorruption.1 ≤ 1 ∧
    wordDistance (protectStationWire (encodeStationExpression reflectionConjugationExample)).2
      reflectionExampleCorruption.2 ≤ 1
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES reflection_example_corruption_bound` and the printed proof in the machine-generated audit.

## `reflection_example_corruption_recovery`

Source: `IndependentDuodenary/StationCodec.lean`. Compilation: **passed**.

```lean
theorem reflection_example_corruption_recovery :
    decodeStationMeaning (recoverStationWire reflectionExampleCorruption) =
      some (Quotient.mk stationSemanticSetoid reflectionConjugationExample)
```

Proof method: Apply the universal recovery theorem with the separately computed concrete error bounds.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES reflection_example_corruption_recovery` and the printed proof in the machine-generated audit.

## `worked_examples_same_output_at_two`

Source: `IndependentDuodenary/StationCodec.lean`. Compilation: **passed**.

```lean
theorem worked_examples_same_output_at_two :
    stationMeaning reflectionConjugationExample 2 = stationMeaning scaleAfterShiftExample 2
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES worked_examples_same_output_at_two` and the printed proof in the machine-generated audit.

## `worked_examples_different_meanings`

Source: `IndependentDuodenary/StationCodec.lean`. Compilation: **passed**.

```lean
theorem worked_examples_different_meanings :
    stationMeaning reflectionConjugationExample ≠ stationMeaning scaleAfterShiftExample
```

Proof method: Semantic equality would imply equal codes, contradicted by the computed distinct wire pairs.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES worked_examples_different_meanings` and the printed proof in the machine-generated audit.

## `source_shift_expression_add`

Source: `IndependentDuodenary/StationCodec.lean`. Compilation: **passed**.

```lean
theorem source_shift_expression_add {K : Type*} [AddMonoid K]
    (χ : K →+ ZMod 2) (h g : K) :
    stationMeaning (sourceShiftExpression χ (h + g)) =
      stationMeaning (.compose (sourceShiftExpression χ h) (sourceShiftExpression χ g))
```

Proof method: Compiler equality, addition preservation of the chosen binary bridge, and additive commutativity.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES source_shift_expression_add` and the printed proof in the machine-generated audit.

## `source_shift_observable_equivariance`

Source: `IndependentDuodenary/StationCodec.lean`. Compilation: **passed**.

```lean
theorem source_shift_observable_equivariance {M K W : Type*} [AddMonoid K]
    (χ : K →+ ZMod 2) (label : M × W → ZMod 12) (h : K) (q : ExactKey M K W) :
    stationMeaning (sourceShiftExpression χ h) (residueAnswerTwelve χ label q) =
      residueAnswerTwelve χ label (translateKey h q)
```

Proof method: Evaluate the grammar shift and apply the previously proved residue_folding_twelve.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES source_shift_observable_equivariance` and the printed proof in the machine-generated audit.

## `affine_permutation_compose`

Source: `IndependentDuodenary/StationGrammar.lean`. Compilation: **passed**.

```lean
theorem affine_permutation_compose (p q : AffineStationParameter) :
    affineStationPermutation (affineStationCompose p q) =
      affineStationPermutation p * affineStationPermutation q
```

Proof method: Permutation extensionality and the proved affine composition formula.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES affine_permutation_compose` and the printed proof in the machine-generated audit.

## `affine_permutation_inverse`

Source: `IndependentDuodenary/StationGrammar.lean`. Compilation: **passed**.

```lean
theorem affine_permutation_inverse (p : AffineStationParameter) :
    affineStationPermutation (affineStationInverse p) = (affineStationPermutation p)⁻¹
```

Proof method: Permutation extensionality and expansion of the unit-affine inverse.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES affine_permutation_inverse` and the printed proof in the machine-generated audit.

## `station_compile_correct`

Source: `IndependentDuodenary/StationGrammar.lean`. Compilation: **passed**.

```lean
theorem station_compile_correct (e : StationExpr) :
    affineStationPermutation (compileStation e) = stationMeaning e
```

Proof method: Structural induction over every grammar constructor; affine composition and inverse laws.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES station_compile_correct` and the printed proof in the machine-generated audit.

## `compile_parameter_expression`

Source: `IndependentDuodenary/StationGrammar.lean`. Compilation: **passed**.

```lean
theorem compile_parameter_expression (p : AffineStationParameter) :
    compileStation (expressionFromParameter p) = p
```

Proof method: Expand the canonical shift/scale expression and simplify its affine parameter.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES compile_parameter_expression` and the printed proof in the machine-generated audit.

## `station_normalization_meaning`

Source: `IndependentDuodenary/StationGrammar.lean`. Compilation: **passed**.

```lean
theorem station_normalization_meaning (e : StationExpr) :
    stationMeaning (normalizeStation e) = stationMeaning e
```

Proof method: Compiler correctness followed by compile_parameter_expression.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES station_normalization_meaning` and the printed proof in the machine-generated audit.

## `station_normalization_idempotent`

Source: `IndependentDuodenary/StationGrammar.lean`. Compilation: **passed**.

```lean
theorem station_normalization_idempotent (e : StationExpr) :
    normalizeStation (normalizeStation e) = normalizeStation e
```

Proof method: Compile the canonical expression and simplify the second normalization.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES station_normalization_idempotent` and the printed proof in the machine-generated audit.

## `station_meaning_iff_compiled`

Source: `IndependentDuodenary/StationGrammar.lean`. Compilation: **passed**.

```lean
theorem station_meaning_iff_compiled (e f : StationExpr) :
    stationMeaning e = stationMeaning f ↔ compileStation e = compileStation f
```

Proof method: Compiler correctness and injectivity of the affine permutation parameterization.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES station_meaning_iff_compiled` and the printed proof in the machine-generated audit.

## `same_station_meaning_correct`

Source: `IndependentDuodenary/StationGrammar.lean`. Compilation: **passed**.

```lean
theorem same_station_meaning_correct (e f : StationExpr) :
    sameStationMeaning e f = true ↔ stationMeaning e = stationMeaning f
```

Proof method: The equality decision on compiled parameters is equivalent to equality of whole permutations.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES same_station_meaning_correct` and the printed proof in the machine-generated audit.

## `meaning_parameter_roundtrip`

Source: `IndependentDuodenary/StationGrammar.lean`. Compilation: **passed**.

```lean
theorem meaning_parameter_roundtrip (p : AffineStationParameter) :
    compileMeaningClass (parameterMeaningClass p) = p
```

Proof method: compile_parameter_expression instantiated on the semantic class encoder.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES meaning_parameter_roundtrip` and the printed proof in the machine-generated audit.

## `parameter_meaning_roundtrip`

Source: `IndependentDuodenary/StationGrammar.lean`. Compilation: **passed**.

```lean
theorem parameter_meaning_roundtrip (q : StationMeaningClass) :
    parameterMeaningClass (compileMeaningClass q) = q
```

Proof method: Quotient induction, normalization preservation and Quotient.sound.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES parameter_meaning_roundtrip` and the printed proof in the machine-generated audit.

## `station_meaning_class_card`

Source: `IndependentDuodenary/StationGrammar.lean`. Compilation: **passed**.

```lean
theorem station_meaning_class_card : Nat.card StationMeaningClass = 48
```

Proof method: The explicit semantic-class/parameter equivalence and the affine parameter cardinality.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES station_meaning_class_card` and the printed proof in the machine-generated audit.

## `reflection_example_parameters`

Source: `IndependentDuodenary/StationGrammar.lean`. Compilation: **passed**.

```lean
theorem reflection_example_parameters : compileStation reflectionConjugationExample = (1, 11)
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES reflection_example_parameters` and the printed proof in the machine-generated audit.

## `reflection_example_meaning`

Source: `IndependentDuodenary/StationGrammar.lean`. Compilation: **passed**.

```lean
theorem reflection_example_meaning :
    stationMeaning reflectionConjugationExample = stationMeaning (.shift 11)
```

Proof method: Equality of compiled parameters implies semantic equality.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES reflection_example_meaning` and the printed proof in the machine-generated audit.

## `scale_shift_example_parameters`

Source: `IndependentDuodenary/StationGrammar.lean`. Compilation: **passed**.

```lean
theorem scale_shift_example_parameters : compileStation scaleAfterShiftExample = (multiplyFiveParameter.1, 3)
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES scale_shift_example_parameters` and the printed proof in the machine-generated audit.

## `scale_shift_example_at_two`

Source: `IndependentDuodenary/StationGrammar.lean`. Compilation: **passed**.

```lean
theorem scale_shift_example_at_two : stationMeaning scaleAfterShiftExample 2 = 1
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES scale_shift_example_at_two` and the printed proof in the machine-generated audit.

## `twelveCRT_bijective`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem twelveCRT_bijective : Function.Bijective twelveCRT
```

Proof method: Bijectivity of the coprime Chinese remainder ring equivalence.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES twelveCRT_bijective` and the printed proof in the machine-generated audit.

## `crt_reconstruct_coordinates`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem crt_reconstruct_coordinates : ∀ p, twelveCRT (crtReconstruct p) = p
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES crt_reconstruct_coordinates` and the printed proof in the machine-generated audit.

## `twelveCRT_inverse_formula`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem twelveCRT_inverse_formula (p : ZMod 4 × ZMod 3) :
    twelveCRT.symm p = crtReconstruct p
```

Proof method: Apply CRT injectivity and the proved coordinate reconstruction identity.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES twelveCRT_inverse_formula` and the printed proof in the machine-generated audit.

## `crt_reconstruct_original`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem crt_reconstruct_original (x : ZMod 12) : crtReconstruct (twelveCRT x) = x
```

Proof method: Rewrite reconstruction as the CRT inverse and use its left inverse law.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES crt_reconstruct_original` and the printed proof in the machine-generated audit.

## `rotation_twelve_returns`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem rotation_twelve_returns : ∀ x, (rotateStation^[12]) x = x
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES rotation_twelve_returns` and the printed proof in the machine-generated audit.

## `rotation_no_shorter_period`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem rotation_no_shorter_period :
    ∀ k : Fin 12, (∀ x, (rotateStation^[k.val]) x = x) ↔ k = 0
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES rotation_no_shorter_period` and the printed proof in the machine-generated audit.

## `reflection_involution`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem reflection_involution (x : ZMod 12) : reflectStation (reflectStation x) = x
```

Proof method: Double negation in ZMod 12.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES reflection_involution` and the printed proof in the machine-generated audit.

## `reflection_rotation_relation`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem reflection_rotation_relation (x : ZMod 12) :
    reflectStation (rotateStation (reflectStation x)) = x - 1
```

Proof method: Negation and commutativity in the additive residue group.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES reflection_rotation_relation` and the printed proof in the machine-generated audit.

## `antipode_involution`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem antipode_involution : ∀ x, antipode (antipode x) = x
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES antipode_involution` and the printed proof in the machine-generated audit.

## `antipode_fixed_point_free`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem antipode_fixed_point_free : ∀ x, antipode x ≠ x
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES antipode_fixed_point_free` and the printed proof in the machine-generated audit.

## `antipodal_pair_card`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem antipodal_pair_card : ∀ i, (antipodalPair i).card = 2
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES antipodal_pair_card` and the printed proof in the machine-generated audit.

## `antipodal_pairs_cover`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem antipodal_pairs_cover : ∀ x : ZMod 12, ∃ i, x ∈ antipodalPair i
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES antipodal_pairs_cover` and the printed proof in the machine-generated audit.

## `antipodal_pairs_disjoint`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem antipodal_pairs_disjoint :
    ∀ i j : Fin 6, i ≠ j → Disjoint (antipodalPair i) (antipodalPair j)
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES antipodal_pairs_disjoint` and the printed proof in the machine-generated audit.

## `antipodal_pairs_injective`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem antipodal_pairs_injective : Function.Injective antipodalPair
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES antipodal_pairs_injective` and the printed proof in the machine-generated audit.

## `antipodal_pair_family_card`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem antipodal_pair_family_card :
    (Finset.univ.image antipodalPair).card = 6
```

Proof method: Injectivity of the pair parameterization and cardinality of Fin 6.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES antipodal_pair_family_card` and the printed proof in the machine-generated audit.

## `directed_difference_translation`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem directed_difference_translation (a b k : ZMod 12) :
    directedDifference (a + k) (b + k) = directedDifference a b
```

Proof method: Cancellation of the common additive translation.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES directed_difference_translation` and the printed proof in the machine-generated audit.

## `cyclic_distance_translation`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem cyclic_distance_translation (a b k : ZMod 12) :
    cyclicDistance (a + k) (b + k) = cyclicDistance a b
```

Proof method: Cancellation inside the modular difference.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES cyclic_distance_translation` and the printed proof in the machine-generated audit.

## `cyclic_distance_reflection`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem cyclic_distance_reflection :
    ∀ a b : ZMod 12, cyclicDistance (-a) (-b) = cyclicDistance a b
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES cyclic_distance_reflection` and the printed proof in the machine-generated audit.

## `cyclic_distance_bound`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem cyclic_distance_bound : ∀ a b : ZMod 12, cyclicDistance a b ≤ 6
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES cyclic_distance_bound` and the printed proof in the machine-generated audit.

## `cyclic_distance_all_values`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem cyclic_distance_all_values :
    ∀ d : Fin 7, ∃ x : ZMod 12, cyclicDistance 0 x = d.val
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES cyclic_distance_all_values` and the printed proof in the machine-generated audit.

## `dihedral_action_one`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem dihedral_action_one (x : ZMod 12) : dihedralStationAction 1 x = x
```

Proof method: Unfold the identity rotation and add zero.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES dihedral_action_one` and the printed proof in the machine-generated audit.

## `dihedral_action_mul`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem dihedral_action_mul (g h : DihedralGroup 12) (x : ZMod 12) :
    dihedralStationAction (g * h) x = dihedralStationAction g (dihedralStationAction h x)
```

Proof method: Four constructor cases and ring normalization.

Axioms: `propext, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES dihedral_action_mul` and the printed proof in the machine-generated audit.

## `dihedral_zero_one_separates`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem dihedral_zero_one_separates : ∀ g h : DihedralGroup 12,
    dihedralStationAction g 0 = dihedralStationAction h 0 →
    dihedralStationAction g 1 = dihedralStationAction h 1 → g = h
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES dihedral_zero_one_separates` and the printed proof in the machine-generated audit.

## `dihedral_station_hom_injective`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem dihedral_station_hom_injective : Function.Injective dihedralStationHom
```

Proof method: Evaluate equal permutations at 0 and 1; dihedral_zero_one_separates.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES dihedral_station_hom_injective` and the printed proof in the machine-generated audit.

## `dihedral_twelve_card`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem dihedral_twelve_card : Fintype.card (DihedralGroup 12) = 24
```

Proof method: Specialize the cardinality theorem for the standard dihedral group.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES dihedral_twelve_card` and the printed proof in the machine-generated audit.

## `dihedral_preserves_cyclic_distance`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem dihedral_preserves_cyclic_distance (g : DihedralGroup 12) (a b : ZMod 12) :
    cyclicDistance (dihedralStationAction g a) (dihedralStationAction g b) =
      cyclicDistance a b
```

Proof method: Rotation/translation invariance and reflection invariance.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES dihedral_preserves_cyclic_distance` and the printed proof in the machine-generated audit.

## `cyclic_zero_one_separates`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem cyclic_zero_one_separates : ∀ x y : ZMod 12,
    cyclicDistance 0 x = cyclicDistance 0 y →
    cyclicDistance 1 x = cyclicDistance 1 y → x = y
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES cyclic_zero_one_separates` and the printed proof in the machine-generated audit.

## `cyclic_distance_one_iff`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem cyclic_distance_one_iff : ∀ a b : ZMod 12,
    cyclicDistance a b = 1 ↔ b = a + 1 ∨ b = a - 1
```

Proof method: Kernel-checked decidable computation (decide).

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES cyclic_distance_one_iff` and the printed proof in the machine-generated audit.

## `dihedral_matches_directed_edge`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem dihedral_matches_directed_edge (a b : ZMod 12) (hab : cyclicDistance a b = 1) :
    ∃ g : DihedralGroup 12, dihedralStationAction g 0 = a ∧ dihedralStationAction g 1 = b
```

Proof method: Use the distance-one characterization to construct a rotation or reflection.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES dihedral_matches_directed_edge` and the printed proof in the machine-generated audit.

## `cyclic_isometry_is_dihedral`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem cyclic_isometry_is_dihedral (f : ZMod 12 → ZMod 12)
    (hf : ∀ a b, cyclicDistance (f a) (f b) = cyclicDistance a b) :
    ∃ g : DihedralGroup 12, f = dihedralStationAction g
```

Proof method: Match the images of 0 and 1, then use the two-distance separation theorem at every point.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES cyclic_isometry_is_dihedral` and the printed proof in the machine-generated audit.

## `cyclic_station_isometry_card`

Source: `IndependentDuodenary/TwelveStateStructure.lean`. Compilation: **passed**.

```lean
theorem cyclic_station_isometry_card : Nat.card CyclicStationIsometry = 24
```

Proof method: Bijection between all cyclic isometries and DihedralGroup 12.

Axioms: `propext, Classical.choice, Quot.sound`.

Dependencies: see `DIRECT DEPENDENCIES cyclic_station_isometry_card` and the printed proof in the machine-generated audit.
