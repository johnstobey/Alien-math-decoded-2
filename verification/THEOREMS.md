# Theorem-by-theorem audit

All names below are in namespace `IndependentDuodenary`. All 52 declarations compiled and passed the axiom audit. Exact elaborated propositions, proof terms, and direct dependency lists are in [axioms-and-proofs.txt](axioms-and-proofs.txt), under the matching theorem name and `DIRECT DEPENDENCIES` record. The Lean source propositions are reproduced below. Standard library infrastructure dependencies are included in that machine-generated record.

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
