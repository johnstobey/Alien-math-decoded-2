# Theorem-by-theorem audit

All names below are in namespace `IndependentDuodenary`. All 92 declarations compiled and passed the axiom audit. Exact elaborated propositions, proof terms, and direct dependency lists are in [axioms-and-proofs.txt](axioms-and-proofs.txt), under the matching theorem name and `DIRECT DEPENDENCIES` record. The Lean source propositions are reproduced below. Standard library infrastructure dependencies are included in that machine-generated record.

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
