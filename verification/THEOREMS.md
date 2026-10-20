# Theorem-by-theorem audit

All names below are in namespace `IndependentDuodenary`. All 27 declarations compiled and passed the axiom audit. Exact elaborated propositions, proof terms, and direct dependency lists are in [axioms-and-proofs.txt](axioms-and-proofs.txt), under the matching theorem name and `DIRECT DEPENDENCIES` record. The Lean source propositions are reproduced below. Standard library infrastructure dependencies are included in that machine-generated record.

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
