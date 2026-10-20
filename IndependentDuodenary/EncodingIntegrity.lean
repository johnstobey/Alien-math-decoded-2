import IndependentDuodenary.BinaryStructure

/-! Exact decoding, finite capacity, and bounded-corruption uniqueness. -/
namespace IndependentDuodenary

/-- An exact decoder on semantic classes forbids collisions between different meanings. -/
theorem semantic_decoder_no_collision {L S : Type*} (r : Setoid L)
    (encode : L → S) (decode : S → Quotient r)
    (h : ∀ x, decode (encode x) = Quotient.mk r x)
    (x y : L) (heq : encode x = encode y) : r.r x y := by
  apply Quotient.exact
  exact (h x).symm.trans ((congrArg decode heq).trans (h y))

theorem exact_decoder_injective {M S : Type*} (encode : M → S) (decode : S → M)
    (h : Function.LeftInverse decode encode) : Function.Injective encode := h.injective

theorem exact_decoder_capacity {M S : Type*} [Fintype M] [Fintype S]
    (encode : M → S) (decode : S → M) (h : Function.LeftInverse decode encode) :
    Fintype.card M ≤ Fintype.card S :=
  Fintype.card_le_of_injective encode h.injective

theorem no_exact_decoder_over_capacity {M S : Type*} [Fintype M] [Fintype S]
    (hcard : Fintype.card S < Fintype.card M) (encode : M → S) (decode : S → M) :
    ¬ Function.LeftInverse decode encode := by
  intro h
  exact (Nat.not_le_of_gt hcard) (exact_decoder_capacity encode decode h)

theorem no_infinite_exact_finite_decoder {M S : Type*} [Infinite M] [Finite S]
    (encode : M → S) (decode : S → M) : ¬ Function.LeftInverse decode encode := by
  intro h
  exact not_injective_infinite_finite encode h.injective

theorem twelve_symbol_word_capacity (n : ℕ) :
    Fintype.card (Fin n → ZMod 12) = 12 ^ n := by
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]

/-- Variable-length structure already permits an unbounded family over a fixed alphabet. -/
def encodeNaturalWord (n : ℕ) : List (ZMod 12) := List.replicate n 0

theorem natural_word_length_left_inverse :
    Function.LeftInverse List.length encodeNaturalWord := by
  intro n
  simp [encodeNaturalWord]

theorem natural_word_encoding_injective : Function.Injective encodeNaturalWord :=
  natural_word_length_left_inverse.injective

variable {ι Alphabet : Type*} [Fintype ι] [DecidableEq Alphabet]

def wordDistance (x y : ι → Alphabet) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ y i)).card

theorem word_distance_self (x : ι → Alphabet) : wordDistance x x = 0 := by
  simp [wordDistance]

theorem word_distance_comm (x y : ι → Alphabet) : wordDistance x y = wordDistance y x := by
  simp only [wordDistance, ne_comm]

theorem word_distance_triangle (x y z : ι → Alphabet) :
    wordDistance x z ≤ wordDistance x y + wordDistance y z := by
  classical
  have hs : Finset.univ.filter (fun i => x i ≠ z i) ⊆
      Finset.univ.filter (fun i => x i ≠ y i) ∪
      Finset.univ.filter (fun i => y i ≠ z i) := by
    intro i hi
    have hxz := (Finset.mem_filter.mp hi).2
    by_cases hxy : x i = y i
    · apply Finset.mem_union.mpr
      right
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, fun hyz => hxz (hxy.trans hyz)⟩
    · apply Finset.mem_union.mpr
      left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hxy⟩
  exact (Finset.card_mono hs).trans (Finset.card_union_le _ _)

/-- Any two codewords within t errors must coincide if their separation exceeds 2t. -/
theorem bounded_error_unique (C : Set (ι → Alphabet)) (d t : ℕ)
    (hsep : ∀ a ∈ C, ∀ b ∈ C, a ≠ b → d ≤ wordDistance a b)
    (hbound : 2 * t < d) (a b received : ι → Alphabet)
    (ha : a ∈ C) (hb : b ∈ C)
    (hea : wordDistance a received ≤ t) (heb : wordDistance b received ≤ t) : a = b := by
  by_contra hab
  have hlower := hsep a ha b hb hab
  have hupper := word_distance_triangle a received b
  rw [word_distance_comm received b] at hupper
  have hd : d ≤ t + t := hlower.trans (hupper.trans (Nat.add_le_add hea heb))
  exact (Nat.not_le_of_gt hbound) (by simpa only [two_mul] using hd)

/-- This statement applies to any concrete decoder satisfying the stated radius guarantee. -/
theorem bounded_error_decoder_correct (C : Set (ι → Alphabet)) (d t : ℕ)
    (hsep : ∀ a ∈ C, ∀ b ∈ C, a ≠ b → d ≤ wordDistance a b)
    (hbound : 2 * t < d) (decode : (ι → Alphabet) → (ι → Alphabet))
    (received sent : ι → Alphabet) (hsent : sent ∈ C)
    (hnoise : wordDistance sent received ≤ t)
    (hdecode : decode received ∈ C)
    (hradius : wordDistance (decode received) received ≤ t) : decode received = sent :=
  bounded_error_unique C d t hsep hbound _ _ received hdecode hsent hradius hnoise

def repetitionWord (n : ℕ) (a : Alphabet) : Fin n → Alphabet := fun _ => a

theorem repetition_word_distance (n : ℕ) (a b : Alphabet) :
    wordDistance (repetitionWord n a) (repetitionWord n b) = if a = b then 0 else n := by
  by_cases h : a = b <;> simp [wordDistance, repetitionWord, h]

omit [DecidableEq Alphabet] in
theorem repetition_word_injective {n : ℕ} (hn : 0 < n) :
    Function.Injective (repetitionWord (Alphabet := Alphabet) n) := by
  intro a b h
  exact congrFun h ⟨0, hn⟩

/-- A supplied code with explicit distance n; it is not merely an assumed separation. -/
theorem repetition_code_separation (n : ℕ) :
    ∀ a ∈ Set.range (repetitionWord (Alphabet := Alphabet) n),
      ∀ b ∈ Set.range (repetitionWord (Alphabet := Alphabet) n),
      a ≠ b → n ≤ wordDistance a b := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
  have hne : a ≠ b := fun h => hab (congrArg (repetitionWord n) h)
  rw [repetition_word_distance, if_neg hne]

theorem repetition_three_one_error_unique (a b : Alphabet) (received : Fin 3 → Alphabet)
    (ha : wordDistance (repetitionWord 3 a) received ≤ 1)
    (hb : wordDistance (repetitionWord 3 b) received ≤ 1) : a = b := by
  have hwords := bounded_error_unique (Set.range (repetitionWord (Alphabet := Alphabet) 3)) 3 1
    (repetition_code_separation 3) (by decide)
    (repetitionWord 3 a) (repetitionWord 3 b) received ⟨a, rfl⟩ ⟨b, rfl⟩ ha hb
  exact repetition_word_injective (by decide : 0 < 3) hwords

/-- Two distinct corrupted positions force distance at least two. -/
theorem two_errors_distance_lower (x y : ι → Alphabet) (i j : ι) (hij : i ≠ j)
    (hi : x i ≠ y i) (hj : x j ≠ y j) : 2 ≤ wordDistance x y := by
  classical
  have hs : ({i, j} : Finset ι) ⊆ Finset.univ.filter (fun k => x k ≠ y k) := by
    intro k hk
    have hk' : k = i ∨ k = j := by simpa using hk
    rcases hk' with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  have hc : ({i, j} : Finset ι).card = 2 := by simp [hij]
  rw [← hc]
  exact Finset.card_mono hs

theorem at_most_one_error_pair (x y : ι → Alphabet) (i j : ι) (hij : i ≠ j)
    (hnoise : wordDistance x y ≤ 1) : x i = y i ∨ x j = y j := by
  by_cases hi : x i = y i
  · exact Or.inl hi
  · right
    by_contra hj
    have htwo := two_errors_distance_lower x y i j hij hi hj
    exact (Nat.not_succ_le_self 1) (htwo.trans hnoise)

def tripleMajority (received : Fin 3 → Alphabet) : Alphabet :=
  if received 0 = received 1 then received 0 else received 2

/-- An explicit encoder and decoder recover every symbol after at most one error. -/
theorem repetition_majority_recovery (a : Alphabet) (received : Fin 3 → Alphabet)
    (hnoise : wordDistance (repetitionWord 3 a) received ≤ 1) :
    tripleMajority received = a := by
  have h01 := at_most_one_error_pair (repetitionWord 3 a) received 0 1 (by decide) hnoise
  have h02 := at_most_one_error_pair (repetitionWord 3 a) received 0 2 (by decide) hnoise
  have h12 := at_most_one_error_pair (repetitionWord 3 a) received 1 2 (by decide) hnoise
  simp only [repetitionWord] at h01 h02 h12
  by_cases h : received 0 = received 1
  · rw [tripleMajority, if_pos h]
    rcases h01 with ha | ha
    · exact ha.symm
    · exact h.trans ha.symm
  · rw [tripleMajority, if_neg h]
    rcases h02 with ha0 | ha2
    · rcases h12 with ha1 | ha2
      · exact False.elim (h (ha0.symm.trans ha1))
      · exact ha2.symm
    · exact ha2.symm

end IndependentDuodenary
