import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Powerset

/-! Binary vectors and their Hamming-weight layers, independent of external sources. -/
namespace IndependentDuodenary

abbrev BinaryVector := Fin 12 → ZMod 2

def support (v : BinaryVector) : Finset (Fin 12) :=
  Finset.univ.filter (fun i => v i ≠ 0)

def bitWeight (v : BinaryVector) : ℕ := (support v).card

def weightLayer (k : ℕ) : Finset BinaryVector :=
  Finset.univ.filter (fun v => bitWeight v = k)

theorem binary_nonzero_eq_one : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide

theorem bitWeight_le (v : BinaryVector) : bitWeight v ≤ 12 := by
  exact (support v).card_le_univ

theorem maximum_weight_iff (v : BinaryVector) :
    bitWeight v = 12 ↔ ∀ i, v i = 1 := by
  constructor
  · intro h i
    have hs : support v = Finset.univ := Finset.eq_univ_of_card _ h
    have hi : i ∈ support v := by rw [hs]; exact Finset.mem_univ i
    exact binary_nonzero_eq_one _ (Finset.mem_filter.mp hi).2
  · intro h
    have hs : support v = Finset.univ := by
      ext i
      simp [support, h i]
    simp [bitWeight, hs]

/-- The support map bijects a weight layer with the k-element subsets of Fin 12. -/
theorem weightLayer_card (k : ℕ) : (weightLayer k).card = Nat.choose 12 k := by
  rw [← show Fintype.card (Fin 12) = 12 from rfl, ← Finset.card_univ,
    ← Finset.card_powersetCard]
  apply Finset.card_bij (fun v _ => support v)
  · intro v hv
    simp only [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, (Finset.mem_filter.mp hv).2⟩
  · intro v hv w hw heq
    funext i
    have hi : (v i ≠ 0) ↔ (w i ≠ 0) := by
      have hm := Finset.ext_iff.mp heq i
      simpa [support] using hm
    by_cases h : v i = 0
    · have hw0 : w i = 0 := by
        by_contra hn
        exact (hi.mpr hn) h
      rw [h, hw0]
    · rw [binary_nonzero_eq_one _ h, binary_nonzero_eq_one _ (hi.mp h)]
  · intro s hs
    let v : BinaryVector := fun i => if i ∈ s then 1 else 0
    have hv : support v = s := by
      ext i
      simp [support, v]
    refine ⟨v, ?_, hv⟩
    simp only [weightLayer, Finset.mem_filter, Finset.mem_univ, true_and]
    change (support v).card = k
    rw [hv]
    exact (Finset.mem_powersetCard.mp hs).2

theorem single_bit_count : (weightLayer 1).card = 12 := by
  rw [weightLayer_card]; decide

theorem all_bits_count : (weightLayer 12).card = 1 := by
  rw [weightLayer_card]; decide

theorem zero_bits_count : (weightLayer 0).card = 1 := by
  rw [weightLayer_card]; decide

end IndependentDuodenary
