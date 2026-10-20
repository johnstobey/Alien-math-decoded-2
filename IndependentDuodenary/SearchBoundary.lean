import IndependentDuodenary.MillenniumBridge
import Mathlib.Data.List.FinRange

/-! Exact decision for one orbit and a global lower bound for orbit covers. -/
namespace IndependentDuodenary

def protocolReachabilityCheck {r : ℕ} (h : RegisterTranslation r)
    (q x : RegisterState r) : Bool :=
  (List.finRange 12).any (fun k => decide (((registerStep h)^[k.val]) q = x))

theorem protocol_reachability_check_correct {r : ℕ} (h : RegisterTranslation r)
    (q x : RegisterState r) :
    protocolReachabilityCheck h q x = true ↔ ∃ n : ℕ, ((registerStep h)^[n]) q = x := by
  rw [protocol_reachability_iff_bounded_search]
  simp [protocolReachabilityCheck, List.mem_finRange]

theorem protocol_reachability_check_rejects_iff {r : ℕ} (h : RegisterTranslation r)
    (q x : RegisterState r) :
    protocolReachabilityCheck h q x = false ↔ ¬ ∃ n : ℕ, ((registerStep h)^[n]) q = x := by
  rw [← protocol_reachability_check_correct]
  cases protocolReachabilityCheck h q x <;> simp

/-- Covering all states requires many distinct orbit seeds, despite the short periods. -/
theorem protocol_global_orbit_cover_bound {r : ℕ} (h : RegisterTranslation r)
    (seeds : Finset (RegisterState r))
    (covers : ∀ x : RegisterState r, ∃ q ∈ seeds, x ∈ protocolOrbitCandidates h q) :
    49152 ^ r ≤ 12 * seeds.card := by
  letI : Fintype RepresentedKey := Fintype.ofEquiv CanonicalCoefficients keyCoefficientEquiv.symm
  let visit : ({q // q ∈ seeds} × Fin 12) → RegisterState r :=
    fun z => ((registerStep h)^[z.2.val]) z.1.val
  have hs : Function.Surjective visit := by
    intro x
    obtain ⟨q, hq, hx⟩ := covers x
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hx
    exact ⟨(⟨q, hq⟩, k), hk⟩
  have hc := Fintype.card_le_of_surjective visit hs
  have count : Fintype.card (RegisterState r) = 49152 ^ r := by
    rw [← Nat.card_eq_fintype_card, complete_register_cardinality]
  rw [count] at hc
  simpa [Nat.mul_comm] using hc

theorem protocol_one_register_cover_needs_4096 (h : RegisterTranslation 1)
    (seeds : Finset (RegisterState 1))
    (covers : ∀ x : RegisterState 1, ∃ q ∈ seeds, x ∈ protocolOrbitCandidates h q) :
    4096 ≤ seeds.card := by
  have hc := protocol_global_orbit_cover_bound h seeds covers
  norm_num at hc
  omega

end IndependentDuodenary
