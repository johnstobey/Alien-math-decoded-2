import IndependentDuodenary.TwelveStateStructure

/-! Source-defined shared state and explicit consistency boundaries.
Locators and ambiguities are recorded in verification/DUAL_RING_FORMAL_MAP.md. -/
namespace IndependentDuodenary

def AntipodallyClosed (s : Set (ZMod 12)) : Prop :=
  ∀ k, k ∈ s ↔ antipode k ∈ s

structure DualRingEvent where
  sector : ZMod 12
  revision : ZMod 12
  winding : ZMod 12
  constraint : Finset (ZMod 12)
  constraint_closed : AntipodallyClosed (constraint : Set (ZMod 12))
  domain : Fin 4
  partition : Fin 2

/-- II.1–4: pointer and admissibility are derived, eliminating inconsistent duplicates.
Tags index the four domain labels and two partition labels in the source order. -/
structure DualRingSourceState where
  revision : ZMod 12
  winding : ZMod 12
  constraints : Set {s : Set (ZMod 12) // AntipodallyClosed s}
  ledger : List DualRingEvent

def dualRingPointer (x : DualRingSourceState) : ZMod 12 := x.winding + x.revision

def dualRingAdmissible (x : DualRingSourceState) : Set (ZMod 12) :=
  {k | ∀ p ∈ x.constraints, k ∈ p.val}

theorem dual_ring_admissible_closed (x : DualRingSourceState) :
    AntipodallyClosed (dualRingAdmissible x) := by
  intro k
  exact ⟨fun h p hp => (p.property k).mp (h p hp),
    fun h p hp => (p.property k).mpr (h p hp)⟩

/-- V.4 retaining winding: compensation is unique; zero compensation requires zero winding. -/
theorem clearing_pointer_reset_classification {G : Type*} [AddGroup G] (n r : G) :
    ((0 : G) = n + r ↔ r = -n) ∧ ((0 : G) = n + 0 ↔ n = 0) := by
  constructor
  · constructor
    · intro h
      calc
        r = -n + (n + r) := by simp
        _ = -n + 0 := by rw [← h]
        _ = -n := add_zero _
    · intro h
      simp [h]
  · simp [eq_comm]

/-- IV.2.2 has no ring-valued midpoint for this source-defined quincunx. -/
theorem quincunx_midpoint_obstruction : ¬ ∃ m : ZMod 12, m + m = 5 := by decide

/-- A common anchor and antipodal closure alone do not synchronize views. -/
theorem dual_ring_common_anchor_insufficient :
    ∃ A B : Set (ZMod 12), AntipodallyClosed A ∧ AntipodallyClosed B ∧
      (0 : ZMod 12) ∈ A ∧ (0 : ZMod 12) ∈ B ∧ A ≠ B := by
  refine ⟨Set.univ, {0, 6}, ?_, ?_, Set.mem_univ _, ?_, ?_⟩
  · intro k
    simp
  · intro k
    change (k = 0 ∨ k = 6) ↔ (k + 6 = 0 ∨ k + 6 = 6)
    exact (by decide : ∀ k : ZMod 12,
      (k = 0 ∨ k = 6) ↔ (k + 6 = 0 ∨ k + 6 = 6)) k
  · exact Or.inl rfl
  · intro h
    have h1 : (1 : ZMod 12) ∈ ({0, 6} : Set (ZMod 12)) := h ▸ Set.mem_univ _
    exact (by decide : ¬ ((1 : ZMod 12) = 0 ∨ (1 : ZMod 12) = 6)) h1

/-- Exact additional condition needed beyond shared-anchor membership, for any carrier. -/
theorem dual_view_integration_iff {X : Type*} (a : X → X) (z : X) (A B : Set X)
    (hA : ∀ x, x ∈ A ↔ a x ∈ A) (hB : ∀ x, x ∈ B ↔ a x ∈ B) :
    A ∩ B = {z, a z} ↔
      (z ∈ A ∧ z ∈ B) ∧ ∀ x, x ≠ z → x ≠ a z → x ∉ A ∨ x ∉ B := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have hz : z ∈ ({z, a z} : Set X) := Or.inl rfl
      rw [← h] at hz
      exact hz
    · intro x hx hax
      by_cases hm : x ∈ A
      · right
        intro hb
        have hp : x ∈ ({z, a z} : Set X) := h ▸ (show x ∈ A ∩ B from ⟨hm, hb⟩)
        exact hp.elim hx hax
      · exact Or.inl hm
  · rintro ⟨hz, he⟩
    ext x
    constructor
    · intro hx
      by_cases h : x = z
      · exact Or.inl h
      · by_cases h' : x = a z
        · exact Or.inr h'
        · exact False.elim ((he x h h').elim (fun hn => hn hx.1) (fun hn => hn hx.2))
    · intro hx
      rcases hx with rfl | rfl
      · exact hz
      · exact And.intro ((hA z).mp hz.1) ((hB z).mp hz.2)

end IndependentDuodenary
