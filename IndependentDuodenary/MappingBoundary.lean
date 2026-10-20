import IndependentDuodenary.ModularCore

/-!
# Boundary between arithmetic and source interpretation

The source-independent implication below is conditional. An external paper-to-model
correspondence requires separately defined source operations and a preservation proof.
-/

namespace IndependentDuodenary

theorem conditional_level_return
    (levels step : ℕ) (hLevels : levels = 12) (hStep : step = 3) :
    station (step * levels) = 0 := by
  subst levels
  subst step
  exact three_times_twelve_returns

/-- Operation preservation is a proof obligation, not an established source mapping. -/
def PreservesOperation {A B : Type*}
    (sourceOp : A → A → A) (targetOp : B → B → B) (f : A → B) : Prop :=
  ∀ x y, f (sourceOp x y) = targetOp (f x) (f y)

end IndependentDuodenary

namespace IndependentDuodenary

/-- An explicit internal mapping from natural addition to modular addition. -/
def stationMap : ℕ → ZMod 12 := station

theorem stationMap_preserves_addition :
    PreservesOperation Nat.add (fun x y : ZMod 12 => x + y) stationMap := by
  intro x y
  exact station_add x y

/-- Closure transfers along a surjective operation-preserving map. -/
theorem conditional_closure {A B : Type*}
    (sourceOp : A → A → A) (targetOp : B → B → B) (f : A → B)
    (S : Set A) (T : Set B)
    (hpres : PreservesOperation sourceOp targetOp f)
    (hclosed : ∀ x ∈ S, ∀ y ∈ S, sourceOp x y ∈ S)
    (himage : ∀ b, b ∈ T ↔ ∃ a ∈ S, f a = b) :
    ∀ x ∈ T, ∀ y ∈ T, targetOp x y ∈ T := by
  intro x hx y hy
  obtain ⟨a, ha, rfl⟩ := (himage x).mp hx
  obtain ⟨b, hb, rfl⟩ := (himage y).mp hy
  exact (himage _).mpr ⟨sourceOp a b, hclosed a ha b hb, hpres a b⟩

end IndependentDuodenary
