import IndependentDuodenary.SourceProjection
import Mathlib.Tactic.FinCases

/-! Explicit support reduction, surjective factorization, and uniqueness. -/
namespace IndependentDuodenary
open scoped BigOperators
variable {E X V : Type*} {k : ℕ}

/-- The support keeps the actual bit selected by the slope pattern. -/
def sourceSupportBlock [Zero V] [DecidableEq V] (b : FullBlock E X V) :
    ProjectedBlock E X V :=
  if b.firstSlope = 0 then
    if b.secondSlope = 0 then .omitted b.origin
    else .singleton b.origin .second b.secondSlope
  else if b.secondSlope = 0 then .singleton b.origin .first b.firstSlope
  else if b.firstSlope = b.secondSlope then .singleton b.origin .third b.firstSlope
  else .retained b.origin b.firstSlope b.secondSlope

theorem sourceSupportBlock_pullback [Zero V] [DecidableEq V] (b : FullBlock E X V) :
    pullbackBlock (sourceSupportBlock b) = b := by
  rcases b with ⟨e, a, d⟩
  by_cases ha : a = 0 <;> by_cases hd : d = 0 <;> by_cases had : a = d <;>
    simp_all [sourceSupportBlock, pullbackBlock]

theorem sourceSupportBlock_correction [Zero V] [DecidableEq V] (b : FullBlock E X V) :
    pullbackCorrection (sourceSupportBlock b) = (reduceFullBlock b).2 := by
  rcases b with ⟨e, a, d⟩
  by_cases ha : a = 0 <;> by_cases hd : d = 0 <;> by_cases had : a = d <;>
    simp_all [sourceSupportBlock, pullbackCorrection, reduceFullBlock, reduceEquation]

def reducedSourceTable [AddCommMonoid V] [DecidableEq V] (t : FullTable k E X V) :
    ProjectedTable k E X V :=
  ⟨fullReducedIntercept t, fun i => sourceSupportBlock (t.blocks i)⟩

/-- The two third-bit corrections cancel in the complete homogeneous intercept. -/
theorem pullback_reducedSourceTable [AddCommMonoid V] [DecidableEq V]
    (hDouble : ∀ v : V, v + v = 0) (t : FullTable k E X V) :
    pullbackTable (reducedSourceTable t) = t := by
  simp only [pullbackTable, reducedSourceTable]
  simp_rw [sourceSupportBlock_pullback, sourceSupportBlock_correction]
  cases t
  simp [fullReducedIntercept, add_assoc, hDouble]

theorem binary_module_double_zero [AddCommMonoid V] [Module (ZMod 2) V] (v : V) :
    v + v = 0 := by
  calc
    v + v = ((1 : ZMod 2) + 1) • v := by rw [add_smul, one_smul]
    _ = 0 := by rw [show (1 : ZMod 2) + 1 = 0 from by decide, zero_smul]

theorem binary_module_add_eq_zero_iff [AddCommMonoid V] [Module (ZMod 2) V]
    (a d : V) : a + d = 0 ↔ a = d := by
  constructor
  · intro h
    have heq := congrArg (fun v => v + d) h
    simpa [add_assoc, binary_module_double_zero] using heq
  · rintro rfl
    exact binary_module_double_zero a

/-- A retained singleton has a genuinely nonzero, injective binary slope map. -/
theorem binary_single_slope_injective [AddCommMonoid V] [Module (ZMod 2) V]
    (a : V) (ha : a ≠ 0) : Function.Injective (fun z : ZMod 2 => z • a) := by
  intro x y h
  fin_cases x <;> fin_cases y <;> simp_all

/-- Two nonzero unequal binary slopes are independent: the pair map is injective. -/
theorem binary_pair_slopes_injective [AddCommMonoid V] [Module (ZMod 2) V]
    (a d : V) (ha : a ≠ 0) (hd : d ≠ 0) (had : a ≠ d) :
    Function.Injective (fun xy : ZMod 2 × ZMod 2 => xy.1 • a + xy.2 • d) := by
  have hk : ∀ x y : ZMod 2, x • a + y • d = 0 → x = 0 ∧ y = 0 := by
    intro x y
    fin_cases x <;> fin_cases y <;>
      simp [binary_module_add_eq_zero_iff, ha, hd, had]
  rintro ⟨x, y⟩ ⟨u, v⟩ h
  change x • a + y • d = u • a + v • d at h
  have hz : (x + u) • a + (y + v) • d = 0 := by
    calc
      _ = (x • a + y • d) + (u • a + v • d) := by
        simp only [add_smul]
        ac_rfl
      _ = 0 := by rw [h, binary_module_double_zero]
  obtain ⟨hx, hy⟩ := hk (x + u) (y + v) hz
  exact Prod.ext ((binary_module_add_eq_zero_iff x u).mp hx)
    ((binary_module_add_eq_zero_iff y v).mp hy)

/-- Every complete coefficient table factors through its explicit retained support. -/
theorem source_reduction_factorization [AddCommMonoid V] [Module (ZMod 2) V]
    [DecidableEq V] (t : FullTable k E X V)
    (p : ZMod 2 × (Fin k → ZMod 2 × ZMod 2)) :
    evaluateFullTable t p = evaluateProjectedTable (reducedSourceTable t)
      (permittedProjection (reducedSourceTable t) p) := by
  have h := source_table_pullback_evaluation (reducedSourceTable t) p
  rw [pullback_reducedSourceTable binary_module_double_zero] at h
  exact h

theorem source_reduction_projection_surjective [AddCommMonoid V] [DecidableEq V]
    (t : FullTable k E X V) :
    Function.Surjective (permittedProjection (reducedSourceTable t)) :=
  permittedProjection_surjective _

/-- Surjectivity makes the reduced table the unique function with this factorization. -/
theorem source_reduction_unique [AddCommMonoid V] [Module (ZMod 2) V]
    [DecidableEq V] (t : FullTable k E X V)
    (g : (ZMod 2 × ((i : Fin k) → ProjectedCoordinates ((reducedSourceTable t).blocks i))) → V)
    (hg : ∀ p, g (permittedProjection (reducedSourceTable t) p) = evaluateFullTable t p) :
    g = evaluateProjectedTable (reducedSourceTable t) := by
  funext z
  obtain ⟨p, rfl⟩ := source_reduction_projection_surjective t z
  rw [hg, source_reduction_factorization]

end IndependentDuodenary
