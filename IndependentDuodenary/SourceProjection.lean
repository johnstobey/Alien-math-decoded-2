import IndependentDuodenary.SourceReduction
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

/-! Homogeneous answer coordinates and the semantics of permitted pullback. -/
namespace IndependentDuodenary
open scoped BigOperators

variable {E X V : Type*} {k : ℕ}

/-- Equation blocks have two local bits, singletons one, omissions none. -/
abbrev ProjectedCoordinates : ProjectedBlock E X V → Type
  | .retained _ _ _ => ZMod 2 × ZMod 2
  | .singleton _ _ _ => ZMod 2
  | .omitted _ => PUnit

def sourceBlockProjection (b : ProjectedBlock E X V) (t₀ : ZMod 2)
    (xy : ZMod 2 × ZMod 2) : ProjectedCoordinates b :=
  match b with
  | .retained _ _ _ => xy
  | .singleton _ .first _ => xy.1
  | .singleton _ .second _ => xy.2
  | .singleton e .third _ => (if e.parity then t₀ else 0) + xy.1 + xy.2
  | .omitted _ => PUnit.unit

def sourceBlockLift (b : ProjectedBlock E X V) (t₀ : ZMod 2)
    (z : ProjectedCoordinates b) : ZMod 2 × ZMod 2 :=
  match b with
  | .retained _ _ _ => z
  | .singleton _ .first _ => (z, 0)
  | .singleton _ .second _ => (0, z)
  | .singleton e .third _ => ((z : ZMod 2) - (if e.parity then t₀ else 0), 0)
  | .omitted _ => (0, 0)

theorem sourceBlockProjection_lift (b : ProjectedBlock E X V) (t₀ : ZMod 2)
    (z : ProjectedCoordinates b) :
    sourceBlockProjection b t₀ (sourceBlockLift b t₀ z) = z := by
  cases b with
  | retained e a d => rfl
  | omitted e => cases z; rfl
  | singleton e p v =>
    cases p <;>
      simp [sourceBlockProjection, sourceBlockLift, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm]

theorem sourceBlockProjection_surjective (b : ProjectedBlock E X V) (t₀ : ZMod 2) :
    Function.Surjective (sourceBlockProjection b t₀) := by
  intro z
  exact ⟨sourceBlockLift b t₀ z, sourceBlockProjection_lift b t₀ z⟩

/-- A common homogeneous bit accompanies independent local answer coordinates. -/
def permittedProjection (t : ProjectedTable k E X V)
    (p : ZMod 2 × (Fin k → ZMod 2 × ZMod 2)) :
    ZMod 2 × ((i : Fin k) → ProjectedCoordinates (t.blocks i)) :=
  (p.1, fun i => sourceBlockProjection (t.blocks i) p.1 (p.2 i))

theorem permittedProjection_preserves_homogeneous (t : ProjectedTable k E X V)
    (p : ZMod 2 × (Fin k → ZMod 2 × ZMod 2)) :
    (permittedProjection t p).1 = p.1 := rfl

theorem permittedProjection_surjective (t : ProjectedTable k E X V) :
    Function.Surjective (permittedProjection t) := by
  rintro ⟨t₀, z⟩
  refine ⟨(t₀, fun i => sourceBlockLift (t.blocks i) t₀ (z i)), ?_⟩
  apply Prod.ext
  · rfl
  · funext i
    exact sourceBlockProjection_lift (t.blocks i) t₀ (z i)

variable [AddCommMonoid V] [Module (ZMod 2) V]

def evaluateProjectedBlock (b : ProjectedBlock E X V) (z : ProjectedCoordinates b) : V :=
  match b with
  | .retained _ a d => z.1 • a + z.2 • d
  | .singleton _ _ v => (z : ZMod 2) • v
  | .omitted _ => 0

def evaluateFullBlock (b : FullBlock E X V) (xy : ZMod 2 × ZMod 2) : V :=
  xy.1 • b.firstSlope + xy.2 • b.secondSlope

/-- The coefficient pullback represents composition with the actual-bit projection. -/
theorem source_block_pullback_evaluation (b : ProjectedBlock E X V)
    (t₀ : ZMod 2) (xy : ZMod 2 × ZMod 2) :
    evaluateFullBlock (pullbackBlock b) xy + t₀ • pullbackCorrection b =
      evaluateProjectedBlock b (sourceBlockProjection b t₀ xy) := by
  cases b with
  | retained e a d =>
    simp [evaluateFullBlock, pullbackBlock, pullbackCorrection,
      evaluateProjectedBlock, sourceBlockProjection]
  | omitted e =>
    simp [evaluateFullBlock, pullbackBlock, pullbackCorrection,
      evaluateProjectedBlock, sourceBlockProjection]
  | singleton e p v =>
    cases p <;> cases hp : e.parity <;>
      simp [evaluateFullBlock, pullbackBlock, pullbackCorrection, parityCorrection,
        evaluateProjectedBlock, sourceBlockProjection, hp, add_smul,
        add_assoc, add_left_comm, add_comm]

def evaluateProjectedTable (t : ProjectedTable k E X V)
    (p : ZMod 2 × ((i : Fin k) → ProjectedCoordinates (t.blocks i))) : V :=
  p.1 • t.intercept + ∑ i, evaluateProjectedBlock (t.blocks i) (p.2 i)

def evaluateFullTable (t : FullTable k E X V)
    (p : ZMod 2 × (Fin k → ZMod 2 × ZMod 2)) : V :=
  p.1 • t.intercept + ∑ i, evaluateFullBlock (t.blocks i) (p.2 i)

/-- P' composed with the permitted homogeneous projection equals its coefficient pullback. -/
theorem source_table_pullback_evaluation (t : ProjectedTable k E X V)
    (p : ZMod 2 × (Fin k → ZMod 2 × ZMod 2)) :
    evaluateFullTable (pullbackTable t) p =
      evaluateProjectedTable t (permittedProjection t p) := by
  simp only [evaluateFullTable, pullbackTable, evaluateProjectedTable, permittedProjection]
  rw [smul_add, Finset.smul_sum]
  have hs : (∑ i, evaluateFullBlock (pullbackBlock (t.blocks i)) (p.2 i)) +
      (∑ i, p.1 • pullbackCorrection (t.blocks i)) =
      ∑ i, evaluateProjectedBlock (t.blocks i)
        (sourceBlockProjection (t.blocks i) p.1 (p.2 i)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact source_block_pullback_evaluation (t.blocks i) p.1 (p.2 i)
  calc
    _ = p.1 • t.intercept +
        ((∑ i, evaluateFullBlock (pullbackBlock (t.blocks i)) (p.2 i)) +
          (∑ i, p.1 • pullbackCorrection (t.blocks i))) := by ac_rfl
    _ = _ := by rw [hs]

end IndependentDuodenary
