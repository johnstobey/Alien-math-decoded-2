import IndependentDuodenary.SourceKeys
import Mathlib.Algebra.BigOperators.Group.Finset

/-!
# Permitted block projections and exact-key compatibility

Coefficient tables are represented in a fixed splitting V = K × W. A block
position remains explicit in Fin k, even when occurrence or variable IDs repeat.
Parity bits use Bool; true acts as 1 and false as 0 on a binary vector group.
-/
namespace IndependentDuodenary
open scoped BigOperators

inductive SourcePosition where
  | first | second | third
  deriving DecidableEq

structure SourceEquation (E X : Type*) where
  occurrence : E
  firstVariable : X
  secondVariable : X
  thirdVariable : X
  parity : Bool

/-- Retained equation coefficients or a singleton's actual-bit coefficient. -/
inductive ReducedBlock (E X V : Type*) where
  | omitted
  | equation (occurrence : E) (firstSlope secondSlope : V)
  | singleton (variableId : X) (slope : V)
  deriving DecidableEq

inductive ProjectedBlock (E X V : Type*) where
  | retained (origin : SourceEquation E X) (firstSlope secondSlope : V)
  | singleton (origin : SourceEquation E X) (position : SourcePosition) (slope : V)
  | omitted (origin : SourceEquation E X)

structure FullBlock (E X V : Type*) where
  origin : SourceEquation E X
  firstSlope : V
  secondSlope : V

variable {E X V : Type*}

def sourceVariable (e : SourceEquation E X) : SourcePosition → X
  | .first => e.firstVariable
  | .second => e.secondVariable
  | .third => e.thirdVariable

def parityCorrection [Zero V] (e : SourceEquation E X) (v : V) : V :=
  if e.parity then v else 0

/-- The source's complete reduction rule, including the third-bit correction. -/
def reduceEquation [Zero V] [DecidableEq V] (e : SourceEquation E X)
    (a d : V) : ReducedBlock E X V × V :=
  if a = 0 then
    if d = 0 then (.omitted, 0) else (.singleton e.secondVariable d, 0)
  else if d = 0 then (.singleton e.firstVariable a, 0)
  else if a = d then (.singleton e.thirdVariable a, parityCorrection e a)
  else (.equation e.occurrence a d, 0)

def reduceSingleton [Zero V] [DecidableEq V] (x : X) (v : V) :
    ReducedBlock E X V × V :=
  if v = 0 then (.omitted, 0) else (.singleton x v, 0)

def reduceProjectedBlock [Zero V] [DecidableEq V] :
    ProjectedBlock E X V → ReducedBlock E X V × V
  | .retained e a d => reduceEquation e a d
  | .singleton e p v => reduceSingleton (sourceVariable e p) v
  | .omitted _ => (.omitted, 0)

def pullbackBlock [Zero V] : ProjectedBlock E X V → FullBlock E X V
  | .retained e a d => ⟨e, a, d⟩
  | .singleton e .first v => ⟨e, v, 0⟩
  | .singleton e .second v => ⟨e, 0, v⟩
  | .singleton e .third v => ⟨e, v, v⟩
  | .omitted e => ⟨e, 0, 0⟩

def pullbackCorrection [Zero V] : ProjectedBlock E X V → V
  | .singleton e .third v => parityCorrection e v
  | _ => 0

def reduceFullBlock [Zero V] [DecidableEq V] (b : FullBlock E X V) :
    ReducedBlock E X V × V :=
  reduceEquation b.origin b.firstSlope b.secondSlope

theorem pullback_block_metadata [AddZeroClass V] [DecidableEq V]
    (b : ProjectedBlock E X V) :
    (reduceFullBlock (pullbackBlock b)).1 = (reduceProjectedBlock b).1 := by
  cases b with
  | retained e a d => rfl
  | omitted e => simp [reduceFullBlock, pullbackBlock, reduceProjectedBlock, reduceEquation]
  | singleton e p v =>
    cases p <;> by_cases hv : v = 0 <;>
      simp [reduceFullBlock, pullbackBlock, reduceProjectedBlock, reduceEquation,
        reduceSingleton, sourceVariable, parityCorrection, hv]

/-- Third-position pullback and reduction add the same correction twice. -/
theorem pullback_block_intercept [AddZeroClass V] [DecidableEq V]
    (hDouble : ∀ v : V, v + v = 0) (b : ProjectedBlock E X V) :
    pullbackCorrection b + (reduceFullBlock (pullbackBlock b)).2 =
      (reduceProjectedBlock b).2 := by
  cases b with
  | retained e a d => simp [pullbackCorrection, reduceFullBlock, pullbackBlock, reduceProjectedBlock]
  | omitted e => simp [pullbackCorrection, reduceFullBlock, pullbackBlock, reduceProjectedBlock, reduceEquation]
  | singleton e p v =>
    cases p <;> by_cases hv : v = 0 <;>
      simp [pullbackCorrection, reduceFullBlock, pullbackBlock, reduceProjectedBlock,
        reduceEquation, reduceSingleton, sourceVariable, parityCorrection, hv, hDouble]

structure ProjectedTable (k : ℕ) (E X V : Type*) where
  intercept : V
  blocks : Fin k → ProjectedBlock E X V

structure FullTable (k : ℕ) (E X V : Type*) where
  intercept : V
  blocks : Fin k → FullBlock E X V

variable {k : ℕ} {K W : Type*}

def pullbackTable [AddCommMonoid V] (t : ProjectedTable k E X V) : FullTable k E X V :=
  ⟨t.intercept + ∑ i, pullbackCorrection (t.blocks i), fun i => pullbackBlock (t.blocks i)⟩

def projectedReducedIntercept [AddCommMonoid V] [DecidableEq V]
    (t : ProjectedTable k E X V) : V :=
  t.intercept + ∑ i, (reduceProjectedBlock (t.blocks i)).2

def fullReducedIntercept [AddCommMonoid V] [DecidableEq V]
    (t : FullTable k E X V) : V :=
  t.intercept + ∑ i, (reduceFullBlock (t.blocks i)).2

theorem pullback_reduced_intercept [AddCommMonoid V] [DecidableEq V]
    (hDouble : ∀ v : V, v + v = 0) (t : ProjectedTable k E X V) :
    fullReducedIntercept (pullbackTable t) = projectedReducedIntercept t := by
  simp only [fullReducedIntercept, projectedReducedIntercept, pullbackTable]
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact pullback_block_intercept hDouble (t.blocks i)

def projectedExactKey [AddCommMonoid K] [AddCommMonoid W] [DecidableEq K] [DecidableEq W]
    (t : ProjectedTable k E X (K × W)) : ExactKey (Fin k → ReducedBlock E X (K × W)) K W :=
  ⟨fun i => (reduceProjectedBlock (t.blocks i)).1,
    (projectedReducedIntercept t).1, (projectedReducedIntercept t).2⟩

def fullExactKey [AddCommMonoid K] [AddCommMonoid W] [DecidableEq K] [DecidableEq W]
    (t : FullTable k E X (K × W)) : ExactKey (Fin k → ReducedBlock E X (K × W)) K W :=
  ⟨fun i => (reduceFullBlock (t.blocks i)).1,
    (fullReducedIntercept t).1, (fullReducedIntercept t).2⟩

/-- Exact-key preservation is proved from the block rules, rather than postulated. -/
theorem permitted_pullback_exact_key [AddCommMonoid K] [AddCommMonoid W]
    [DecidableEq K] [DecidableEq W] (hDouble : ∀ v : K × W, v + v = 0)
    (t : ProjectedTable k E X (K × W)) :
    fullExactKey (pullbackTable t) = projectedExactKey t := by
  have hi := pullback_reduced_intercept hDouble t
  have hm : (fun i => (reduceFullBlock ((pullbackTable t).blocks i)).1) =
      (fun i => (reduceProjectedBlock (t.blocks i)).1) := by
    funext i
    exact pullback_block_metadata (t.blocks i)
  simp only [fullExactKey, projectedExactKey]
  rw [hi, hm]

def translateProjectedTable [Add K] [AddZeroClass W] (h : K)
    (t : ProjectedTable k E X (K × W)) : ProjectedTable k E X (K × W) :=
  ⟨t.intercept + (h, 0), t.blocks⟩

theorem projected_exact_key_translate [AddCommMonoid K] [AddCommMonoid W]
    [DecidableEq K] [DecidableEq W] (h : K) (t : ProjectedTable k E X (K × W)) :
    projectedExactKey (translateProjectedTable h t) = translateKey h (projectedExactKey t) := by
  simp [projectedExactKey, projectedReducedIntercept, translateProjectedTable, translateKey,
    add_assoc, add_left_comm, add_comm]

/-- Intercept translation stays inside the universe of represented table keys. -/
theorem source_key_translation_representable [AddCommMonoid K] [AddCommMonoid W]
    [DecidableEq K] [DecidableEq W] (h : K) (t : ProjectedTable k E X (K × W)) :
    ∃ s : ProjectedTable k E X (K × W),
      projectedExactKey s = translateKey h (projectedExactKey t) :=
  ⟨translateProjectedTable h t, projected_exact_key_translate h t⟩

/-- Every represented key has a represented canonical zero-K-intercept key. -/
theorem source_canonical_key_representable [AddCommGroup K] [AddCommMonoid W]
    [DecidableEq K] [DecidableEq W] (t : ProjectedTable k E X (K × W)) :
    ∃ s : ProjectedTable k E X (K × W),
      projectedExactKey s = canonicalKey (projectedExactKey t) := by
  refine ⟨translateProjectedTable (-(projectedExactKey t).binaryIntercept) t, ?_⟩
  rw [projected_exact_key_translate]
  simp [translateKey, canonicalKey]

/-- The primary source's eq:table-folding, for the represented coefficient tables. -/
theorem source_table_folding [AddCommMonoid K] [AddCommMonoid W]
    [DecidableEq K] [DecidableEq W]
    (label : (Fin k → ReducedBlock E X (K × W)) × W → K)
    (h : K) (t : ProjectedTable k E X (K × W)) :
    restoredAnswer label (projectedExactKey (translateProjectedTable h t)) =
      restoredAnswer label (projectedExactKey t) + h := by
  rw [projected_exact_key_translate, source_folding]

/-- The primary source's eq:key-sharing, derived from explicit permitted pullback. -/
theorem source_key_sharing [AddCommMonoid K] [AddCommMonoid W]
    [DecidableEq K] [DecidableEq W] (hDouble : ∀ v : K × W, v + v = 0)
    (label : (Fin k → ReducedBlock E X (K × W)) × W → K)
    (t : ProjectedTable k E X (K × W)) :
    restoredAnswer label (fullExactKey (pullbackTable t)) =
      restoredAnswer label (projectedExactKey t) := by
  rw [permitted_pullback_exact_key hDouble]

/-- Binary source spaces discharge the exponent-two condition in every dimension. -/
theorem split_binary_double_zero {ℓ d : ℕ}
    (v : (Fin ℓ → ZMod 2) × (Fin d → ZMod 2)) : v + v = 0 := by
  apply Prod.ext
  · exact binary_vector_double_zero v.1
  · exact binary_vector_double_zero v.2

theorem binary_source_key_sharing {ℓ d : ℕ}
    (label : (Fin k → ReducedBlock E X ((Fin ℓ → ZMod 2) × (Fin d → ZMod 2))) ×
      (Fin d → ZMod 2) → (Fin ℓ → ZMod 2))
    (t : ProjectedTable k E X ((Fin ℓ → ZMod 2) × (Fin d → ZMod 2))) :
    restoredAnswer label (fullExactKey (pullbackTable t)) =
      restoredAnswer label (projectedExactKey t) :=
  source_key_sharing split_binary_double_zero label t

end IndependentDuodenary
