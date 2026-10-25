import IndependentDuodenary.ObservationReconstruction
import IndependentDuodenary.DualRingConsistency

open IndependentDuodenary

-- The original reset fails at winding one; the compensated reset is consistent.
example : ¬ ((0 : ZMod 12) = 1 + 0) := by decide
example : (0 : ZMod 12) = 1 + (-1) := by decide
example : ¬ ∃ m : ZMod 12, m + m = 5 := quincunx_midpoint_obstruction
-- The obstruction depends on the modulus: modulo three, a midpoint exists.
example : ∃ m : ZMod 3, m + m = 2 := ⟨1, by decide⟩

-- No nonempty-carrier premise is hidden in observation factorization.
example : ∃ U : PEmpty → PEmpty,
    Function.Semiconj (id : PEmpty → PEmpty) id U := by
  exact (observation_dynamics_iff_kernel_stable id id).mpr (fun _ _ h => h)

example : ∃ D : (ℕ → Unit) → Option Unit,
    ∀ x : Unit, D (observationTrace id (id : Unit → Unit) x) = some x := by
  apply (observation_trace_reconstruction_iff id id).mpr
  intro x y _
  cases x
  cases y
  rfl

-- Autonomous observed evolution can exist while all initial-state information is lost.
example : (∃ U : Unit → Unit, Function.Semiconj (fun _ : Bool => ()) Bool.not U) ∧
    ¬ ∃ D : (ℕ → Unit) → Option Bool,
      ∀ x, D (observationTrace Bool.not (fun _ : Bool => ()) x) = some x := by
  constructor
  · exact ⟨id, fun _ => rfl⟩
  · intro h
    have hi := (observation_trace_reconstruction_iff Bool.not (fun _ : Bool => ())).mp h
    have hf : false = true := hi (show observationTrace Bool.not (fun _ : Bool => ()) false =
      observationTrace Bool.not (fun _ : Bool => ()) true from rfl)
    exact (by decide : false ≠ true) hf

-- A mismatched target transition violates the required intertwining equation.
example : ¬ Function.Semiconj (id : Bool → Bool) Bool.not id := by
  intro h
  have hf : true = false := h false
  exact (by decide : true ≠ false) hf
