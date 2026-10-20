import IndependentDuodenary.SourceKeyRepresentation

/-! Finite products of the constructed key operator. Phase equivariance has
an explicit one-hot boundary; it is not asserted on arbitrary binary vectors. -/
namespace IndependentDuodenary

abbrev RegisterState (r : ℕ) := Fin r → RepresentedKey
abbrev RegisterTranslation (r : ℕ) := Fin r → KeyBinary
abbrev RegisterPhase (r : ℕ) := Fin r → ZMod 12

def registerCycle {r : ℕ} (q : RegisterState r) : RegisterState r :=
  fun i => keyCoordinateCycle (q i)

def registerTranslate {r : ℕ} (h : RegisterTranslation r) (q : RegisterState r) : RegisterState r :=
  fun i => translateKey (h i) (q i)

def registerStep {r : ℕ} (h : RegisterTranslation r) (q : RegisterState r) : RegisterState r :=
  registerTranslate h (registerCycle q)

def projectRegisters {r s : ℕ} (select : Fin s → Fin r) (q : RegisterState r) : RegisterState s :=
  fun i => q (select i)

def registerPhases {r : ℕ} (q : RegisterState r) : RegisterPhase r :=
  fun i => keyPhaseLabel (keyVertex (q i))

def PhaseRegular {r : ℕ} (q : RegisterState r) : Prop :=
  ∀ i, ∃ a : ZMod 12, (q i).complementIntercept = keyOneHot a

def phaseRegisterState {r : ℕ} (a : RegisterPhase r) : RegisterState r :=
  fun i => ⟨0, 0, keyOneHot (a i)⟩

def phaseAdvance {r : ℕ} (a : RegisterPhase r) : RegisterPhase r := fun i => a i + 1

def relativePhases {r : ℕ} (a : RegisterPhase r) (i j : Fin r) : ZMod 12 := a j - a i

theorem register_cycle_projection {r s : ℕ} (select : Fin s → Fin r) (q : RegisterState r) :
    projectRegisters select (registerCycle q) = registerCycle (projectRegisters select q) := rfl

theorem register_translate_projection {r s : ℕ} (select : Fin s → Fin r)
    (h : RegisterTranslation r) (q : RegisterState r) :
    projectRegisters select (registerTranslate h q) =
      registerTranslate (fun i => h (select i)) (projectRegisters select q) := rfl

theorem register_step_projection {r s : ℕ} (select : Fin s → Fin r)
    (h : RegisterTranslation r) (q : RegisterState r) :
    projectRegisters select (registerStep h q) =
      registerStep (fun i => h (select i)) (projectRegisters select q) := rfl

theorem register_step_projection_iterate {r s : ℕ} (select : Fin s → Fin r)
    (h : RegisterTranslation r) (n : ℕ) (q : RegisterState r) :
    projectRegisters select (((registerStep h)^[n]) q) =
      (((registerStep (fun i => h (select i)))^[n]) (projectRegisters select q)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', register_step_projection, ih]

theorem register_relative_projection {r s : ℕ} (select : Fin s → Fin r)
    (q : RegisterState r) (i j : Fin s) :
    relativePhases (registerPhases (projectRegisters select q)) i j =
      relativePhases (registerPhases q) (select i) (select j) := rfl

theorem register_cycle_commutes_translation {r : ℕ} (h : RegisterTranslation r)
    (q : RegisterState r) :
    registerCycle (registerTranslate h q) = registerTranslate h (registerCycle q) := by
  funext i
  exact key_cycle_commutes_translation (h i) (q i)

theorem register_translation_vertex_invariant {r : ℕ} (h : RegisterTranslation r)
    (q : RegisterState r) (i : Fin r) :
    keyVertex (registerTranslate h q i) = keyVertex (q i) := rfl

theorem register_translation_phase_invariant {r : ℕ} (h : RegisterTranslation r)
    (q : RegisterState r) : registerPhases (registerTranslate h q) = registerPhases q := rfl

theorem register_cycle_iterate {r : ℕ} (n : ℕ) (q : RegisterState r) (i : Fin r) :
    ((registerCycle^[n]) q) i = (keyCoordinateCycle^[n]) (q i) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply']; exact congrArg keyCoordinateCycle ih

theorem register_cycle_period_iff {r : ℕ} (hr : 0 < r) (n : ℕ) :
    (∀ q : RegisterState r, (registerCycle^[n]) q = q) ↔ 12 ∣ n := by
  constructor
  · intro h
    apply (key_cycle_period_iff n).mp
    intro q
    have heq := congrFun (h (fun _ => q)) (⟨0, hr⟩ : Fin r)
    simpa only [register_cycle_iterate] using heq
  · intro h q
    funext i
    rw [register_cycle_iterate]
    exact (key_cycle_period_iff n).mpr h (q i)

theorem register_empty_cycle_period (n : ℕ) (q : RegisterState 0) :
    (registerCycle^[n]) q = q := Subsingleton.elim _ _

theorem key_phase_from_one_hot (q : RepresentedKey) (a : ZMod 12)
    (ha : q.complementIntercept = keyOneHot a) : keyPhaseLabel (keyVertex q) = a := by
  change (∑ i : ZMod 12, if q.complementIntercept i = 1 then -i else 0) = a
  rw [ha]
  exact key_one_hot_phase a

theorem key_cycle_one_hot (q : RepresentedKey) (a : ZMod 12)
    (ha : q.complementIntercept = keyOneHot a) :
    (keyCoordinateCycle q).complementIntercept = keyOneHot (a + 1) := by
  funext i
  simp [keyCoordinateCycle, ha, keyOneHot, add_assoc, add_comm, add_left_comm]

theorem phase_register_regular {r : ℕ} (a : RegisterPhase r) : PhaseRegular (phaseRegisterState a) :=
  fun i => ⟨a i, rfl⟩

theorem phase_register_label {r : ℕ} (a : RegisterPhase r) :
    registerPhases (phaseRegisterState a) = a := by
  funext i
  exact key_one_hot_phase (a i)

theorem register_regular_cycle {r : ℕ} (q : RegisterState r) (hq : PhaseRegular q) :
    PhaseRegular (registerCycle q) := by
  intro i
  obtain ⟨a, ha⟩ := hq i
  exact ⟨a + 1, key_cycle_one_hot (q i) a ha⟩

theorem register_regular_translation {r : ℕ} (h : RegisterTranslation r)
    (q : RegisterState r) (hq : PhaseRegular q) : PhaseRegular (registerTranslate h q) := hq

theorem register_regular_step {r : ℕ} (h : RegisterTranslation r)
    (q : RegisterState r) (hq : PhaseRegular q) : PhaseRegular (registerStep h q) :=
  register_regular_translation h _ (register_regular_cycle q hq)

theorem register_regular_projection {r s : ℕ} (select : Fin s → Fin r)
    (q : RegisterState r) (hq : PhaseRegular q) : PhaseRegular (projectRegisters select q) :=
  fun i => hq (select i)

theorem register_cycle_phase {r : ℕ} (q : RegisterState r) (hq : PhaseRegular q) :
    registerPhases (registerCycle q) = phaseAdvance (registerPhases q) := by
  funext i
  obtain ⟨a, ha⟩ := hq i
  change keyPhaseLabel (keyVertex (keyCoordinateCycle (q i))) = keyPhaseLabel (keyVertex (q i)) + 1
  rw [key_phase_from_one_hot (q i) a ha,
    key_phase_from_one_hot _ (a + 1) (key_cycle_one_hot (q i) a ha)]

theorem register_step_phase {r : ℕ} (h : RegisterTranslation r)
    (q : RegisterState r) (hq : PhaseRegular q) :
    registerPhases (registerStep h q) = phaseAdvance (registerPhases q) := by
  exact register_cycle_phase q hq

theorem register_step_regular_iterate {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (q : RegisterState r) (hq : PhaseRegular q) : PhaseRegular (((registerStep h)^[n]) q) := by
  induction n with
  | zero => exact hq
  | succ n ih => rw [Function.iterate_succ_apply']; exact register_regular_step h _ ih

theorem register_step_phase_iterate {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (q : RegisterState r) (hq : PhaseRegular q) :
    registerPhases (((registerStep h)^[n]) q) = fun i => registerPhases q i + (n : ZMod 12) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', register_step_phase _ _ (register_step_regular_iterate h n q hq), ih]
    funext i
    simp [phaseAdvance, add_assoc]

theorem register_step_relative_invariant {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (q : RegisterState r) (hq : PhaseRegular q) (i j : Fin r) :
    relativePhases (registerPhases (((registerStep h)^[n]) q)) i j =
      relativePhases (registerPhases q) i j := by
  rw [register_step_phase_iterate h n q hq]
  simp [relativePhases]

theorem register_step_iterate_formula {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (q : RegisterState r) (i : Fin r) :
    (((registerStep h)^[n]) q) i = translateKey (n • h i) ((keyCoordinateCycle^[n]) (q i)) := by
  induction n with
  | zero => simp [translateKey_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change translateKey (h i) (keyCoordinateCycle ((((registerStep h)^[n]) q) i)) = _
    rw [ih, key_cycle_commutes_translation, translateKey_add]
    simp only [succ_nsmul, add_comm]

theorem register_step_metadata_invariant {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (q : RegisterState r) (i : Fin r) :
    (((registerStep h)^[n]) q i).metadata = (q i).metadata := by
  rw [register_step_iterate_formula, key_cycle_iterate]
  rfl

theorem register_step_period_twelve {r : ℕ} (h : RegisterTranslation r) (q : RegisterState r) :
    ((registerStep h)^[12]) q = q := by
  funext i
  rw [register_step_iterate_formula, key_cycle_period_twelve]
  have htwelve : (12 : ℕ) • h i = 0 := by
    change (6 * 2) • h i = 0
    rw [mul_nsmul, two_nsmul]
    exact binary_vector_double_zero (6 • h i)
  rw [htwelve, translateKey_zero]

theorem register_regular_orbit_no_collapse {r : ℕ} (base : Fin r)
    (h : RegisterTranslation r) (q : RegisterState r) (hq : PhaseRegular q) (n m : ℕ)
    (heq : ((registerStep h)^[n]) q = ((registerStep h)^[m]) q) :
    (n : ZMod 12) = (m : ZMod 12) := by
  have hp := congrFun (congrArg registerPhases heq) base
  rw [register_step_phase_iterate h n q hq, register_step_phase_iterate h m q hq] at hp
  exact add_left_cancel hp

theorem register_step_period_iff {r : ℕ} (hr : 0 < r) (h : RegisterTranslation r) (n : ℕ) :
    (∀ q : RegisterState r, ((registerStep h)^[n]) q = q) ↔ 12 ∣ n := by
  constructor
  · intro hp
    let q : RegisterState r := phaseRegisterState 0
    have heq : ((registerStep h)^[n]) q = ((registerStep h)^[0]) q := hp q
    have hc := register_regular_orbit_no_collapse (⟨0, hr⟩ : Fin r) h q
      (phase_register_regular 0) n 0 heq
    exact (ZMod.natCast_zmod_eq_zero_iff_dvd n 12).mp (by simpa using hc)
  · rintro ⟨k, rfl⟩ q
    have hid : (registerStep h)^[12] = id := funext (register_step_period_twelve h)
    rw [Function.iterate_mul, hid]
    simp

theorem register_regular_orbit_injective {r : ℕ} (base : Fin r)
    (h : RegisterTranslation r) (q : RegisterState r) (hq : PhaseRegular q) :
    Function.Injective (fun n : Fin 12 => ((registerStep h)^[n.val]) q) := by
  intro n m heq
  have hp := register_regular_orbit_no_collapse base h q hq n.val m.val heq
  have hv := congrArg ZMod.val hp
  apply Fin.ext
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt n.isLt, Nat.mod_eq_of_lt m.isLt] using hv

theorem relative_phases_iff_common_offset {r : ℕ} (base : Fin r) (a b : RegisterPhase r) :
    (∀ i j, relativePhases b i j = relativePhases a i j) ↔
      ∃ c : ZMod 12, ∀ i, b i = a i + c := by
  constructor
  · intro h
    refine ⟨b base - a base, fun i => ?_⟩
    have hi := h base i
    change b i - b base = a i - a base at hi
    calc
      b i = (b i - b base) + b base := by abel
      _ = (a i - a base) + b base := by rw [hi]
      _ = a i + (b base - a base) := by abel
  · rintro ⟨c, hc⟩ i j
    simp [relativePhases, hc]

theorem register_aggregate_phase_formula {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (q : RegisterState r) (hq : PhaseRegular q) :
    (∑ i : Fin r, registerPhases (((registerStep h)^[n]) q) i) =
      (∑ i : Fin r, registerPhases q i) + (r : ZMod 12) * (n : ZMod 12) := by
  rw [register_step_phase_iterate h n q hq]
  simp [Finset.sum_add_distrib]

/-- A scalar sum can collapse even when the vector of phases does not. -/
theorem two_register_sum_collapse :
    (∑ i : Fin 2, (fun _ : Fin 2 => (6 : ZMod 12)) i) =
      (∑ i : Fin 2, (fun _ : Fin 2 => (0 : ZMod 12)) i) ∧
    (fun _ : Fin 2 => (6 : ZMod 12)) ≠ (fun _ : Fin 2 => (0 : ZMod 12)) := by decide

end IndependentDuodenary
