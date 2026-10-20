import IndependentDuodenary.ReferenceMachines

/-! Finite-control acceptance-convention conversion. One extra transition emits
or reads the output symbol; multi-tape compilation into TM0 remains separate. -/
namespace IndependentDuodenary

inductive AcceptanceConvention where
  | stateToHead | headToState
  deriving DecidableEq

structure NormalizationConfiguration (a s k : ℕ) where
  body : ReferenceConfiguration a s k
  done : Bool

def normalizationLift {a s k : ℕ} (q : ReferenceConfiguration a s k) :
    NormalizationConfiguration a s k := ⟨q, false⟩

def normalizationVerdict {a s k : ℕ} (mode : AcceptanceConvention)
    (state : Fin (s + 2)) (read : Fin (k + 1) → Fin (a + 3)) : Bool :=
  match mode with
  | .stateToHead => decide (state = 0)
  | .headToState => decide (read 0 = 1)

def normalizationFinishInstruction {a s k : ℕ} (mode : AcceptanceConvention)
    (state : Fin (s + 2)) (read : Fin (k + 1) → Fin (a + 3)) :
    ReferenceInstruction a s k where
  state := if normalizationVerdict mode state read then 0 else 1
  write i := match mode with
    | .stateToHead => if i = 0 then (if state = 0 then 1 else 2) else read i
    | .headToState => read i
  move _ := .stay

/-- Complete local transition table on the finite control (state, done) and
finite tuple of head symbols. None means halted. -/
def normalizationTable {a s k : ℕ} (M : ReferenceDeterministicMachine a s k)
    (mode : AcceptanceConvention) (control : Fin (s + 2) × Bool)
    (read : Fin (k + 1) → Fin (a + 3)) : Option (ReferenceInstruction a s k × Bool) :=
  if control.2 then none
  else if control.1 = 0 ∨ control.1 = 1 then
    some (normalizationFinishInstruction mode control.1 read, true)
  else some (M.transition control.1 read, false)

def normalizationStep {a s k : ℕ} (M : ReferenceDeterministicMachine a s k)
    (mode : AcceptanceConvention) (q : NormalizationConfiguration a s k) :
    Option (NormalizationConfiguration a s k) :=
  (normalizationTable M mode (q.body.state, q.done) (referenceRead q.body)).map
    (fun instruction => ⟨referenceApply q.body instruction.1, instruction.2⟩)

def normalizationFinish {a s k : ℕ} (mode : AcceptanceConvention)
    (q : ReferenceConfiguration a s k) : NormalizationConfiguration a s k :=
  ⟨referenceApply q (normalizationFinishInstruction mode q.state (referenceRead q)), true⟩

def normalizationEdge {a s k : ℕ} (M : ReferenceDeterministicMachine a s k)
    (mode : AcceptanceConvention) (q q' : NormalizationConfiguration a s k) : Prop :=
  normalizationStep M mode q = some q'

theorem normalization_control_cardinality (s : ℕ) :
    Fintype.card (Fin (s + 2) × Bool) = 2 * (s + 2) := by simp; omega

theorem normalization_done_stops {a s k : ℕ} (M : ReferenceDeterministicMachine a s k)
    (mode : AcceptanceConvention) (q : NormalizationConfiguration a s k)
    (done : q.done = true) : normalizationStep M mode q = none := by
  simp [normalizationStep, normalizationTable, done]

theorem normalization_halted_iff_done {a s k : ℕ} (M : ReferenceDeterministicMachine a s k)
    (mode : AcceptanceConvention) (q : NormalizationConfiguration a s k) :
    normalizationStep M mode q = none ↔ q.done = true := by
  rcases q with ⟨body, done⟩
  cases done <;> simp [normalizationStep, normalizationTable]
  split <;> simp

theorem normalization_running_step {a s k : ℕ} (M : ReferenceDeterministicMachine a s k)
    (mode : AcceptanceConvention) (q : ReferenceConfiguration a s k) :
    normalizationStep M mode (normalizationLift q) =
      match referenceDStep M q with
      | none => some (normalizationFinish mode q)
      | some q' => some (normalizationLift q') := by
  by_cases halt : referenceTerminal q
  · simp [normalizationStep, normalizationTable, normalizationLift, normalizationFinish,
      referenceDStep, referenceTerminal] at halt ⊢
    rcases halt with h | h <;> simp [h]
  · simp [normalizationStep, normalizationTable, normalizationLift, normalizationFinish,
      referenceDStep, referenceTerminal] at halt ⊢
    simp [halt]

theorem normalization_finish_head {a s k : ℕ} (q : ReferenceConfiguration a s k) :
    (normalizationFinish .stateToHead q).body.tape 0
      ((normalizationFinish .stateToHead q).body.head 0) =
        if q.state = 0 then 1 else 2 := by
  simp [normalizationFinish, referenceApply, normalizationFinishInstruction, referenceDisplacement]

theorem normalization_finish_head_boolean {a s k : ℕ} (q : ReferenceConfiguration a s k) :
    let out := (normalizationFinish .stateToHead q).body
    out.tape 0 (out.head 0) = 1 ∨ out.tape 0 (out.head 0) = 2 := by
  simp only [normalization_finish_head]
  split <;> simp

theorem normalization_finish_head_accepts {a s k : ℕ} (q : ReferenceConfiguration a s k) :
    let out := (normalizationFinish .stateToHead q).body
    out.tape 0 (out.head 0) = 1 ↔ q.state = 0 := by
  simp only [normalization_finish_head]
  have h : (2 : Fin (a + 3)) ≠ 1 := by intro e; have := congrArg Fin.val e; simp at this
  split <;> simp_all

theorem normalization_finish_state_accepts {a s k : ℕ} (q : ReferenceConfiguration a s k) :
    (normalizationFinish .headToState q).body.state = 0 ↔ q.tape 0 (q.head 0) = 1 := by
  have h : (1 : Fin (s + 2)) ≠ 0 := Ne.symm reference_accept_reject_distinct
  simp [normalizationFinish, referenceApply, normalizationFinishInstruction,
    normalizationVerdict, referenceRead, h]

theorem normalization_source_step {a s k : ℕ} (M : ReferenceDeterministicMachine a s k)
    (mode : AcceptanceConvention) (q q' : ReferenceConfiguration a s k)
    (step : referenceDEdge M q q') :
    normalizationEdge M mode (normalizationLift q) (normalizationLift q') := by
  unfold normalizationEdge
  rw [normalization_running_step, step]

theorem normalization_halt_step {a s k : ℕ} (M : ReferenceDeterministicMachine a s k)
    (mode : AcceptanceConvention) (q : ReferenceConfiguration a s k)
    (halt : referenceTerminal q) :
    normalizationEdge M mode (normalizationLift q) (normalizationFinish mode q) := by
  unfold normalizationEdge
  rw [normalization_running_step, (reference_dstep_none_iff M q).mpr halt]

theorem normalization_forward_run {a s k : ℕ} (M : ReferenceDeterministicMachine a s k)
    (mode : AcceptanceConvention) {n : ℕ} {q q' : ReferenceConfiguration a s k}
    (run : ReferenceRun (referenceDEdge M) n q q') :
    ReferenceRun (normalizationEdge M mode) n (normalizationLift q) (normalizationLift q') := by
  induction run with
  | zero _ => exact ReferenceRun.zero _
  | next run step ih => exact ReferenceRun.next ih (normalization_source_step M mode _ _ step)

theorem normalization_finished_run {a s k : ℕ} (M : ReferenceDeterministicMachine a s k)
    (mode : AcceptanceConvention) {n : ℕ} {q q' : ReferenceConfiguration a s k}
    (run : ReferenceRun (referenceDEdge M) n q q') (halt : referenceTerminal q') :
    ReferenceRun (normalizationEdge M mode) (n + 1)
      (normalizationLift q) (normalizationFinish mode q') := by
  exact ReferenceRun.next (normalization_forward_run M mode run) (normalization_halt_step M mode q' halt)

theorem normalization_reverse_run {a s k : ℕ} (M : ReferenceDeterministicMachine a s k)
    (mode : AcceptanceConvention) (initial : ReferenceConfiguration a s k)
    {n : ℕ} {out : NormalizationConfiguration a s k}
    (run : ReferenceRun (normalizationEdge M mode) n (normalizationLift initial) out) :
    (∃ q, ReferenceRun (referenceDEdge M) n initial q ∧ out = normalizationLift q) ∨
    (∃ t q, n = t + 1 ∧ ReferenceRun (referenceDEdge M) t initial q ∧
      referenceTerminal q ∧ out = normalizationFinish mode q) := by
  generalize start_eq : normalizationLift initial = start at run
  induction run with
  | zero _ => exact Or.inl ⟨initial, ReferenceRun.zero _, start_eq.symm⟩
  | next run step ih =>
    rcases ih start_eq with ⟨q, source, eq⟩ | ⟨t, q, count, source, halt, eq⟩
    · rw [eq] at step
      unfold normalizationEdge at step
      rw [normalization_running_step] at step
      cases hs : referenceDStep M q with
      | none =>
        simp [hs] at step
        exact Or.inr ⟨_, q, rfl, source, (reference_dstep_none_iff M q).mp hs, step.symm⟩
      | some q' =>
        simp [hs] at step
        exact Or.inl ⟨q', ReferenceRun.next source hs, step.symm⟩
    · rw [eq] at step
      have stopped := normalization_done_stops M mode (normalizationFinish mode q) rfl
      unfold normalizationEdge at step
      rw [stopped] at step
      contradiction

theorem normalization_exact_overhead {a s k : ℕ} (M : ReferenceDeterministicMachine a s k)
    (mode : AcceptanceConvention) (initial : ReferenceConfiguration a s k)
    {n : ℕ} {out : NormalizationConfiguration a s k}
    (run : ReferenceRun (normalizationEdge M mode) n (normalizationLift initial) out)
    (done : out.done = true) :
    ∃ t q, n = t + 1 ∧ ReferenceRun (referenceDEdge M) t initial q ∧
      referenceTerminal q ∧ out = normalizationFinish mode q := by
  rcases normalization_reverse_run M mode initial run with ⟨q, source, eq⟩ | finished
  · rw [eq] at done
    contradiction
  · exact finished

theorem normalization_empty_input {a s k : ℕ} (M : ReferenceDeterministicMachine a s k)
    (mode : AcceptanceConvention) (halt : referenceTerminal (referenceInitial (a := a) (k := k) M.initial [])) :
    ReferenceRun (normalizationEdge M mode) 1
      (normalizationLift (referenceInitial M.initial []))
      (normalizationFinish mode (referenceInitial M.initial [])) := by
  exact normalization_finished_run M mode (ReferenceRun.zero _) halt

theorem normalization_state_to_head_language {a s k : ℕ}
    (M : ReferenceDeterministicMachine a s k) (initial : ReferenceConfiguration a s k) :
    (∃ t q, ReferenceRun (referenceDEdge M) t initial q ∧ referenceTerminal q ∧ q.state = 0) ↔
      ∃ n out, ReferenceRun (normalizationEdge M .stateToHead) n (normalizationLift initial) out ∧
        out.done = true ∧ out.body.tape 0 (out.body.head 0) = 1 := by
  constructor
  · rintro ⟨t, q, run, halt, accepts⟩
    exact ⟨t + 1, normalizationFinish .stateToHead q,
      normalization_finished_run M .stateToHead run halt, rfl,
      (normalization_finish_head_accepts q).mpr accepts⟩
  · rintro ⟨n, out, run, done, accepts⟩
    obtain ⟨t, q, count, source, halt, eq⟩ := normalization_exact_overhead M .stateToHead initial run done
    rw [eq] at accepts
    exact ⟨t, q, source, halt, (normalization_finish_head_accepts q).mp accepts⟩

theorem normalization_head_to_state_language {a s k : ℕ}
    (M : ReferenceDeterministicMachine a s k) (initial : ReferenceConfiguration a s k) :
    (∃ t q, ReferenceRun (referenceDEdge M) t initial q ∧ referenceTerminal q ∧
      q.tape 0 (q.head 0) = 1) ↔
      ∃ n out, ReferenceRun (normalizationEdge M .headToState) n (normalizationLift initial) out ∧
        out.done = true ∧ out.body.state = 0 := by
  constructor
  · rintro ⟨t, q, run, halt, accepts⟩
    exact ⟨t + 1, normalizationFinish .headToState q,
      normalization_finished_run M .headToState run halt, rfl,
      (normalization_finish_state_accepts q).mpr accepts⟩
  · rintro ⟨n, out, run, done, accepts⟩
    obtain ⟨t, q, count, source, halt, eq⟩ := normalization_exact_overhead M .headToState initial run done
    rw [eq] at accepts
    exact ⟨t, q, source, halt, (normalization_finish_state_accepts q).mp accepts⟩

theorem normalization_polynomial_overhead (c d length time : ℕ)
    (bound : time ≤ prizePolynomialBound c d length) :
    time + 1 ≤ prizePolynomialBound (c + 1) d length := by
  have positive : 0 < (length + 1) ^ d := pow_pos (by omega) d
  unfold prizePolynomialBound at bound ⊢
  nlinarith

theorem normalization_finish_heads_unchanged {a s k : ℕ} (mode : AcceptanceConvention)
    (q : ReferenceConfiguration a s k) : (normalizationFinish mode q).body.head = q.head := by
  funext i
  simp [normalizationFinish, referenceApply, normalizationFinishInstruction, referenceDisplacement]

theorem normalization_head_to_state_tape_unchanged {a s k : ℕ}
    (q : ReferenceConfiguration a s k) : (normalizationFinish .headToState q).body.tape = q.tape := by
  funext i j
  by_cases h : j = q.head i <;>
    simp [normalizationFinish, referenceApply, normalizationFinishInstruction, referenceRead, h]

theorem normalization_finish_head_rejects {a s k : ℕ} (q : ReferenceConfiguration a s k)
    (halt : referenceTerminal q) :
    let out := (normalizationFinish .stateToHead q).body
    out.tape 0 (out.head 0) = 2 ↔ q.state = 1 := by
  have h : (1 : Fin (a + 3)) ≠ 2 := by intro e; have := congrArg Fin.val e; simp at this
  rcases halt with hs | hs <;>
    simp [normalization_finish_head, hs, h, reference_accept_reject_distinct,
      Ne.symm reference_accept_reject_distinct]

theorem normalization_finish_state_rejects {a s k : ℕ} (q : ReferenceConfiguration a s k)
    (boolean : q.tape 0 (q.head 0) = 1 ∨ q.tape 0 (q.head 0) = 2) :
    (normalizationFinish .headToState q).body.state = 1 ↔ q.tape 0 (q.head 0) = 2 := by
  have h : (1 : Fin (a + 3)) ≠ 2 := by intro e; have := congrArg Fin.val e; simp at this
  rcases boolean with hs | hs <;>
    simp [normalizationFinish, referenceApply, normalizationFinishInstruction,
      normalizationVerdict, referenceRead, hs, h, Ne.symm h,
      reference_accept_reject_distinct, Ne.symm reference_accept_reject_distinct]

end IndependentDuodenary
