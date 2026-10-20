import IndependentDuodenary.AcceptanceNormalization
import Mathlib.Logic.Equiv.Fin

/-! A concrete single-tape, four-symbol compiler component for obligation 1.14.
It does not implement multi-tape layout or alphabet block encoding. -/
namespace IndependentDuodenary

structure WriteMoveInstruction (s : ℕ) where
  next : Fin (s + 1)
  symbol : Fin 4
  move : ReferenceMove

abbrev WriteMoveMachine (s : ℕ) := Fin (s + 1) → Fin 4 → Option (WriteMoveInstruction s)
abbrev WriteMoveConfiguration (s : ℕ) := Turing.TM0.Cfg (Fin 4) (Fin (s + 1))
abbrev MicroConfiguration (s : ℕ) := Turing.TM0.Cfg (Fin 4) (Fin (s + 1) × Fin 4)

def writeMoveTape (move : ReferenceMove) (tape : Turing.Tape (Fin 4)) : Turing.Tape (Fin 4) :=
  match move with
  | .stay => tape
  | .left => tape.move .left
  | .right => tape.move .right

def writeMoveApply {s : ℕ} (q : WriteMoveConfiguration s) (i : WriteMoveInstruction s) :
    WriteMoveConfiguration s := ⟨i.next, writeMoveTape i.move (q.Tape.write i.symbol)⟩

def writeMoveStep {s : ℕ} (M : WriteMoveMachine s) (q : WriteMoveConfiguration s) :
    Option (WriteMoveConfiguration s) := (M q.q q.Tape.head).map (writeMoveApply q)

def writeMoveTick {s : ℕ} (M : WriteMoveMachine s) (q : WriteMoveConfiguration s) :
    WriteMoveConfiguration s := (writeMoveStep M q).getD q

def writeMoveRun {s : ℕ} (M : WriteMoveMachine s) (input : List (Fin 4)) (n : ℕ) :
    WriteMoveConfiguration s := ((writeMoveTick M)^[n]) (Turing.TM0.init input)

def microPhase : ReferenceMove → Fin 4
  | .stay => 1
  | .left => 2
  | .right => 3

/-- Phase zero fetches/writes; phases one, two and three finish stay/left/right. -/
def postMicroMachine {s : ℕ} (M : WriteMoveMachine s) :
    Turing.TM0.Machine (Fin 4) (Fin (s + 1) × Fin 4) := fun control symbol =>
  if control.2 = 0 then
    (M control.1 symbol).map (fun i => ((i.next, microPhase i.move), .write i.symbol))
  else if control.2 = 1 then some ((control.1, 0), .write symbol)
  else if control.2 = 2 then some ((control.1, 0), .move .left)
  else some ((control.1, 0), .move .right)

def postMachineTick {Λ : Type} [Inhabited Λ] (M : Turing.TM0.Machine (Fin 4) Λ)
    (q : Turing.TM0.Cfg (Fin 4) Λ) : Turing.TM0.Cfg (Fin 4) Λ :=
  (Turing.TM0.step M q).getD q

def microLift {s : ℕ} (q : WriteMoveConfiguration s) : MicroConfiguration s := ⟨(q.q, 0), q.Tape⟩

theorem post_micro_instruction {s : ℕ} (M : WriteMoveMachine s)
    (q : WriteMoveConfiguration s) (i : WriteMoveInstruction s)
    (instruction : M q.q q.Tape.head = some i) :
    postMachineTick (postMicroMachine M) (postMachineTick (postMicroMachine M) (microLift q)) =
      microLift (writeMoveApply q i) := by
  rcases i with ⟨next, symbol, move⟩
  cases move <;>
    simp [postMachineTick, Turing.TM0.step, postMicroMachine, microLift, instruction,
      microPhase, writeMoveApply, writeMoveTape, Turing.Tape.write_self]

theorem post_micro_two_ticks {s : ℕ} (M : WriteMoveMachine s) (q : WriteMoveConfiguration s) :
    postMachineTick (postMicroMachine M) (postMachineTick (postMicroMachine M) (microLift q)) =
      microLift (writeMoveTick M q) := by
  cases h : M q.q q.Tape.head with
  | none => simp [postMachineTick, Turing.TM0.step, postMicroMachine, microLift,
      writeMoveTick, writeMoveStep, h]
  | some i => simpa [writeMoveTick, writeMoveStep, h] using post_micro_instruction M q i h

theorem post_micro_run {s : ℕ} (M : WriteMoveMachine s) (input : List (Fin 4)) (n : ℕ) :
    ((postMachineTick (postMicroMachine M))^[2 * n]) (Turing.TM0.init input) =
      microLift (writeMoveRun M input n) := by
  unfold writeMoveRun
  change ((postMachineTick (postMicroMachine M))^[2 * n])
    (microLift (Turing.TM0.init input)) =
      microLift (((writeMoveTick M)^[n]) (Turing.TM0.init input))
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      Function.iterate_succ_apply']
    exact post_micro_two_ticks M _

def microControlEquiv (s : ℕ) : (Fin (s + 1) × Fin 4) ≃ Fin ((4 * s + 3) + 1) :=
  finProdFinEquiv.trans (finCongr (by omega))

def microPrizeConfiguration {s : ℕ} (q : MicroConfiguration s) :
    Turing.TM0.Cfg (Fin 4) (Fin ((4 * s + 3) + 1)) := ⟨microControlEquiv s q.q, q.Tape⟩

/-- The target has exactly the finite control type required by PrizeMachine. -/
def compileWriteMove {s : ℕ} (M : WriteMoveMachine s) : PrizeMachine (4 * s + 3) :=
  fun state symbol =>
    (postMicroMachine M ((microControlEquiv s).symm state) symbol).map
      (fun instruction => (microControlEquiv s instruction.1, instruction.2))

theorem post_micro_prize_step {s : ℕ} (M : WriteMoveMachine s) (q : MicroConfiguration s) :
    Turing.TM0.step (compileWriteMove M) (microPrizeConfiguration q) =
      (Turing.TM0.step (postMicroMachine M) q).map microPrizeConfiguration := by
  rcases q with ⟨state, tape⟩
  simp only [Turing.TM0.step, compileWriteMove, microPrizeConfiguration,
    Equiv.symm_apply_apply]
  cases h : postMicroMachine M state tape.head with
  | none => rfl
  | some instruction => rcases instruction with ⟨next, stmt⟩; cases stmt <;> rfl

theorem post_micro_prize_tick {s : ℕ} (M : WriteMoveMachine s) (q : MicroConfiguration s) :
    postMachineTick (compileWriteMove M) (microPrizeConfiguration q) =
      microPrizeConfiguration (postMachineTick (postMicroMachine M) q) := by
  unfold postMachineTick
  rw [post_micro_prize_step]
  cases h : Turing.TM0.step (postMicroMachine M) q <;> rfl

theorem post_micro_prize_iterate {s : ℕ} (M : WriteMoveMachine s) (q : MicroConfiguration s)
    (n : ℕ) :
    ((postMachineTick (compileWriteMove M))^[n]) (microPrizeConfiguration q) =
      microPrizeConfiguration (((postMachineTick (postMicroMachine M))^[n]) q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, post_micro_prize_tick]

theorem post_micro_prize_initial (s : ℕ) (input : List (Fin 4)) :
    microPrizeConfiguration (s := s) (Turing.TM0.init input) = Turing.TM0.init input := by
  unfold microPrizeConfiguration Turing.TM0.init
  congr 1

theorem post_compiler_run {s : ℕ} (M : WriteMoveMachine s) (input : List (Fin 4)) (n : ℕ) :
    prizeRun (compileWriteMove M) input (2 * n) =
      microPrizeConfiguration (microLift (writeMoveRun M input n)) := by
  change ((postMachineTick (compileWriteMove M))^[2 * n]) (Turing.TM0.init input) = _
  rw [← post_micro_prize_initial s input, post_micro_prize_iterate, post_micro_run]

theorem post_compiler_accepts {s : ℕ} (M : WriteMoveMachine s) (input : List (Fin 4)) (n : ℕ) :
    prizeAccepts (compileWriteMove M) input (2 * n) ↔
      (writeMoveRun M input n).Tape.head = 1 := by
  simp only [prizeAccepts, post_compiler_run, microPrizeConfiguration, microLift]

theorem post_micro_halt {s : ℕ} (M : WriteMoveMachine s) (q : WriteMoveConfiguration s) :
    Turing.TM0.step (postMicroMachine M) (microLift q) = none ↔ writeMoveStep M q = none := by
  simp [Turing.TM0.step, postMicroMachine, microLift, writeMoveStep]

theorem post_compiler_halts {s : ℕ} (M : WriteMoveMachine s) (input : List (Fin 4)) (n : ℕ) :
    prizeHalted (compileWriteMove M) input (2 * n) ↔
      writeMoveStep M (writeMoveRun M input n) = none := by
  unfold prizeHalted
  rw [post_compiler_run, post_micro_prize_step]
  simpa using post_micro_halt M (writeMoveRun M input n)

theorem post_compiler_polynomial_bound (c d length time : ℕ)
    (bound : time ≤ prizePolynomialBound c d length) :
    2 * time ≤ prizePolynomialBound (2 * c) d length := by
  unfold prizePolynomialBound at bound ⊢
  nlinarith

/-- The two ticks of a nonhalting source instruction are actual transitions. -/
theorem post_micro_actual_step {s : ℕ} (M : WriteMoveMachine s)
    (q q' : WriteMoveConfiguration s) (step : writeMoveStep M q = some q') :
    ∃ mid : MicroConfiguration s,
      Turing.TM0.step (postMicroMachine M) (microLift q) = some mid ∧
      Turing.TM0.step (postMicroMachine M) mid = some (microLift q') := by
  cases h : M q.q q.Tape.head with
  | none => simp [writeMoveStep, h] at step
  | some instruction =>
    have eq : writeMoveApply q instruction = q' := by simpa [writeMoveStep, h] using step
    rw [← eq]
    refine ⟨⟨(instruction.next, microPhase instruction.move), q.Tape.write instruction.symbol⟩, ?_, ?_⟩
    · simp [Turing.TM0.step, postMicroMachine, microLift, h]
    · rcases instruction with ⟨next, symbol, move⟩
      cases move <;> simp [Turing.TM0.step, postMicroMachine, microPhase, microLift,
        writeMoveApply, writeMoveTape, Turing.Tape.write_self]

theorem post_micro_actual_run {s : ℕ} (M : WriteMoveMachine s)
    {n : ℕ} {q q' : WriteMoveConfiguration s}
    (run : ReferenceRun (fun x y => writeMoveStep M x = some y) n q q') :
    ReferenceRun (fun x y => Turing.TM0.step (postMicroMachine M) x = some y)
      (2 * n) (microLift q) (microLift q') := by
  induction run with
  | zero _ => exact ReferenceRun.zero _
  | next run step ih =>
    obtain ⟨mid, first, second⟩ := post_micro_actual_step M _ _ step
    have result := ReferenceRun.next (ReferenceRun.next ih first) second
    simpa [Nat.mul_add, Nat.add_assoc] using result

theorem post_micro_rename_actual_run {s : ℕ} (M : WriteMoveMachine s)
    {n : ℕ} {q q' : MicroConfiguration s}
    (run : ReferenceRun (fun x y => Turing.TM0.step (postMicroMachine M) x = some y) n q q') :
    ReferenceRun (fun x y => Turing.TM0.step (compileWriteMove M) x = some y)
      n (microPrizeConfiguration q) (microPrizeConfiguration q') := by
  induction run with
  | zero _ => exact ReferenceRun.zero _
  | next run step ih =>
    apply ReferenceRun.next ih
    rw [post_micro_prize_step, step]
    rfl

theorem post_compiler_actual_run {s : ℕ} (M : WriteMoveMachine s)
    {n : ℕ} {q q' : WriteMoveConfiguration s}
    (run : ReferenceRun (fun x y => writeMoveStep M x = some y) n q q') :
    ReferenceRun (fun x y => Turing.TM0.step (compileWriteMove M) x = some y)
      (2 * n) (microPrizeConfiguration (microLift q)) (microPrizeConfiguration (microLift q')) := by
  exact post_micro_rename_actual_run M (post_micro_actual_run M run)

theorem post_micro_pending_not_halted {s : ℕ} (M : WriteMoveMachine s)
    (state : Fin (s + 1)) (phase : Fin 4) (pending : phase ≠ 0) (tape : Turing.Tape (Fin 4)) :
    Turing.TM0.step (postMicroMachine M) ⟨(state, phase), tape⟩ ≠ none := by
  fin_cases phase <;> simp_all [Turing.TM0.step, postMicroMachine]

end IndependentDuodenary
