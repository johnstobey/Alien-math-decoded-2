import IndependentDuodenary.PostMicrocode

open IndependentDuodenary

private def oneInstruction (move : ReferenceMove) : WriteMoveMachine 1 :=
  fun state _ => if state = 0 then some ⟨1, 1, move⟩ else none

private def initiallyHalted : WriteMoveMachine 0 := fun _ _ => none

example : prizeAccepts (compileWriteMove (oneInstruction .stay)) [] 2 := rfl
example : prizeHalted (compileWriteMove (oneInstruction .stay)) [] 2 := rfl

-- Writing an accepting symbol does not halt in the pending phase.
example : ¬ prizeHalted (compileWriteMove (oneInstruction .stay)) [] 1 := by
  intro h
  cases h

example : (prizeRun (compileWriteMove (oneInstruction .left)) [2] 2).Tape.head = 0 := rfl
example : (prizeRun (compileWriteMove (oneInstruction .left)) [2] 2).Tape.nth 1 = 1 := rfl
example : (prizeRun (compileWriteMove (oneInstruction .right)) [2, 3] 2).Tape.head = 3 := rfl
example : (prizeRun (compileWriteMove (oneInstruction .right)) [2, 3] 2).Tape.nth (-1) = 1 := rfl

example : prizeHalted (compileWriteMove initiallyHalted) [] 0 := rfl
example : (prizeRun (compileWriteMove initiallyHalted) [2] 14).Tape.head = 2 := rfl

example (input : List (Fin 4)) :
    prizeRun (compileWriteMove initiallyHalted) input 0 =
      microPrizeConfiguration (microLift (writeMoveRun initiallyHalted input 0)) := by
  exact post_compiler_run initiallyHalted input 0
