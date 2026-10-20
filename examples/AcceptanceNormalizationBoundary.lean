import IndependentDuodenary.AcceptanceNormalization

open IndependentDuodenary

private def acceptNow : ReferenceDeterministicMachine 0 0 0 where
  initial := 0
  transition _ read := ⟨0, read, fun _ => .stay⟩

private def rejectNow : ReferenceDeterministicMachine 0 0 0 where
  initial := 1
  transition _ read := ⟨1, read, fun _ => .stay⟩

example : normalizationStep acceptNow .stateToHead
    (normalizationLift (referenceInitial 0 [])) =
      some (normalizationFinish .stateToHead (referenceInitial 0 [])) := by
  exact normalization_halt_step acceptNow .stateToHead _ (Or.inl rfl)

example : (normalizationFinish .stateToHead
    (referenceInitial (a := 0) (s := 0) (k := 0) 0 [])).body.tape 0 0 = 1 := by decide

example : (normalizationFinish .stateToHead
    (referenceInitial (a := 0) (s := 0) (k := 0) 1 [])).body.tape 0 0 = 2 := by decide

-- Empty input's blank head is not interpreted as an accepting output.
example : (normalizationFinish .headToState
    (referenceInitial (a := 0) (s := 0) (k := 0) 0 [])).body.state = 1 := by decide

-- Head-output convention reads the head, independently of the old terminal label.
example : (normalizationFinish .headToState
    (referenceInitial (a := 0) (s := 0) (k := 0) 1 [false])).body.state = 0 := by decide

example : (normalizationFinish .headToState
    (referenceInitial (a := 0) (s := 0) (k := 0) 0 [true])).body.state = 1 := by decide

example : ReferenceRun (normalizationEdge rejectNow .stateToHead) 1
    (normalizationLift (referenceInitial 1 []))
    (normalizationFinish .stateToHead (referenceInitial 1 [])) := by
  exact normalization_empty_input rejectNow .stateToHead (Or.inr rfl)

example : normalizationStep acceptNow .stateToHead
    (normalizationFinish .stateToHead (referenceInitial 0 [])) = none := by
  exact normalization_done_stops _ _ _ rfl

example : 0 + 1 ≤ prizePolynomialBound (0 + 1) 0 0 := by
  exact normalization_polynomial_overhead 0 0 0 0 (by decide)

private def oneStepMachine : ReferenceDeterministicMachine 0 1 0 where
  initial := 2
  transition _ read := ⟨0, read, fun _ => .right⟩

example : (normalizationStep oneStepMachine .stateToHead
    (normalizationLift (referenceInitial 2 []))).map (fun q => q.done) = some false := rfl

example : (normalizationFinish .stateToHead
    (referenceApply (referenceInitial (a := 0) (s := 1) (k := 0) 2 [])
      ⟨0, fun _ => 0, fun _ => .right⟩)).body.tape 0 1 = 1 := by decide
