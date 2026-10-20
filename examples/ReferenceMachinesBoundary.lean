import IndependentDuodenary.ReferenceMachines

open IndependentDuodenary

private def acceptMachine : ReferenceDeterministicMachine 0 0 0 where
  initial := 0
  transition _ _ := ⟨0, fun _ => 0, fun _ => .stay⟩

private def branchMachine : ReferenceNondeterministicMachine 0 1 0 where
  initial := 2
  first _ _ := ⟨0, fun _ => 1, fun _ => .right⟩
  rest _ _ := [⟨1, fun _ => 2, fun _ => .left⟩]

example : ReferenceP Set.univ := by
  refine ⟨0, 0, 0, acceptMachine, 1, 0, ?_⟩
  intro x
  refine ⟨0, by simp [prizePolynomialBound], referenceInitial 0 x,
    ReferenceRun.zero _, ?_, ?_⟩
  · exact Or.inl rfl
  · simp [referenceInitial]

example : (referenceInitial (a := 0) (s := 0) (k := 0) 0 [false, true]).tape 0 0 = 1 := by
  decide
example : (referenceInitial (a := 0) (s := 0) (k := 0) 0 [false, true]).tape 0 1 = 2 := by
  decide
example : (referenceInitial (a := 0) (s := 0) (k := 0) 0 [false, true]).tape 0 2 = 0 := by
  decide
example : (referenceInitial (a := 0) (s := 0) (k := 0) 0 [false, true]).tape 0 (-1) = 0 := by
  decide
example : (referenceNSuccessors branchMachine (referenceInitial 2 [])).length = 2 := by
  decide
example : referenceNEdge branchMachine (referenceInitial 2 [])
    (referenceApply (referenceInitial 2 []) ⟨0, fun _ => 1, fun _ => .right⟩) := by
  simp [referenceNEdge, referenceNSuccessors, referenceTerminal, referenceInitial, branchMachine]

example : referenceNEdge branchMachine (referenceInitial 2 [])
    (referenceApply (referenceInitial 2 []) ⟨1, fun _ => 2, fun _ => .left⟩) := by
  simp [referenceNEdge, referenceNSuccessors, referenceTerminal, referenceInitial, branchMachine]

example : ReferenceRun (referenceNEdge branchMachine) 1 (referenceInitial 2 [])
    (referenceApply (referenceInitial 2 []) ⟨0, fun _ => 1, fun _ => .right⟩) := by
  apply ReferenceRun.next (ReferenceRun.zero _)
  simp [referenceNEdge, referenceNSuccessors, referenceTerminal, referenceInitial, branchMachine]

example : (referenceApply (referenceInitial (a := 0) (s := 1) (k := 0) 2 [])
    ⟨0, fun _ => 1, fun _ => .right⟩).head 0 = 1 := by decide

example : (referenceApply (referenceInitial (a := 0) (s := 1) (k := 0) 2 [])
    ⟨1, fun _ => 2, fun _ => .left⟩).head 0 = -1 := by decide
