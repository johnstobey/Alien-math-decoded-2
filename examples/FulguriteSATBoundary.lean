import IndependentDuodenary.FulguriteSAT

open IndependentDuodenary

private def witnessFormula : DiscoveryFormula 2 :=
  .conjunction (.disjunction (.atom 0) (.atom 1)) (.negation (.atom 0))

private def contradictionFormula : DiscoveryFormula 1 :=
  .conjunction (.atom 0) (.negation (.atom 0))

example : discoveryEval (fun i => decide (i.val = 1)) witnessFormula = true := by decide

example : fulguriteEval (fulguriteCompileAssignment (fun i => decide (i.val = 1)))
    (discoveryCompile witnessFormula) = 6 := by decide

example : ∃ p : RegisterPhase 2, obsidianAssignmentLaw p ∧
    fulguriteEval p (discoveryCompile witnessFormula) = 6 := by
  apply (fulgurite_satisfiability_equivalence witnessFormula).mp
  exact ⟨fun i => decide (i.val = 1), by decide⟩

example : ¬ ∃ p : RegisterPhase 1, obsidianAssignmentLaw p ∧
    fulguriteEval p (discoveryCompile contradictionFormula) = 6 := by
  intro h
  obtain ⟨a, ha⟩ := (fulgurite_satisfiability_equivalence contradictionFormula).mpr h
  cases hv : a 0 <;> simp [contradictionFormula, discoveryEval, hv] at ha

example : (fulguriteDiscover 1
    (.halfTurn (.halfTurn (.read (0 : Fin 1))))).val = .read 0 := rfl

example : (fulguriteDiscover 1
    (.meet (.read (0 : Fin 2)) (.read 1))).val = .meet (.read 1) (.read 0) := rfl

-- Commutation can cycle: fuel bounds the search without claiming convergence.
example : (fulguriteDiscover 2
    (.meet (.read (0 : Fin 2)) (.read 1))).val = .meet (.read 0) (.read 1) := rfl

-- The bit law is necessary for commutation of the conditional gates.
example : fulguriteMeet 6 1 ≠ fulguriteMeet 1 6 := by decide

-- Conjunction is not multiplication in this encoding.
example : fulguriteBit true * fulguriteBit true ≠ fulguriteBit (true && true) := by decide

example : ∃ p : RegisterPhase 1, ¬ obsidianAssignmentLaw p := by
  refine ⟨fun _ => 1, ?_⟩
  intro h
  have hi := h 0
  have bad : ¬ obsidianBitLaw (1 : ZMod 12) := by unfold obsidianBitLaw; decide
  exact bad hi
