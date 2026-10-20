import IndependentDuodenary.MillenniumBridge

open IndependentDuodenary

example : Nat.card RepresentedKey = 49152 := complete_key_cardinality
example (r : ℕ) : Nat.card (RegisterState r) = 49152 ^ r :=
  complete_register_cardinality r
example {r : ℕ} (h : RegisterTranslation r) (q : RegisterState r) :
    (protocolOrbitCandidates h q).card ≤ 12 := protocol_orbit_candidate_bound h q
example {r : ℕ} (h : RegisterTranslation r) (q : RegisterState r) (n : ℕ) :
    ((registerStep h)^[n]) q ∈ protocolOrbitCandidates h q :=
  protocol_orbit_candidates_complete h n q
example : Nat.card (RegisterState 0) = 1 := by
  rw [complete_register_cardinality]; rfl
#guard majoritySymbolBudget 0 = 0
#guard majoritySymbolBudget 2 = 102
#guard prizePolynomialBound 3 2 4 = 75
#guard prizeEncodePair [false] [true] = [1, 3, 2]
