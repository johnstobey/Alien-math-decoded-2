import IndependentDuodenary.SearchBoundary

open IndependentDuodenary

def searchBoundaryZero : RegisterState 1 := fun _ => ⟨0, 0, 0⟩
def searchBoundaryOtherMetadata : RegisterState 1 := fun _ => ⟨1, 0, 0⟩

#guard protocolReachabilityCheck (fun _ => 0) searchBoundaryZero searchBoundaryZero = true
#guard protocolReachabilityCheck (fun _ => 0) searchBoundaryZero searchBoundaryOtherMetadata = false
#guard protocolReachabilityCheck (r := 0) (fun _ => 0) Fin.elim0 Fin.elim0 = true
#guard protocolReachabilityCheck (fun _ => 0) (fun _ => keyCycleWitness)
  (((registerStep (r := 1) (fun _ => 0))^[7]) (fun _ => keyCycleWitness)) = true

example (h : RegisterTranslation 1) (seeds : Finset (RegisterState 1))
    (covers : ∀ x : RegisterState 1, ∃ q ∈ seeds, x ∈ protocolOrbitCandidates h q) :
    4096 ≤ seeds.card := protocol_one_register_cover_needs_4096 h seeds covers
