import IndependentDuodenary

open IndependentDuodenary

example {r s : ℕ} (select : Fin s → Fin r) (h : RegisterTranslation r) (n : ℕ)
    (q : RegisterState r) :
    projectRegisters select (((registerStep h)^[n]) q) =
      (((registerStep (fun i => h (select i)))^[n]) (projectRegisters select q)) :=
  register_step_projection_iterate select h n q

example {r : ℕ} (hr : 0 < r) (h : RegisterTranslation r) (n : ℕ) :
    (∀ q : RegisterState r, ((registerStep h)^[n]) q = q) ↔ 12 ∣ n :=
  register_step_period_iff hr h n

example {r : ℕ} (base : Fin r) (h : RegisterTranslation r) (q : RegisterState r)
    (hq : PhaseRegular q) :
    Function.Injective (fun n : Fin 12 => ((registerStep h)^[n.val]) q) :=
  register_regular_orbit_injective base h q hq

example {r : ℕ} (A : RegisterState r → RegisterState r) (n : ℕ) (q : RegisterState r) :
    ((transportRegisterWords A)^[n]) (encodeRegisterState q) = encodeRegisterState ((A^[n]) q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, register_transport_encode]

example {r : ℕ} (h : RegisterTranslation r) (n : ℕ) (a : RegisterPhase r) :
    DecodedRegisterProperty (fun p => PhaseRegular p ∧
      ExternalRelativeEquivalent a (registerPhases p))
      (((transportRegisterWords (registerStep h))^[n]) (encodeRegisterState (phaseRegisterState a))) := by
  have hp := register_word_modular_bridge h n (phaseRegisterState a) (phase_register_regular a)
  simpa only [phase_register_label] using hp

example {r : ℕ} (h : RegisterTranslation r) (n : ℕ) (q : RegisterState r) :
    DecodedRegisterProperty (fun p => ∀ i, (p i).metadata = (q i).metadata)
      (((transportRegisterWords (registerStep h))^[n]) (encodeRegisterState q)) := by
  rw [register_transport_iterate, decoded_register_property_encode]
  exact fun i => register_step_metadata_invariant h n q i

example {r : ℕ} (base : Fin r) (a b : RegisterPhase r) :
    ExternalRelativeEquivalent a b ↔ ∃ c : ZMod 12, ∀ i, b i = a i + c :=
  external_relative_equivalence_offset base a b

def initialRegisters : RegisterState 3 := phaseRegisterState ![0, 4, 11]
def registerFixtureTranslation : RegisterTranslation 3 := ![![1, 0], ![0, 1], ![1, 1]]
def registerFixtureStep := registerStep registerFixtureTranslation

def twoInitialRegisters : RegisterState 2 := phaseRegisterState 0

#guard registerPhases initialRegisters = ![0, 4, 11]
#guard registerPhases ((registerFixtureStep^[13]) initialRegisters) = ![1, 5, 0]
#guard (registerFixtureStep^[12]) initialRegisters = initialRegisters
#guard (registerFixtureStep^[6]) initialRegisters ≠ initialRegisters
#guard relativePhases (registerPhases ((registerFixtureStep^[13]) initialRegisters)) 0 1 = 4
#guard projectRegisters ![2, 0] ((registerFixtureStep^[13]) initialRegisters) =
  (((registerStep (fun i : Fin 2 => registerFixtureTranslation (![2, 0] i)))^[13])
    (projectRegisters ![2, 0] initialRegisters))
#guard decodeRegisterWords 3 (encodeRegisterState initialRegisters) = some initialRegisters
#guard decodeRegisterWords 3 (fun i => if i = 1 then [] else encodeRegisterState initialRegisters i) = none
#guard ((transportRegisterWords registerFixtureStep)^[2]) (encodeRegisterState initialRegisters) =
  encodeRegisterState ((registerFixtureStep^[2]) initialRegisters)
#guard decodeRegisterWords 3 (((transportRegisterWords registerFixtureStep)^[2])
  (encodeRegisterState initialRegisters)) = some ((registerFixtureStep^[2]) initialRegisters)
#guard (∑ i : Fin 2, registerPhases ((registerCycle^[6]) twoInitialRegisters) i) = 0
#guard (registerCycle^[6]) twoInitialRegisters ≠ twoInitialRegisters
