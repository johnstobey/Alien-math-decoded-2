import IndependentDuodenary.RegisterDynamics

/-! Exact conjugacy on encoded states and a concrete modular comparison.
ExternalRelativeEquivalent means equality of modular relative phases only;
it does not mean equality of full keys or identify an external paper theorem. -/
namespace IndependentDuodenary

abbrev RegisterWords (r : ℕ) := Fin r → List (ZMod 12)

def encodeRegisterState {r : ℕ} (q : RegisterState r) : RegisterWords r :=
  fun i => encodeExactKey (q i)

def decodeRegisterWords : (r : ℕ) → RegisterWords r → Option (RegisterState r)
  | 0, _ => some Fin.elim0
  | r + 1, words => do
    let q ← decodeExactKey (words 0)
    let qs ← decodeRegisterWords r (fun i => words i.succ)
    pure (Fin.cons q qs)

theorem register_decode_encode (r : ℕ) (q : RegisterState r) :
    decodeRegisterWords r (encodeRegisterState q) = some q := by
  induction r with
  | zero =>
    have hq : q = Fin.elim0 := Subsingleton.elim _ _
    simp [decodeRegisterWords, hq]
  | succ r ih =>
    simp only [decodeRegisterWords, encodeRegisterState, exact_key_decode_encode, Option.some_bind]
    change (decodeRegisterWords r (encodeRegisterState (fun i => q i.succ))).bind
      (fun qs : RegisterState r => some (Fin.cons (α := fun _ => RepresentedKey) (q 0) qs)) = some q
    rw [ih]
    simpa only [Option.some_bind, Option.some.injEq] using (Fin.cons_self_tail q)

theorem register_parse_sound (r : ℕ) (words : RegisterWords r) (q : RegisterState r)
    (h : decodeRegisterWords r words = some q) : words = encodeRegisterState q := by
  induction r with
  | zero => exact Subsingleton.elim _ _
  | succ r ih =>
    cases hh : decodeExactKey (words 0) with
    | none => simp [decodeRegisterWords, hh] at h
    | some head =>
      cases ht : decodeRegisterWords r (fun i => words i.succ) with
      | none => simp [decodeRegisterWords, hh, ht] at h
      | some tail =>
        have hq : Fin.cons (α := fun _ => RepresentedKey) head tail = q := by
          simpa [decodeRegisterWords, hh, ht] using h
        subst q
        have hs := ih (fun i => words i.succ) tail ht
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact exact_key_parse_sound (words 0) head hh
        · exact congrFun hs j

theorem register_encoding_injective {r : ℕ} : Function.Injective (@encodeRegisterState r) := by
  intro q p heq
  have hd := congrArg (decodeRegisterWords r) heq
  simpa only [register_decode_encode, Option.some.injEq] using hd

theorem register_reject_malformed {r : ℕ} (words : RegisterWords r)
    (h : ∀ q : RegisterState r, words ≠ encodeRegisterState q) : decodeRegisterWords r words = none := by
  cases hd : decodeRegisterWords r words with
  | none => rfl
  | some q => exact False.elim (h q (register_parse_sound r words q hd))

def projectRegisterWords {r s : ℕ} (select : Fin s → Fin r) (words : RegisterWords r) :
    RegisterWords s := fun i => words (select i)

theorem register_encoding_projection {r s : ℕ} (select : Fin s → Fin r) (q : RegisterState r) :
    projectRegisterWords select (encodeRegisterState q) =
      encodeRegisterState (projectRegisters select q) := rfl

/-- The action is specified on all words, with exact conjugacy on encoded states. -/
def transportRegisterWords {r : ℕ} (A : RegisterState r → RegisterState r)
    (words : RegisterWords r) : RegisterWords r :=
  match decodeRegisterWords r words with
  | none => fun _ => []
  | some q => encodeRegisterState (A q)

theorem register_transport_encode {r : ℕ} (A : RegisterState r → RegisterState r)
    (q : RegisterState r) :
    transportRegisterWords A (encodeRegisterState q) = encodeRegisterState (A q) := by
  simp [transportRegisterWords, register_decode_encode]

/-- Inductive bridge from arbitrary structural iterations to exact word iterations. -/
theorem register_transport_iterate {r : ℕ} (A : RegisterState r → RegisterState r)
    (n : ℕ) (q : RegisterState r) :
    ((transportRegisterWords A)^[n]) (encodeRegisterState q) = encodeRegisterState ((A^[n]) q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, register_transport_encode]

theorem register_decoded_transport_iterate {r : ℕ} (A : RegisterState r → RegisterState r)
    (n : ℕ) (q : RegisterState r) :
    decodeRegisterWords r (((transportRegisterWords A)^[n]) (encodeRegisterState q)) =
      some ((A^[n]) q) := by
  rw [register_transport_iterate, register_decode_encode]

theorem register_transport_reflects_equality {r : ℕ}
    (A B : RegisterState r → RegisterState r) (n m : ℕ) (q p : RegisterState r) :
    ((transportRegisterWords A)^[n]) (encodeRegisterState q) =
      ((transportRegisterWords B)^[m]) (encodeRegisterState p) ↔ (A^[n]) q = (B^[m]) p := by
  rw [register_transport_iterate, register_transport_iterate]
  exact register_encoding_injective.eq_iff

def DecodedRegisterProperty {r : ℕ} (P : RegisterState r → Prop) (words : RegisterWords r) : Prop :=
  ∃ q, decodeRegisterWords r words = some q ∧ P q

theorem decoded_register_property_encode {r : ℕ} (P : RegisterState r → Prop)
    (q : RegisterState r) : DecodedRegisterProperty P (encodeRegisterState q) ↔ P q := by
  simp [DecodedRegisterProperty, register_decode_encode]

/-- The invariance premise is explicit; concrete instances are discharged below. -/
theorem register_inductive_invariant_transport {r : ℕ}
    (A : RegisterState r → RegisterState r) (P : RegisterState r → Prop)
    (hstep : ∀ q, P q → P (A q)) (n : ℕ) (q : RegisterState r) (hq : P q) :
    DecodedRegisterProperty P (((transportRegisterWords A)^[n]) (encodeRegisterState q)) := by
  rw [register_transport_iterate, decoded_register_property_encode]
  induction n with
  | zero => exact hq
  | succ n ih => rw [Function.iterate_succ_apply']; exact hstep _ ih

/-- A specified modular comparison, not an unspecified external equivalence. -/
def ExternalRelativeEquivalent {r : ℕ} (a b : RegisterPhase r) : Prop :=
  ∀ i j, relativePhases b i j = relativePhases a i j

theorem external_relative_equivalence_offset {r : ℕ} (base : Fin r) (a b : RegisterPhase r) :
    ExternalRelativeEquivalent a b ↔ ∃ c : ZMod 12, ∀ i, b i = a i + c :=
  relative_phases_iff_common_offset base a b

theorem external_relative_equivalence_step {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (q : RegisterState r) (hq : PhaseRegular q) :
    ExternalRelativeEquivalent (registerPhases q) (registerPhases (((registerStep h)^[n]) q)) :=
  fun i j => register_step_relative_invariant h n q hq i j

/-- Concrete modular invariant, with the regularity boundary proved preserved. -/
theorem register_word_modular_bridge {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (q : RegisterState r) (hq : PhaseRegular q) :
    DecodedRegisterProperty (fun p => PhaseRegular p ∧
      ExternalRelativeEquivalent (registerPhases q) (registerPhases p))
      (((transportRegisterWords (registerStep h))^[n]) (encodeRegisterState q)) := by
  rw [register_transport_iterate, decoded_register_property_encode]
  exact ⟨register_step_regular_iterate h n q hq, external_relative_equivalence_step h n q hq⟩

theorem register_word_metadata_bridge {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (q : RegisterState r) :
    DecodedRegisterProperty (fun p => ∀ i, (p i).metadata = (q i).metadata)
      (((transportRegisterWords (registerStep h))^[n]) (encodeRegisterState q)) := by
  rw [register_transport_iterate, decoded_register_property_encode]
  exact fun i => register_step_metadata_invariant h n q i

theorem register_word_modular_bridge_phase {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (a : RegisterPhase r) :
    DecodedRegisterProperty (fun p => PhaseRegular p ∧
      ExternalRelativeEquivalent a (registerPhases p))
      (((transportRegisterWords (registerStep h))^[n]) (encodeRegisterState (phaseRegisterState a))) := by
  have hp := register_word_modular_bridge h n (phaseRegisterState a) (phase_register_regular a)
  simpa only [phase_register_label] using hp

theorem register_word_projection_bridge {r s : ℕ} (select : Fin s → Fin r)
    (h : RegisterTranslation r) (n : ℕ) (q : RegisterState r) :
    projectRegisterWords select
      (((transportRegisterWords (registerStep h))^[n]) (encodeRegisterState q)) =
    (((transportRegisterWords (registerStep (fun i => h (select i))))^[n])
      (encodeRegisterState (projectRegisters select q))) := by
  rw [register_transport_iterate, register_transport_iterate, register_encoding_projection,
    register_step_projection_iterate]

theorem register_word_regular_orbit_injective {r : ℕ} (base : Fin r)
    (h : RegisterTranslation r) (q : RegisterState r) (hq : PhaseRegular q) :
    Function.Injective (fun n : Fin 12 =>
      ((transportRegisterWords (registerStep h))^[n.val]) (encodeRegisterState q)) := by
  intro n m heq
  change ((transportRegisterWords (registerStep h))^[n.val]) (encodeRegisterState q) =
    ((transportRegisterWords (registerStep h))^[m.val]) (encodeRegisterState q) at heq
  rw [register_transport_iterate, register_transport_iterate] at heq
  exact register_regular_orbit_injective base h q hq (register_encoding_injective heq)

/-- Relative modular equivalence is strictly weaker than exact representation equality. -/
theorem external_relative_equivalence_not_lossless :
    ∃ q p : RegisterState 1, ExternalRelativeEquivalent (registerPhases q) (registerPhases p) ∧
      encodeRegisterState q ≠ encodeRegisterState p := by
  let q : RegisterState 1 := fun _ => keyCycleWitness
  let h : RegisterTranslation 1 := fun _ => ![1, 0]
  refine ⟨q, registerTranslate h q, ?_, ?_⟩
  · rw [register_translation_phase_invariant]
    exact fun _ _ => rfl
  · intro heq
    have hqp := register_encoding_injective heq
    have hb := congrArg (fun p : RegisterState 1 => (p 0).binaryIntercept 0) hqp
    change (0 : ZMod 2) = 1 at hb
    exact (by decide : (0 : ZMod 2) ≠ 1) hb

end IndependentDuodenary
