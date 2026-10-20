import IndependentDuodenary.PipelineSynthesis
import Mathlib.Computability.TuringMachine

/-! Finite-protocol bounds and a separately stated machine-model conjecture.
The conjecture below is a definition, not a proved consequence of these bounds. -/
namespace IndependentDuodenary

theorem protocol_iterate_mod_twelve {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (q : RegisterState r) :
    ((registerStep h)^[n]) q = ((registerStep h)^[n % 12]) q := by
  have hid : (registerStep h)^[12] = id := funext (register_step_period_twelve h)
  calc
    _ = ((registerStep h)^[n % 12 + 12 * (n / 12)]) q :=
      congrArg (fun k => ((registerStep h)^[k]) q) (Nat.mod_add_div n 12).symm
    _ = _ := by rw [Function.iterate_add_apply, Function.iterate_mul, hid]; simp

def protocolOrbitCandidates {r : ℕ} (h : RegisterTranslation r) (q : RegisterState r) :
    Finset (RegisterState r) := Finset.univ.image (fun k : Fin 12 => ((registerStep h)^[k.val]) q)

theorem protocol_orbit_candidate_bound {r : ℕ} (h : RegisterTranslation r) (q : RegisterState r) :
    (protocolOrbitCandidates h q).card ≤ 12 := by
  exact (Finset.card_image_le).trans (by simp)

theorem protocol_orbit_candidates_complete {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (q : RegisterState r) : ((registerStep h)^[n]) q ∈ protocolOrbitCandidates h q := by
  rw [protocol_iterate_mod_twelve]
  exact Finset.mem_image.mpr ⟨⟨n % 12, Nat.mod_lt _ (by decide)⟩, Finset.mem_univ _, rfl⟩

def keyCoefficientEquiv : RepresentedKey ≃ CanonicalCoefficients where
  toFun q := (q.metadata, q.binaryIntercept, q.complementIntercept)
  invFun c := ⟨c.1, c.2.1, c.2.2⟩
  left_inv q := by cases q; rfl
  right_inv c := by rcases c with ⟨m, k, w⟩; rfl

theorem complete_key_cardinality : Nat.card RepresentedKey = 49152 := by
  rw [Nat.card_congr keyCoefficientEquiv]
  simp [CanonicalCoefficients, KeyMetadata, KeyBinary, KeyComplement, Nat.card_eq_fintype_card,
    Fintype.card_fun]

theorem complete_register_cardinality (r : ℕ) : Nat.card (RegisterState r) = 49152 ^ r := by
  rw [Nat.card_fun, complete_key_cardinality]
  simp

/-- Number of majority-decoder symbol positions in one protected full frame. -/
def majoritySymbolBudget (r : ℕ) : ℕ := 51 * r

theorem majority_symbol_budget_linear (r : ℕ) : majoritySymbolBudget r = 3 * (17 * r) := by
  unfold majoritySymbolBudget
  omega

/-- Counts frames, not Turing-machine execution time. -/
theorem protected_frame_width {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (ops : List StationExpr) (x : CanonicalSubstrate r) (i : Fin r) :
    (pipelineTransmit h n ops x i).length = 17 := by
  unfold pipelineTransmit
  rw [station_program_compilation]
  exact canonical_transmitted_word_length (registerStep h) n (compileStationProgram ops) x i

/-! Explicit verifier-based complexity definitions on Mathlib's finite Post-Turing
machines. Equivalence with other standard machine encodings is not proved here. -/
abbrev PrizeBinaryWord := List Bool
abbrev PrizeBinaryLanguage := Set PrizeBinaryWord
abbrev PrizeMachine (states : ℕ) := Turing.TM0.Machine (Fin 4) (Fin (states + 1))

def prizeEncodeWord (x : PrizeBinaryWord) : List (Fin 4) := x.map (fun b => if b then 2 else 1)

def prizeEncodePair (x w : PrizeBinaryWord) : List (Fin 4) :=
  prizeEncodeWord x ++ [3] ++ prizeEncodeWord w

def prizeRun {states : ℕ} (M : PrizeMachine states) (input : List (Fin 4)) (t : ℕ) :
    Turing.TM0.Cfg (Fin 4) (Fin (states + 1)) :=
  ((fun cfg => (Turing.TM0.step M cfg).getD cfg)^[t]) (Turing.TM0.init input)

def prizeHalted {states : ℕ} (M : PrizeMachine states) (input : List (Fin 4)) (t : ℕ) : Prop :=
  Turing.TM0.step M (prizeRun M input t) = none

def prizeAccepts {states : ℕ} (M : PrizeMachine states) (input : List (Fin 4)) (t : ℕ) : Prop :=
  (prizeRun M input t).Tape.head = 1

def prizeBooleanOutput {states : ℕ} (M : PrizeMachine states) (input : List (Fin 4)) (t : ℕ) : Prop :=
  (prizeRun M input t).Tape.head = 1 ∨ (prizeRun M input t).Tape.head = 2

def prizePolynomialBound (c d n : ℕ) : ℕ := c * (n + 1) ^ d

def PrizeDeterministicPolynomial (L : PrizeBinaryLanguage) : Prop :=
  ∃ states, ∃ M : PrizeMachine states, ∃ c d : ℕ, ∀ x : PrizeBinaryWord,
    prizeHalted M (prizeEncodeWord x) (prizePolynomialBound c d x.length) ∧
    prizeBooleanOutput M (prizeEncodeWord x) (prizePolynomialBound c d x.length) ∧
    (x ∈ L ↔ prizeAccepts M (prizeEncodeWord x) (prizePolynomialBound c d x.length))

def PrizeCertificatePolynomial (L : PrizeBinaryLanguage) : Prop :=
  ∃ states, ∃ M : PrizeMachine states, ∃ c d cw dw : ℕ,
    (∀ x w : PrizeBinaryWord,
      prizeHalted M (prizeEncodePair x w) (prizePolynomialBound c d (x.length + w.length)) ∧
      prizeBooleanOutput M (prizeEncodePair x w) (prizePolynomialBound c d (x.length + w.length))) ∧
    (∀ x : PrizeBinaryWord, x ∈ L ↔ ∃ w : PrizeBinaryWord,
      w.length ≤ prizePolynomialBound cw dw x.length ∧
      prizeAccepts M (prizeEncodePair x w) (prizePolynomialBound c d (x.length + w.length)))

/-- An unproved P-versus-NP inequality for the explicitly defined machine model. -/
def PVersusNPConjecture : Prop :=
  {L : PrizeBinaryLanguage | PrizeDeterministicPolynomial L} ≠
    {L : PrizeBinaryLanguage | PrizeCertificatePolynomial L}

end IndependentDuodenary
