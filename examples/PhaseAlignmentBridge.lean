import IndependentDuodenary.FulguriteSAT

/-! Experimental phase relations and conditional-free ring semantics.
No identification of physical, cognitive or historical sources is a premise.
This is not a construction of fixed-registerStep reachability. -/
namespace IndependentDuodenary.PhaseAlignmentInvestigation

def aligned (x y : ZMod 12) : Prop := y - x = 0

def bit : Bool → ZMod 12
  | false => 0
  | true => 1

def valid {n : ℕ} (p : RegisterPhase n) : Prop := ∀ i, p i = 0 ∨ p i = 1

def encode {n : ℕ} (a : Fin n → Bool) : RegisterPhase n := fun i => bit (a i)

def decode {n : ℕ} (p : RegisterPhase n) : Fin n → Bool := fun i => decide (p i = 1)

/-- NOT, AND and OR are represented by ring subtraction, multiplication and
addition. The input encoding does not inspect the formula's satisfying inputs. -/
def arithmeticEval {n : ℕ} (p : RegisterPhase n) : DiscoveryFormula n → ZMod 12
  | .atom i => p i
  | .negation f => 1 - arithmeticEval p f
  | .conjunction f g => arithmeticEval p f * arithmeticEval p g
  | .disjunction f g =>
    let x := arithmeticEval p f
    let y := arithmeticEval p g
    x + y - x * y

theorem zero_ne_one_phase : (0 : ZMod 12) ≠ 1 := by decide

theorem alignment_iff_equal (x y : ZMod 12) : aligned x y ↔ x = y := by
  simp [aligned, sub_eq_zero, eq_comm]

theorem alignment_rotation_invariant (x y t : ZMod 12) :
    aligned (x + t) (y + t) ↔ aligned x y := by
  simp [alignment_iff_equal]

theorem alignment_is_boolean_equality (a b : Bool) :
    aligned (bit a) (bit b) ↔ a = b := by
  cases a <;> cases b <;> unfold aligned bit <;> decide

theorem unanchored_alignment_is_not_and :
    ¬ (∀ a b : Bool, aligned (bit a) (bit b) ↔ (a && b) = true) := by
  intro h
  have hh := (h false false).mp (by unfold aligned bit; decide)
  contradiction

/-- Translate the false/true anchors together with the operands. The true
endpoint has coordinate origin+1, so its doubled coordinate is 2*origin+2. -/
theorem anchored_sum_encodes_and (origin : ZMod 12) (a b : Bool) :
    aligned ((origin + bit a) + (origin + bit b))
      ((origin + 1) + (origin + 1)) ↔ (a && b) = true := by
  cases a <;> cases b <;> simp only [aligned, bit]
  all_goals ring_nf
  all_goals decide

theorem multiplication_encodes_and (a b : Bool) :
    bit a * bit b = bit (a && b) := by
  cases a <;> cases b <;> decide

theorem ring_encodes_or (a b : Bool) :
    bit a + bit b - bit a * bit b = bit (a || b) := by
  cases a <;> cases b <;> decide

theorem ring_encodes_not (a : Bool) : 1 - bit a = bit (!a) := by
  cases a <;> decide

theorem encode_valid {n : ℕ} (a : Fin n → Bool) : valid (encode a) := by
  intro i
  cases h : a i <;> simp [encode, bit, h]

theorem decode_encode {n : ℕ} (a : Fin n → Bool) : decode (encode a) = a := by
  funext i
  cases h : a i <;> simp [decode, encode, bit, h, zero_ne_one_phase]

theorem encode_decode {n : ℕ} (p : RegisterPhase n) (law : valid p) :
    encode (decode p) = p := by
  funext i
  rcases law i with h | h <;> simp [decode, encode, bit, h, zero_ne_one_phase]

theorem arithmetic_correct {n : ℕ} (f : DiscoveryFormula n) (a : Fin n → Bool) :
    arithmeticEval (encode a) f = bit (discoveryEval a f) := by
  induction f with
  | atom i => rfl
  | negation f ih =>
    simp only [arithmeticEval, discoveryEval, ih]
    exact ring_encodes_not _
  | conjunction f g ihf ihg =>
    simp only [arithmeticEval, discoveryEval, ihf, ihg]
    exact multiplication_encodes_and _ _
  | disjunction f g ihf ihg =>
    simp only [arithmeticEval, discoveryEval, ihf, ihg]
    exact ring_encodes_or _ _

theorem alignment_sat_equivalence {n : ℕ} (f : DiscoveryFormula n) :
    (∃ a : Fin n → Bool, discoveryEval a f = true) ↔
      ∃ p : RegisterPhase n, valid p ∧ aligned (arithmeticEval p f) 1 := by
  constructor
  · rintro ⟨a, h⟩
    refine ⟨encode a, encode_valid a, ?_⟩
    rw [arithmetic_correct, h]
    unfold aligned bit
    decide
  · rintro ⟨p, law, h⟩
    refine ⟨decode p, ?_⟩
    have correct := arithmetic_correct f (decode p)
    rw [encode_decode p law] at correct
    have output := (alignment_iff_equal _ _).mp h
    rw [correct] at output
    cases hv : discoveryEval (decode p) f
    · simp [hv, bit, zero_ne_one_phase] at output
    · rfl

def assignmentEquiv (n : ℕ) : (Fin n → Bool) ≃ { p : RegisterPhase n // valid p } where
  toFun a := ⟨encode a, encode_valid a⟩
  invFun p := decode p.val
  left_inv := decode_encode
  right_inv p := Subtype.ext (encode_decode p.val p.property)

theorem valid_phase_cardinality (n : ℕ) :
    Nat.card { p : RegisterPhase n // valid p } = 2 ^ n := by
  rw [← Nat.card_congr (assignmentEquiv n)]
  simp [Nat.card_eq_fintype_card, Fintype.card_fun]

theorem represented_register_phase_roundtrip {n : ℕ} (a : Fin n → Bool) :
    registerPhases (phaseRegisterState (encode a)) = encode a := by
  funext i
  exact key_one_hot_phase _

example : aligned (0 : ZMod 12) 0 := by unfold aligned; decide
example : ¬ aligned (0 : ZMod 12) 1 := by unfold aligned; decide
example : aligned ((7 + bit true) + (7 + bit true)) ((7 + 1) + (7 + 1)) := by
  exact (anchored_sum_encodes_and 7 true true).mpr rfl
example : ¬ aligned ((7 + bit false) + (7 + bit false)) ((7 + 1) + (7 + 1)) := by
  intro h
  have bad := (anchored_sum_encodes_and 7 false false).mp h
  contradiction
example : arithmeticEval (encode (fun _ : Fin 1 => true))
    (.conjunction (.atom 0) (.negation (.atom 0))) = 0 := by decide

end IndependentDuodenary.PhaseAlignmentInvestigation
