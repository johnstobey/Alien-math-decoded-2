import IndependentDuodenary.ReferenceMachines

/-! Experimental semantic core, not a parser for the full uploaded languages.
Boolean formulas translate to guarded operations on twelve-position registers.
The conditional binary gates are additional operations, not registerStep. -/
namespace IndependentDuodenary

inductive DiscoveryFormula (n : ℕ) where
  | atom : Fin n → DiscoveryFormula n
  | negation : DiscoveryFormula n → DiscoveryFormula n
  | conjunction : DiscoveryFormula n → DiscoveryFormula n → DiscoveryFormula n
  | disjunction : DiscoveryFormula n → DiscoveryFormula n → DiscoveryFormula n

def discoveryEval {n : ℕ} (a : Fin n → Bool) : DiscoveryFormula n → Bool
  | .atom i => a i
  | .negation f => !(discoveryEval a f)
  | .conjunction f g => discoveryEval a f && discoveryEval a g
  | .disjunction f g => discoveryEval a f || discoveryEval a g

def discoverySize {n : ℕ} : DiscoveryFormula n → ℕ
  | .atom _ => 1
  | .negation f => 1 + discoverySize f
  | .conjunction f g => 1 + discoverySize f + discoverySize g
  | .disjunction f g => 1 + discoverySize f + discoverySize g

inductive FulguriteCircuit (n : ℕ) where
  | read : Fin n → FulguriteCircuit n
  | halfTurn : FulguriteCircuit n → FulguriteCircuit n
  | meet : FulguriteCircuit n → FulguriteCircuit n → FulguriteCircuit n
  | join : FulguriteCircuit n → FulguriteCircuit n → FulguriteCircuit n

def fulguriteBit (b : Bool) : ZMod 12 := if b then 6 else 0

def obsidianBitLaw (x : ZMod 12) : Prop := x = 0 ∨ x = 6

def obsidianAssignmentLaw {n : ℕ} (p : RegisterPhase n) : Prop :=
  ∀ i, obsidianBitLaw (p i)

def fulguriteMeet (x y : ZMod 12) : ZMod 12 := if x = 6 then y else 0

def fulguriteJoin (x y : ZMod 12) : ZMod 12 := if x = 6 then 6 else y

def fulguriteEval {n : ℕ} (p : RegisterPhase n) : FulguriteCircuit n → ZMod 12
  | .read i => p i
  | .halfTurn f => fulguriteEval p f + 6
  | .meet f g => fulguriteMeet (fulguriteEval p f) (fulguriteEval p g)
  | .join f g => fulguriteJoin (fulguriteEval p f) (fulguriteEval p g)

def fulguriteSize {n : ℕ} : FulguriteCircuit n → ℕ
  | .read _ => 1
  | .halfTurn f => 1 + fulguriteSize f
  | .meet f g => 1 + fulguriteSize f + fulguriteSize g
  | .join f g => 1 + fulguriteSize f + fulguriteSize g

/-- No satisfying assignment is consulted by this structural compiler. -/
def discoveryCompile {n : ℕ} : DiscoveryFormula n → FulguriteCircuit n
  | .atom i => .read i
  | .negation f => .halfTurn (discoveryCompile f)
  | .conjunction f g => .meet (discoveryCompile f) (discoveryCompile g)
  | .disjunction f g => .join (discoveryCompile f) (discoveryCompile g)

def fulguriteCompileAssignment {n : ℕ} (a : Fin n → Bool) : RegisterPhase n :=
  fun i => fulguriteBit (a i)

def fulguriteDecodeAssignment {n : ℕ} (p : RegisterPhase n) : Fin n → Bool :=
  fun i => decide (p i = 6)

theorem fulgurite_zero_ne_six : (0 : ZMod 12) ≠ 6 := by decide

theorem fulgurite_half_turn_twice (x : ZMod 12) : x + 6 + 6 = x := by
  have h : (6 + 6 : ZMod 12) = 0 := by decide
  rw [add_assoc, h, add_zero]

theorem fulgurite_bit_negation (b : Bool) :
    fulguriteBit (!b) = fulguriteBit b + 6 := by
  cases b <;> decide

theorem fulgurite_bit_conjunction (b c : Bool) :
    fulguriteMeet (fulguriteBit b) (fulguriteBit c) = fulguriteBit (b && c) := by
  cases b <;> cases c <;> decide

theorem fulgurite_bit_disjunction (b c : Bool) :
    fulguriteJoin (fulguriteBit b) (fulguriteBit c) = fulguriteBit (b || c) := by
  cases b <;> cases c <;> decide

theorem fulgurite_bit_injective : Function.Injective fulguriteBit := by
  intro a b h
  cases a <;> cases b <;> norm_num [fulguriteBit, fulgurite_zero_ne_six, Ne.symm fulgurite_zero_ne_six] at h ⊢

theorem fulgurite_bit_law (b : Bool) : obsidianBitLaw (fulguriteBit b) := by
  cases b <;> simp [fulguriteBit, obsidianBitLaw]

theorem fulgurite_assignment_law {n : ℕ} (a : Fin n → Bool) :
    obsidianAssignmentLaw (fulguriteCompileAssignment a) := by
  intro i
  exact fulgurite_bit_law (a i)

theorem fulgurite_assignment_decode_encode {n : ℕ} (a : Fin n → Bool) :
    fulguriteDecodeAssignment (fulguriteCompileAssignment a) = a := by
  funext i
  cases h : a i <;> simp [fulguriteDecodeAssignment, fulguriteCompileAssignment, fulguriteBit, h, fulgurite_zero_ne_six]

theorem fulgurite_assignment_encode_decode {n : ℕ} (p : RegisterPhase n)
    (valid : obsidianAssignmentLaw p) :
    fulguriteCompileAssignment (fulguriteDecodeAssignment p) = p := by
  funext i
  rcases valid i with h | h <;>
    simp [fulguriteCompileAssignment, fulguriteDecodeAssignment, fulguriteBit, h, fulgurite_zero_ne_six]

def fulguriteAssignmentEquiv (n : ℕ) :
    (Fin n → Bool) ≃ { p : RegisterPhase n // obsidianAssignmentLaw p } where
  toFun a := ⟨fulguriteCompileAssignment a, fulgurite_assignment_law a⟩
  invFun p := fulguriteDecodeAssignment p.val
  left_inv := fulgurite_assignment_decode_encode
  right_inv p := Subtype.ext (fulgurite_assignment_encode_decode p.val p.property)

/-- The native representation retains all 2^n assignments; no search-space
collapse follows from placing each bit on a twelve-position ring. -/
theorem fulgurite_assignment_cardinality (n : ℕ) :
    Nat.card { p : RegisterPhase n // obsidianAssignmentLaw p } = 2 ^ n := by
  rw [← Nat.card_congr (fulguriteAssignmentEquiv n)]
  simp [Nat.card_eq_fintype_card, Fintype.card_fun]

theorem fulgurite_compile_size {n : ℕ} (f : DiscoveryFormula n) :
    fulguriteSize (discoveryCompile f) = discoverySize f := by
  induction f <;> simp_all [discoveryCompile, fulguriteSize, discoverySize]

theorem fulgurite_compile_correct {n : ℕ} (f : DiscoveryFormula n) (a : Fin n → Bool) :
    fulguriteEval (fulguriteCompileAssignment a) (discoveryCompile f) =
      fulguriteBit (discoveryEval a f) := by
  induction f with
  | atom i => rfl
  | negation f ih =>
    simp only [discoveryCompile, fulguriteEval, discoveryEval, ih]
    exact (fulgurite_bit_negation _).symm
  | conjunction f g ihf ihg =>
    simp only [discoveryCompile, fulguriteEval, discoveryEval, ihf, ihg]
    exact fulgurite_bit_conjunction _ _
  | disjunction f g ihf ihg =>
    simp only [discoveryCompile, fulguriteEval, discoveryEval, ihf, ihg]
    exact fulgurite_bit_disjunction _ _

theorem fulgurite_eval_preserves_law {n : ℕ} (e : FulguriteCircuit n)
    (p : RegisterPhase n) (valid : obsidianAssignmentLaw p) :
    obsidianBitLaw (fulguriteEval p e) := by
  induction e with
  | read i => exact valid i
  | halfTurn e ih =>
    rcases ih with h | h <;> simp only [fulguriteEval, h, obsidianBitLaw] <;> decide
  | meet e f ihe ihf =>
    simp only [fulguriteEval, fulguriteMeet]
    split
    · exact ihf
    · exact Or.inl rfl
  | join e f ihe ihf =>
    simp only [fulguriteEval, fulguriteJoin]
    split
    · exact Or.inr rfl
    · exact ihf

/-- Satisfiability equivalence for arbitrary finite formula sizes. The target is
circuit satisfiability, not fixed-registerStep reachability. -/
theorem fulgurite_satisfiability_equivalence {n : ℕ} (f : DiscoveryFormula n) :
    (∃ a : Fin n → Bool, discoveryEval a f = true) ↔
      ∃ p : RegisterPhase n, obsidianAssignmentLaw p ∧
        fulguriteEval p (discoveryCompile f) = 6 := by
  constructor
  · rintro ⟨a, h⟩
    refine ⟨fulguriteCompileAssignment a, fulgurite_assignment_law a, ?_⟩
    rw [fulgurite_compile_correct, h]
    rfl
  · rintro ⟨p, valid, h⟩
    refine ⟨fulguriteDecodeAssignment p, ?_⟩
    have correct := fulgurite_compile_correct f (fulguriteDecodeAssignment p)
    rw [fulgurite_assignment_encode_decode p valid, h] at correct
    cases he : discoveryEval (fulguriteDecodeAssignment p) f
    · norm_num [he, fulguriteBit, Ne.symm fulgurite_zero_ne_six] at correct
    · rfl

/-- Exact connection to the repository's one-hot represented-key registers. -/
theorem fulgurite_register_phase_roundtrip {n : ℕ} (a : Fin n → Bool) :
    registerPhases (phaseRegisterState (fulguriteCompileAssignment a)) =
      fulguriteCompileAssignment a := by
  funext i
  exact key_one_hot_phase _

/-- These Boolean conjunction gates are not affine arithmetic over ZMod 12. -/
theorem fulgurite_meet_not_affine :
    ¬ ∃ A B C : ZMod 12, ∀ x y : Bool,
      A * fulguriteBit x + B * fulguriteBit y + C = fulguriteBit (x && y) := by
  rintro ⟨A, B, C, h⟩
  have hc := h false false
  norm_num [fulguriteBit, fulgurite_zero_ne_six, Ne.symm fulgurite_zero_ne_six] at hc
  subst C
  have ha := h true false
  have hb := h false true
  norm_num [fulguriteBit, fulgurite_zero_ne_six, Ne.symm fulgurite_zero_ne_six] at ha hb
  have hab := h true true
  norm_num [fulguriteBit, ha, hb, fulgurite_zero_ne_six] at hab

/-- A typed rewrite language. Conditional binary gates require the bit law. -/
inductive FulguriteRewrite {n : ℕ} : FulguriteCircuit n → FulguriteCircuit n → Prop
  | doubleTurn (e) : FulguriteRewrite (.halfTurn (.halfTurn e)) e
  | meetComm (e f) : FulguriteRewrite (.meet e f) (.meet f e)
  | joinComm (e f) : FulguriteRewrite (.join e f) (.join f e)

inductive FulguriteTrace {n : ℕ} : FulguriteCircuit n → FulguriteCircuit n → Prop
  | reflexive (e) : FulguriteTrace e e
  | append {e f g} : FulguriteTrace e f → FulguriteRewrite f g → FulguriteTrace e g

theorem fulgurite_rewrite_sound {n : ℕ} {e f : FulguriteCircuit n}
    (rule : FulguriteRewrite e f) (p : RegisterPhase n)
    (valid : obsidianAssignmentLaw p) : fulguriteEval p e = fulguriteEval p f := by
  cases rule with
  | doubleTurn e => exact fulgurite_half_turn_twice _
  | meetComm e f =>
    have he := fulgurite_eval_preserves_law e p valid
    have hf := fulgurite_eval_preserves_law f p valid
    rcases he with he | he <;> rcases hf with hf | hf <;>
      norm_num [fulguriteEval, fulguriteMeet, he, hf, fulgurite_zero_ne_six]
  | joinComm e f =>
    have he := fulgurite_eval_preserves_law e p valid
    have hf := fulgurite_eval_preserves_law f p valid
    rcases he with he | he <;> rcases hf with hf | hf <;>
      norm_num [fulguriteEval, fulguriteJoin, he, hf, fulgurite_zero_ne_six]

theorem fulgurite_trace_sound {n : ℕ} {e f : FulguriteCircuit n}
    (trace : FulguriteTrace e f) (p : RegisterPhase n)
    (valid : obsidianAssignmentLaw p) : fulguriteEval p e = fulguriteEval p f := by
  induction trace with
  | reflexive => rfl
  | append trace rule ih => exact ih.trans (fulgurite_rewrite_sound rule p valid)

theorem fulgurite_trace_preserves_satisfiability {n : ℕ} {e f : FulguriteCircuit n}
    (trace : FulguriteTrace e f) :
    (∃ p : RegisterPhase n, obsidianAssignmentLaw p ∧ fulguriteEval p e = 6) ↔
      ∃ p : RegisterPhase n, obsidianAssignmentLaw p ∧ fulguriteEval p f = 6 := by
  constructor
  · rintro ⟨p, valid, h⟩
    exact ⟨p, valid, (fulgurite_trace_sound trace p valid).symm.trans h⟩
  · rintro ⟨p, valid, h⟩
    exact ⟨p, valid, (fulgurite_trace_sound trace p valid).trans h⟩

/-- Concatenate independently checkable derivation traces. -/
theorem fulgurite_trace_trans {n : ℕ} {e f g : FulguriteCircuit n}
    (first : FulguriteTrace e f) (second : FulguriteTrace f g) : FulguriteTrace e g := by
  induction second with
  | reflexive => exact first
  | append trace rule ih => exact FulguriteTrace.append ih rule

/-- A small rule proposer, not a complete proof search algorithm. -/
def fulguritePropose {n : ℕ} (e : FulguriteCircuit n) :
    Option { f : FulguriteCircuit n // FulguriteRewrite e f } :=
  match e with
  | .halfTurn (.halfTurn f) => some ⟨f, .doubleTurn f⟩
  | .meet f g => some ⟨.meet g f, .meetComm f g⟩
  | .join f g => some ⟨.join g f, .joinComm f g⟩
  | _ => none

/-- Bounded execution always returns a derivation certificate. Commuting gates
may cycle, so fuel limits search; no normalization or completeness is asserted. -/
def fulguriteDiscover {n : ℕ} : (fuel : ℕ) → (e : FulguriteCircuit n) →
    { f : FulguriteCircuit n // FulguriteTrace e f }
  | 0, e => ⟨e, .reflexive e⟩
  | fuel + 1, e =>
    match fulguritePropose e with
    | none => ⟨e, .reflexive e⟩
    | some proposed =>
      let result := fulguriteDiscover fuel proposed.val
      ⟨result.val, fulgurite_trace_trans
        (.append (.reflexive e) proposed.property) result.property⟩

theorem fulgurite_discovery_preserves_satisfiability {n : ℕ}
    (fuel : ℕ) (e : FulguriteCircuit n) :
    (∃ p : RegisterPhase n, obsidianAssignmentLaw p ∧ fulguriteEval p e = 6) ↔
      ∃ p : RegisterPhase n, obsidianAssignmentLaw p ∧
        fulguriteEval p (fulguriteDiscover fuel e).val = 6 := by
  exact fulgurite_trace_preserves_satisfiability (fulguriteDiscover fuel e).property

end IndependentDuodenary
