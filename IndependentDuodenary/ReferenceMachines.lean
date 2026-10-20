import IndependentDuodenary.ComplexityEncoding

/-! Explicit finite-control, multi-tape reference machines. A run counts actual
transitions and cannot continue after reaching an accepting or rejecting state. -/
namespace IndependentDuodenary

inductive ReferenceMove where
  | left | stay | right
  deriving DecidableEq

def referenceDisplacement : ReferenceMove → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

/-- There is at least one tape, three alphabet symbols and two control states.
Symbol 0 is blank, symbols 1/2 encode bits, and states 0/1 accept/reject. -/
structure ReferenceConfiguration (a s k : ℕ) where
  state : Fin (s + 2)
  head : Fin (k + 1) → ℤ
  tape : Fin (k + 1) → ℤ → Fin (a + 3)

structure ReferenceInstruction (a s k : ℕ) where
  state : Fin (s + 2)
  write : Fin (k + 1) → Fin (a + 3)
  move : Fin (k + 1) → ReferenceMove

structure ReferenceDeterministicMachine (a s k : ℕ) where
  initial : Fin (s + 2)
  transition : Fin (s + 2) → (Fin (k + 1) → Fin (a + 3)) →
    ReferenceInstruction a s k

/-- A mandatory first choice makes nonterminal deadlock impossible; the finite
list contains all additional choices. Choices may repeat without changing runs. -/
structure ReferenceNondeterministicMachine (a s k : ℕ) where
  initial : Fin (s + 2)
  first : Fin (s + 2) → (Fin (k + 1) → Fin (a + 3)) →
    ReferenceInstruction a s k
  rest : Fin (s + 2) → (Fin (k + 1) → Fin (a + 3)) →
    List (ReferenceInstruction a s k)

def referenceTerminal {a s k : ℕ} (q : ReferenceConfiguration a s k) : Prop :=
  q.state = 0 ∨ q.state = 1

instance {a s k : ℕ} (q : ReferenceConfiguration a s k) :
    Decidable (referenceTerminal q) := inferInstanceAs (Decidable (q.state = 0 ∨ q.state = 1))

def referenceRead {a s k : ℕ} (q : ReferenceConfiguration a s k) :
    Fin (k + 1) → Fin (a + 3) := fun i => q.tape i (q.head i)

def referenceApply {a s k : ℕ} (q : ReferenceConfiguration a s k)
    (instruction : ReferenceInstruction a s k) : ReferenceConfiguration a s k where
  state := instruction.state
  head i := q.head i + referenceDisplacement (instruction.move i)
  tape i j := if j = q.head i then instruction.write i else q.tape i j

/-- The first tape contains the complete input from position zero; every other
cell starts blank. All heads start at zero. Negative cells are blank. -/
def referenceInitial {a s k : ℕ} (state : Fin (s + 2)) (x : PrizeBinaryWord) :
    ReferenceConfiguration a s k where
  state := state
  head _ := 0
  tape i j := if i = 0 ∧ 0 ≤ j then
    match x[j.toNat]? with
    | none => 0
    | some b => if b then 2 else 1
    else 0

def referenceDStep {a s k : ℕ} (M : ReferenceDeterministicMachine a s k)
    (q : ReferenceConfiguration a s k) : Option (ReferenceConfiguration a s k) :=
  if referenceTerminal q then none else some (referenceApply q (M.transition q.state (referenceRead q)))

def referenceNSuccessors {a s k : ℕ} (M : ReferenceNondeterministicMachine a s k)
    (q : ReferenceConfiguration a s k) : List (ReferenceConfiguration a s k) :=
  if referenceTerminal q then [] else
    (M.first q.state (referenceRead q) :: M.rest q.state (referenceRead q)).map (referenceApply q)

def referenceDEdge {a s k : ℕ} (M : ReferenceDeterministicMachine a s k)
    (q q' : ReferenceConfiguration a s k) : Prop := referenceDStep M q = some q'

def referenceNEdge {a s k : ℕ} (M : ReferenceNondeterministicMachine a s k)
    (q q' : ReferenceConfiguration a s k) : Prop := q' ∈ referenceNSuccessors M q

/-- Exactly n actual transitions. There are no artificial waiting steps. -/
inductive ReferenceRun {C : Type} (edge : C → C → Prop) : ℕ → C → C → Prop
  | zero (q : C) : ReferenceRun edge 0 q q
  | next {n : ℕ} {q q' q'' : C} : ReferenceRun edge n q q' → edge q' q'' →
      ReferenceRun edge (n + 1) q q''

def ReferenceP (L : PrizeBinaryLanguage) : Prop :=
  ∃ a s k, ∃ M : ReferenceDeterministicMachine a s k, ∃ c d : ℕ,
    ∀ x : PrizeBinaryWord, ∃ t ≤ prizePolynomialBound c d x.length,
      ∃ q : ReferenceConfiguration a s k,
        ReferenceRun (referenceDEdge M) t (referenceInitial M.initial x) q ∧
        referenceTerminal q ∧ (x ∈ L ↔ q.state = 0)

/-- One uniform polynomial bounds every branch on every binary input; membership
requires an accepting branch. No promise about valid instance encodings is used. -/
def ReferenceNP (L : PrizeBinaryLanguage) : Prop :=
  ∃ a s k, ∃ M : ReferenceNondeterministicMachine a s k, ∃ c d : ℕ,
    (∀ (x : PrizeBinaryWord) (t : ℕ) (q : ReferenceConfiguration a s k),
      ReferenceRun (referenceNEdge M) t (referenceInitial M.initial x) q →
        t ≤ prizePolynomialBound c d x.length) ∧
    (∀ x : PrizeBinaryWord, x ∈ L ↔ ∃ t, ∃ q : ReferenceConfiguration a s k,
      ReferenceRun (referenceNEdge M) t (referenceInitial M.initial x) q ∧ q.state = 0)

theorem reference_accept_reject_distinct {s : ℕ} : (0 : Fin (s + 2)) ≠ 1 := by
  intro h
  have := congrArg Fin.val h
  simp at this

theorem reference_initial_heads {a s k : ℕ} (state : Fin (s + 2))
    (x : PrizeBinaryWord) (i : Fin (k + 1)) :
    (referenceInitial (a := a) state x).head i = 0 := rfl

theorem reference_initial_negative_blank {a s k : ℕ} (state : Fin (s + 2))
    (x : PrizeBinaryWord) (i : Fin (k + 1)) (j : ℤ) (hj : j < 0) :
    (referenceInitial (a := a) state x).tape i j = 0 := by
  simp [referenceInitial, not_le.mpr hj]

theorem reference_initial_other_tape_blank {a s k : ℕ} (state : Fin (s + 2))
    (x : PrizeBinaryWord) (i : Fin (k + 1)) (hi : i ≠ 0) (j : ℤ) :
    (referenceInitial (a := a) state x).tape i j = 0 := by
  simp [referenceInitial, hi]

theorem reference_initial_empty_blank {a s k : ℕ} (state : Fin (s + 2))
    (i : Fin (k + 1)) (j : ℤ) :
    (referenceInitial (a := a) state []).tape i j = 0 := by
  simp [referenceInitial]

theorem reference_write_at_head {a s k : ℕ} (q : ReferenceConfiguration a s k)
    (instruction : ReferenceInstruction a s k) (i : Fin (k + 1)) :
    (referenceApply q instruction).tape i (q.head i) = instruction.write i := by
  simp [referenceApply]

theorem reference_write_other_cell {a s k : ℕ} (q : ReferenceConfiguration a s k)
    (instruction : ReferenceInstruction a s k) (i : Fin (k + 1)) (j : ℤ)
    (hj : j ≠ q.head i) :
    (referenceApply q instruction).tape i j = q.tape i j := by
  simp [referenceApply, hj]

theorem reference_dstep_none_iff {a s k : ℕ} (M : ReferenceDeterministicMachine a s k)
    (q : ReferenceConfiguration a s k) : referenceDStep M q = none ↔ referenceTerminal q := by
  simp [referenceDStep]

theorem reference_deterministic_transition {a s k : ℕ}
    (M : ReferenceDeterministicMachine a s k) (q q₁ q₂ : ReferenceConfiguration a s k)
    (h₁ : referenceDEdge M q q₁) (h₂ : referenceDEdge M q q₂) : q₁ = q₂ := by
  exact Option.some.inj (h₁.symm.trans h₂)

theorem reference_nondeterministic_finite_branching {a s k : ℕ}
    (M : ReferenceNondeterministicMachine a s k) (q : ReferenceConfiguration a s k) :
    ∃ successors : List (ReferenceConfiguration a s k),
      ∀ q', referenceNEdge M q q' ↔ q' ∈ successors := by
  exact ⟨referenceNSuccessors M q, fun _ => Iff.rfl⟩

theorem reference_terminal_no_nstep {a s k : ℕ}
    (M : ReferenceNondeterministicMachine a s k) (q q' : ReferenceConfiguration a s k)
    (halt : referenceTerminal q) : ¬ referenceNEdge M q q' := by
  simp [referenceNEdge, referenceNSuccessors, halt]

theorem reference_nonterminal_has_nstep {a s k : ℕ}
    (M : ReferenceNondeterministicMachine a s k) (q : ReferenceConfiguration a s k)
    (halt : ¬ referenceTerminal q) : ∃ q', referenceNEdge M q q' := by
  refine ⟨referenceApply q (M.first q.state (referenceRead q)), ?_⟩
  simp [referenceNEdge, referenceNSuccessors, halt]

theorem reference_nbranch_bound_forces_terminal {a s k : ℕ}
    (M : ReferenceNondeterministicMachine a s k) (initial : ReferenceConfiguration a s k)
    (bound : ℕ)
    (bounded : ∀ t q, ReferenceRun (referenceNEdge M) t initial q → t ≤ bound)
    (q : ReferenceConfiguration a s k)
    (run : ReferenceRun (referenceNEdge M) bound initial q) : referenceTerminal q := by
  by_contra halt
  obtain ⟨q', step⟩ := reference_nonterminal_has_nstep M q halt
  have h := bounded (bound + 1) q' (ReferenceRun.next run step)
  omega

end IndependentDuodenary
