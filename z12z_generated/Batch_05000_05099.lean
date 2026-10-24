import Mathlib

namespace Z12ZCompilerV4

abbrev Ring12 := ZMod 12
abbrev Constraint := Set Ring12

def anchor : Ring12 := 0
def antipode (k : Ring12) : Ring12 := k + 6

def Antipodal (s : Constraint) : Prop := ∀ k, k ∈ s ↔ antipode k ∈ s

inductive Domain where
  | constraint
  | suppression
  | contamination
  | sabotage
  deriving DecidableEq, Repr

inductive Partition where
  | airWater
  | fireEarth
  deriving DecidableEq, Repr

structure Event where
  k : Ring12
  r : Ring12
  n : Ring12
  constraint : Constraint
  domain : Domain
  partition : Partition

structure State where
  k : Ring12
  r : Ring12
  n : Ring12
  P : Set Constraint
  S : Constraint
  E : List Event

def Coherent (x : State) : Prop := x.k = x.n + x.r
def Consistent (x : State) : Prop := ∀ k, k ∈ x.S ↔ ∀ p ∈ x.P, k ∈ p

def initial : State := ⟨anchor, 0, 0, ∅, Set.univ, []⟩

def delta (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : State :=
  let n' := x.n + 1
  let r' := if lawful then x.r + dr else x.r
  { k := n' + r'
    r := r'
    n := n'
    P := insert e.constraint x.P
    S := x.S ∩ e.constraint
    E := x.E ++ [e] }

def tighten (T : Set (Ring12 × Ring12)) (s : Constraint) : Set (Ring12 × Ring12) :=
  T ∩ Set.prod s s

def anchorReset (x : State) : State :=
  { x with k := anchor, r := 0 }

theorem initial_coherent : Coherent initial := by rfl
theorem initial_consistent : Consistent initial := by intro k; simp [initial]
theorem initial_antipodal : Antipodal initial.S := by intro k; simp [initial]

theorem intersection_antipodal (s p : Constraint) (hs : Antipodal s) (hp : Antipodal p) : Antipodal (s ∩ p) := by
  intro k
  exact and_congr (hs k) (hp k)

theorem delta_consistent (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : Consistent (delta x e dr lawful) := by
  intro k
  change (k ∈ x.S ∧ k ∈ e.constraint) ↔ ∀ p ∈ insert e.constraint x.P, k ∈ p
  rw [hx k]
  constructor
  · rintro ⟨hold, hnew⟩ p hp
    rcases Set.mem_insert_iff.mp hp with heq | hp
    · subst p; exact hnew
    · exact hold p hp
  · intro h
    exact ⟨fun p hp => h p (Set.mem_insert_of_mem _ hp), h e.constraint (Set.mem_insert _ _)⟩
theorem generated_05000 (tag : Fin 10000) (htag : tag.val = 5000) (k : Ring12) : tag.val = 5000 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05001 (tag : Fin 10000) (htag : tag.val = 5001) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5001 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05002 (tag : Fin 10000) (htag : tag.val = 5002) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5002 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05003 (tag : Fin 10000) (htag : tag.val = 5003) (x : State) (e : Event) (dr : Ring12) : tag.val = 5003 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05004 (tag : Fin 10000) (htag : tag.val = 5004) (x : State) (e : Event) (dr : Ring12) : tag.val = 5004 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05005 (tag : Fin 10000) (htag : tag.val = 5005) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5005 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05006 (tag : Fin 10000) (htag : tag.val = 5006) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5006 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05007 (tag : Fin 10000) (htag : tag.val = 5007) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5007 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05008 (tag : Fin 10000) (htag : tag.val = 5008) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5008 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05009 (tag : Fin 10000) (htag : tag.val = 5009) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5009 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05010 (tag : Fin 10000) (htag : tag.val = 5010) (k : Ring12) : tag.val = 5010 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05011 (tag : Fin 10000) (htag : tag.val = 5011) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5011 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05012 (tag : Fin 10000) (htag : tag.val = 5012) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5012 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05013 (tag : Fin 10000) (htag : tag.val = 5013) (x : State) (e : Event) (dr : Ring12) : tag.val = 5013 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05014 (tag : Fin 10000) (htag : tag.val = 5014) (x : State) (e : Event) (dr : Ring12) : tag.val = 5014 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05015 (tag : Fin 10000) (htag : tag.val = 5015) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5015 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05016 (tag : Fin 10000) (htag : tag.val = 5016) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5016 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05017 (tag : Fin 10000) (htag : tag.val = 5017) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5017 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05018 (tag : Fin 10000) (htag : tag.val = 5018) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5018 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05019 (tag : Fin 10000) (htag : tag.val = 5019) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5019 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05020 (tag : Fin 10000) (htag : tag.val = 5020) (k : Ring12) : tag.val = 5020 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05021 (tag : Fin 10000) (htag : tag.val = 5021) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5021 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05022 (tag : Fin 10000) (htag : tag.val = 5022) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5022 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05023 (tag : Fin 10000) (htag : tag.val = 5023) (x : State) (e : Event) (dr : Ring12) : tag.val = 5023 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05024 (tag : Fin 10000) (htag : tag.val = 5024) (x : State) (e : Event) (dr : Ring12) : tag.val = 5024 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05025 (tag : Fin 10000) (htag : tag.val = 5025) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5025 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05026 (tag : Fin 10000) (htag : tag.val = 5026) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5026 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05027 (tag : Fin 10000) (htag : tag.val = 5027) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5027 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05028 (tag : Fin 10000) (htag : tag.val = 5028) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5028 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05029 (tag : Fin 10000) (htag : tag.val = 5029) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5029 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05030 (tag : Fin 10000) (htag : tag.val = 5030) (k : Ring12) : tag.val = 5030 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05031 (tag : Fin 10000) (htag : tag.val = 5031) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5031 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05032 (tag : Fin 10000) (htag : tag.val = 5032) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5032 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05033 (tag : Fin 10000) (htag : tag.val = 5033) (x : State) (e : Event) (dr : Ring12) : tag.val = 5033 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05034 (tag : Fin 10000) (htag : tag.val = 5034) (x : State) (e : Event) (dr : Ring12) : tag.val = 5034 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05035 (tag : Fin 10000) (htag : tag.val = 5035) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5035 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05036 (tag : Fin 10000) (htag : tag.val = 5036) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5036 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05037 (tag : Fin 10000) (htag : tag.val = 5037) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5037 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05038 (tag : Fin 10000) (htag : tag.val = 5038) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5038 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05039 (tag : Fin 10000) (htag : tag.val = 5039) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5039 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05040 (tag : Fin 10000) (htag : tag.val = 5040) (k : Ring12) : tag.val = 5040 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05041 (tag : Fin 10000) (htag : tag.val = 5041) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5041 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05042 (tag : Fin 10000) (htag : tag.val = 5042) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5042 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05043 (tag : Fin 10000) (htag : tag.val = 5043) (x : State) (e : Event) (dr : Ring12) : tag.val = 5043 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05044 (tag : Fin 10000) (htag : tag.val = 5044) (x : State) (e : Event) (dr : Ring12) : tag.val = 5044 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05045 (tag : Fin 10000) (htag : tag.val = 5045) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5045 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05046 (tag : Fin 10000) (htag : tag.val = 5046) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5046 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05047 (tag : Fin 10000) (htag : tag.val = 5047) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5047 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05048 (tag : Fin 10000) (htag : tag.val = 5048) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5048 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05049 (tag : Fin 10000) (htag : tag.val = 5049) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5049 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05050 (tag : Fin 10000) (htag : tag.val = 5050) (k : Ring12) : tag.val = 5050 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05051 (tag : Fin 10000) (htag : tag.val = 5051) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5051 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05052 (tag : Fin 10000) (htag : tag.val = 5052) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5052 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05053 (tag : Fin 10000) (htag : tag.val = 5053) (x : State) (e : Event) (dr : Ring12) : tag.val = 5053 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05054 (tag : Fin 10000) (htag : tag.val = 5054) (x : State) (e : Event) (dr : Ring12) : tag.val = 5054 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05055 (tag : Fin 10000) (htag : tag.val = 5055) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5055 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05056 (tag : Fin 10000) (htag : tag.val = 5056) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5056 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05057 (tag : Fin 10000) (htag : tag.val = 5057) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5057 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05058 (tag : Fin 10000) (htag : tag.val = 5058) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5058 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05059 (tag : Fin 10000) (htag : tag.val = 5059) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5059 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05060 (tag : Fin 10000) (htag : tag.val = 5060) (k : Ring12) : tag.val = 5060 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05061 (tag : Fin 10000) (htag : tag.val = 5061) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5061 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05062 (tag : Fin 10000) (htag : tag.val = 5062) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5062 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05063 (tag : Fin 10000) (htag : tag.val = 5063) (x : State) (e : Event) (dr : Ring12) : tag.val = 5063 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05064 (tag : Fin 10000) (htag : tag.val = 5064) (x : State) (e : Event) (dr : Ring12) : tag.val = 5064 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05065 (tag : Fin 10000) (htag : tag.val = 5065) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5065 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05066 (tag : Fin 10000) (htag : tag.val = 5066) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5066 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05067 (tag : Fin 10000) (htag : tag.val = 5067) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5067 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05068 (tag : Fin 10000) (htag : tag.val = 5068) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5068 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05069 (tag : Fin 10000) (htag : tag.val = 5069) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5069 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05070 (tag : Fin 10000) (htag : tag.val = 5070) (k : Ring12) : tag.val = 5070 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05071 (tag : Fin 10000) (htag : tag.val = 5071) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5071 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05072 (tag : Fin 10000) (htag : tag.val = 5072) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5072 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05073 (tag : Fin 10000) (htag : tag.val = 5073) (x : State) (e : Event) (dr : Ring12) : tag.val = 5073 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05074 (tag : Fin 10000) (htag : tag.val = 5074) (x : State) (e : Event) (dr : Ring12) : tag.val = 5074 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05075 (tag : Fin 10000) (htag : tag.val = 5075) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5075 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05076 (tag : Fin 10000) (htag : tag.val = 5076) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5076 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05077 (tag : Fin 10000) (htag : tag.val = 5077) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5077 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05078 (tag : Fin 10000) (htag : tag.val = 5078) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5078 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05079 (tag : Fin 10000) (htag : tag.val = 5079) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5079 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05080 (tag : Fin 10000) (htag : tag.val = 5080) (k : Ring12) : tag.val = 5080 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05081 (tag : Fin 10000) (htag : tag.val = 5081) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5081 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05082 (tag : Fin 10000) (htag : tag.val = 5082) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5082 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05083 (tag : Fin 10000) (htag : tag.val = 5083) (x : State) (e : Event) (dr : Ring12) : tag.val = 5083 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05084 (tag : Fin 10000) (htag : tag.val = 5084) (x : State) (e : Event) (dr : Ring12) : tag.val = 5084 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05085 (tag : Fin 10000) (htag : tag.val = 5085) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5085 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05086 (tag : Fin 10000) (htag : tag.val = 5086) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5086 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05087 (tag : Fin 10000) (htag : tag.val = 5087) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5087 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05088 (tag : Fin 10000) (htag : tag.val = 5088) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5088 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05089 (tag : Fin 10000) (htag : tag.val = 5089) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5089 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05090 (tag : Fin 10000) (htag : tag.val = 5090) (k : Ring12) : tag.val = 5090 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05091 (tag : Fin 10000) (htag : tag.val = 5091) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5091 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05092 (tag : Fin 10000) (htag : tag.val = 5092) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5092 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05093 (tag : Fin 10000) (htag : tag.val = 5093) (x : State) (e : Event) (dr : Ring12) : tag.val = 5093 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05094 (tag : Fin 10000) (htag : tag.val = 5094) (x : State) (e : Event) (dr : Ring12) : tag.val = 5094 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05095 (tag : Fin 10000) (htag : tag.val = 5095) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5095 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05096 (tag : Fin 10000) (htag : tag.val = 5096) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5096 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05097 (tag : Fin 10000) (htag : tag.val = 5097) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5097 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05098 (tag : Fin 10000) (htag : tag.val = 5098) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5098 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05099 (tag : Fin 10000) (htag : tag.val = 5099) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5099 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
