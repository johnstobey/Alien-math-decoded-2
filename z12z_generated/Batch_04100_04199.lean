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
theorem generated_04100 (tag : Fin 10000) (htag : tag.val = 4100) (k : Ring12) : tag.val = 4100 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04101 (tag : Fin 10000) (htag : tag.val = 4101) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4101 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04102 (tag : Fin 10000) (htag : tag.val = 4102) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4102 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04103 (tag : Fin 10000) (htag : tag.val = 4103) (x : State) (e : Event) (dr : Ring12) : tag.val = 4103 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04104 (tag : Fin 10000) (htag : tag.val = 4104) (x : State) (e : Event) (dr : Ring12) : tag.val = 4104 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04105 (tag : Fin 10000) (htag : tag.val = 4105) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4105 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04106 (tag : Fin 10000) (htag : tag.val = 4106) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4106 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04107 (tag : Fin 10000) (htag : tag.val = 4107) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4107 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04108 (tag : Fin 10000) (htag : tag.val = 4108) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4108 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04109 (tag : Fin 10000) (htag : tag.val = 4109) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4109 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04110 (tag : Fin 10000) (htag : tag.val = 4110) (k : Ring12) : tag.val = 4110 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04111 (tag : Fin 10000) (htag : tag.val = 4111) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4111 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04112 (tag : Fin 10000) (htag : tag.val = 4112) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4112 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04113 (tag : Fin 10000) (htag : tag.val = 4113) (x : State) (e : Event) (dr : Ring12) : tag.val = 4113 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04114 (tag : Fin 10000) (htag : tag.val = 4114) (x : State) (e : Event) (dr : Ring12) : tag.val = 4114 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04115 (tag : Fin 10000) (htag : tag.val = 4115) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4115 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04116 (tag : Fin 10000) (htag : tag.val = 4116) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4116 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04117 (tag : Fin 10000) (htag : tag.val = 4117) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4117 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04118 (tag : Fin 10000) (htag : tag.val = 4118) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4118 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04119 (tag : Fin 10000) (htag : tag.val = 4119) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4119 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04120 (tag : Fin 10000) (htag : tag.val = 4120) (k : Ring12) : tag.val = 4120 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04121 (tag : Fin 10000) (htag : tag.val = 4121) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4121 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04122 (tag : Fin 10000) (htag : tag.val = 4122) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4122 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04123 (tag : Fin 10000) (htag : tag.val = 4123) (x : State) (e : Event) (dr : Ring12) : tag.val = 4123 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04124 (tag : Fin 10000) (htag : tag.val = 4124) (x : State) (e : Event) (dr : Ring12) : tag.val = 4124 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04125 (tag : Fin 10000) (htag : tag.val = 4125) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4125 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04126 (tag : Fin 10000) (htag : tag.val = 4126) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4126 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04127 (tag : Fin 10000) (htag : tag.val = 4127) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4127 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04128 (tag : Fin 10000) (htag : tag.val = 4128) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4128 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04129 (tag : Fin 10000) (htag : tag.val = 4129) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4129 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04130 (tag : Fin 10000) (htag : tag.val = 4130) (k : Ring12) : tag.val = 4130 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04131 (tag : Fin 10000) (htag : tag.val = 4131) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4131 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04132 (tag : Fin 10000) (htag : tag.val = 4132) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4132 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04133 (tag : Fin 10000) (htag : tag.val = 4133) (x : State) (e : Event) (dr : Ring12) : tag.val = 4133 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04134 (tag : Fin 10000) (htag : tag.val = 4134) (x : State) (e : Event) (dr : Ring12) : tag.val = 4134 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04135 (tag : Fin 10000) (htag : tag.val = 4135) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4135 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04136 (tag : Fin 10000) (htag : tag.val = 4136) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4136 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04137 (tag : Fin 10000) (htag : tag.val = 4137) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4137 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04138 (tag : Fin 10000) (htag : tag.val = 4138) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4138 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04139 (tag : Fin 10000) (htag : tag.val = 4139) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4139 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04140 (tag : Fin 10000) (htag : tag.val = 4140) (k : Ring12) : tag.val = 4140 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04141 (tag : Fin 10000) (htag : tag.val = 4141) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4141 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04142 (tag : Fin 10000) (htag : tag.val = 4142) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4142 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04143 (tag : Fin 10000) (htag : tag.val = 4143) (x : State) (e : Event) (dr : Ring12) : tag.val = 4143 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04144 (tag : Fin 10000) (htag : tag.val = 4144) (x : State) (e : Event) (dr : Ring12) : tag.val = 4144 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04145 (tag : Fin 10000) (htag : tag.val = 4145) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4145 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04146 (tag : Fin 10000) (htag : tag.val = 4146) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4146 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04147 (tag : Fin 10000) (htag : tag.val = 4147) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4147 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04148 (tag : Fin 10000) (htag : tag.val = 4148) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4148 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04149 (tag : Fin 10000) (htag : tag.val = 4149) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4149 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04150 (tag : Fin 10000) (htag : tag.val = 4150) (k : Ring12) : tag.val = 4150 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04151 (tag : Fin 10000) (htag : tag.val = 4151) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4151 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04152 (tag : Fin 10000) (htag : tag.val = 4152) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4152 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04153 (tag : Fin 10000) (htag : tag.val = 4153) (x : State) (e : Event) (dr : Ring12) : tag.val = 4153 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04154 (tag : Fin 10000) (htag : tag.val = 4154) (x : State) (e : Event) (dr : Ring12) : tag.val = 4154 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04155 (tag : Fin 10000) (htag : tag.val = 4155) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4155 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04156 (tag : Fin 10000) (htag : tag.val = 4156) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4156 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04157 (tag : Fin 10000) (htag : tag.val = 4157) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4157 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04158 (tag : Fin 10000) (htag : tag.val = 4158) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4158 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04159 (tag : Fin 10000) (htag : tag.val = 4159) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4159 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04160 (tag : Fin 10000) (htag : tag.val = 4160) (k : Ring12) : tag.val = 4160 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04161 (tag : Fin 10000) (htag : tag.val = 4161) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4161 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04162 (tag : Fin 10000) (htag : tag.val = 4162) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4162 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04163 (tag : Fin 10000) (htag : tag.val = 4163) (x : State) (e : Event) (dr : Ring12) : tag.val = 4163 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04164 (tag : Fin 10000) (htag : tag.val = 4164) (x : State) (e : Event) (dr : Ring12) : tag.val = 4164 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04165 (tag : Fin 10000) (htag : tag.val = 4165) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4165 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04166 (tag : Fin 10000) (htag : tag.val = 4166) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4166 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04167 (tag : Fin 10000) (htag : tag.val = 4167) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4167 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04168 (tag : Fin 10000) (htag : tag.val = 4168) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4168 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04169 (tag : Fin 10000) (htag : tag.val = 4169) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4169 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04170 (tag : Fin 10000) (htag : tag.val = 4170) (k : Ring12) : tag.val = 4170 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04171 (tag : Fin 10000) (htag : tag.val = 4171) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4171 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04172 (tag : Fin 10000) (htag : tag.val = 4172) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4172 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04173 (tag : Fin 10000) (htag : tag.val = 4173) (x : State) (e : Event) (dr : Ring12) : tag.val = 4173 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04174 (tag : Fin 10000) (htag : tag.val = 4174) (x : State) (e : Event) (dr : Ring12) : tag.val = 4174 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04175 (tag : Fin 10000) (htag : tag.val = 4175) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4175 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04176 (tag : Fin 10000) (htag : tag.val = 4176) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4176 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04177 (tag : Fin 10000) (htag : tag.val = 4177) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4177 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04178 (tag : Fin 10000) (htag : tag.val = 4178) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4178 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04179 (tag : Fin 10000) (htag : tag.val = 4179) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4179 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04180 (tag : Fin 10000) (htag : tag.val = 4180) (k : Ring12) : tag.val = 4180 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04181 (tag : Fin 10000) (htag : tag.val = 4181) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4181 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04182 (tag : Fin 10000) (htag : tag.val = 4182) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4182 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04183 (tag : Fin 10000) (htag : tag.val = 4183) (x : State) (e : Event) (dr : Ring12) : tag.val = 4183 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04184 (tag : Fin 10000) (htag : tag.val = 4184) (x : State) (e : Event) (dr : Ring12) : tag.val = 4184 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04185 (tag : Fin 10000) (htag : tag.val = 4185) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4185 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04186 (tag : Fin 10000) (htag : tag.val = 4186) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4186 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04187 (tag : Fin 10000) (htag : tag.val = 4187) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4187 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04188 (tag : Fin 10000) (htag : tag.val = 4188) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4188 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04189 (tag : Fin 10000) (htag : tag.val = 4189) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4189 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04190 (tag : Fin 10000) (htag : tag.val = 4190) (k : Ring12) : tag.val = 4190 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04191 (tag : Fin 10000) (htag : tag.val = 4191) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4191 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04192 (tag : Fin 10000) (htag : tag.val = 4192) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4192 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04193 (tag : Fin 10000) (htag : tag.val = 4193) (x : State) (e : Event) (dr : Ring12) : tag.val = 4193 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04194 (tag : Fin 10000) (htag : tag.val = 4194) (x : State) (e : Event) (dr : Ring12) : tag.val = 4194 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04195 (tag : Fin 10000) (htag : tag.val = 4195) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4195 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04196 (tag : Fin 10000) (htag : tag.val = 4196) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4196 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04197 (tag : Fin 10000) (htag : tag.val = 4197) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4197 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04198 (tag : Fin 10000) (htag : tag.val = 4198) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4198 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04199 (tag : Fin 10000) (htag : tag.val = 4199) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4199 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
