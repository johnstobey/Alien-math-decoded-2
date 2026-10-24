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
theorem generated_04000 (tag : Fin 10000) (htag : tag.val = 4000) (k : Ring12) : tag.val = 4000 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04001 (tag : Fin 10000) (htag : tag.val = 4001) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4001 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04002 (tag : Fin 10000) (htag : tag.val = 4002) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4002 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04003 (tag : Fin 10000) (htag : tag.val = 4003) (x : State) (e : Event) (dr : Ring12) : tag.val = 4003 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04004 (tag : Fin 10000) (htag : tag.val = 4004) (x : State) (e : Event) (dr : Ring12) : tag.val = 4004 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04005 (tag : Fin 10000) (htag : tag.val = 4005) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4005 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04006 (tag : Fin 10000) (htag : tag.val = 4006) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4006 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04007 (tag : Fin 10000) (htag : tag.val = 4007) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4007 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04008 (tag : Fin 10000) (htag : tag.val = 4008) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4008 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04009 (tag : Fin 10000) (htag : tag.val = 4009) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4009 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04010 (tag : Fin 10000) (htag : tag.val = 4010) (k : Ring12) : tag.val = 4010 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04011 (tag : Fin 10000) (htag : tag.val = 4011) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4011 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04012 (tag : Fin 10000) (htag : tag.val = 4012) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4012 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04013 (tag : Fin 10000) (htag : tag.val = 4013) (x : State) (e : Event) (dr : Ring12) : tag.val = 4013 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04014 (tag : Fin 10000) (htag : tag.val = 4014) (x : State) (e : Event) (dr : Ring12) : tag.val = 4014 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04015 (tag : Fin 10000) (htag : tag.val = 4015) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4015 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04016 (tag : Fin 10000) (htag : tag.val = 4016) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4016 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04017 (tag : Fin 10000) (htag : tag.val = 4017) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4017 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04018 (tag : Fin 10000) (htag : tag.val = 4018) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4018 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04019 (tag : Fin 10000) (htag : tag.val = 4019) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4019 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04020 (tag : Fin 10000) (htag : tag.val = 4020) (k : Ring12) : tag.val = 4020 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04021 (tag : Fin 10000) (htag : tag.val = 4021) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4021 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04022 (tag : Fin 10000) (htag : tag.val = 4022) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4022 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04023 (tag : Fin 10000) (htag : tag.val = 4023) (x : State) (e : Event) (dr : Ring12) : tag.val = 4023 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04024 (tag : Fin 10000) (htag : tag.val = 4024) (x : State) (e : Event) (dr : Ring12) : tag.val = 4024 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04025 (tag : Fin 10000) (htag : tag.val = 4025) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4025 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04026 (tag : Fin 10000) (htag : tag.val = 4026) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4026 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04027 (tag : Fin 10000) (htag : tag.val = 4027) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4027 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04028 (tag : Fin 10000) (htag : tag.val = 4028) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4028 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04029 (tag : Fin 10000) (htag : tag.val = 4029) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4029 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04030 (tag : Fin 10000) (htag : tag.val = 4030) (k : Ring12) : tag.val = 4030 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04031 (tag : Fin 10000) (htag : tag.val = 4031) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4031 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04032 (tag : Fin 10000) (htag : tag.val = 4032) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4032 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04033 (tag : Fin 10000) (htag : tag.val = 4033) (x : State) (e : Event) (dr : Ring12) : tag.val = 4033 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04034 (tag : Fin 10000) (htag : tag.val = 4034) (x : State) (e : Event) (dr : Ring12) : tag.val = 4034 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04035 (tag : Fin 10000) (htag : tag.val = 4035) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4035 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04036 (tag : Fin 10000) (htag : tag.val = 4036) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4036 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04037 (tag : Fin 10000) (htag : tag.val = 4037) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4037 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04038 (tag : Fin 10000) (htag : tag.val = 4038) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4038 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04039 (tag : Fin 10000) (htag : tag.val = 4039) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4039 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04040 (tag : Fin 10000) (htag : tag.val = 4040) (k : Ring12) : tag.val = 4040 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04041 (tag : Fin 10000) (htag : tag.val = 4041) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4041 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04042 (tag : Fin 10000) (htag : tag.val = 4042) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4042 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04043 (tag : Fin 10000) (htag : tag.val = 4043) (x : State) (e : Event) (dr : Ring12) : tag.val = 4043 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04044 (tag : Fin 10000) (htag : tag.val = 4044) (x : State) (e : Event) (dr : Ring12) : tag.val = 4044 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04045 (tag : Fin 10000) (htag : tag.val = 4045) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4045 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04046 (tag : Fin 10000) (htag : tag.val = 4046) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4046 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04047 (tag : Fin 10000) (htag : tag.val = 4047) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4047 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04048 (tag : Fin 10000) (htag : tag.val = 4048) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4048 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04049 (tag : Fin 10000) (htag : tag.val = 4049) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4049 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04050 (tag : Fin 10000) (htag : tag.val = 4050) (k : Ring12) : tag.val = 4050 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04051 (tag : Fin 10000) (htag : tag.val = 4051) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4051 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04052 (tag : Fin 10000) (htag : tag.val = 4052) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4052 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04053 (tag : Fin 10000) (htag : tag.val = 4053) (x : State) (e : Event) (dr : Ring12) : tag.val = 4053 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04054 (tag : Fin 10000) (htag : tag.val = 4054) (x : State) (e : Event) (dr : Ring12) : tag.val = 4054 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04055 (tag : Fin 10000) (htag : tag.val = 4055) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4055 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04056 (tag : Fin 10000) (htag : tag.val = 4056) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4056 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04057 (tag : Fin 10000) (htag : tag.val = 4057) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4057 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04058 (tag : Fin 10000) (htag : tag.val = 4058) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4058 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04059 (tag : Fin 10000) (htag : tag.val = 4059) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4059 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04060 (tag : Fin 10000) (htag : tag.val = 4060) (k : Ring12) : tag.val = 4060 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04061 (tag : Fin 10000) (htag : tag.val = 4061) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4061 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04062 (tag : Fin 10000) (htag : tag.val = 4062) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4062 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04063 (tag : Fin 10000) (htag : tag.val = 4063) (x : State) (e : Event) (dr : Ring12) : tag.val = 4063 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04064 (tag : Fin 10000) (htag : tag.val = 4064) (x : State) (e : Event) (dr : Ring12) : tag.val = 4064 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04065 (tag : Fin 10000) (htag : tag.val = 4065) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4065 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04066 (tag : Fin 10000) (htag : tag.val = 4066) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4066 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04067 (tag : Fin 10000) (htag : tag.val = 4067) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4067 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04068 (tag : Fin 10000) (htag : tag.val = 4068) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4068 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04069 (tag : Fin 10000) (htag : tag.val = 4069) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4069 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04070 (tag : Fin 10000) (htag : tag.val = 4070) (k : Ring12) : tag.val = 4070 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04071 (tag : Fin 10000) (htag : tag.val = 4071) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4071 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04072 (tag : Fin 10000) (htag : tag.val = 4072) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4072 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04073 (tag : Fin 10000) (htag : tag.val = 4073) (x : State) (e : Event) (dr : Ring12) : tag.val = 4073 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04074 (tag : Fin 10000) (htag : tag.val = 4074) (x : State) (e : Event) (dr : Ring12) : tag.val = 4074 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04075 (tag : Fin 10000) (htag : tag.val = 4075) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4075 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04076 (tag : Fin 10000) (htag : tag.val = 4076) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4076 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04077 (tag : Fin 10000) (htag : tag.val = 4077) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4077 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04078 (tag : Fin 10000) (htag : tag.val = 4078) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4078 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04079 (tag : Fin 10000) (htag : tag.val = 4079) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4079 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04080 (tag : Fin 10000) (htag : tag.val = 4080) (k : Ring12) : tag.val = 4080 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04081 (tag : Fin 10000) (htag : tag.val = 4081) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4081 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04082 (tag : Fin 10000) (htag : tag.val = 4082) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4082 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04083 (tag : Fin 10000) (htag : tag.val = 4083) (x : State) (e : Event) (dr : Ring12) : tag.val = 4083 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04084 (tag : Fin 10000) (htag : tag.val = 4084) (x : State) (e : Event) (dr : Ring12) : tag.val = 4084 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04085 (tag : Fin 10000) (htag : tag.val = 4085) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4085 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04086 (tag : Fin 10000) (htag : tag.val = 4086) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4086 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04087 (tag : Fin 10000) (htag : tag.val = 4087) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4087 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04088 (tag : Fin 10000) (htag : tag.val = 4088) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4088 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04089 (tag : Fin 10000) (htag : tag.val = 4089) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4089 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04090 (tag : Fin 10000) (htag : tag.val = 4090) (k : Ring12) : tag.val = 4090 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04091 (tag : Fin 10000) (htag : tag.val = 4091) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4091 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04092 (tag : Fin 10000) (htag : tag.val = 4092) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4092 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04093 (tag : Fin 10000) (htag : tag.val = 4093) (x : State) (e : Event) (dr : Ring12) : tag.val = 4093 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04094 (tag : Fin 10000) (htag : tag.val = 4094) (x : State) (e : Event) (dr : Ring12) : tag.val = 4094 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04095 (tag : Fin 10000) (htag : tag.val = 4095) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4095 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04096 (tag : Fin 10000) (htag : tag.val = 4096) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4096 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04097 (tag : Fin 10000) (htag : tag.val = 4097) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4097 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04098 (tag : Fin 10000) (htag : tag.val = 4098) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4098 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04099 (tag : Fin 10000) (htag : tag.val = 4099) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4099 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
