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
theorem generated_02000 (tag : Fin 10000) (htag : tag.val = 2000) (k : Ring12) : tag.val = 2000 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02001 (tag : Fin 10000) (htag : tag.val = 2001) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2001 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02002 (tag : Fin 10000) (htag : tag.val = 2002) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2002 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02003 (tag : Fin 10000) (htag : tag.val = 2003) (x : State) (e : Event) (dr : Ring12) : tag.val = 2003 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02004 (tag : Fin 10000) (htag : tag.val = 2004) (x : State) (e : Event) (dr : Ring12) : tag.val = 2004 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02005 (tag : Fin 10000) (htag : tag.val = 2005) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2005 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02006 (tag : Fin 10000) (htag : tag.val = 2006) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2006 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02007 (tag : Fin 10000) (htag : tag.val = 2007) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2007 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02008 (tag : Fin 10000) (htag : tag.val = 2008) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2008 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02009 (tag : Fin 10000) (htag : tag.val = 2009) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2009 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02010 (tag : Fin 10000) (htag : tag.val = 2010) (k : Ring12) : tag.val = 2010 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02011 (tag : Fin 10000) (htag : tag.val = 2011) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2011 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02012 (tag : Fin 10000) (htag : tag.val = 2012) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2012 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02013 (tag : Fin 10000) (htag : tag.val = 2013) (x : State) (e : Event) (dr : Ring12) : tag.val = 2013 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02014 (tag : Fin 10000) (htag : tag.val = 2014) (x : State) (e : Event) (dr : Ring12) : tag.val = 2014 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02015 (tag : Fin 10000) (htag : tag.val = 2015) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2015 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02016 (tag : Fin 10000) (htag : tag.val = 2016) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2016 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02017 (tag : Fin 10000) (htag : tag.val = 2017) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2017 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02018 (tag : Fin 10000) (htag : tag.val = 2018) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2018 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02019 (tag : Fin 10000) (htag : tag.val = 2019) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2019 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02020 (tag : Fin 10000) (htag : tag.val = 2020) (k : Ring12) : tag.val = 2020 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02021 (tag : Fin 10000) (htag : tag.val = 2021) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2021 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02022 (tag : Fin 10000) (htag : tag.val = 2022) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2022 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02023 (tag : Fin 10000) (htag : tag.val = 2023) (x : State) (e : Event) (dr : Ring12) : tag.val = 2023 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02024 (tag : Fin 10000) (htag : tag.val = 2024) (x : State) (e : Event) (dr : Ring12) : tag.val = 2024 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02025 (tag : Fin 10000) (htag : tag.val = 2025) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2025 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02026 (tag : Fin 10000) (htag : tag.val = 2026) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2026 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02027 (tag : Fin 10000) (htag : tag.val = 2027) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2027 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02028 (tag : Fin 10000) (htag : tag.val = 2028) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2028 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02029 (tag : Fin 10000) (htag : tag.val = 2029) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2029 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02030 (tag : Fin 10000) (htag : tag.val = 2030) (k : Ring12) : tag.val = 2030 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02031 (tag : Fin 10000) (htag : tag.val = 2031) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2031 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02032 (tag : Fin 10000) (htag : tag.val = 2032) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2032 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02033 (tag : Fin 10000) (htag : tag.val = 2033) (x : State) (e : Event) (dr : Ring12) : tag.val = 2033 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02034 (tag : Fin 10000) (htag : tag.val = 2034) (x : State) (e : Event) (dr : Ring12) : tag.val = 2034 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02035 (tag : Fin 10000) (htag : tag.val = 2035) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2035 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02036 (tag : Fin 10000) (htag : tag.val = 2036) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2036 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02037 (tag : Fin 10000) (htag : tag.val = 2037) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2037 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02038 (tag : Fin 10000) (htag : tag.val = 2038) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2038 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02039 (tag : Fin 10000) (htag : tag.val = 2039) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2039 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02040 (tag : Fin 10000) (htag : tag.val = 2040) (k : Ring12) : tag.val = 2040 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02041 (tag : Fin 10000) (htag : tag.val = 2041) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2041 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02042 (tag : Fin 10000) (htag : tag.val = 2042) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2042 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02043 (tag : Fin 10000) (htag : tag.val = 2043) (x : State) (e : Event) (dr : Ring12) : tag.val = 2043 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02044 (tag : Fin 10000) (htag : tag.val = 2044) (x : State) (e : Event) (dr : Ring12) : tag.val = 2044 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02045 (tag : Fin 10000) (htag : tag.val = 2045) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2045 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02046 (tag : Fin 10000) (htag : tag.val = 2046) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2046 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02047 (tag : Fin 10000) (htag : tag.val = 2047) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2047 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02048 (tag : Fin 10000) (htag : tag.val = 2048) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2048 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02049 (tag : Fin 10000) (htag : tag.val = 2049) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2049 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02050 (tag : Fin 10000) (htag : tag.val = 2050) (k : Ring12) : tag.val = 2050 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02051 (tag : Fin 10000) (htag : tag.val = 2051) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2051 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02052 (tag : Fin 10000) (htag : tag.val = 2052) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2052 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02053 (tag : Fin 10000) (htag : tag.val = 2053) (x : State) (e : Event) (dr : Ring12) : tag.val = 2053 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02054 (tag : Fin 10000) (htag : tag.val = 2054) (x : State) (e : Event) (dr : Ring12) : tag.val = 2054 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02055 (tag : Fin 10000) (htag : tag.val = 2055) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2055 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02056 (tag : Fin 10000) (htag : tag.val = 2056) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2056 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02057 (tag : Fin 10000) (htag : tag.val = 2057) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2057 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02058 (tag : Fin 10000) (htag : tag.val = 2058) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2058 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02059 (tag : Fin 10000) (htag : tag.val = 2059) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2059 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02060 (tag : Fin 10000) (htag : tag.val = 2060) (k : Ring12) : tag.val = 2060 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02061 (tag : Fin 10000) (htag : tag.val = 2061) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2061 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02062 (tag : Fin 10000) (htag : tag.val = 2062) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2062 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02063 (tag : Fin 10000) (htag : tag.val = 2063) (x : State) (e : Event) (dr : Ring12) : tag.val = 2063 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02064 (tag : Fin 10000) (htag : tag.val = 2064) (x : State) (e : Event) (dr : Ring12) : tag.val = 2064 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02065 (tag : Fin 10000) (htag : tag.val = 2065) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2065 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02066 (tag : Fin 10000) (htag : tag.val = 2066) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2066 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02067 (tag : Fin 10000) (htag : tag.val = 2067) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2067 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02068 (tag : Fin 10000) (htag : tag.val = 2068) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2068 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02069 (tag : Fin 10000) (htag : tag.val = 2069) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2069 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02070 (tag : Fin 10000) (htag : tag.val = 2070) (k : Ring12) : tag.val = 2070 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02071 (tag : Fin 10000) (htag : tag.val = 2071) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2071 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02072 (tag : Fin 10000) (htag : tag.val = 2072) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2072 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02073 (tag : Fin 10000) (htag : tag.val = 2073) (x : State) (e : Event) (dr : Ring12) : tag.val = 2073 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02074 (tag : Fin 10000) (htag : tag.val = 2074) (x : State) (e : Event) (dr : Ring12) : tag.val = 2074 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02075 (tag : Fin 10000) (htag : tag.val = 2075) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2075 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02076 (tag : Fin 10000) (htag : tag.val = 2076) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2076 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02077 (tag : Fin 10000) (htag : tag.val = 2077) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2077 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02078 (tag : Fin 10000) (htag : tag.val = 2078) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2078 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02079 (tag : Fin 10000) (htag : tag.val = 2079) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2079 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02080 (tag : Fin 10000) (htag : tag.val = 2080) (k : Ring12) : tag.val = 2080 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02081 (tag : Fin 10000) (htag : tag.val = 2081) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2081 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02082 (tag : Fin 10000) (htag : tag.val = 2082) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2082 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02083 (tag : Fin 10000) (htag : tag.val = 2083) (x : State) (e : Event) (dr : Ring12) : tag.val = 2083 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02084 (tag : Fin 10000) (htag : tag.val = 2084) (x : State) (e : Event) (dr : Ring12) : tag.val = 2084 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02085 (tag : Fin 10000) (htag : tag.val = 2085) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2085 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02086 (tag : Fin 10000) (htag : tag.val = 2086) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2086 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02087 (tag : Fin 10000) (htag : tag.val = 2087) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2087 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02088 (tag : Fin 10000) (htag : tag.val = 2088) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2088 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02089 (tag : Fin 10000) (htag : tag.val = 2089) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2089 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02090 (tag : Fin 10000) (htag : tag.val = 2090) (k : Ring12) : tag.val = 2090 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02091 (tag : Fin 10000) (htag : tag.val = 2091) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2091 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02092 (tag : Fin 10000) (htag : tag.val = 2092) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2092 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02093 (tag : Fin 10000) (htag : tag.val = 2093) (x : State) (e : Event) (dr : Ring12) : tag.val = 2093 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02094 (tag : Fin 10000) (htag : tag.val = 2094) (x : State) (e : Event) (dr : Ring12) : tag.val = 2094 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02095 (tag : Fin 10000) (htag : tag.val = 2095) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2095 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02096 (tag : Fin 10000) (htag : tag.val = 2096) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2096 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02097 (tag : Fin 10000) (htag : tag.val = 2097) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2097 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02098 (tag : Fin 10000) (htag : tag.val = 2098) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2098 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02099 (tag : Fin 10000) (htag : tag.val = 2099) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2099 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
