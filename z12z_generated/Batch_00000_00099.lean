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
theorem generated_00000 (tag : Fin 10000) (htag : tag.val = 0) (k : Ring12) : tag.val = 0 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00001 (tag : Fin 10000) (htag : tag.val = 1) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00002 (tag : Fin 10000) (htag : tag.val = 2) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00003 (tag : Fin 10000) (htag : tag.val = 3) (x : State) (e : Event) (dr : Ring12) : tag.val = 3 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00004 (tag : Fin 10000) (htag : tag.val = 4) (x : State) (e : Event) (dr : Ring12) : tag.val = 4 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00005 (tag : Fin 10000) (htag : tag.val = 5) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00006 (tag : Fin 10000) (htag : tag.val = 6) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00007 (tag : Fin 10000) (htag : tag.val = 7) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00008 (tag : Fin 10000) (htag : tag.val = 8) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00009 (tag : Fin 10000) (htag : tag.val = 9) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00010 (tag : Fin 10000) (htag : tag.val = 10) (k : Ring12) : tag.val = 10 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00011 (tag : Fin 10000) (htag : tag.val = 11) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 11 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00012 (tag : Fin 10000) (htag : tag.val = 12) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 12 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00013 (tag : Fin 10000) (htag : tag.val = 13) (x : State) (e : Event) (dr : Ring12) : tag.val = 13 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00014 (tag : Fin 10000) (htag : tag.val = 14) (x : State) (e : Event) (dr : Ring12) : tag.val = 14 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00015 (tag : Fin 10000) (htag : tag.val = 15) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 15 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00016 (tag : Fin 10000) (htag : tag.val = 16) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 16 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00017 (tag : Fin 10000) (htag : tag.val = 17) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 17 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00018 (tag : Fin 10000) (htag : tag.val = 18) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 18 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00019 (tag : Fin 10000) (htag : tag.val = 19) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 19 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00020 (tag : Fin 10000) (htag : tag.val = 20) (k : Ring12) : tag.val = 20 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00021 (tag : Fin 10000) (htag : tag.val = 21) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 21 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00022 (tag : Fin 10000) (htag : tag.val = 22) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 22 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00023 (tag : Fin 10000) (htag : tag.val = 23) (x : State) (e : Event) (dr : Ring12) : tag.val = 23 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00024 (tag : Fin 10000) (htag : tag.val = 24) (x : State) (e : Event) (dr : Ring12) : tag.val = 24 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00025 (tag : Fin 10000) (htag : tag.val = 25) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 25 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00026 (tag : Fin 10000) (htag : tag.val = 26) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 26 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00027 (tag : Fin 10000) (htag : tag.val = 27) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 27 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00028 (tag : Fin 10000) (htag : tag.val = 28) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 28 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00029 (tag : Fin 10000) (htag : tag.val = 29) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 29 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00030 (tag : Fin 10000) (htag : tag.val = 30) (k : Ring12) : tag.val = 30 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00031 (tag : Fin 10000) (htag : tag.val = 31) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 31 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00032 (tag : Fin 10000) (htag : tag.val = 32) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 32 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00033 (tag : Fin 10000) (htag : tag.val = 33) (x : State) (e : Event) (dr : Ring12) : tag.val = 33 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00034 (tag : Fin 10000) (htag : tag.val = 34) (x : State) (e : Event) (dr : Ring12) : tag.val = 34 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00035 (tag : Fin 10000) (htag : tag.val = 35) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 35 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00036 (tag : Fin 10000) (htag : tag.val = 36) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 36 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00037 (tag : Fin 10000) (htag : tag.val = 37) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 37 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00038 (tag : Fin 10000) (htag : tag.val = 38) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 38 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00039 (tag : Fin 10000) (htag : tag.val = 39) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 39 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00040 (tag : Fin 10000) (htag : tag.val = 40) (k : Ring12) : tag.val = 40 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00041 (tag : Fin 10000) (htag : tag.val = 41) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 41 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00042 (tag : Fin 10000) (htag : tag.val = 42) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 42 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00043 (tag : Fin 10000) (htag : tag.val = 43) (x : State) (e : Event) (dr : Ring12) : tag.val = 43 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00044 (tag : Fin 10000) (htag : tag.val = 44) (x : State) (e : Event) (dr : Ring12) : tag.val = 44 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00045 (tag : Fin 10000) (htag : tag.val = 45) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 45 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00046 (tag : Fin 10000) (htag : tag.val = 46) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 46 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00047 (tag : Fin 10000) (htag : tag.val = 47) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 47 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00048 (tag : Fin 10000) (htag : tag.val = 48) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 48 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00049 (tag : Fin 10000) (htag : tag.val = 49) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 49 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00050 (tag : Fin 10000) (htag : tag.val = 50) (k : Ring12) : tag.val = 50 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00051 (tag : Fin 10000) (htag : tag.val = 51) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 51 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00052 (tag : Fin 10000) (htag : tag.val = 52) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 52 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00053 (tag : Fin 10000) (htag : tag.val = 53) (x : State) (e : Event) (dr : Ring12) : tag.val = 53 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00054 (tag : Fin 10000) (htag : tag.val = 54) (x : State) (e : Event) (dr : Ring12) : tag.val = 54 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00055 (tag : Fin 10000) (htag : tag.val = 55) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 55 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00056 (tag : Fin 10000) (htag : tag.val = 56) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 56 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00057 (tag : Fin 10000) (htag : tag.val = 57) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 57 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00058 (tag : Fin 10000) (htag : tag.val = 58) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 58 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00059 (tag : Fin 10000) (htag : tag.val = 59) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 59 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00060 (tag : Fin 10000) (htag : tag.val = 60) (k : Ring12) : tag.val = 60 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00061 (tag : Fin 10000) (htag : tag.val = 61) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 61 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00062 (tag : Fin 10000) (htag : tag.val = 62) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 62 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00063 (tag : Fin 10000) (htag : tag.val = 63) (x : State) (e : Event) (dr : Ring12) : tag.val = 63 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00064 (tag : Fin 10000) (htag : tag.val = 64) (x : State) (e : Event) (dr : Ring12) : tag.val = 64 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00065 (tag : Fin 10000) (htag : tag.val = 65) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 65 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00066 (tag : Fin 10000) (htag : tag.val = 66) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 66 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00067 (tag : Fin 10000) (htag : tag.val = 67) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 67 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00068 (tag : Fin 10000) (htag : tag.val = 68) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 68 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00069 (tag : Fin 10000) (htag : tag.val = 69) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 69 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00070 (tag : Fin 10000) (htag : tag.val = 70) (k : Ring12) : tag.val = 70 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00071 (tag : Fin 10000) (htag : tag.val = 71) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 71 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00072 (tag : Fin 10000) (htag : tag.val = 72) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 72 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00073 (tag : Fin 10000) (htag : tag.val = 73) (x : State) (e : Event) (dr : Ring12) : tag.val = 73 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00074 (tag : Fin 10000) (htag : tag.val = 74) (x : State) (e : Event) (dr : Ring12) : tag.val = 74 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00075 (tag : Fin 10000) (htag : tag.val = 75) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 75 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00076 (tag : Fin 10000) (htag : tag.val = 76) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 76 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00077 (tag : Fin 10000) (htag : tag.val = 77) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 77 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00078 (tag : Fin 10000) (htag : tag.val = 78) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 78 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00079 (tag : Fin 10000) (htag : tag.val = 79) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 79 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00080 (tag : Fin 10000) (htag : tag.val = 80) (k : Ring12) : tag.val = 80 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00081 (tag : Fin 10000) (htag : tag.val = 81) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 81 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00082 (tag : Fin 10000) (htag : tag.val = 82) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 82 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00083 (tag : Fin 10000) (htag : tag.val = 83) (x : State) (e : Event) (dr : Ring12) : tag.val = 83 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00084 (tag : Fin 10000) (htag : tag.val = 84) (x : State) (e : Event) (dr : Ring12) : tag.val = 84 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00085 (tag : Fin 10000) (htag : tag.val = 85) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 85 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00086 (tag : Fin 10000) (htag : tag.val = 86) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 86 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00087 (tag : Fin 10000) (htag : tag.val = 87) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 87 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00088 (tag : Fin 10000) (htag : tag.val = 88) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 88 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00089 (tag : Fin 10000) (htag : tag.val = 89) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 89 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00090 (tag : Fin 10000) (htag : tag.val = 90) (k : Ring12) : tag.val = 90 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00091 (tag : Fin 10000) (htag : tag.val = 91) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 91 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00092 (tag : Fin 10000) (htag : tag.val = 92) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 92 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00093 (tag : Fin 10000) (htag : tag.val = 93) (x : State) (e : Event) (dr : Ring12) : tag.val = 93 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00094 (tag : Fin 10000) (htag : tag.val = 94) (x : State) (e : Event) (dr : Ring12) : tag.val = 94 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00095 (tag : Fin 10000) (htag : tag.val = 95) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 95 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00096 (tag : Fin 10000) (htag : tag.val = 96) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 96 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00097 (tag : Fin 10000) (htag : tag.val = 97) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 97 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00098 (tag : Fin 10000) (htag : tag.val = 98) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 98 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00099 (tag : Fin 10000) (htag : tag.val = 99) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 99 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
