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
theorem generated_01000 (tag : Fin 10000) (htag : tag.val = 1000) (k : Ring12) : tag.val = 1000 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01001 (tag : Fin 10000) (htag : tag.val = 1001) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1001 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01002 (tag : Fin 10000) (htag : tag.val = 1002) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1002 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01003 (tag : Fin 10000) (htag : tag.val = 1003) (x : State) (e : Event) (dr : Ring12) : tag.val = 1003 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01004 (tag : Fin 10000) (htag : tag.val = 1004) (x : State) (e : Event) (dr : Ring12) : tag.val = 1004 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01005 (tag : Fin 10000) (htag : tag.val = 1005) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1005 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01006 (tag : Fin 10000) (htag : tag.val = 1006) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1006 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01007 (tag : Fin 10000) (htag : tag.val = 1007) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1007 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01008 (tag : Fin 10000) (htag : tag.val = 1008) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1008 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01009 (tag : Fin 10000) (htag : tag.val = 1009) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1009 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01010 (tag : Fin 10000) (htag : tag.val = 1010) (k : Ring12) : tag.val = 1010 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01011 (tag : Fin 10000) (htag : tag.val = 1011) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1011 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01012 (tag : Fin 10000) (htag : tag.val = 1012) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1012 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01013 (tag : Fin 10000) (htag : tag.val = 1013) (x : State) (e : Event) (dr : Ring12) : tag.val = 1013 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01014 (tag : Fin 10000) (htag : tag.val = 1014) (x : State) (e : Event) (dr : Ring12) : tag.val = 1014 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01015 (tag : Fin 10000) (htag : tag.val = 1015) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1015 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01016 (tag : Fin 10000) (htag : tag.val = 1016) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1016 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01017 (tag : Fin 10000) (htag : tag.val = 1017) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1017 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01018 (tag : Fin 10000) (htag : tag.val = 1018) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1018 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01019 (tag : Fin 10000) (htag : tag.val = 1019) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1019 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01020 (tag : Fin 10000) (htag : tag.val = 1020) (k : Ring12) : tag.val = 1020 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01021 (tag : Fin 10000) (htag : tag.val = 1021) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1021 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01022 (tag : Fin 10000) (htag : tag.val = 1022) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1022 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01023 (tag : Fin 10000) (htag : tag.val = 1023) (x : State) (e : Event) (dr : Ring12) : tag.val = 1023 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01024 (tag : Fin 10000) (htag : tag.val = 1024) (x : State) (e : Event) (dr : Ring12) : tag.val = 1024 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01025 (tag : Fin 10000) (htag : tag.val = 1025) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1025 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01026 (tag : Fin 10000) (htag : tag.val = 1026) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1026 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01027 (tag : Fin 10000) (htag : tag.val = 1027) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1027 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01028 (tag : Fin 10000) (htag : tag.val = 1028) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1028 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01029 (tag : Fin 10000) (htag : tag.val = 1029) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1029 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01030 (tag : Fin 10000) (htag : tag.val = 1030) (k : Ring12) : tag.val = 1030 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01031 (tag : Fin 10000) (htag : tag.val = 1031) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1031 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01032 (tag : Fin 10000) (htag : tag.val = 1032) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1032 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01033 (tag : Fin 10000) (htag : tag.val = 1033) (x : State) (e : Event) (dr : Ring12) : tag.val = 1033 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01034 (tag : Fin 10000) (htag : tag.val = 1034) (x : State) (e : Event) (dr : Ring12) : tag.val = 1034 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01035 (tag : Fin 10000) (htag : tag.val = 1035) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1035 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01036 (tag : Fin 10000) (htag : tag.val = 1036) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1036 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01037 (tag : Fin 10000) (htag : tag.val = 1037) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1037 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01038 (tag : Fin 10000) (htag : tag.val = 1038) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1038 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01039 (tag : Fin 10000) (htag : tag.val = 1039) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1039 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01040 (tag : Fin 10000) (htag : tag.val = 1040) (k : Ring12) : tag.val = 1040 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01041 (tag : Fin 10000) (htag : tag.val = 1041) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1041 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01042 (tag : Fin 10000) (htag : tag.val = 1042) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1042 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01043 (tag : Fin 10000) (htag : tag.val = 1043) (x : State) (e : Event) (dr : Ring12) : tag.val = 1043 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01044 (tag : Fin 10000) (htag : tag.val = 1044) (x : State) (e : Event) (dr : Ring12) : tag.val = 1044 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01045 (tag : Fin 10000) (htag : tag.val = 1045) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1045 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01046 (tag : Fin 10000) (htag : tag.val = 1046) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1046 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01047 (tag : Fin 10000) (htag : tag.val = 1047) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1047 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01048 (tag : Fin 10000) (htag : tag.val = 1048) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1048 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01049 (tag : Fin 10000) (htag : tag.val = 1049) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1049 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01050 (tag : Fin 10000) (htag : tag.val = 1050) (k : Ring12) : tag.val = 1050 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01051 (tag : Fin 10000) (htag : tag.val = 1051) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1051 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01052 (tag : Fin 10000) (htag : tag.val = 1052) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1052 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01053 (tag : Fin 10000) (htag : tag.val = 1053) (x : State) (e : Event) (dr : Ring12) : tag.val = 1053 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01054 (tag : Fin 10000) (htag : tag.val = 1054) (x : State) (e : Event) (dr : Ring12) : tag.val = 1054 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01055 (tag : Fin 10000) (htag : tag.val = 1055) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1055 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01056 (tag : Fin 10000) (htag : tag.val = 1056) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1056 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01057 (tag : Fin 10000) (htag : tag.val = 1057) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1057 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01058 (tag : Fin 10000) (htag : tag.val = 1058) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1058 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01059 (tag : Fin 10000) (htag : tag.val = 1059) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1059 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01060 (tag : Fin 10000) (htag : tag.val = 1060) (k : Ring12) : tag.val = 1060 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01061 (tag : Fin 10000) (htag : tag.val = 1061) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1061 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01062 (tag : Fin 10000) (htag : tag.val = 1062) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1062 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01063 (tag : Fin 10000) (htag : tag.val = 1063) (x : State) (e : Event) (dr : Ring12) : tag.val = 1063 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01064 (tag : Fin 10000) (htag : tag.val = 1064) (x : State) (e : Event) (dr : Ring12) : tag.val = 1064 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01065 (tag : Fin 10000) (htag : tag.val = 1065) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1065 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01066 (tag : Fin 10000) (htag : tag.val = 1066) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1066 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01067 (tag : Fin 10000) (htag : tag.val = 1067) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1067 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01068 (tag : Fin 10000) (htag : tag.val = 1068) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1068 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01069 (tag : Fin 10000) (htag : tag.val = 1069) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1069 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01070 (tag : Fin 10000) (htag : tag.val = 1070) (k : Ring12) : tag.val = 1070 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01071 (tag : Fin 10000) (htag : tag.val = 1071) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1071 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01072 (tag : Fin 10000) (htag : tag.val = 1072) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1072 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01073 (tag : Fin 10000) (htag : tag.val = 1073) (x : State) (e : Event) (dr : Ring12) : tag.val = 1073 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01074 (tag : Fin 10000) (htag : tag.val = 1074) (x : State) (e : Event) (dr : Ring12) : tag.val = 1074 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01075 (tag : Fin 10000) (htag : tag.val = 1075) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1075 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01076 (tag : Fin 10000) (htag : tag.val = 1076) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1076 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01077 (tag : Fin 10000) (htag : tag.val = 1077) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1077 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01078 (tag : Fin 10000) (htag : tag.val = 1078) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1078 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01079 (tag : Fin 10000) (htag : tag.val = 1079) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1079 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01080 (tag : Fin 10000) (htag : tag.val = 1080) (k : Ring12) : tag.val = 1080 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01081 (tag : Fin 10000) (htag : tag.val = 1081) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1081 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01082 (tag : Fin 10000) (htag : tag.val = 1082) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1082 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01083 (tag : Fin 10000) (htag : tag.val = 1083) (x : State) (e : Event) (dr : Ring12) : tag.val = 1083 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01084 (tag : Fin 10000) (htag : tag.val = 1084) (x : State) (e : Event) (dr : Ring12) : tag.val = 1084 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01085 (tag : Fin 10000) (htag : tag.val = 1085) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1085 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01086 (tag : Fin 10000) (htag : tag.val = 1086) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1086 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01087 (tag : Fin 10000) (htag : tag.val = 1087) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1087 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01088 (tag : Fin 10000) (htag : tag.val = 1088) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1088 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01089 (tag : Fin 10000) (htag : tag.val = 1089) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1089 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01090 (tag : Fin 10000) (htag : tag.val = 1090) (k : Ring12) : tag.val = 1090 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01091 (tag : Fin 10000) (htag : tag.val = 1091) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1091 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01092 (tag : Fin 10000) (htag : tag.val = 1092) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1092 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01093 (tag : Fin 10000) (htag : tag.val = 1093) (x : State) (e : Event) (dr : Ring12) : tag.val = 1093 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01094 (tag : Fin 10000) (htag : tag.val = 1094) (x : State) (e : Event) (dr : Ring12) : tag.val = 1094 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01095 (tag : Fin 10000) (htag : tag.val = 1095) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1095 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01096 (tag : Fin 10000) (htag : tag.val = 1096) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1096 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01097 (tag : Fin 10000) (htag : tag.val = 1097) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1097 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01098 (tag : Fin 10000) (htag : tag.val = 1098) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1098 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01099 (tag : Fin 10000) (htag : tag.val = 1099) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1099 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
