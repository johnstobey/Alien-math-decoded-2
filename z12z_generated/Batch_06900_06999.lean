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
theorem generated_06900 (tag : Fin 10000) (htag : tag.val = 6900) (k : Ring12) : tag.val = 6900 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06901 (tag : Fin 10000) (htag : tag.val = 6901) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6901 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06902 (tag : Fin 10000) (htag : tag.val = 6902) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6902 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06903 (tag : Fin 10000) (htag : tag.val = 6903) (x : State) (e : Event) (dr : Ring12) : tag.val = 6903 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06904 (tag : Fin 10000) (htag : tag.val = 6904) (x : State) (e : Event) (dr : Ring12) : tag.val = 6904 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06905 (tag : Fin 10000) (htag : tag.val = 6905) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6905 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06906 (tag : Fin 10000) (htag : tag.val = 6906) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6906 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06907 (tag : Fin 10000) (htag : tag.val = 6907) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6907 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06908 (tag : Fin 10000) (htag : tag.val = 6908) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6908 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06909 (tag : Fin 10000) (htag : tag.val = 6909) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6909 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06910 (tag : Fin 10000) (htag : tag.val = 6910) (k : Ring12) : tag.val = 6910 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06911 (tag : Fin 10000) (htag : tag.val = 6911) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6911 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06912 (tag : Fin 10000) (htag : tag.val = 6912) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6912 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06913 (tag : Fin 10000) (htag : tag.val = 6913) (x : State) (e : Event) (dr : Ring12) : tag.val = 6913 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06914 (tag : Fin 10000) (htag : tag.val = 6914) (x : State) (e : Event) (dr : Ring12) : tag.val = 6914 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06915 (tag : Fin 10000) (htag : tag.val = 6915) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6915 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06916 (tag : Fin 10000) (htag : tag.val = 6916) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6916 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06917 (tag : Fin 10000) (htag : tag.val = 6917) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6917 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06918 (tag : Fin 10000) (htag : tag.val = 6918) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6918 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06919 (tag : Fin 10000) (htag : tag.val = 6919) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6919 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06920 (tag : Fin 10000) (htag : tag.val = 6920) (k : Ring12) : tag.val = 6920 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06921 (tag : Fin 10000) (htag : tag.val = 6921) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6921 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06922 (tag : Fin 10000) (htag : tag.val = 6922) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6922 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06923 (tag : Fin 10000) (htag : tag.val = 6923) (x : State) (e : Event) (dr : Ring12) : tag.val = 6923 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06924 (tag : Fin 10000) (htag : tag.val = 6924) (x : State) (e : Event) (dr : Ring12) : tag.val = 6924 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06925 (tag : Fin 10000) (htag : tag.val = 6925) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6925 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06926 (tag : Fin 10000) (htag : tag.val = 6926) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6926 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06927 (tag : Fin 10000) (htag : tag.val = 6927) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6927 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06928 (tag : Fin 10000) (htag : tag.val = 6928) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6928 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06929 (tag : Fin 10000) (htag : tag.val = 6929) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6929 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06930 (tag : Fin 10000) (htag : tag.val = 6930) (k : Ring12) : tag.val = 6930 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06931 (tag : Fin 10000) (htag : tag.val = 6931) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6931 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06932 (tag : Fin 10000) (htag : tag.val = 6932) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6932 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06933 (tag : Fin 10000) (htag : tag.val = 6933) (x : State) (e : Event) (dr : Ring12) : tag.val = 6933 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06934 (tag : Fin 10000) (htag : tag.val = 6934) (x : State) (e : Event) (dr : Ring12) : tag.val = 6934 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06935 (tag : Fin 10000) (htag : tag.val = 6935) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6935 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06936 (tag : Fin 10000) (htag : tag.val = 6936) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6936 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06937 (tag : Fin 10000) (htag : tag.val = 6937) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6937 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06938 (tag : Fin 10000) (htag : tag.val = 6938) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6938 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06939 (tag : Fin 10000) (htag : tag.val = 6939) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6939 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06940 (tag : Fin 10000) (htag : tag.val = 6940) (k : Ring12) : tag.val = 6940 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06941 (tag : Fin 10000) (htag : tag.val = 6941) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6941 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06942 (tag : Fin 10000) (htag : tag.val = 6942) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6942 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06943 (tag : Fin 10000) (htag : tag.val = 6943) (x : State) (e : Event) (dr : Ring12) : tag.val = 6943 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06944 (tag : Fin 10000) (htag : tag.val = 6944) (x : State) (e : Event) (dr : Ring12) : tag.val = 6944 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06945 (tag : Fin 10000) (htag : tag.val = 6945) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6945 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06946 (tag : Fin 10000) (htag : tag.val = 6946) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6946 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06947 (tag : Fin 10000) (htag : tag.val = 6947) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6947 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06948 (tag : Fin 10000) (htag : tag.val = 6948) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6948 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06949 (tag : Fin 10000) (htag : tag.val = 6949) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6949 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06950 (tag : Fin 10000) (htag : tag.val = 6950) (k : Ring12) : tag.val = 6950 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06951 (tag : Fin 10000) (htag : tag.val = 6951) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6951 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06952 (tag : Fin 10000) (htag : tag.val = 6952) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6952 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06953 (tag : Fin 10000) (htag : tag.val = 6953) (x : State) (e : Event) (dr : Ring12) : tag.val = 6953 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06954 (tag : Fin 10000) (htag : tag.val = 6954) (x : State) (e : Event) (dr : Ring12) : tag.val = 6954 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06955 (tag : Fin 10000) (htag : tag.val = 6955) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6955 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06956 (tag : Fin 10000) (htag : tag.val = 6956) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6956 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06957 (tag : Fin 10000) (htag : tag.val = 6957) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6957 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06958 (tag : Fin 10000) (htag : tag.val = 6958) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6958 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06959 (tag : Fin 10000) (htag : tag.val = 6959) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6959 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06960 (tag : Fin 10000) (htag : tag.val = 6960) (k : Ring12) : tag.val = 6960 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06961 (tag : Fin 10000) (htag : tag.val = 6961) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6961 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06962 (tag : Fin 10000) (htag : tag.val = 6962) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6962 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06963 (tag : Fin 10000) (htag : tag.val = 6963) (x : State) (e : Event) (dr : Ring12) : tag.val = 6963 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06964 (tag : Fin 10000) (htag : tag.val = 6964) (x : State) (e : Event) (dr : Ring12) : tag.val = 6964 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06965 (tag : Fin 10000) (htag : tag.val = 6965) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6965 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06966 (tag : Fin 10000) (htag : tag.val = 6966) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6966 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06967 (tag : Fin 10000) (htag : tag.val = 6967) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6967 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06968 (tag : Fin 10000) (htag : tag.val = 6968) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6968 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06969 (tag : Fin 10000) (htag : tag.val = 6969) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6969 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06970 (tag : Fin 10000) (htag : tag.val = 6970) (k : Ring12) : tag.val = 6970 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06971 (tag : Fin 10000) (htag : tag.val = 6971) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6971 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06972 (tag : Fin 10000) (htag : tag.val = 6972) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6972 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06973 (tag : Fin 10000) (htag : tag.val = 6973) (x : State) (e : Event) (dr : Ring12) : tag.val = 6973 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06974 (tag : Fin 10000) (htag : tag.val = 6974) (x : State) (e : Event) (dr : Ring12) : tag.val = 6974 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06975 (tag : Fin 10000) (htag : tag.val = 6975) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6975 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06976 (tag : Fin 10000) (htag : tag.val = 6976) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6976 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06977 (tag : Fin 10000) (htag : tag.val = 6977) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6977 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06978 (tag : Fin 10000) (htag : tag.val = 6978) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6978 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06979 (tag : Fin 10000) (htag : tag.val = 6979) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6979 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06980 (tag : Fin 10000) (htag : tag.val = 6980) (k : Ring12) : tag.val = 6980 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06981 (tag : Fin 10000) (htag : tag.val = 6981) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6981 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06982 (tag : Fin 10000) (htag : tag.val = 6982) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6982 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06983 (tag : Fin 10000) (htag : tag.val = 6983) (x : State) (e : Event) (dr : Ring12) : tag.val = 6983 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06984 (tag : Fin 10000) (htag : tag.val = 6984) (x : State) (e : Event) (dr : Ring12) : tag.val = 6984 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06985 (tag : Fin 10000) (htag : tag.val = 6985) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6985 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06986 (tag : Fin 10000) (htag : tag.val = 6986) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6986 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06987 (tag : Fin 10000) (htag : tag.val = 6987) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6987 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06988 (tag : Fin 10000) (htag : tag.val = 6988) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6988 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06989 (tag : Fin 10000) (htag : tag.val = 6989) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6989 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06990 (tag : Fin 10000) (htag : tag.val = 6990) (k : Ring12) : tag.val = 6990 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06991 (tag : Fin 10000) (htag : tag.val = 6991) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6991 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06992 (tag : Fin 10000) (htag : tag.val = 6992) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6992 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06993 (tag : Fin 10000) (htag : tag.val = 6993) (x : State) (e : Event) (dr : Ring12) : tag.val = 6993 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06994 (tag : Fin 10000) (htag : tag.val = 6994) (x : State) (e : Event) (dr : Ring12) : tag.val = 6994 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06995 (tag : Fin 10000) (htag : tag.val = 6995) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6995 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06996 (tag : Fin 10000) (htag : tag.val = 6996) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6996 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06997 (tag : Fin 10000) (htag : tag.val = 6997) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6997 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06998 (tag : Fin 10000) (htag : tag.val = 6998) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6998 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06999 (tag : Fin 10000) (htag : tag.val = 6999) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6999 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
