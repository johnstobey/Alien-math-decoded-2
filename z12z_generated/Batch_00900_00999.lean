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
theorem generated_00900 (tag : Fin 10000) (htag : tag.val = 900) (k : Ring12) : tag.val = 900 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00901 (tag : Fin 10000) (htag : tag.val = 901) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 901 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00902 (tag : Fin 10000) (htag : tag.val = 902) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 902 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00903 (tag : Fin 10000) (htag : tag.val = 903) (x : State) (e : Event) (dr : Ring12) : tag.val = 903 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00904 (tag : Fin 10000) (htag : tag.val = 904) (x : State) (e : Event) (dr : Ring12) : tag.val = 904 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00905 (tag : Fin 10000) (htag : tag.val = 905) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 905 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00906 (tag : Fin 10000) (htag : tag.val = 906) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 906 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00907 (tag : Fin 10000) (htag : tag.val = 907) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 907 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00908 (tag : Fin 10000) (htag : tag.val = 908) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 908 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00909 (tag : Fin 10000) (htag : tag.val = 909) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 909 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00910 (tag : Fin 10000) (htag : tag.val = 910) (k : Ring12) : tag.val = 910 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00911 (tag : Fin 10000) (htag : tag.val = 911) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 911 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00912 (tag : Fin 10000) (htag : tag.val = 912) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 912 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00913 (tag : Fin 10000) (htag : tag.val = 913) (x : State) (e : Event) (dr : Ring12) : tag.val = 913 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00914 (tag : Fin 10000) (htag : tag.val = 914) (x : State) (e : Event) (dr : Ring12) : tag.val = 914 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00915 (tag : Fin 10000) (htag : tag.val = 915) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 915 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00916 (tag : Fin 10000) (htag : tag.val = 916) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 916 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00917 (tag : Fin 10000) (htag : tag.val = 917) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 917 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00918 (tag : Fin 10000) (htag : tag.val = 918) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 918 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00919 (tag : Fin 10000) (htag : tag.val = 919) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 919 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00920 (tag : Fin 10000) (htag : tag.val = 920) (k : Ring12) : tag.val = 920 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00921 (tag : Fin 10000) (htag : tag.val = 921) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 921 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00922 (tag : Fin 10000) (htag : tag.val = 922) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 922 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00923 (tag : Fin 10000) (htag : tag.val = 923) (x : State) (e : Event) (dr : Ring12) : tag.val = 923 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00924 (tag : Fin 10000) (htag : tag.val = 924) (x : State) (e : Event) (dr : Ring12) : tag.val = 924 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00925 (tag : Fin 10000) (htag : tag.val = 925) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 925 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00926 (tag : Fin 10000) (htag : tag.val = 926) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 926 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00927 (tag : Fin 10000) (htag : tag.val = 927) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 927 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00928 (tag : Fin 10000) (htag : tag.val = 928) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 928 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00929 (tag : Fin 10000) (htag : tag.val = 929) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 929 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00930 (tag : Fin 10000) (htag : tag.val = 930) (k : Ring12) : tag.val = 930 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00931 (tag : Fin 10000) (htag : tag.val = 931) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 931 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00932 (tag : Fin 10000) (htag : tag.val = 932) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 932 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00933 (tag : Fin 10000) (htag : tag.val = 933) (x : State) (e : Event) (dr : Ring12) : tag.val = 933 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00934 (tag : Fin 10000) (htag : tag.val = 934) (x : State) (e : Event) (dr : Ring12) : tag.val = 934 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00935 (tag : Fin 10000) (htag : tag.val = 935) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 935 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00936 (tag : Fin 10000) (htag : tag.val = 936) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 936 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00937 (tag : Fin 10000) (htag : tag.val = 937) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 937 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00938 (tag : Fin 10000) (htag : tag.val = 938) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 938 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00939 (tag : Fin 10000) (htag : tag.val = 939) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 939 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00940 (tag : Fin 10000) (htag : tag.val = 940) (k : Ring12) : tag.val = 940 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00941 (tag : Fin 10000) (htag : tag.val = 941) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 941 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00942 (tag : Fin 10000) (htag : tag.val = 942) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 942 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00943 (tag : Fin 10000) (htag : tag.val = 943) (x : State) (e : Event) (dr : Ring12) : tag.val = 943 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00944 (tag : Fin 10000) (htag : tag.val = 944) (x : State) (e : Event) (dr : Ring12) : tag.val = 944 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00945 (tag : Fin 10000) (htag : tag.val = 945) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 945 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00946 (tag : Fin 10000) (htag : tag.val = 946) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 946 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00947 (tag : Fin 10000) (htag : tag.val = 947) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 947 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00948 (tag : Fin 10000) (htag : tag.val = 948) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 948 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00949 (tag : Fin 10000) (htag : tag.val = 949) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 949 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00950 (tag : Fin 10000) (htag : tag.val = 950) (k : Ring12) : tag.val = 950 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00951 (tag : Fin 10000) (htag : tag.val = 951) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 951 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00952 (tag : Fin 10000) (htag : tag.val = 952) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 952 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00953 (tag : Fin 10000) (htag : tag.val = 953) (x : State) (e : Event) (dr : Ring12) : tag.val = 953 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00954 (tag : Fin 10000) (htag : tag.val = 954) (x : State) (e : Event) (dr : Ring12) : tag.val = 954 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00955 (tag : Fin 10000) (htag : tag.val = 955) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 955 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00956 (tag : Fin 10000) (htag : tag.val = 956) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 956 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00957 (tag : Fin 10000) (htag : tag.val = 957) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 957 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00958 (tag : Fin 10000) (htag : tag.val = 958) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 958 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00959 (tag : Fin 10000) (htag : tag.val = 959) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 959 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00960 (tag : Fin 10000) (htag : tag.val = 960) (k : Ring12) : tag.val = 960 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00961 (tag : Fin 10000) (htag : tag.val = 961) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 961 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00962 (tag : Fin 10000) (htag : tag.val = 962) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 962 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00963 (tag : Fin 10000) (htag : tag.val = 963) (x : State) (e : Event) (dr : Ring12) : tag.val = 963 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00964 (tag : Fin 10000) (htag : tag.val = 964) (x : State) (e : Event) (dr : Ring12) : tag.val = 964 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00965 (tag : Fin 10000) (htag : tag.val = 965) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 965 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00966 (tag : Fin 10000) (htag : tag.val = 966) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 966 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00967 (tag : Fin 10000) (htag : tag.val = 967) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 967 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00968 (tag : Fin 10000) (htag : tag.val = 968) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 968 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00969 (tag : Fin 10000) (htag : tag.val = 969) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 969 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00970 (tag : Fin 10000) (htag : tag.val = 970) (k : Ring12) : tag.val = 970 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00971 (tag : Fin 10000) (htag : tag.val = 971) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 971 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00972 (tag : Fin 10000) (htag : tag.val = 972) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 972 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00973 (tag : Fin 10000) (htag : tag.val = 973) (x : State) (e : Event) (dr : Ring12) : tag.val = 973 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00974 (tag : Fin 10000) (htag : tag.val = 974) (x : State) (e : Event) (dr : Ring12) : tag.val = 974 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00975 (tag : Fin 10000) (htag : tag.val = 975) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 975 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00976 (tag : Fin 10000) (htag : tag.val = 976) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 976 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00977 (tag : Fin 10000) (htag : tag.val = 977) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 977 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00978 (tag : Fin 10000) (htag : tag.val = 978) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 978 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00979 (tag : Fin 10000) (htag : tag.val = 979) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 979 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00980 (tag : Fin 10000) (htag : tag.val = 980) (k : Ring12) : tag.val = 980 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00981 (tag : Fin 10000) (htag : tag.val = 981) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 981 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00982 (tag : Fin 10000) (htag : tag.val = 982) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 982 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00983 (tag : Fin 10000) (htag : tag.val = 983) (x : State) (e : Event) (dr : Ring12) : tag.val = 983 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00984 (tag : Fin 10000) (htag : tag.val = 984) (x : State) (e : Event) (dr : Ring12) : tag.val = 984 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00985 (tag : Fin 10000) (htag : tag.val = 985) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 985 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00986 (tag : Fin 10000) (htag : tag.val = 986) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 986 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00987 (tag : Fin 10000) (htag : tag.val = 987) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 987 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00988 (tag : Fin 10000) (htag : tag.val = 988) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 988 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00989 (tag : Fin 10000) (htag : tag.val = 989) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 989 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00990 (tag : Fin 10000) (htag : tag.val = 990) (k : Ring12) : tag.val = 990 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00991 (tag : Fin 10000) (htag : tag.val = 991) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 991 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00992 (tag : Fin 10000) (htag : tag.val = 992) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 992 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00993 (tag : Fin 10000) (htag : tag.val = 993) (x : State) (e : Event) (dr : Ring12) : tag.val = 993 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00994 (tag : Fin 10000) (htag : tag.val = 994) (x : State) (e : Event) (dr : Ring12) : tag.val = 994 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00995 (tag : Fin 10000) (htag : tag.val = 995) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 995 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00996 (tag : Fin 10000) (htag : tag.val = 996) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 996 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00997 (tag : Fin 10000) (htag : tag.val = 997) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 997 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00998 (tag : Fin 10000) (htag : tag.val = 998) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 998 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00999 (tag : Fin 10000) (htag : tag.val = 999) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 999 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
