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
theorem generated_07900 (tag : Fin 10000) (htag : tag.val = 7900) (k : Ring12) : tag.val = 7900 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07901 (tag : Fin 10000) (htag : tag.val = 7901) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7901 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07902 (tag : Fin 10000) (htag : tag.val = 7902) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7902 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07903 (tag : Fin 10000) (htag : tag.val = 7903) (x : State) (e : Event) (dr : Ring12) : tag.val = 7903 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07904 (tag : Fin 10000) (htag : tag.val = 7904) (x : State) (e : Event) (dr : Ring12) : tag.val = 7904 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07905 (tag : Fin 10000) (htag : tag.val = 7905) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7905 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07906 (tag : Fin 10000) (htag : tag.val = 7906) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7906 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07907 (tag : Fin 10000) (htag : tag.val = 7907) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7907 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07908 (tag : Fin 10000) (htag : tag.val = 7908) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7908 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07909 (tag : Fin 10000) (htag : tag.val = 7909) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7909 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07910 (tag : Fin 10000) (htag : tag.val = 7910) (k : Ring12) : tag.val = 7910 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07911 (tag : Fin 10000) (htag : tag.val = 7911) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7911 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07912 (tag : Fin 10000) (htag : tag.val = 7912) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7912 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07913 (tag : Fin 10000) (htag : tag.val = 7913) (x : State) (e : Event) (dr : Ring12) : tag.val = 7913 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07914 (tag : Fin 10000) (htag : tag.val = 7914) (x : State) (e : Event) (dr : Ring12) : tag.val = 7914 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07915 (tag : Fin 10000) (htag : tag.val = 7915) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7915 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07916 (tag : Fin 10000) (htag : tag.val = 7916) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7916 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07917 (tag : Fin 10000) (htag : tag.val = 7917) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7917 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07918 (tag : Fin 10000) (htag : tag.val = 7918) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7918 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07919 (tag : Fin 10000) (htag : tag.val = 7919) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7919 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07920 (tag : Fin 10000) (htag : tag.val = 7920) (k : Ring12) : tag.val = 7920 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07921 (tag : Fin 10000) (htag : tag.val = 7921) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7921 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07922 (tag : Fin 10000) (htag : tag.val = 7922) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7922 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07923 (tag : Fin 10000) (htag : tag.val = 7923) (x : State) (e : Event) (dr : Ring12) : tag.val = 7923 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07924 (tag : Fin 10000) (htag : tag.val = 7924) (x : State) (e : Event) (dr : Ring12) : tag.val = 7924 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07925 (tag : Fin 10000) (htag : tag.val = 7925) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7925 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07926 (tag : Fin 10000) (htag : tag.val = 7926) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7926 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07927 (tag : Fin 10000) (htag : tag.val = 7927) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7927 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07928 (tag : Fin 10000) (htag : tag.val = 7928) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7928 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07929 (tag : Fin 10000) (htag : tag.val = 7929) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7929 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07930 (tag : Fin 10000) (htag : tag.val = 7930) (k : Ring12) : tag.val = 7930 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07931 (tag : Fin 10000) (htag : tag.val = 7931) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7931 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07932 (tag : Fin 10000) (htag : tag.val = 7932) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7932 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07933 (tag : Fin 10000) (htag : tag.val = 7933) (x : State) (e : Event) (dr : Ring12) : tag.val = 7933 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07934 (tag : Fin 10000) (htag : tag.val = 7934) (x : State) (e : Event) (dr : Ring12) : tag.val = 7934 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07935 (tag : Fin 10000) (htag : tag.val = 7935) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7935 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07936 (tag : Fin 10000) (htag : tag.val = 7936) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7936 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07937 (tag : Fin 10000) (htag : tag.val = 7937) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7937 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07938 (tag : Fin 10000) (htag : tag.val = 7938) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7938 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07939 (tag : Fin 10000) (htag : tag.val = 7939) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7939 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07940 (tag : Fin 10000) (htag : tag.val = 7940) (k : Ring12) : tag.val = 7940 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07941 (tag : Fin 10000) (htag : tag.val = 7941) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7941 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07942 (tag : Fin 10000) (htag : tag.val = 7942) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7942 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07943 (tag : Fin 10000) (htag : tag.val = 7943) (x : State) (e : Event) (dr : Ring12) : tag.val = 7943 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07944 (tag : Fin 10000) (htag : tag.val = 7944) (x : State) (e : Event) (dr : Ring12) : tag.val = 7944 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07945 (tag : Fin 10000) (htag : tag.val = 7945) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7945 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07946 (tag : Fin 10000) (htag : tag.val = 7946) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7946 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07947 (tag : Fin 10000) (htag : tag.val = 7947) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7947 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07948 (tag : Fin 10000) (htag : tag.val = 7948) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7948 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07949 (tag : Fin 10000) (htag : tag.val = 7949) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7949 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07950 (tag : Fin 10000) (htag : tag.val = 7950) (k : Ring12) : tag.val = 7950 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07951 (tag : Fin 10000) (htag : tag.val = 7951) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7951 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07952 (tag : Fin 10000) (htag : tag.val = 7952) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7952 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07953 (tag : Fin 10000) (htag : tag.val = 7953) (x : State) (e : Event) (dr : Ring12) : tag.val = 7953 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07954 (tag : Fin 10000) (htag : tag.val = 7954) (x : State) (e : Event) (dr : Ring12) : tag.val = 7954 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07955 (tag : Fin 10000) (htag : tag.val = 7955) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7955 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07956 (tag : Fin 10000) (htag : tag.val = 7956) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7956 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07957 (tag : Fin 10000) (htag : tag.val = 7957) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7957 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07958 (tag : Fin 10000) (htag : tag.val = 7958) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7958 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07959 (tag : Fin 10000) (htag : tag.val = 7959) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7959 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07960 (tag : Fin 10000) (htag : tag.val = 7960) (k : Ring12) : tag.val = 7960 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07961 (tag : Fin 10000) (htag : tag.val = 7961) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7961 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07962 (tag : Fin 10000) (htag : tag.val = 7962) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7962 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07963 (tag : Fin 10000) (htag : tag.val = 7963) (x : State) (e : Event) (dr : Ring12) : tag.val = 7963 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07964 (tag : Fin 10000) (htag : tag.val = 7964) (x : State) (e : Event) (dr : Ring12) : tag.val = 7964 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07965 (tag : Fin 10000) (htag : tag.val = 7965) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7965 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07966 (tag : Fin 10000) (htag : tag.val = 7966) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7966 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07967 (tag : Fin 10000) (htag : tag.val = 7967) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7967 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07968 (tag : Fin 10000) (htag : tag.val = 7968) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7968 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07969 (tag : Fin 10000) (htag : tag.val = 7969) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7969 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07970 (tag : Fin 10000) (htag : tag.val = 7970) (k : Ring12) : tag.val = 7970 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07971 (tag : Fin 10000) (htag : tag.val = 7971) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7971 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07972 (tag : Fin 10000) (htag : tag.val = 7972) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7972 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07973 (tag : Fin 10000) (htag : tag.val = 7973) (x : State) (e : Event) (dr : Ring12) : tag.val = 7973 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07974 (tag : Fin 10000) (htag : tag.val = 7974) (x : State) (e : Event) (dr : Ring12) : tag.val = 7974 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07975 (tag : Fin 10000) (htag : tag.val = 7975) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7975 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07976 (tag : Fin 10000) (htag : tag.val = 7976) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7976 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07977 (tag : Fin 10000) (htag : tag.val = 7977) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7977 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07978 (tag : Fin 10000) (htag : tag.val = 7978) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7978 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07979 (tag : Fin 10000) (htag : tag.val = 7979) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7979 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07980 (tag : Fin 10000) (htag : tag.val = 7980) (k : Ring12) : tag.val = 7980 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07981 (tag : Fin 10000) (htag : tag.val = 7981) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7981 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07982 (tag : Fin 10000) (htag : tag.val = 7982) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7982 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07983 (tag : Fin 10000) (htag : tag.val = 7983) (x : State) (e : Event) (dr : Ring12) : tag.val = 7983 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07984 (tag : Fin 10000) (htag : tag.val = 7984) (x : State) (e : Event) (dr : Ring12) : tag.val = 7984 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07985 (tag : Fin 10000) (htag : tag.val = 7985) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7985 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07986 (tag : Fin 10000) (htag : tag.val = 7986) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7986 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07987 (tag : Fin 10000) (htag : tag.val = 7987) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7987 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07988 (tag : Fin 10000) (htag : tag.val = 7988) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7988 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07989 (tag : Fin 10000) (htag : tag.val = 7989) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7989 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07990 (tag : Fin 10000) (htag : tag.val = 7990) (k : Ring12) : tag.val = 7990 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07991 (tag : Fin 10000) (htag : tag.val = 7991) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7991 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07992 (tag : Fin 10000) (htag : tag.val = 7992) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7992 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07993 (tag : Fin 10000) (htag : tag.val = 7993) (x : State) (e : Event) (dr : Ring12) : tag.val = 7993 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07994 (tag : Fin 10000) (htag : tag.val = 7994) (x : State) (e : Event) (dr : Ring12) : tag.val = 7994 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07995 (tag : Fin 10000) (htag : tag.val = 7995) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7995 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07996 (tag : Fin 10000) (htag : tag.val = 7996) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7996 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07997 (tag : Fin 10000) (htag : tag.val = 7997) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7997 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07998 (tag : Fin 10000) (htag : tag.val = 7998) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7998 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07999 (tag : Fin 10000) (htag : tag.val = 7999) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7999 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
