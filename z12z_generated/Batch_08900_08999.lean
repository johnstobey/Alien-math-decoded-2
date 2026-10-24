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
theorem generated_08900 (tag : Fin 10000) (htag : tag.val = 8900) (k : Ring12) : tag.val = 8900 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08901 (tag : Fin 10000) (htag : tag.val = 8901) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8901 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08902 (tag : Fin 10000) (htag : tag.val = 8902) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8902 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08903 (tag : Fin 10000) (htag : tag.val = 8903) (x : State) (e : Event) (dr : Ring12) : tag.val = 8903 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08904 (tag : Fin 10000) (htag : tag.val = 8904) (x : State) (e : Event) (dr : Ring12) : tag.val = 8904 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08905 (tag : Fin 10000) (htag : tag.val = 8905) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8905 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08906 (tag : Fin 10000) (htag : tag.val = 8906) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8906 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08907 (tag : Fin 10000) (htag : tag.val = 8907) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8907 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08908 (tag : Fin 10000) (htag : tag.val = 8908) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8908 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08909 (tag : Fin 10000) (htag : tag.val = 8909) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8909 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08910 (tag : Fin 10000) (htag : tag.val = 8910) (k : Ring12) : tag.val = 8910 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08911 (tag : Fin 10000) (htag : tag.val = 8911) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8911 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08912 (tag : Fin 10000) (htag : tag.val = 8912) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8912 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08913 (tag : Fin 10000) (htag : tag.val = 8913) (x : State) (e : Event) (dr : Ring12) : tag.val = 8913 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08914 (tag : Fin 10000) (htag : tag.val = 8914) (x : State) (e : Event) (dr : Ring12) : tag.val = 8914 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08915 (tag : Fin 10000) (htag : tag.val = 8915) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8915 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08916 (tag : Fin 10000) (htag : tag.val = 8916) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8916 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08917 (tag : Fin 10000) (htag : tag.val = 8917) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8917 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08918 (tag : Fin 10000) (htag : tag.val = 8918) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8918 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08919 (tag : Fin 10000) (htag : tag.val = 8919) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8919 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08920 (tag : Fin 10000) (htag : tag.val = 8920) (k : Ring12) : tag.val = 8920 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08921 (tag : Fin 10000) (htag : tag.val = 8921) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8921 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08922 (tag : Fin 10000) (htag : tag.val = 8922) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8922 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08923 (tag : Fin 10000) (htag : tag.val = 8923) (x : State) (e : Event) (dr : Ring12) : tag.val = 8923 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08924 (tag : Fin 10000) (htag : tag.val = 8924) (x : State) (e : Event) (dr : Ring12) : tag.val = 8924 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08925 (tag : Fin 10000) (htag : tag.val = 8925) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8925 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08926 (tag : Fin 10000) (htag : tag.val = 8926) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8926 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08927 (tag : Fin 10000) (htag : tag.val = 8927) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8927 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08928 (tag : Fin 10000) (htag : tag.val = 8928) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8928 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08929 (tag : Fin 10000) (htag : tag.val = 8929) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8929 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08930 (tag : Fin 10000) (htag : tag.val = 8930) (k : Ring12) : tag.val = 8930 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08931 (tag : Fin 10000) (htag : tag.val = 8931) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8931 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08932 (tag : Fin 10000) (htag : tag.val = 8932) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8932 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08933 (tag : Fin 10000) (htag : tag.val = 8933) (x : State) (e : Event) (dr : Ring12) : tag.val = 8933 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08934 (tag : Fin 10000) (htag : tag.val = 8934) (x : State) (e : Event) (dr : Ring12) : tag.val = 8934 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08935 (tag : Fin 10000) (htag : tag.val = 8935) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8935 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08936 (tag : Fin 10000) (htag : tag.val = 8936) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8936 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08937 (tag : Fin 10000) (htag : tag.val = 8937) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8937 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08938 (tag : Fin 10000) (htag : tag.val = 8938) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8938 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08939 (tag : Fin 10000) (htag : tag.val = 8939) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8939 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08940 (tag : Fin 10000) (htag : tag.val = 8940) (k : Ring12) : tag.val = 8940 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08941 (tag : Fin 10000) (htag : tag.val = 8941) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8941 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08942 (tag : Fin 10000) (htag : tag.val = 8942) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8942 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08943 (tag : Fin 10000) (htag : tag.val = 8943) (x : State) (e : Event) (dr : Ring12) : tag.val = 8943 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08944 (tag : Fin 10000) (htag : tag.val = 8944) (x : State) (e : Event) (dr : Ring12) : tag.val = 8944 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08945 (tag : Fin 10000) (htag : tag.val = 8945) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8945 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08946 (tag : Fin 10000) (htag : tag.val = 8946) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8946 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08947 (tag : Fin 10000) (htag : tag.val = 8947) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8947 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08948 (tag : Fin 10000) (htag : tag.val = 8948) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8948 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08949 (tag : Fin 10000) (htag : tag.val = 8949) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8949 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08950 (tag : Fin 10000) (htag : tag.val = 8950) (k : Ring12) : tag.val = 8950 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08951 (tag : Fin 10000) (htag : tag.val = 8951) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8951 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08952 (tag : Fin 10000) (htag : tag.val = 8952) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8952 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08953 (tag : Fin 10000) (htag : tag.val = 8953) (x : State) (e : Event) (dr : Ring12) : tag.val = 8953 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08954 (tag : Fin 10000) (htag : tag.val = 8954) (x : State) (e : Event) (dr : Ring12) : tag.val = 8954 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08955 (tag : Fin 10000) (htag : tag.val = 8955) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8955 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08956 (tag : Fin 10000) (htag : tag.val = 8956) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8956 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08957 (tag : Fin 10000) (htag : tag.val = 8957) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8957 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08958 (tag : Fin 10000) (htag : tag.val = 8958) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8958 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08959 (tag : Fin 10000) (htag : tag.val = 8959) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8959 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08960 (tag : Fin 10000) (htag : tag.val = 8960) (k : Ring12) : tag.val = 8960 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08961 (tag : Fin 10000) (htag : tag.val = 8961) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8961 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08962 (tag : Fin 10000) (htag : tag.val = 8962) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8962 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08963 (tag : Fin 10000) (htag : tag.val = 8963) (x : State) (e : Event) (dr : Ring12) : tag.val = 8963 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08964 (tag : Fin 10000) (htag : tag.val = 8964) (x : State) (e : Event) (dr : Ring12) : tag.val = 8964 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08965 (tag : Fin 10000) (htag : tag.val = 8965) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8965 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08966 (tag : Fin 10000) (htag : tag.val = 8966) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8966 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08967 (tag : Fin 10000) (htag : tag.val = 8967) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8967 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08968 (tag : Fin 10000) (htag : tag.val = 8968) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8968 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08969 (tag : Fin 10000) (htag : tag.val = 8969) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8969 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08970 (tag : Fin 10000) (htag : tag.val = 8970) (k : Ring12) : tag.val = 8970 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08971 (tag : Fin 10000) (htag : tag.val = 8971) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8971 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08972 (tag : Fin 10000) (htag : tag.val = 8972) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8972 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08973 (tag : Fin 10000) (htag : tag.val = 8973) (x : State) (e : Event) (dr : Ring12) : tag.val = 8973 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08974 (tag : Fin 10000) (htag : tag.val = 8974) (x : State) (e : Event) (dr : Ring12) : tag.val = 8974 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08975 (tag : Fin 10000) (htag : tag.val = 8975) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8975 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08976 (tag : Fin 10000) (htag : tag.val = 8976) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8976 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08977 (tag : Fin 10000) (htag : tag.val = 8977) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8977 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08978 (tag : Fin 10000) (htag : tag.val = 8978) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8978 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08979 (tag : Fin 10000) (htag : tag.val = 8979) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8979 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08980 (tag : Fin 10000) (htag : tag.val = 8980) (k : Ring12) : tag.val = 8980 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08981 (tag : Fin 10000) (htag : tag.val = 8981) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8981 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08982 (tag : Fin 10000) (htag : tag.val = 8982) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8982 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08983 (tag : Fin 10000) (htag : tag.val = 8983) (x : State) (e : Event) (dr : Ring12) : tag.val = 8983 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08984 (tag : Fin 10000) (htag : tag.val = 8984) (x : State) (e : Event) (dr : Ring12) : tag.val = 8984 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08985 (tag : Fin 10000) (htag : tag.val = 8985) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8985 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08986 (tag : Fin 10000) (htag : tag.val = 8986) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8986 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08987 (tag : Fin 10000) (htag : tag.val = 8987) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8987 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08988 (tag : Fin 10000) (htag : tag.val = 8988) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8988 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08989 (tag : Fin 10000) (htag : tag.val = 8989) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8989 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08990 (tag : Fin 10000) (htag : tag.val = 8990) (k : Ring12) : tag.val = 8990 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08991 (tag : Fin 10000) (htag : tag.val = 8991) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8991 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08992 (tag : Fin 10000) (htag : tag.val = 8992) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8992 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08993 (tag : Fin 10000) (htag : tag.val = 8993) (x : State) (e : Event) (dr : Ring12) : tag.val = 8993 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08994 (tag : Fin 10000) (htag : tag.val = 8994) (x : State) (e : Event) (dr : Ring12) : tag.val = 8994 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08995 (tag : Fin 10000) (htag : tag.val = 8995) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8995 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08996 (tag : Fin 10000) (htag : tag.val = 8996) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8996 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08997 (tag : Fin 10000) (htag : tag.val = 8997) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8997 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08998 (tag : Fin 10000) (htag : tag.val = 8998) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8998 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08999 (tag : Fin 10000) (htag : tag.val = 8999) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8999 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
