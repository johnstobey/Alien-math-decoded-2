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
theorem generated_09900 (tag : Fin 10000) (htag : tag.val = 9900) (k : Ring12) : tag.val = 9900 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09901 (tag : Fin 10000) (htag : tag.val = 9901) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9901 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09902 (tag : Fin 10000) (htag : tag.val = 9902) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9902 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09903 (tag : Fin 10000) (htag : tag.val = 9903) (x : State) (e : Event) (dr : Ring12) : tag.val = 9903 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09904 (tag : Fin 10000) (htag : tag.val = 9904) (x : State) (e : Event) (dr : Ring12) : tag.val = 9904 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09905 (tag : Fin 10000) (htag : tag.val = 9905) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9905 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09906 (tag : Fin 10000) (htag : tag.val = 9906) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9906 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09907 (tag : Fin 10000) (htag : tag.val = 9907) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9907 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09908 (tag : Fin 10000) (htag : tag.val = 9908) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9908 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09909 (tag : Fin 10000) (htag : tag.val = 9909) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9909 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09910 (tag : Fin 10000) (htag : tag.val = 9910) (k : Ring12) : tag.val = 9910 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09911 (tag : Fin 10000) (htag : tag.val = 9911) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9911 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09912 (tag : Fin 10000) (htag : tag.val = 9912) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9912 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09913 (tag : Fin 10000) (htag : tag.val = 9913) (x : State) (e : Event) (dr : Ring12) : tag.val = 9913 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09914 (tag : Fin 10000) (htag : tag.val = 9914) (x : State) (e : Event) (dr : Ring12) : tag.val = 9914 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09915 (tag : Fin 10000) (htag : tag.val = 9915) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9915 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09916 (tag : Fin 10000) (htag : tag.val = 9916) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9916 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09917 (tag : Fin 10000) (htag : tag.val = 9917) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9917 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09918 (tag : Fin 10000) (htag : tag.val = 9918) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9918 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09919 (tag : Fin 10000) (htag : tag.val = 9919) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9919 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09920 (tag : Fin 10000) (htag : tag.val = 9920) (k : Ring12) : tag.val = 9920 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09921 (tag : Fin 10000) (htag : tag.val = 9921) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9921 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09922 (tag : Fin 10000) (htag : tag.val = 9922) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9922 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09923 (tag : Fin 10000) (htag : tag.val = 9923) (x : State) (e : Event) (dr : Ring12) : tag.val = 9923 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09924 (tag : Fin 10000) (htag : tag.val = 9924) (x : State) (e : Event) (dr : Ring12) : tag.val = 9924 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09925 (tag : Fin 10000) (htag : tag.val = 9925) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9925 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09926 (tag : Fin 10000) (htag : tag.val = 9926) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9926 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09927 (tag : Fin 10000) (htag : tag.val = 9927) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9927 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09928 (tag : Fin 10000) (htag : tag.val = 9928) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9928 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09929 (tag : Fin 10000) (htag : tag.val = 9929) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9929 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09930 (tag : Fin 10000) (htag : tag.val = 9930) (k : Ring12) : tag.val = 9930 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09931 (tag : Fin 10000) (htag : tag.val = 9931) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9931 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09932 (tag : Fin 10000) (htag : tag.val = 9932) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9932 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09933 (tag : Fin 10000) (htag : tag.val = 9933) (x : State) (e : Event) (dr : Ring12) : tag.val = 9933 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09934 (tag : Fin 10000) (htag : tag.val = 9934) (x : State) (e : Event) (dr : Ring12) : tag.val = 9934 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09935 (tag : Fin 10000) (htag : tag.val = 9935) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9935 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09936 (tag : Fin 10000) (htag : tag.val = 9936) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9936 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09937 (tag : Fin 10000) (htag : tag.val = 9937) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9937 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09938 (tag : Fin 10000) (htag : tag.val = 9938) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9938 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09939 (tag : Fin 10000) (htag : tag.val = 9939) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9939 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09940 (tag : Fin 10000) (htag : tag.val = 9940) (k : Ring12) : tag.val = 9940 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09941 (tag : Fin 10000) (htag : tag.val = 9941) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9941 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09942 (tag : Fin 10000) (htag : tag.val = 9942) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9942 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09943 (tag : Fin 10000) (htag : tag.val = 9943) (x : State) (e : Event) (dr : Ring12) : tag.val = 9943 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09944 (tag : Fin 10000) (htag : tag.val = 9944) (x : State) (e : Event) (dr : Ring12) : tag.val = 9944 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09945 (tag : Fin 10000) (htag : tag.val = 9945) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9945 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09946 (tag : Fin 10000) (htag : tag.val = 9946) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9946 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09947 (tag : Fin 10000) (htag : tag.val = 9947) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9947 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09948 (tag : Fin 10000) (htag : tag.val = 9948) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9948 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09949 (tag : Fin 10000) (htag : tag.val = 9949) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9949 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09950 (tag : Fin 10000) (htag : tag.val = 9950) (k : Ring12) : tag.val = 9950 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09951 (tag : Fin 10000) (htag : tag.val = 9951) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9951 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09952 (tag : Fin 10000) (htag : tag.val = 9952) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9952 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09953 (tag : Fin 10000) (htag : tag.val = 9953) (x : State) (e : Event) (dr : Ring12) : tag.val = 9953 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09954 (tag : Fin 10000) (htag : tag.val = 9954) (x : State) (e : Event) (dr : Ring12) : tag.val = 9954 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09955 (tag : Fin 10000) (htag : tag.val = 9955) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9955 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09956 (tag : Fin 10000) (htag : tag.val = 9956) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9956 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09957 (tag : Fin 10000) (htag : tag.val = 9957) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9957 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09958 (tag : Fin 10000) (htag : tag.val = 9958) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9958 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09959 (tag : Fin 10000) (htag : tag.val = 9959) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9959 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09960 (tag : Fin 10000) (htag : tag.val = 9960) (k : Ring12) : tag.val = 9960 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09961 (tag : Fin 10000) (htag : tag.val = 9961) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9961 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09962 (tag : Fin 10000) (htag : tag.val = 9962) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9962 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09963 (tag : Fin 10000) (htag : tag.val = 9963) (x : State) (e : Event) (dr : Ring12) : tag.val = 9963 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09964 (tag : Fin 10000) (htag : tag.val = 9964) (x : State) (e : Event) (dr : Ring12) : tag.val = 9964 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09965 (tag : Fin 10000) (htag : tag.val = 9965) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9965 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09966 (tag : Fin 10000) (htag : tag.val = 9966) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9966 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09967 (tag : Fin 10000) (htag : tag.val = 9967) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9967 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09968 (tag : Fin 10000) (htag : tag.val = 9968) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9968 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09969 (tag : Fin 10000) (htag : tag.val = 9969) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9969 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09970 (tag : Fin 10000) (htag : tag.val = 9970) (k : Ring12) : tag.val = 9970 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09971 (tag : Fin 10000) (htag : tag.val = 9971) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9971 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09972 (tag : Fin 10000) (htag : tag.val = 9972) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9972 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09973 (tag : Fin 10000) (htag : tag.val = 9973) (x : State) (e : Event) (dr : Ring12) : tag.val = 9973 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09974 (tag : Fin 10000) (htag : tag.val = 9974) (x : State) (e : Event) (dr : Ring12) : tag.val = 9974 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09975 (tag : Fin 10000) (htag : tag.val = 9975) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9975 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09976 (tag : Fin 10000) (htag : tag.val = 9976) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9976 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09977 (tag : Fin 10000) (htag : tag.val = 9977) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9977 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09978 (tag : Fin 10000) (htag : tag.val = 9978) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9978 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09979 (tag : Fin 10000) (htag : tag.val = 9979) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9979 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09980 (tag : Fin 10000) (htag : tag.val = 9980) (k : Ring12) : tag.val = 9980 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09981 (tag : Fin 10000) (htag : tag.val = 9981) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9981 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09982 (tag : Fin 10000) (htag : tag.val = 9982) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9982 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09983 (tag : Fin 10000) (htag : tag.val = 9983) (x : State) (e : Event) (dr : Ring12) : tag.val = 9983 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09984 (tag : Fin 10000) (htag : tag.val = 9984) (x : State) (e : Event) (dr : Ring12) : tag.val = 9984 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09985 (tag : Fin 10000) (htag : tag.val = 9985) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9985 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09986 (tag : Fin 10000) (htag : tag.val = 9986) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9986 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09987 (tag : Fin 10000) (htag : tag.val = 9987) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9987 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09988 (tag : Fin 10000) (htag : tag.val = 9988) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9988 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09989 (tag : Fin 10000) (htag : tag.val = 9989) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9989 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09990 (tag : Fin 10000) (htag : tag.val = 9990) (k : Ring12) : tag.val = 9990 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09991 (tag : Fin 10000) (htag : tag.val = 9991) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9991 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09992 (tag : Fin 10000) (htag : tag.val = 9992) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9992 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09993 (tag : Fin 10000) (htag : tag.val = 9993) (x : State) (e : Event) (dr : Ring12) : tag.val = 9993 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09994 (tag : Fin 10000) (htag : tag.val = 9994) (x : State) (e : Event) (dr : Ring12) : tag.val = 9994 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09995 (tag : Fin 10000) (htag : tag.val = 9995) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9995 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09996 (tag : Fin 10000) (htag : tag.val = 9996) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9996 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09997 (tag : Fin 10000) (htag : tag.val = 9997) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9997 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09998 (tag : Fin 10000) (htag : tag.val = 9998) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9998 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09999 (tag : Fin 10000) (htag : tag.val = 9999) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9999 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
