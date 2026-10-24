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
theorem generated_05900 (tag : Fin 10000) (htag : tag.val = 5900) (k : Ring12) : tag.val = 5900 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05901 (tag : Fin 10000) (htag : tag.val = 5901) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5901 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05902 (tag : Fin 10000) (htag : tag.val = 5902) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5902 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05903 (tag : Fin 10000) (htag : tag.val = 5903) (x : State) (e : Event) (dr : Ring12) : tag.val = 5903 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05904 (tag : Fin 10000) (htag : tag.val = 5904) (x : State) (e : Event) (dr : Ring12) : tag.val = 5904 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05905 (tag : Fin 10000) (htag : tag.val = 5905) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5905 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05906 (tag : Fin 10000) (htag : tag.val = 5906) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5906 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05907 (tag : Fin 10000) (htag : tag.val = 5907) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5907 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05908 (tag : Fin 10000) (htag : tag.val = 5908) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5908 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05909 (tag : Fin 10000) (htag : tag.val = 5909) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5909 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05910 (tag : Fin 10000) (htag : tag.val = 5910) (k : Ring12) : tag.val = 5910 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05911 (tag : Fin 10000) (htag : tag.val = 5911) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5911 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05912 (tag : Fin 10000) (htag : tag.val = 5912) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5912 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05913 (tag : Fin 10000) (htag : tag.val = 5913) (x : State) (e : Event) (dr : Ring12) : tag.val = 5913 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05914 (tag : Fin 10000) (htag : tag.val = 5914) (x : State) (e : Event) (dr : Ring12) : tag.val = 5914 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05915 (tag : Fin 10000) (htag : tag.val = 5915) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5915 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05916 (tag : Fin 10000) (htag : tag.val = 5916) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5916 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05917 (tag : Fin 10000) (htag : tag.val = 5917) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5917 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05918 (tag : Fin 10000) (htag : tag.val = 5918) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5918 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05919 (tag : Fin 10000) (htag : tag.val = 5919) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5919 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05920 (tag : Fin 10000) (htag : tag.val = 5920) (k : Ring12) : tag.val = 5920 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05921 (tag : Fin 10000) (htag : tag.val = 5921) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5921 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05922 (tag : Fin 10000) (htag : tag.val = 5922) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5922 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05923 (tag : Fin 10000) (htag : tag.val = 5923) (x : State) (e : Event) (dr : Ring12) : tag.val = 5923 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05924 (tag : Fin 10000) (htag : tag.val = 5924) (x : State) (e : Event) (dr : Ring12) : tag.val = 5924 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05925 (tag : Fin 10000) (htag : tag.val = 5925) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5925 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05926 (tag : Fin 10000) (htag : tag.val = 5926) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5926 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05927 (tag : Fin 10000) (htag : tag.val = 5927) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5927 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05928 (tag : Fin 10000) (htag : tag.val = 5928) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5928 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05929 (tag : Fin 10000) (htag : tag.val = 5929) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5929 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05930 (tag : Fin 10000) (htag : tag.val = 5930) (k : Ring12) : tag.val = 5930 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05931 (tag : Fin 10000) (htag : tag.val = 5931) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5931 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05932 (tag : Fin 10000) (htag : tag.val = 5932) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5932 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05933 (tag : Fin 10000) (htag : tag.val = 5933) (x : State) (e : Event) (dr : Ring12) : tag.val = 5933 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05934 (tag : Fin 10000) (htag : tag.val = 5934) (x : State) (e : Event) (dr : Ring12) : tag.val = 5934 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05935 (tag : Fin 10000) (htag : tag.val = 5935) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5935 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05936 (tag : Fin 10000) (htag : tag.val = 5936) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5936 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05937 (tag : Fin 10000) (htag : tag.val = 5937) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5937 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05938 (tag : Fin 10000) (htag : tag.val = 5938) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5938 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05939 (tag : Fin 10000) (htag : tag.val = 5939) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5939 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05940 (tag : Fin 10000) (htag : tag.val = 5940) (k : Ring12) : tag.val = 5940 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05941 (tag : Fin 10000) (htag : tag.val = 5941) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5941 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05942 (tag : Fin 10000) (htag : tag.val = 5942) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5942 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05943 (tag : Fin 10000) (htag : tag.val = 5943) (x : State) (e : Event) (dr : Ring12) : tag.val = 5943 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05944 (tag : Fin 10000) (htag : tag.val = 5944) (x : State) (e : Event) (dr : Ring12) : tag.val = 5944 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05945 (tag : Fin 10000) (htag : tag.val = 5945) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5945 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05946 (tag : Fin 10000) (htag : tag.val = 5946) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5946 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05947 (tag : Fin 10000) (htag : tag.val = 5947) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5947 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05948 (tag : Fin 10000) (htag : tag.val = 5948) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5948 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05949 (tag : Fin 10000) (htag : tag.val = 5949) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5949 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05950 (tag : Fin 10000) (htag : tag.val = 5950) (k : Ring12) : tag.val = 5950 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05951 (tag : Fin 10000) (htag : tag.val = 5951) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5951 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05952 (tag : Fin 10000) (htag : tag.val = 5952) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5952 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05953 (tag : Fin 10000) (htag : tag.val = 5953) (x : State) (e : Event) (dr : Ring12) : tag.val = 5953 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05954 (tag : Fin 10000) (htag : tag.val = 5954) (x : State) (e : Event) (dr : Ring12) : tag.val = 5954 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05955 (tag : Fin 10000) (htag : tag.val = 5955) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5955 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05956 (tag : Fin 10000) (htag : tag.val = 5956) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5956 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05957 (tag : Fin 10000) (htag : tag.val = 5957) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5957 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05958 (tag : Fin 10000) (htag : tag.val = 5958) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5958 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05959 (tag : Fin 10000) (htag : tag.val = 5959) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5959 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05960 (tag : Fin 10000) (htag : tag.val = 5960) (k : Ring12) : tag.val = 5960 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05961 (tag : Fin 10000) (htag : tag.val = 5961) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5961 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05962 (tag : Fin 10000) (htag : tag.val = 5962) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5962 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05963 (tag : Fin 10000) (htag : tag.val = 5963) (x : State) (e : Event) (dr : Ring12) : tag.val = 5963 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05964 (tag : Fin 10000) (htag : tag.val = 5964) (x : State) (e : Event) (dr : Ring12) : tag.val = 5964 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05965 (tag : Fin 10000) (htag : tag.val = 5965) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5965 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05966 (tag : Fin 10000) (htag : tag.val = 5966) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5966 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05967 (tag : Fin 10000) (htag : tag.val = 5967) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5967 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05968 (tag : Fin 10000) (htag : tag.val = 5968) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5968 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05969 (tag : Fin 10000) (htag : tag.val = 5969) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5969 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05970 (tag : Fin 10000) (htag : tag.val = 5970) (k : Ring12) : tag.val = 5970 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05971 (tag : Fin 10000) (htag : tag.val = 5971) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5971 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05972 (tag : Fin 10000) (htag : tag.val = 5972) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5972 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05973 (tag : Fin 10000) (htag : tag.val = 5973) (x : State) (e : Event) (dr : Ring12) : tag.val = 5973 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05974 (tag : Fin 10000) (htag : tag.val = 5974) (x : State) (e : Event) (dr : Ring12) : tag.val = 5974 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05975 (tag : Fin 10000) (htag : tag.val = 5975) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5975 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05976 (tag : Fin 10000) (htag : tag.val = 5976) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5976 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05977 (tag : Fin 10000) (htag : tag.val = 5977) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5977 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05978 (tag : Fin 10000) (htag : tag.val = 5978) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5978 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05979 (tag : Fin 10000) (htag : tag.val = 5979) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5979 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05980 (tag : Fin 10000) (htag : tag.val = 5980) (k : Ring12) : tag.val = 5980 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05981 (tag : Fin 10000) (htag : tag.val = 5981) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5981 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05982 (tag : Fin 10000) (htag : tag.val = 5982) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5982 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05983 (tag : Fin 10000) (htag : tag.val = 5983) (x : State) (e : Event) (dr : Ring12) : tag.val = 5983 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05984 (tag : Fin 10000) (htag : tag.val = 5984) (x : State) (e : Event) (dr : Ring12) : tag.val = 5984 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05985 (tag : Fin 10000) (htag : tag.val = 5985) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5985 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05986 (tag : Fin 10000) (htag : tag.val = 5986) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5986 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05987 (tag : Fin 10000) (htag : tag.val = 5987) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5987 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05988 (tag : Fin 10000) (htag : tag.val = 5988) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5988 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05989 (tag : Fin 10000) (htag : tag.val = 5989) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5989 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05990 (tag : Fin 10000) (htag : tag.val = 5990) (k : Ring12) : tag.val = 5990 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05991 (tag : Fin 10000) (htag : tag.val = 5991) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5991 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05992 (tag : Fin 10000) (htag : tag.val = 5992) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5992 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05993 (tag : Fin 10000) (htag : tag.val = 5993) (x : State) (e : Event) (dr : Ring12) : tag.val = 5993 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05994 (tag : Fin 10000) (htag : tag.val = 5994) (x : State) (e : Event) (dr : Ring12) : tag.val = 5994 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05995 (tag : Fin 10000) (htag : tag.val = 5995) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5995 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05996 (tag : Fin 10000) (htag : tag.val = 5996) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5996 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05997 (tag : Fin 10000) (htag : tag.val = 5997) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5997 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05998 (tag : Fin 10000) (htag : tag.val = 5998) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5998 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05999 (tag : Fin 10000) (htag : tag.val = 5999) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5999 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
