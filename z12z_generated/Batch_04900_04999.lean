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
theorem generated_04900 (tag : Fin 10000) (htag : tag.val = 4900) (k : Ring12) : tag.val = 4900 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04901 (tag : Fin 10000) (htag : tag.val = 4901) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4901 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04902 (tag : Fin 10000) (htag : tag.val = 4902) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4902 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04903 (tag : Fin 10000) (htag : tag.val = 4903) (x : State) (e : Event) (dr : Ring12) : tag.val = 4903 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04904 (tag : Fin 10000) (htag : tag.val = 4904) (x : State) (e : Event) (dr : Ring12) : tag.val = 4904 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04905 (tag : Fin 10000) (htag : tag.val = 4905) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4905 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04906 (tag : Fin 10000) (htag : tag.val = 4906) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4906 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04907 (tag : Fin 10000) (htag : tag.val = 4907) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4907 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04908 (tag : Fin 10000) (htag : tag.val = 4908) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4908 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04909 (tag : Fin 10000) (htag : tag.val = 4909) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4909 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04910 (tag : Fin 10000) (htag : tag.val = 4910) (k : Ring12) : tag.val = 4910 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04911 (tag : Fin 10000) (htag : tag.val = 4911) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4911 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04912 (tag : Fin 10000) (htag : tag.val = 4912) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4912 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04913 (tag : Fin 10000) (htag : tag.val = 4913) (x : State) (e : Event) (dr : Ring12) : tag.val = 4913 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04914 (tag : Fin 10000) (htag : tag.val = 4914) (x : State) (e : Event) (dr : Ring12) : tag.val = 4914 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04915 (tag : Fin 10000) (htag : tag.val = 4915) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4915 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04916 (tag : Fin 10000) (htag : tag.val = 4916) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4916 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04917 (tag : Fin 10000) (htag : tag.val = 4917) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4917 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04918 (tag : Fin 10000) (htag : tag.val = 4918) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4918 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04919 (tag : Fin 10000) (htag : tag.val = 4919) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4919 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04920 (tag : Fin 10000) (htag : tag.val = 4920) (k : Ring12) : tag.val = 4920 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04921 (tag : Fin 10000) (htag : tag.val = 4921) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4921 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04922 (tag : Fin 10000) (htag : tag.val = 4922) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4922 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04923 (tag : Fin 10000) (htag : tag.val = 4923) (x : State) (e : Event) (dr : Ring12) : tag.val = 4923 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04924 (tag : Fin 10000) (htag : tag.val = 4924) (x : State) (e : Event) (dr : Ring12) : tag.val = 4924 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04925 (tag : Fin 10000) (htag : tag.val = 4925) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4925 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04926 (tag : Fin 10000) (htag : tag.val = 4926) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4926 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04927 (tag : Fin 10000) (htag : tag.val = 4927) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4927 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04928 (tag : Fin 10000) (htag : tag.val = 4928) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4928 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04929 (tag : Fin 10000) (htag : tag.val = 4929) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4929 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04930 (tag : Fin 10000) (htag : tag.val = 4930) (k : Ring12) : tag.val = 4930 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04931 (tag : Fin 10000) (htag : tag.val = 4931) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4931 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04932 (tag : Fin 10000) (htag : tag.val = 4932) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4932 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04933 (tag : Fin 10000) (htag : tag.val = 4933) (x : State) (e : Event) (dr : Ring12) : tag.val = 4933 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04934 (tag : Fin 10000) (htag : tag.val = 4934) (x : State) (e : Event) (dr : Ring12) : tag.val = 4934 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04935 (tag : Fin 10000) (htag : tag.val = 4935) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4935 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04936 (tag : Fin 10000) (htag : tag.val = 4936) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4936 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04937 (tag : Fin 10000) (htag : tag.val = 4937) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4937 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04938 (tag : Fin 10000) (htag : tag.val = 4938) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4938 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04939 (tag : Fin 10000) (htag : tag.val = 4939) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4939 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04940 (tag : Fin 10000) (htag : tag.val = 4940) (k : Ring12) : tag.val = 4940 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04941 (tag : Fin 10000) (htag : tag.val = 4941) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4941 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04942 (tag : Fin 10000) (htag : tag.val = 4942) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4942 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04943 (tag : Fin 10000) (htag : tag.val = 4943) (x : State) (e : Event) (dr : Ring12) : tag.val = 4943 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04944 (tag : Fin 10000) (htag : tag.val = 4944) (x : State) (e : Event) (dr : Ring12) : tag.val = 4944 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04945 (tag : Fin 10000) (htag : tag.val = 4945) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4945 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04946 (tag : Fin 10000) (htag : tag.val = 4946) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4946 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04947 (tag : Fin 10000) (htag : tag.val = 4947) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4947 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04948 (tag : Fin 10000) (htag : tag.val = 4948) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4948 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04949 (tag : Fin 10000) (htag : tag.val = 4949) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4949 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04950 (tag : Fin 10000) (htag : tag.val = 4950) (k : Ring12) : tag.val = 4950 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04951 (tag : Fin 10000) (htag : tag.val = 4951) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4951 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04952 (tag : Fin 10000) (htag : tag.val = 4952) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4952 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04953 (tag : Fin 10000) (htag : tag.val = 4953) (x : State) (e : Event) (dr : Ring12) : tag.val = 4953 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04954 (tag : Fin 10000) (htag : tag.val = 4954) (x : State) (e : Event) (dr : Ring12) : tag.val = 4954 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04955 (tag : Fin 10000) (htag : tag.val = 4955) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4955 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04956 (tag : Fin 10000) (htag : tag.val = 4956) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4956 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04957 (tag : Fin 10000) (htag : tag.val = 4957) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4957 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04958 (tag : Fin 10000) (htag : tag.val = 4958) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4958 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04959 (tag : Fin 10000) (htag : tag.val = 4959) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4959 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04960 (tag : Fin 10000) (htag : tag.val = 4960) (k : Ring12) : tag.val = 4960 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04961 (tag : Fin 10000) (htag : tag.val = 4961) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4961 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04962 (tag : Fin 10000) (htag : tag.val = 4962) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4962 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04963 (tag : Fin 10000) (htag : tag.val = 4963) (x : State) (e : Event) (dr : Ring12) : tag.val = 4963 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04964 (tag : Fin 10000) (htag : tag.val = 4964) (x : State) (e : Event) (dr : Ring12) : tag.val = 4964 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04965 (tag : Fin 10000) (htag : tag.val = 4965) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4965 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04966 (tag : Fin 10000) (htag : tag.val = 4966) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4966 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04967 (tag : Fin 10000) (htag : tag.val = 4967) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4967 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04968 (tag : Fin 10000) (htag : tag.val = 4968) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4968 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04969 (tag : Fin 10000) (htag : tag.val = 4969) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4969 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04970 (tag : Fin 10000) (htag : tag.val = 4970) (k : Ring12) : tag.val = 4970 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04971 (tag : Fin 10000) (htag : tag.val = 4971) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4971 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04972 (tag : Fin 10000) (htag : tag.val = 4972) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4972 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04973 (tag : Fin 10000) (htag : tag.val = 4973) (x : State) (e : Event) (dr : Ring12) : tag.val = 4973 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04974 (tag : Fin 10000) (htag : tag.val = 4974) (x : State) (e : Event) (dr : Ring12) : tag.val = 4974 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04975 (tag : Fin 10000) (htag : tag.val = 4975) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4975 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04976 (tag : Fin 10000) (htag : tag.val = 4976) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4976 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04977 (tag : Fin 10000) (htag : tag.val = 4977) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4977 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04978 (tag : Fin 10000) (htag : tag.val = 4978) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4978 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04979 (tag : Fin 10000) (htag : tag.val = 4979) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4979 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04980 (tag : Fin 10000) (htag : tag.val = 4980) (k : Ring12) : tag.val = 4980 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04981 (tag : Fin 10000) (htag : tag.val = 4981) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4981 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04982 (tag : Fin 10000) (htag : tag.val = 4982) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4982 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04983 (tag : Fin 10000) (htag : tag.val = 4983) (x : State) (e : Event) (dr : Ring12) : tag.val = 4983 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04984 (tag : Fin 10000) (htag : tag.val = 4984) (x : State) (e : Event) (dr : Ring12) : tag.val = 4984 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04985 (tag : Fin 10000) (htag : tag.val = 4985) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4985 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04986 (tag : Fin 10000) (htag : tag.val = 4986) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4986 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04987 (tag : Fin 10000) (htag : tag.val = 4987) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4987 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04988 (tag : Fin 10000) (htag : tag.val = 4988) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4988 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04989 (tag : Fin 10000) (htag : tag.val = 4989) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4989 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04990 (tag : Fin 10000) (htag : tag.val = 4990) (k : Ring12) : tag.val = 4990 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04991 (tag : Fin 10000) (htag : tag.val = 4991) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4991 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04992 (tag : Fin 10000) (htag : tag.val = 4992) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4992 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04993 (tag : Fin 10000) (htag : tag.val = 4993) (x : State) (e : Event) (dr : Ring12) : tag.val = 4993 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04994 (tag : Fin 10000) (htag : tag.val = 4994) (x : State) (e : Event) (dr : Ring12) : tag.val = 4994 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04995 (tag : Fin 10000) (htag : tag.val = 4995) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4995 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04996 (tag : Fin 10000) (htag : tag.val = 4996) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4996 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04997 (tag : Fin 10000) (htag : tag.val = 4997) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4997 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04998 (tag : Fin 10000) (htag : tag.val = 4998) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4998 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04999 (tag : Fin 10000) (htag : tag.val = 4999) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4999 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
