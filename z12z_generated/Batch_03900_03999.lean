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
theorem generated_03900 (tag : Fin 10000) (htag : tag.val = 3900) (k : Ring12) : tag.val = 3900 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03901 (tag : Fin 10000) (htag : tag.val = 3901) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3901 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03902 (tag : Fin 10000) (htag : tag.val = 3902) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3902 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03903 (tag : Fin 10000) (htag : tag.val = 3903) (x : State) (e : Event) (dr : Ring12) : tag.val = 3903 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03904 (tag : Fin 10000) (htag : tag.val = 3904) (x : State) (e : Event) (dr : Ring12) : tag.val = 3904 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03905 (tag : Fin 10000) (htag : tag.val = 3905) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3905 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03906 (tag : Fin 10000) (htag : tag.val = 3906) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3906 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03907 (tag : Fin 10000) (htag : tag.val = 3907) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3907 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03908 (tag : Fin 10000) (htag : tag.val = 3908) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3908 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03909 (tag : Fin 10000) (htag : tag.val = 3909) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3909 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03910 (tag : Fin 10000) (htag : tag.val = 3910) (k : Ring12) : tag.val = 3910 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03911 (tag : Fin 10000) (htag : tag.val = 3911) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3911 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03912 (tag : Fin 10000) (htag : tag.val = 3912) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3912 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03913 (tag : Fin 10000) (htag : tag.val = 3913) (x : State) (e : Event) (dr : Ring12) : tag.val = 3913 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03914 (tag : Fin 10000) (htag : tag.val = 3914) (x : State) (e : Event) (dr : Ring12) : tag.val = 3914 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03915 (tag : Fin 10000) (htag : tag.val = 3915) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3915 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03916 (tag : Fin 10000) (htag : tag.val = 3916) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3916 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03917 (tag : Fin 10000) (htag : tag.val = 3917) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3917 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03918 (tag : Fin 10000) (htag : tag.val = 3918) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3918 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03919 (tag : Fin 10000) (htag : tag.val = 3919) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3919 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03920 (tag : Fin 10000) (htag : tag.val = 3920) (k : Ring12) : tag.val = 3920 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03921 (tag : Fin 10000) (htag : tag.val = 3921) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3921 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03922 (tag : Fin 10000) (htag : tag.val = 3922) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3922 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03923 (tag : Fin 10000) (htag : tag.val = 3923) (x : State) (e : Event) (dr : Ring12) : tag.val = 3923 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03924 (tag : Fin 10000) (htag : tag.val = 3924) (x : State) (e : Event) (dr : Ring12) : tag.val = 3924 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03925 (tag : Fin 10000) (htag : tag.val = 3925) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3925 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03926 (tag : Fin 10000) (htag : tag.val = 3926) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3926 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03927 (tag : Fin 10000) (htag : tag.val = 3927) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3927 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03928 (tag : Fin 10000) (htag : tag.val = 3928) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3928 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03929 (tag : Fin 10000) (htag : tag.val = 3929) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3929 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03930 (tag : Fin 10000) (htag : tag.val = 3930) (k : Ring12) : tag.val = 3930 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03931 (tag : Fin 10000) (htag : tag.val = 3931) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3931 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03932 (tag : Fin 10000) (htag : tag.val = 3932) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3932 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03933 (tag : Fin 10000) (htag : tag.val = 3933) (x : State) (e : Event) (dr : Ring12) : tag.val = 3933 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03934 (tag : Fin 10000) (htag : tag.val = 3934) (x : State) (e : Event) (dr : Ring12) : tag.val = 3934 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03935 (tag : Fin 10000) (htag : tag.val = 3935) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3935 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03936 (tag : Fin 10000) (htag : tag.val = 3936) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3936 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03937 (tag : Fin 10000) (htag : tag.val = 3937) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3937 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03938 (tag : Fin 10000) (htag : tag.val = 3938) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3938 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03939 (tag : Fin 10000) (htag : tag.val = 3939) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3939 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03940 (tag : Fin 10000) (htag : tag.val = 3940) (k : Ring12) : tag.val = 3940 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03941 (tag : Fin 10000) (htag : tag.val = 3941) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3941 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03942 (tag : Fin 10000) (htag : tag.val = 3942) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3942 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03943 (tag : Fin 10000) (htag : tag.val = 3943) (x : State) (e : Event) (dr : Ring12) : tag.val = 3943 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03944 (tag : Fin 10000) (htag : tag.val = 3944) (x : State) (e : Event) (dr : Ring12) : tag.val = 3944 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03945 (tag : Fin 10000) (htag : tag.val = 3945) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3945 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03946 (tag : Fin 10000) (htag : tag.val = 3946) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3946 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03947 (tag : Fin 10000) (htag : tag.val = 3947) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3947 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03948 (tag : Fin 10000) (htag : tag.val = 3948) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3948 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03949 (tag : Fin 10000) (htag : tag.val = 3949) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3949 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03950 (tag : Fin 10000) (htag : tag.val = 3950) (k : Ring12) : tag.val = 3950 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03951 (tag : Fin 10000) (htag : tag.val = 3951) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3951 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03952 (tag : Fin 10000) (htag : tag.val = 3952) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3952 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03953 (tag : Fin 10000) (htag : tag.val = 3953) (x : State) (e : Event) (dr : Ring12) : tag.val = 3953 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03954 (tag : Fin 10000) (htag : tag.val = 3954) (x : State) (e : Event) (dr : Ring12) : tag.val = 3954 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03955 (tag : Fin 10000) (htag : tag.val = 3955) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3955 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03956 (tag : Fin 10000) (htag : tag.val = 3956) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3956 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03957 (tag : Fin 10000) (htag : tag.val = 3957) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3957 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03958 (tag : Fin 10000) (htag : tag.val = 3958) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3958 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03959 (tag : Fin 10000) (htag : tag.val = 3959) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3959 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03960 (tag : Fin 10000) (htag : tag.val = 3960) (k : Ring12) : tag.val = 3960 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03961 (tag : Fin 10000) (htag : tag.val = 3961) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3961 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03962 (tag : Fin 10000) (htag : tag.val = 3962) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3962 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03963 (tag : Fin 10000) (htag : tag.val = 3963) (x : State) (e : Event) (dr : Ring12) : tag.val = 3963 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03964 (tag : Fin 10000) (htag : tag.val = 3964) (x : State) (e : Event) (dr : Ring12) : tag.val = 3964 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03965 (tag : Fin 10000) (htag : tag.val = 3965) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3965 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03966 (tag : Fin 10000) (htag : tag.val = 3966) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3966 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03967 (tag : Fin 10000) (htag : tag.val = 3967) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3967 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03968 (tag : Fin 10000) (htag : tag.val = 3968) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3968 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03969 (tag : Fin 10000) (htag : tag.val = 3969) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3969 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03970 (tag : Fin 10000) (htag : tag.val = 3970) (k : Ring12) : tag.val = 3970 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03971 (tag : Fin 10000) (htag : tag.val = 3971) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3971 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03972 (tag : Fin 10000) (htag : tag.val = 3972) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3972 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03973 (tag : Fin 10000) (htag : tag.val = 3973) (x : State) (e : Event) (dr : Ring12) : tag.val = 3973 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03974 (tag : Fin 10000) (htag : tag.val = 3974) (x : State) (e : Event) (dr : Ring12) : tag.val = 3974 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03975 (tag : Fin 10000) (htag : tag.val = 3975) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3975 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03976 (tag : Fin 10000) (htag : tag.val = 3976) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3976 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03977 (tag : Fin 10000) (htag : tag.val = 3977) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3977 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03978 (tag : Fin 10000) (htag : tag.val = 3978) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3978 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03979 (tag : Fin 10000) (htag : tag.val = 3979) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3979 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03980 (tag : Fin 10000) (htag : tag.val = 3980) (k : Ring12) : tag.val = 3980 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03981 (tag : Fin 10000) (htag : tag.val = 3981) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3981 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03982 (tag : Fin 10000) (htag : tag.val = 3982) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3982 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03983 (tag : Fin 10000) (htag : tag.val = 3983) (x : State) (e : Event) (dr : Ring12) : tag.val = 3983 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03984 (tag : Fin 10000) (htag : tag.val = 3984) (x : State) (e : Event) (dr : Ring12) : tag.val = 3984 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03985 (tag : Fin 10000) (htag : tag.val = 3985) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3985 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03986 (tag : Fin 10000) (htag : tag.val = 3986) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3986 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03987 (tag : Fin 10000) (htag : tag.val = 3987) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3987 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03988 (tag : Fin 10000) (htag : tag.val = 3988) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3988 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03989 (tag : Fin 10000) (htag : tag.val = 3989) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3989 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03990 (tag : Fin 10000) (htag : tag.val = 3990) (k : Ring12) : tag.val = 3990 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03991 (tag : Fin 10000) (htag : tag.val = 3991) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3991 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03992 (tag : Fin 10000) (htag : tag.val = 3992) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3992 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03993 (tag : Fin 10000) (htag : tag.val = 3993) (x : State) (e : Event) (dr : Ring12) : tag.val = 3993 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03994 (tag : Fin 10000) (htag : tag.val = 3994) (x : State) (e : Event) (dr : Ring12) : tag.val = 3994 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03995 (tag : Fin 10000) (htag : tag.val = 3995) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3995 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03996 (tag : Fin 10000) (htag : tag.val = 3996) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3996 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03997 (tag : Fin 10000) (htag : tag.val = 3997) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3997 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03998 (tag : Fin 10000) (htag : tag.val = 3998) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3998 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03999 (tag : Fin 10000) (htag : tag.val = 3999) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3999 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
