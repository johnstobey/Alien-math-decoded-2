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
theorem generated_02900 (tag : Fin 10000) (htag : tag.val = 2900) (k : Ring12) : tag.val = 2900 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02901 (tag : Fin 10000) (htag : tag.val = 2901) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2901 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02902 (tag : Fin 10000) (htag : tag.val = 2902) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2902 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02903 (tag : Fin 10000) (htag : tag.val = 2903) (x : State) (e : Event) (dr : Ring12) : tag.val = 2903 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02904 (tag : Fin 10000) (htag : tag.val = 2904) (x : State) (e : Event) (dr : Ring12) : tag.val = 2904 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02905 (tag : Fin 10000) (htag : tag.val = 2905) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2905 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02906 (tag : Fin 10000) (htag : tag.val = 2906) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2906 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02907 (tag : Fin 10000) (htag : tag.val = 2907) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2907 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02908 (tag : Fin 10000) (htag : tag.val = 2908) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2908 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02909 (tag : Fin 10000) (htag : tag.val = 2909) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2909 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02910 (tag : Fin 10000) (htag : tag.val = 2910) (k : Ring12) : tag.val = 2910 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02911 (tag : Fin 10000) (htag : tag.val = 2911) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2911 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02912 (tag : Fin 10000) (htag : tag.val = 2912) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2912 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02913 (tag : Fin 10000) (htag : tag.val = 2913) (x : State) (e : Event) (dr : Ring12) : tag.val = 2913 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02914 (tag : Fin 10000) (htag : tag.val = 2914) (x : State) (e : Event) (dr : Ring12) : tag.val = 2914 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02915 (tag : Fin 10000) (htag : tag.val = 2915) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2915 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02916 (tag : Fin 10000) (htag : tag.val = 2916) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2916 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02917 (tag : Fin 10000) (htag : tag.val = 2917) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2917 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02918 (tag : Fin 10000) (htag : tag.val = 2918) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2918 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02919 (tag : Fin 10000) (htag : tag.val = 2919) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2919 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02920 (tag : Fin 10000) (htag : tag.val = 2920) (k : Ring12) : tag.val = 2920 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02921 (tag : Fin 10000) (htag : tag.val = 2921) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2921 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02922 (tag : Fin 10000) (htag : tag.val = 2922) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2922 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02923 (tag : Fin 10000) (htag : tag.val = 2923) (x : State) (e : Event) (dr : Ring12) : tag.val = 2923 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02924 (tag : Fin 10000) (htag : tag.val = 2924) (x : State) (e : Event) (dr : Ring12) : tag.val = 2924 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02925 (tag : Fin 10000) (htag : tag.val = 2925) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2925 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02926 (tag : Fin 10000) (htag : tag.val = 2926) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2926 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02927 (tag : Fin 10000) (htag : tag.val = 2927) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2927 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02928 (tag : Fin 10000) (htag : tag.val = 2928) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2928 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02929 (tag : Fin 10000) (htag : tag.val = 2929) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2929 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02930 (tag : Fin 10000) (htag : tag.val = 2930) (k : Ring12) : tag.val = 2930 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02931 (tag : Fin 10000) (htag : tag.val = 2931) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2931 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02932 (tag : Fin 10000) (htag : tag.val = 2932) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2932 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02933 (tag : Fin 10000) (htag : tag.val = 2933) (x : State) (e : Event) (dr : Ring12) : tag.val = 2933 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02934 (tag : Fin 10000) (htag : tag.val = 2934) (x : State) (e : Event) (dr : Ring12) : tag.val = 2934 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02935 (tag : Fin 10000) (htag : tag.val = 2935) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2935 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02936 (tag : Fin 10000) (htag : tag.val = 2936) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2936 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02937 (tag : Fin 10000) (htag : tag.val = 2937) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2937 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02938 (tag : Fin 10000) (htag : tag.val = 2938) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2938 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02939 (tag : Fin 10000) (htag : tag.val = 2939) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2939 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02940 (tag : Fin 10000) (htag : tag.val = 2940) (k : Ring12) : tag.val = 2940 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02941 (tag : Fin 10000) (htag : tag.val = 2941) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2941 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02942 (tag : Fin 10000) (htag : tag.val = 2942) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2942 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02943 (tag : Fin 10000) (htag : tag.val = 2943) (x : State) (e : Event) (dr : Ring12) : tag.val = 2943 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02944 (tag : Fin 10000) (htag : tag.val = 2944) (x : State) (e : Event) (dr : Ring12) : tag.val = 2944 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02945 (tag : Fin 10000) (htag : tag.val = 2945) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2945 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02946 (tag : Fin 10000) (htag : tag.val = 2946) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2946 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02947 (tag : Fin 10000) (htag : tag.val = 2947) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2947 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02948 (tag : Fin 10000) (htag : tag.val = 2948) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2948 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02949 (tag : Fin 10000) (htag : tag.val = 2949) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2949 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02950 (tag : Fin 10000) (htag : tag.val = 2950) (k : Ring12) : tag.val = 2950 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02951 (tag : Fin 10000) (htag : tag.val = 2951) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2951 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02952 (tag : Fin 10000) (htag : tag.val = 2952) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2952 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02953 (tag : Fin 10000) (htag : tag.val = 2953) (x : State) (e : Event) (dr : Ring12) : tag.val = 2953 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02954 (tag : Fin 10000) (htag : tag.val = 2954) (x : State) (e : Event) (dr : Ring12) : tag.val = 2954 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02955 (tag : Fin 10000) (htag : tag.val = 2955) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2955 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02956 (tag : Fin 10000) (htag : tag.val = 2956) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2956 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02957 (tag : Fin 10000) (htag : tag.val = 2957) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2957 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02958 (tag : Fin 10000) (htag : tag.val = 2958) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2958 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02959 (tag : Fin 10000) (htag : tag.val = 2959) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2959 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02960 (tag : Fin 10000) (htag : tag.val = 2960) (k : Ring12) : tag.val = 2960 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02961 (tag : Fin 10000) (htag : tag.val = 2961) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2961 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02962 (tag : Fin 10000) (htag : tag.val = 2962) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2962 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02963 (tag : Fin 10000) (htag : tag.val = 2963) (x : State) (e : Event) (dr : Ring12) : tag.val = 2963 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02964 (tag : Fin 10000) (htag : tag.val = 2964) (x : State) (e : Event) (dr : Ring12) : tag.val = 2964 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02965 (tag : Fin 10000) (htag : tag.val = 2965) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2965 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02966 (tag : Fin 10000) (htag : tag.val = 2966) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2966 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02967 (tag : Fin 10000) (htag : tag.val = 2967) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2967 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02968 (tag : Fin 10000) (htag : tag.val = 2968) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2968 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02969 (tag : Fin 10000) (htag : tag.val = 2969) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2969 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02970 (tag : Fin 10000) (htag : tag.val = 2970) (k : Ring12) : tag.val = 2970 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02971 (tag : Fin 10000) (htag : tag.val = 2971) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2971 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02972 (tag : Fin 10000) (htag : tag.val = 2972) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2972 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02973 (tag : Fin 10000) (htag : tag.val = 2973) (x : State) (e : Event) (dr : Ring12) : tag.val = 2973 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02974 (tag : Fin 10000) (htag : tag.val = 2974) (x : State) (e : Event) (dr : Ring12) : tag.val = 2974 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02975 (tag : Fin 10000) (htag : tag.val = 2975) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2975 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02976 (tag : Fin 10000) (htag : tag.val = 2976) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2976 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02977 (tag : Fin 10000) (htag : tag.val = 2977) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2977 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02978 (tag : Fin 10000) (htag : tag.val = 2978) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2978 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02979 (tag : Fin 10000) (htag : tag.val = 2979) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2979 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02980 (tag : Fin 10000) (htag : tag.val = 2980) (k : Ring12) : tag.val = 2980 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02981 (tag : Fin 10000) (htag : tag.val = 2981) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2981 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02982 (tag : Fin 10000) (htag : tag.val = 2982) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2982 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02983 (tag : Fin 10000) (htag : tag.val = 2983) (x : State) (e : Event) (dr : Ring12) : tag.val = 2983 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02984 (tag : Fin 10000) (htag : tag.val = 2984) (x : State) (e : Event) (dr : Ring12) : tag.val = 2984 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02985 (tag : Fin 10000) (htag : tag.val = 2985) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2985 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02986 (tag : Fin 10000) (htag : tag.val = 2986) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2986 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02987 (tag : Fin 10000) (htag : tag.val = 2987) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2987 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02988 (tag : Fin 10000) (htag : tag.val = 2988) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2988 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02989 (tag : Fin 10000) (htag : tag.val = 2989) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2989 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02990 (tag : Fin 10000) (htag : tag.val = 2990) (k : Ring12) : tag.val = 2990 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02991 (tag : Fin 10000) (htag : tag.val = 2991) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2991 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02992 (tag : Fin 10000) (htag : tag.val = 2992) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2992 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02993 (tag : Fin 10000) (htag : tag.val = 2993) (x : State) (e : Event) (dr : Ring12) : tag.val = 2993 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02994 (tag : Fin 10000) (htag : tag.val = 2994) (x : State) (e : Event) (dr : Ring12) : tag.val = 2994 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02995 (tag : Fin 10000) (htag : tag.val = 2995) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2995 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02996 (tag : Fin 10000) (htag : tag.val = 2996) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2996 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02997 (tag : Fin 10000) (htag : tag.val = 2997) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2997 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02998 (tag : Fin 10000) (htag : tag.val = 2998) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2998 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02999 (tag : Fin 10000) (htag : tag.val = 2999) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2999 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
