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
theorem generated_03000 (tag : Fin 10000) (htag : tag.val = 3000) (k : Ring12) : tag.val = 3000 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03001 (tag : Fin 10000) (htag : tag.val = 3001) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3001 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03002 (tag : Fin 10000) (htag : tag.val = 3002) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3002 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03003 (tag : Fin 10000) (htag : tag.val = 3003) (x : State) (e : Event) (dr : Ring12) : tag.val = 3003 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03004 (tag : Fin 10000) (htag : tag.val = 3004) (x : State) (e : Event) (dr : Ring12) : tag.val = 3004 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03005 (tag : Fin 10000) (htag : tag.val = 3005) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3005 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03006 (tag : Fin 10000) (htag : tag.val = 3006) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3006 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03007 (tag : Fin 10000) (htag : tag.val = 3007) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3007 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03008 (tag : Fin 10000) (htag : tag.val = 3008) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3008 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03009 (tag : Fin 10000) (htag : tag.val = 3009) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3009 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03010 (tag : Fin 10000) (htag : tag.val = 3010) (k : Ring12) : tag.val = 3010 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03011 (tag : Fin 10000) (htag : tag.val = 3011) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3011 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03012 (tag : Fin 10000) (htag : tag.val = 3012) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3012 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03013 (tag : Fin 10000) (htag : tag.val = 3013) (x : State) (e : Event) (dr : Ring12) : tag.val = 3013 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03014 (tag : Fin 10000) (htag : tag.val = 3014) (x : State) (e : Event) (dr : Ring12) : tag.val = 3014 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03015 (tag : Fin 10000) (htag : tag.val = 3015) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3015 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03016 (tag : Fin 10000) (htag : tag.val = 3016) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3016 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03017 (tag : Fin 10000) (htag : tag.val = 3017) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3017 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03018 (tag : Fin 10000) (htag : tag.val = 3018) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3018 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03019 (tag : Fin 10000) (htag : tag.val = 3019) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3019 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03020 (tag : Fin 10000) (htag : tag.val = 3020) (k : Ring12) : tag.val = 3020 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03021 (tag : Fin 10000) (htag : tag.val = 3021) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3021 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03022 (tag : Fin 10000) (htag : tag.val = 3022) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3022 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03023 (tag : Fin 10000) (htag : tag.val = 3023) (x : State) (e : Event) (dr : Ring12) : tag.val = 3023 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03024 (tag : Fin 10000) (htag : tag.val = 3024) (x : State) (e : Event) (dr : Ring12) : tag.val = 3024 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03025 (tag : Fin 10000) (htag : tag.val = 3025) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3025 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03026 (tag : Fin 10000) (htag : tag.val = 3026) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3026 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03027 (tag : Fin 10000) (htag : tag.val = 3027) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3027 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03028 (tag : Fin 10000) (htag : tag.val = 3028) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3028 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03029 (tag : Fin 10000) (htag : tag.val = 3029) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3029 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03030 (tag : Fin 10000) (htag : tag.val = 3030) (k : Ring12) : tag.val = 3030 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03031 (tag : Fin 10000) (htag : tag.val = 3031) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3031 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03032 (tag : Fin 10000) (htag : tag.val = 3032) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3032 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03033 (tag : Fin 10000) (htag : tag.val = 3033) (x : State) (e : Event) (dr : Ring12) : tag.val = 3033 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03034 (tag : Fin 10000) (htag : tag.val = 3034) (x : State) (e : Event) (dr : Ring12) : tag.val = 3034 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03035 (tag : Fin 10000) (htag : tag.val = 3035) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3035 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03036 (tag : Fin 10000) (htag : tag.val = 3036) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3036 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03037 (tag : Fin 10000) (htag : tag.val = 3037) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3037 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03038 (tag : Fin 10000) (htag : tag.val = 3038) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3038 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03039 (tag : Fin 10000) (htag : tag.val = 3039) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3039 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03040 (tag : Fin 10000) (htag : tag.val = 3040) (k : Ring12) : tag.val = 3040 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03041 (tag : Fin 10000) (htag : tag.val = 3041) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3041 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03042 (tag : Fin 10000) (htag : tag.val = 3042) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3042 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03043 (tag : Fin 10000) (htag : tag.val = 3043) (x : State) (e : Event) (dr : Ring12) : tag.val = 3043 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03044 (tag : Fin 10000) (htag : tag.val = 3044) (x : State) (e : Event) (dr : Ring12) : tag.val = 3044 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03045 (tag : Fin 10000) (htag : tag.val = 3045) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3045 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03046 (tag : Fin 10000) (htag : tag.val = 3046) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3046 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03047 (tag : Fin 10000) (htag : tag.val = 3047) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3047 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03048 (tag : Fin 10000) (htag : tag.val = 3048) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3048 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03049 (tag : Fin 10000) (htag : tag.val = 3049) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3049 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03050 (tag : Fin 10000) (htag : tag.val = 3050) (k : Ring12) : tag.val = 3050 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03051 (tag : Fin 10000) (htag : tag.val = 3051) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3051 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03052 (tag : Fin 10000) (htag : tag.val = 3052) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3052 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03053 (tag : Fin 10000) (htag : tag.val = 3053) (x : State) (e : Event) (dr : Ring12) : tag.val = 3053 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03054 (tag : Fin 10000) (htag : tag.val = 3054) (x : State) (e : Event) (dr : Ring12) : tag.val = 3054 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03055 (tag : Fin 10000) (htag : tag.val = 3055) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3055 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03056 (tag : Fin 10000) (htag : tag.val = 3056) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3056 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03057 (tag : Fin 10000) (htag : tag.val = 3057) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3057 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03058 (tag : Fin 10000) (htag : tag.val = 3058) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3058 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03059 (tag : Fin 10000) (htag : tag.val = 3059) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3059 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03060 (tag : Fin 10000) (htag : tag.val = 3060) (k : Ring12) : tag.val = 3060 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03061 (tag : Fin 10000) (htag : tag.val = 3061) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3061 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03062 (tag : Fin 10000) (htag : tag.val = 3062) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3062 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03063 (tag : Fin 10000) (htag : tag.val = 3063) (x : State) (e : Event) (dr : Ring12) : tag.val = 3063 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03064 (tag : Fin 10000) (htag : tag.val = 3064) (x : State) (e : Event) (dr : Ring12) : tag.val = 3064 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03065 (tag : Fin 10000) (htag : tag.val = 3065) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3065 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03066 (tag : Fin 10000) (htag : tag.val = 3066) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3066 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03067 (tag : Fin 10000) (htag : tag.val = 3067) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3067 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03068 (tag : Fin 10000) (htag : tag.val = 3068) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3068 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03069 (tag : Fin 10000) (htag : tag.val = 3069) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3069 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03070 (tag : Fin 10000) (htag : tag.val = 3070) (k : Ring12) : tag.val = 3070 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03071 (tag : Fin 10000) (htag : tag.val = 3071) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3071 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03072 (tag : Fin 10000) (htag : tag.val = 3072) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3072 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03073 (tag : Fin 10000) (htag : tag.val = 3073) (x : State) (e : Event) (dr : Ring12) : tag.val = 3073 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03074 (tag : Fin 10000) (htag : tag.val = 3074) (x : State) (e : Event) (dr : Ring12) : tag.val = 3074 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03075 (tag : Fin 10000) (htag : tag.val = 3075) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3075 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03076 (tag : Fin 10000) (htag : tag.val = 3076) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3076 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03077 (tag : Fin 10000) (htag : tag.val = 3077) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3077 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03078 (tag : Fin 10000) (htag : tag.val = 3078) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3078 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03079 (tag : Fin 10000) (htag : tag.val = 3079) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3079 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03080 (tag : Fin 10000) (htag : tag.val = 3080) (k : Ring12) : tag.val = 3080 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03081 (tag : Fin 10000) (htag : tag.val = 3081) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3081 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03082 (tag : Fin 10000) (htag : tag.val = 3082) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3082 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03083 (tag : Fin 10000) (htag : tag.val = 3083) (x : State) (e : Event) (dr : Ring12) : tag.val = 3083 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03084 (tag : Fin 10000) (htag : tag.val = 3084) (x : State) (e : Event) (dr : Ring12) : tag.val = 3084 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03085 (tag : Fin 10000) (htag : tag.val = 3085) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3085 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03086 (tag : Fin 10000) (htag : tag.val = 3086) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3086 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03087 (tag : Fin 10000) (htag : tag.val = 3087) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3087 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03088 (tag : Fin 10000) (htag : tag.val = 3088) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3088 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03089 (tag : Fin 10000) (htag : tag.val = 3089) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3089 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03090 (tag : Fin 10000) (htag : tag.val = 3090) (k : Ring12) : tag.val = 3090 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03091 (tag : Fin 10000) (htag : tag.val = 3091) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3091 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03092 (tag : Fin 10000) (htag : tag.val = 3092) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3092 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03093 (tag : Fin 10000) (htag : tag.val = 3093) (x : State) (e : Event) (dr : Ring12) : tag.val = 3093 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03094 (tag : Fin 10000) (htag : tag.val = 3094) (x : State) (e : Event) (dr : Ring12) : tag.val = 3094 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03095 (tag : Fin 10000) (htag : tag.val = 3095) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3095 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03096 (tag : Fin 10000) (htag : tag.val = 3096) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3096 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03097 (tag : Fin 10000) (htag : tag.val = 3097) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3097 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03098 (tag : Fin 10000) (htag : tag.val = 3098) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3098 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03099 (tag : Fin 10000) (htag : tag.val = 3099) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3099 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
