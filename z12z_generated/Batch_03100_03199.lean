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
theorem generated_03100 (tag : Fin 10000) (htag : tag.val = 3100) (k : Ring12) : tag.val = 3100 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03101 (tag : Fin 10000) (htag : tag.val = 3101) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3101 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03102 (tag : Fin 10000) (htag : tag.val = 3102) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3102 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03103 (tag : Fin 10000) (htag : tag.val = 3103) (x : State) (e : Event) (dr : Ring12) : tag.val = 3103 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03104 (tag : Fin 10000) (htag : tag.val = 3104) (x : State) (e : Event) (dr : Ring12) : tag.val = 3104 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03105 (tag : Fin 10000) (htag : tag.val = 3105) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3105 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03106 (tag : Fin 10000) (htag : tag.val = 3106) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3106 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03107 (tag : Fin 10000) (htag : tag.val = 3107) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3107 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03108 (tag : Fin 10000) (htag : tag.val = 3108) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3108 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03109 (tag : Fin 10000) (htag : tag.val = 3109) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3109 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03110 (tag : Fin 10000) (htag : tag.val = 3110) (k : Ring12) : tag.val = 3110 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03111 (tag : Fin 10000) (htag : tag.val = 3111) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3111 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03112 (tag : Fin 10000) (htag : tag.val = 3112) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3112 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03113 (tag : Fin 10000) (htag : tag.val = 3113) (x : State) (e : Event) (dr : Ring12) : tag.val = 3113 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03114 (tag : Fin 10000) (htag : tag.val = 3114) (x : State) (e : Event) (dr : Ring12) : tag.val = 3114 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03115 (tag : Fin 10000) (htag : tag.val = 3115) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3115 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03116 (tag : Fin 10000) (htag : tag.val = 3116) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3116 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03117 (tag : Fin 10000) (htag : tag.val = 3117) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3117 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03118 (tag : Fin 10000) (htag : tag.val = 3118) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3118 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03119 (tag : Fin 10000) (htag : tag.val = 3119) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3119 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03120 (tag : Fin 10000) (htag : tag.val = 3120) (k : Ring12) : tag.val = 3120 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03121 (tag : Fin 10000) (htag : tag.val = 3121) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3121 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03122 (tag : Fin 10000) (htag : tag.val = 3122) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3122 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03123 (tag : Fin 10000) (htag : tag.val = 3123) (x : State) (e : Event) (dr : Ring12) : tag.val = 3123 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03124 (tag : Fin 10000) (htag : tag.val = 3124) (x : State) (e : Event) (dr : Ring12) : tag.val = 3124 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03125 (tag : Fin 10000) (htag : tag.val = 3125) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3125 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03126 (tag : Fin 10000) (htag : tag.val = 3126) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3126 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03127 (tag : Fin 10000) (htag : tag.val = 3127) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3127 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03128 (tag : Fin 10000) (htag : tag.val = 3128) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3128 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03129 (tag : Fin 10000) (htag : tag.val = 3129) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3129 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03130 (tag : Fin 10000) (htag : tag.val = 3130) (k : Ring12) : tag.val = 3130 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03131 (tag : Fin 10000) (htag : tag.val = 3131) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3131 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03132 (tag : Fin 10000) (htag : tag.val = 3132) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3132 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03133 (tag : Fin 10000) (htag : tag.val = 3133) (x : State) (e : Event) (dr : Ring12) : tag.val = 3133 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03134 (tag : Fin 10000) (htag : tag.val = 3134) (x : State) (e : Event) (dr : Ring12) : tag.val = 3134 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03135 (tag : Fin 10000) (htag : tag.val = 3135) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3135 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03136 (tag : Fin 10000) (htag : tag.val = 3136) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3136 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03137 (tag : Fin 10000) (htag : tag.val = 3137) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3137 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03138 (tag : Fin 10000) (htag : tag.val = 3138) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3138 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03139 (tag : Fin 10000) (htag : tag.val = 3139) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3139 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03140 (tag : Fin 10000) (htag : tag.val = 3140) (k : Ring12) : tag.val = 3140 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03141 (tag : Fin 10000) (htag : tag.val = 3141) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3141 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03142 (tag : Fin 10000) (htag : tag.val = 3142) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3142 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03143 (tag : Fin 10000) (htag : tag.val = 3143) (x : State) (e : Event) (dr : Ring12) : tag.val = 3143 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03144 (tag : Fin 10000) (htag : tag.val = 3144) (x : State) (e : Event) (dr : Ring12) : tag.val = 3144 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03145 (tag : Fin 10000) (htag : tag.val = 3145) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3145 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03146 (tag : Fin 10000) (htag : tag.val = 3146) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3146 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03147 (tag : Fin 10000) (htag : tag.val = 3147) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3147 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03148 (tag : Fin 10000) (htag : tag.val = 3148) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3148 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03149 (tag : Fin 10000) (htag : tag.val = 3149) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3149 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03150 (tag : Fin 10000) (htag : tag.val = 3150) (k : Ring12) : tag.val = 3150 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03151 (tag : Fin 10000) (htag : tag.val = 3151) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3151 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03152 (tag : Fin 10000) (htag : tag.val = 3152) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3152 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03153 (tag : Fin 10000) (htag : tag.val = 3153) (x : State) (e : Event) (dr : Ring12) : tag.val = 3153 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03154 (tag : Fin 10000) (htag : tag.val = 3154) (x : State) (e : Event) (dr : Ring12) : tag.val = 3154 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03155 (tag : Fin 10000) (htag : tag.val = 3155) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3155 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03156 (tag : Fin 10000) (htag : tag.val = 3156) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3156 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03157 (tag : Fin 10000) (htag : tag.val = 3157) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3157 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03158 (tag : Fin 10000) (htag : tag.val = 3158) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3158 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03159 (tag : Fin 10000) (htag : tag.val = 3159) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3159 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03160 (tag : Fin 10000) (htag : tag.val = 3160) (k : Ring12) : tag.val = 3160 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03161 (tag : Fin 10000) (htag : tag.val = 3161) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3161 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03162 (tag : Fin 10000) (htag : tag.val = 3162) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3162 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03163 (tag : Fin 10000) (htag : tag.val = 3163) (x : State) (e : Event) (dr : Ring12) : tag.val = 3163 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03164 (tag : Fin 10000) (htag : tag.val = 3164) (x : State) (e : Event) (dr : Ring12) : tag.val = 3164 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03165 (tag : Fin 10000) (htag : tag.val = 3165) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3165 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03166 (tag : Fin 10000) (htag : tag.val = 3166) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3166 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03167 (tag : Fin 10000) (htag : tag.val = 3167) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3167 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03168 (tag : Fin 10000) (htag : tag.val = 3168) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3168 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03169 (tag : Fin 10000) (htag : tag.val = 3169) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3169 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03170 (tag : Fin 10000) (htag : tag.val = 3170) (k : Ring12) : tag.val = 3170 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03171 (tag : Fin 10000) (htag : tag.val = 3171) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3171 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03172 (tag : Fin 10000) (htag : tag.val = 3172) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3172 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03173 (tag : Fin 10000) (htag : tag.val = 3173) (x : State) (e : Event) (dr : Ring12) : tag.val = 3173 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03174 (tag : Fin 10000) (htag : tag.val = 3174) (x : State) (e : Event) (dr : Ring12) : tag.val = 3174 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03175 (tag : Fin 10000) (htag : tag.val = 3175) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3175 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03176 (tag : Fin 10000) (htag : tag.val = 3176) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3176 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03177 (tag : Fin 10000) (htag : tag.val = 3177) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3177 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03178 (tag : Fin 10000) (htag : tag.val = 3178) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3178 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03179 (tag : Fin 10000) (htag : tag.val = 3179) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3179 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03180 (tag : Fin 10000) (htag : tag.val = 3180) (k : Ring12) : tag.val = 3180 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03181 (tag : Fin 10000) (htag : tag.val = 3181) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3181 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03182 (tag : Fin 10000) (htag : tag.val = 3182) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3182 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03183 (tag : Fin 10000) (htag : tag.val = 3183) (x : State) (e : Event) (dr : Ring12) : tag.val = 3183 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03184 (tag : Fin 10000) (htag : tag.val = 3184) (x : State) (e : Event) (dr : Ring12) : tag.val = 3184 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03185 (tag : Fin 10000) (htag : tag.val = 3185) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3185 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03186 (tag : Fin 10000) (htag : tag.val = 3186) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3186 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03187 (tag : Fin 10000) (htag : tag.val = 3187) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3187 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03188 (tag : Fin 10000) (htag : tag.val = 3188) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3188 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03189 (tag : Fin 10000) (htag : tag.val = 3189) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3189 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03190 (tag : Fin 10000) (htag : tag.val = 3190) (k : Ring12) : tag.val = 3190 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03191 (tag : Fin 10000) (htag : tag.val = 3191) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3191 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03192 (tag : Fin 10000) (htag : tag.val = 3192) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3192 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03193 (tag : Fin 10000) (htag : tag.val = 3193) (x : State) (e : Event) (dr : Ring12) : tag.val = 3193 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03194 (tag : Fin 10000) (htag : tag.val = 3194) (x : State) (e : Event) (dr : Ring12) : tag.val = 3194 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03195 (tag : Fin 10000) (htag : tag.val = 3195) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3195 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03196 (tag : Fin 10000) (htag : tag.val = 3196) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3196 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03197 (tag : Fin 10000) (htag : tag.val = 3197) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3197 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03198 (tag : Fin 10000) (htag : tag.val = 3198) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3198 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03199 (tag : Fin 10000) (htag : tag.val = 3199) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3199 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
