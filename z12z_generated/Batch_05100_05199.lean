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
theorem generated_05100 (tag : Fin 10000) (htag : tag.val = 5100) (k : Ring12) : tag.val = 5100 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05101 (tag : Fin 10000) (htag : tag.val = 5101) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5101 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05102 (tag : Fin 10000) (htag : tag.val = 5102) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5102 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05103 (tag : Fin 10000) (htag : tag.val = 5103) (x : State) (e : Event) (dr : Ring12) : tag.val = 5103 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05104 (tag : Fin 10000) (htag : tag.val = 5104) (x : State) (e : Event) (dr : Ring12) : tag.val = 5104 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05105 (tag : Fin 10000) (htag : tag.val = 5105) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5105 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05106 (tag : Fin 10000) (htag : tag.val = 5106) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5106 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05107 (tag : Fin 10000) (htag : tag.val = 5107) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5107 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05108 (tag : Fin 10000) (htag : tag.val = 5108) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5108 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05109 (tag : Fin 10000) (htag : tag.val = 5109) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5109 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05110 (tag : Fin 10000) (htag : tag.val = 5110) (k : Ring12) : tag.val = 5110 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05111 (tag : Fin 10000) (htag : tag.val = 5111) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5111 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05112 (tag : Fin 10000) (htag : tag.val = 5112) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5112 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05113 (tag : Fin 10000) (htag : tag.val = 5113) (x : State) (e : Event) (dr : Ring12) : tag.val = 5113 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05114 (tag : Fin 10000) (htag : tag.val = 5114) (x : State) (e : Event) (dr : Ring12) : tag.val = 5114 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05115 (tag : Fin 10000) (htag : tag.val = 5115) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5115 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05116 (tag : Fin 10000) (htag : tag.val = 5116) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5116 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05117 (tag : Fin 10000) (htag : tag.val = 5117) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5117 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05118 (tag : Fin 10000) (htag : tag.val = 5118) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5118 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05119 (tag : Fin 10000) (htag : tag.val = 5119) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5119 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05120 (tag : Fin 10000) (htag : tag.val = 5120) (k : Ring12) : tag.val = 5120 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05121 (tag : Fin 10000) (htag : tag.val = 5121) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5121 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05122 (tag : Fin 10000) (htag : tag.val = 5122) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5122 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05123 (tag : Fin 10000) (htag : tag.val = 5123) (x : State) (e : Event) (dr : Ring12) : tag.val = 5123 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05124 (tag : Fin 10000) (htag : tag.val = 5124) (x : State) (e : Event) (dr : Ring12) : tag.val = 5124 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05125 (tag : Fin 10000) (htag : tag.val = 5125) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5125 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05126 (tag : Fin 10000) (htag : tag.val = 5126) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5126 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05127 (tag : Fin 10000) (htag : tag.val = 5127) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5127 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05128 (tag : Fin 10000) (htag : tag.val = 5128) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5128 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05129 (tag : Fin 10000) (htag : tag.val = 5129) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5129 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05130 (tag : Fin 10000) (htag : tag.val = 5130) (k : Ring12) : tag.val = 5130 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05131 (tag : Fin 10000) (htag : tag.val = 5131) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5131 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05132 (tag : Fin 10000) (htag : tag.val = 5132) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5132 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05133 (tag : Fin 10000) (htag : tag.val = 5133) (x : State) (e : Event) (dr : Ring12) : tag.val = 5133 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05134 (tag : Fin 10000) (htag : tag.val = 5134) (x : State) (e : Event) (dr : Ring12) : tag.val = 5134 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05135 (tag : Fin 10000) (htag : tag.val = 5135) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5135 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05136 (tag : Fin 10000) (htag : tag.val = 5136) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5136 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05137 (tag : Fin 10000) (htag : tag.val = 5137) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5137 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05138 (tag : Fin 10000) (htag : tag.val = 5138) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5138 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05139 (tag : Fin 10000) (htag : tag.val = 5139) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5139 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05140 (tag : Fin 10000) (htag : tag.val = 5140) (k : Ring12) : tag.val = 5140 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05141 (tag : Fin 10000) (htag : tag.val = 5141) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5141 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05142 (tag : Fin 10000) (htag : tag.val = 5142) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5142 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05143 (tag : Fin 10000) (htag : tag.val = 5143) (x : State) (e : Event) (dr : Ring12) : tag.val = 5143 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05144 (tag : Fin 10000) (htag : tag.val = 5144) (x : State) (e : Event) (dr : Ring12) : tag.val = 5144 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05145 (tag : Fin 10000) (htag : tag.val = 5145) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5145 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05146 (tag : Fin 10000) (htag : tag.val = 5146) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5146 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05147 (tag : Fin 10000) (htag : tag.val = 5147) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5147 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05148 (tag : Fin 10000) (htag : tag.val = 5148) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5148 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05149 (tag : Fin 10000) (htag : tag.val = 5149) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5149 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05150 (tag : Fin 10000) (htag : tag.val = 5150) (k : Ring12) : tag.val = 5150 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05151 (tag : Fin 10000) (htag : tag.val = 5151) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5151 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05152 (tag : Fin 10000) (htag : tag.val = 5152) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5152 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05153 (tag : Fin 10000) (htag : tag.val = 5153) (x : State) (e : Event) (dr : Ring12) : tag.val = 5153 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05154 (tag : Fin 10000) (htag : tag.val = 5154) (x : State) (e : Event) (dr : Ring12) : tag.val = 5154 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05155 (tag : Fin 10000) (htag : tag.val = 5155) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5155 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05156 (tag : Fin 10000) (htag : tag.val = 5156) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5156 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05157 (tag : Fin 10000) (htag : tag.val = 5157) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5157 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05158 (tag : Fin 10000) (htag : tag.val = 5158) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5158 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05159 (tag : Fin 10000) (htag : tag.val = 5159) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5159 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05160 (tag : Fin 10000) (htag : tag.val = 5160) (k : Ring12) : tag.val = 5160 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05161 (tag : Fin 10000) (htag : tag.val = 5161) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5161 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05162 (tag : Fin 10000) (htag : tag.val = 5162) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5162 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05163 (tag : Fin 10000) (htag : tag.val = 5163) (x : State) (e : Event) (dr : Ring12) : tag.val = 5163 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05164 (tag : Fin 10000) (htag : tag.val = 5164) (x : State) (e : Event) (dr : Ring12) : tag.val = 5164 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05165 (tag : Fin 10000) (htag : tag.val = 5165) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5165 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05166 (tag : Fin 10000) (htag : tag.val = 5166) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5166 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05167 (tag : Fin 10000) (htag : tag.val = 5167) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5167 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05168 (tag : Fin 10000) (htag : tag.val = 5168) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5168 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05169 (tag : Fin 10000) (htag : tag.val = 5169) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5169 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05170 (tag : Fin 10000) (htag : tag.val = 5170) (k : Ring12) : tag.val = 5170 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05171 (tag : Fin 10000) (htag : tag.val = 5171) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5171 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05172 (tag : Fin 10000) (htag : tag.val = 5172) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5172 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05173 (tag : Fin 10000) (htag : tag.val = 5173) (x : State) (e : Event) (dr : Ring12) : tag.val = 5173 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05174 (tag : Fin 10000) (htag : tag.val = 5174) (x : State) (e : Event) (dr : Ring12) : tag.val = 5174 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05175 (tag : Fin 10000) (htag : tag.val = 5175) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5175 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05176 (tag : Fin 10000) (htag : tag.val = 5176) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5176 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05177 (tag : Fin 10000) (htag : tag.val = 5177) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5177 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05178 (tag : Fin 10000) (htag : tag.val = 5178) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5178 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05179 (tag : Fin 10000) (htag : tag.val = 5179) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5179 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05180 (tag : Fin 10000) (htag : tag.val = 5180) (k : Ring12) : tag.val = 5180 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05181 (tag : Fin 10000) (htag : tag.val = 5181) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5181 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05182 (tag : Fin 10000) (htag : tag.val = 5182) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5182 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05183 (tag : Fin 10000) (htag : tag.val = 5183) (x : State) (e : Event) (dr : Ring12) : tag.val = 5183 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05184 (tag : Fin 10000) (htag : tag.val = 5184) (x : State) (e : Event) (dr : Ring12) : tag.val = 5184 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05185 (tag : Fin 10000) (htag : tag.val = 5185) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5185 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05186 (tag : Fin 10000) (htag : tag.val = 5186) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5186 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05187 (tag : Fin 10000) (htag : tag.val = 5187) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5187 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05188 (tag : Fin 10000) (htag : tag.val = 5188) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5188 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05189 (tag : Fin 10000) (htag : tag.val = 5189) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5189 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05190 (tag : Fin 10000) (htag : tag.val = 5190) (k : Ring12) : tag.val = 5190 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05191 (tag : Fin 10000) (htag : tag.val = 5191) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5191 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05192 (tag : Fin 10000) (htag : tag.val = 5192) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5192 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05193 (tag : Fin 10000) (htag : tag.val = 5193) (x : State) (e : Event) (dr : Ring12) : tag.val = 5193 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05194 (tag : Fin 10000) (htag : tag.val = 5194) (x : State) (e : Event) (dr : Ring12) : tag.val = 5194 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05195 (tag : Fin 10000) (htag : tag.val = 5195) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5195 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05196 (tag : Fin 10000) (htag : tag.val = 5196) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5196 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05197 (tag : Fin 10000) (htag : tag.val = 5197) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5197 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05198 (tag : Fin 10000) (htag : tag.val = 5198) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5198 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05199 (tag : Fin 10000) (htag : tag.val = 5199) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5199 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
