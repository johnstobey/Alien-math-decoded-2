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
theorem generated_06100 (tag : Fin 10000) (htag : tag.val = 6100) (k : Ring12) : tag.val = 6100 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06101 (tag : Fin 10000) (htag : tag.val = 6101) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6101 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06102 (tag : Fin 10000) (htag : tag.val = 6102) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6102 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06103 (tag : Fin 10000) (htag : tag.val = 6103) (x : State) (e : Event) (dr : Ring12) : tag.val = 6103 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06104 (tag : Fin 10000) (htag : tag.val = 6104) (x : State) (e : Event) (dr : Ring12) : tag.val = 6104 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06105 (tag : Fin 10000) (htag : tag.val = 6105) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6105 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06106 (tag : Fin 10000) (htag : tag.val = 6106) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6106 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06107 (tag : Fin 10000) (htag : tag.val = 6107) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6107 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06108 (tag : Fin 10000) (htag : tag.val = 6108) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6108 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06109 (tag : Fin 10000) (htag : tag.val = 6109) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6109 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06110 (tag : Fin 10000) (htag : tag.val = 6110) (k : Ring12) : tag.val = 6110 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06111 (tag : Fin 10000) (htag : tag.val = 6111) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6111 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06112 (tag : Fin 10000) (htag : tag.val = 6112) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6112 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06113 (tag : Fin 10000) (htag : tag.val = 6113) (x : State) (e : Event) (dr : Ring12) : tag.val = 6113 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06114 (tag : Fin 10000) (htag : tag.val = 6114) (x : State) (e : Event) (dr : Ring12) : tag.val = 6114 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06115 (tag : Fin 10000) (htag : tag.val = 6115) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6115 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06116 (tag : Fin 10000) (htag : tag.val = 6116) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6116 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06117 (tag : Fin 10000) (htag : tag.val = 6117) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6117 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06118 (tag : Fin 10000) (htag : tag.val = 6118) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6118 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06119 (tag : Fin 10000) (htag : tag.val = 6119) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6119 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06120 (tag : Fin 10000) (htag : tag.val = 6120) (k : Ring12) : tag.val = 6120 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06121 (tag : Fin 10000) (htag : tag.val = 6121) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6121 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06122 (tag : Fin 10000) (htag : tag.val = 6122) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6122 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06123 (tag : Fin 10000) (htag : tag.val = 6123) (x : State) (e : Event) (dr : Ring12) : tag.val = 6123 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06124 (tag : Fin 10000) (htag : tag.val = 6124) (x : State) (e : Event) (dr : Ring12) : tag.val = 6124 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06125 (tag : Fin 10000) (htag : tag.val = 6125) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6125 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06126 (tag : Fin 10000) (htag : tag.val = 6126) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6126 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06127 (tag : Fin 10000) (htag : tag.val = 6127) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6127 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06128 (tag : Fin 10000) (htag : tag.val = 6128) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6128 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06129 (tag : Fin 10000) (htag : tag.val = 6129) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6129 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06130 (tag : Fin 10000) (htag : tag.val = 6130) (k : Ring12) : tag.val = 6130 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06131 (tag : Fin 10000) (htag : tag.val = 6131) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6131 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06132 (tag : Fin 10000) (htag : tag.val = 6132) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6132 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06133 (tag : Fin 10000) (htag : tag.val = 6133) (x : State) (e : Event) (dr : Ring12) : tag.val = 6133 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06134 (tag : Fin 10000) (htag : tag.val = 6134) (x : State) (e : Event) (dr : Ring12) : tag.val = 6134 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06135 (tag : Fin 10000) (htag : tag.val = 6135) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6135 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06136 (tag : Fin 10000) (htag : tag.val = 6136) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6136 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06137 (tag : Fin 10000) (htag : tag.val = 6137) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6137 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06138 (tag : Fin 10000) (htag : tag.val = 6138) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6138 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06139 (tag : Fin 10000) (htag : tag.val = 6139) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6139 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06140 (tag : Fin 10000) (htag : tag.val = 6140) (k : Ring12) : tag.val = 6140 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06141 (tag : Fin 10000) (htag : tag.val = 6141) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6141 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06142 (tag : Fin 10000) (htag : tag.val = 6142) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6142 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06143 (tag : Fin 10000) (htag : tag.val = 6143) (x : State) (e : Event) (dr : Ring12) : tag.val = 6143 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06144 (tag : Fin 10000) (htag : tag.val = 6144) (x : State) (e : Event) (dr : Ring12) : tag.val = 6144 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06145 (tag : Fin 10000) (htag : tag.val = 6145) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6145 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06146 (tag : Fin 10000) (htag : tag.val = 6146) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6146 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06147 (tag : Fin 10000) (htag : tag.val = 6147) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6147 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06148 (tag : Fin 10000) (htag : tag.val = 6148) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6148 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06149 (tag : Fin 10000) (htag : tag.val = 6149) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6149 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06150 (tag : Fin 10000) (htag : tag.val = 6150) (k : Ring12) : tag.val = 6150 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06151 (tag : Fin 10000) (htag : tag.val = 6151) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6151 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06152 (tag : Fin 10000) (htag : tag.val = 6152) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6152 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06153 (tag : Fin 10000) (htag : tag.val = 6153) (x : State) (e : Event) (dr : Ring12) : tag.val = 6153 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06154 (tag : Fin 10000) (htag : tag.val = 6154) (x : State) (e : Event) (dr : Ring12) : tag.val = 6154 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06155 (tag : Fin 10000) (htag : tag.val = 6155) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6155 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06156 (tag : Fin 10000) (htag : tag.val = 6156) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6156 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06157 (tag : Fin 10000) (htag : tag.val = 6157) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6157 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06158 (tag : Fin 10000) (htag : tag.val = 6158) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6158 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06159 (tag : Fin 10000) (htag : tag.val = 6159) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6159 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06160 (tag : Fin 10000) (htag : tag.val = 6160) (k : Ring12) : tag.val = 6160 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06161 (tag : Fin 10000) (htag : tag.val = 6161) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6161 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06162 (tag : Fin 10000) (htag : tag.val = 6162) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6162 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06163 (tag : Fin 10000) (htag : tag.val = 6163) (x : State) (e : Event) (dr : Ring12) : tag.val = 6163 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06164 (tag : Fin 10000) (htag : tag.val = 6164) (x : State) (e : Event) (dr : Ring12) : tag.val = 6164 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06165 (tag : Fin 10000) (htag : tag.val = 6165) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6165 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06166 (tag : Fin 10000) (htag : tag.val = 6166) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6166 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06167 (tag : Fin 10000) (htag : tag.val = 6167) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6167 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06168 (tag : Fin 10000) (htag : tag.val = 6168) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6168 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06169 (tag : Fin 10000) (htag : tag.val = 6169) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6169 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06170 (tag : Fin 10000) (htag : tag.val = 6170) (k : Ring12) : tag.val = 6170 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06171 (tag : Fin 10000) (htag : tag.val = 6171) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6171 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06172 (tag : Fin 10000) (htag : tag.val = 6172) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6172 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06173 (tag : Fin 10000) (htag : tag.val = 6173) (x : State) (e : Event) (dr : Ring12) : tag.val = 6173 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06174 (tag : Fin 10000) (htag : tag.val = 6174) (x : State) (e : Event) (dr : Ring12) : tag.val = 6174 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06175 (tag : Fin 10000) (htag : tag.val = 6175) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6175 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06176 (tag : Fin 10000) (htag : tag.val = 6176) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6176 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06177 (tag : Fin 10000) (htag : tag.val = 6177) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6177 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06178 (tag : Fin 10000) (htag : tag.val = 6178) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6178 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06179 (tag : Fin 10000) (htag : tag.val = 6179) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6179 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06180 (tag : Fin 10000) (htag : tag.val = 6180) (k : Ring12) : tag.val = 6180 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06181 (tag : Fin 10000) (htag : tag.val = 6181) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6181 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06182 (tag : Fin 10000) (htag : tag.val = 6182) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6182 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06183 (tag : Fin 10000) (htag : tag.val = 6183) (x : State) (e : Event) (dr : Ring12) : tag.val = 6183 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06184 (tag : Fin 10000) (htag : tag.val = 6184) (x : State) (e : Event) (dr : Ring12) : tag.val = 6184 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06185 (tag : Fin 10000) (htag : tag.val = 6185) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6185 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06186 (tag : Fin 10000) (htag : tag.val = 6186) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6186 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06187 (tag : Fin 10000) (htag : tag.val = 6187) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6187 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06188 (tag : Fin 10000) (htag : tag.val = 6188) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6188 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06189 (tag : Fin 10000) (htag : tag.val = 6189) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6189 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06190 (tag : Fin 10000) (htag : tag.val = 6190) (k : Ring12) : tag.val = 6190 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06191 (tag : Fin 10000) (htag : tag.val = 6191) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6191 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06192 (tag : Fin 10000) (htag : tag.val = 6192) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6192 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06193 (tag : Fin 10000) (htag : tag.val = 6193) (x : State) (e : Event) (dr : Ring12) : tag.val = 6193 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06194 (tag : Fin 10000) (htag : tag.val = 6194) (x : State) (e : Event) (dr : Ring12) : tag.val = 6194 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06195 (tag : Fin 10000) (htag : tag.val = 6195) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6195 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06196 (tag : Fin 10000) (htag : tag.val = 6196) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6196 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06197 (tag : Fin 10000) (htag : tag.val = 6197) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6197 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06198 (tag : Fin 10000) (htag : tag.val = 6198) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6198 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06199 (tag : Fin 10000) (htag : tag.val = 6199) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6199 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
