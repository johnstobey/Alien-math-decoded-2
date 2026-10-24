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
theorem generated_00100 (tag : Fin 10000) (htag : tag.val = 100) (k : Ring12) : tag.val = 100 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00101 (tag : Fin 10000) (htag : tag.val = 101) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 101 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00102 (tag : Fin 10000) (htag : tag.val = 102) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 102 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00103 (tag : Fin 10000) (htag : tag.val = 103) (x : State) (e : Event) (dr : Ring12) : tag.val = 103 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00104 (tag : Fin 10000) (htag : tag.val = 104) (x : State) (e : Event) (dr : Ring12) : tag.val = 104 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00105 (tag : Fin 10000) (htag : tag.val = 105) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 105 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00106 (tag : Fin 10000) (htag : tag.val = 106) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 106 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00107 (tag : Fin 10000) (htag : tag.val = 107) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 107 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00108 (tag : Fin 10000) (htag : tag.val = 108) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 108 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00109 (tag : Fin 10000) (htag : tag.val = 109) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 109 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00110 (tag : Fin 10000) (htag : tag.val = 110) (k : Ring12) : tag.val = 110 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00111 (tag : Fin 10000) (htag : tag.val = 111) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 111 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00112 (tag : Fin 10000) (htag : tag.val = 112) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 112 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00113 (tag : Fin 10000) (htag : tag.val = 113) (x : State) (e : Event) (dr : Ring12) : tag.val = 113 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00114 (tag : Fin 10000) (htag : tag.val = 114) (x : State) (e : Event) (dr : Ring12) : tag.val = 114 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00115 (tag : Fin 10000) (htag : tag.val = 115) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 115 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00116 (tag : Fin 10000) (htag : tag.val = 116) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 116 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00117 (tag : Fin 10000) (htag : tag.val = 117) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 117 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00118 (tag : Fin 10000) (htag : tag.val = 118) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 118 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00119 (tag : Fin 10000) (htag : tag.val = 119) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 119 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00120 (tag : Fin 10000) (htag : tag.val = 120) (k : Ring12) : tag.val = 120 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00121 (tag : Fin 10000) (htag : tag.val = 121) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 121 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00122 (tag : Fin 10000) (htag : tag.val = 122) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 122 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00123 (tag : Fin 10000) (htag : tag.val = 123) (x : State) (e : Event) (dr : Ring12) : tag.val = 123 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00124 (tag : Fin 10000) (htag : tag.val = 124) (x : State) (e : Event) (dr : Ring12) : tag.val = 124 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00125 (tag : Fin 10000) (htag : tag.val = 125) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 125 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00126 (tag : Fin 10000) (htag : tag.val = 126) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 126 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00127 (tag : Fin 10000) (htag : tag.val = 127) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 127 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00128 (tag : Fin 10000) (htag : tag.val = 128) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 128 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00129 (tag : Fin 10000) (htag : tag.val = 129) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 129 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00130 (tag : Fin 10000) (htag : tag.val = 130) (k : Ring12) : tag.val = 130 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00131 (tag : Fin 10000) (htag : tag.val = 131) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 131 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00132 (tag : Fin 10000) (htag : tag.val = 132) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 132 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00133 (tag : Fin 10000) (htag : tag.val = 133) (x : State) (e : Event) (dr : Ring12) : tag.val = 133 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00134 (tag : Fin 10000) (htag : tag.val = 134) (x : State) (e : Event) (dr : Ring12) : tag.val = 134 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00135 (tag : Fin 10000) (htag : tag.val = 135) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 135 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00136 (tag : Fin 10000) (htag : tag.val = 136) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 136 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00137 (tag : Fin 10000) (htag : tag.val = 137) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 137 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00138 (tag : Fin 10000) (htag : tag.val = 138) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 138 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00139 (tag : Fin 10000) (htag : tag.val = 139) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 139 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00140 (tag : Fin 10000) (htag : tag.val = 140) (k : Ring12) : tag.val = 140 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00141 (tag : Fin 10000) (htag : tag.val = 141) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 141 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00142 (tag : Fin 10000) (htag : tag.val = 142) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 142 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00143 (tag : Fin 10000) (htag : tag.val = 143) (x : State) (e : Event) (dr : Ring12) : tag.val = 143 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00144 (tag : Fin 10000) (htag : tag.val = 144) (x : State) (e : Event) (dr : Ring12) : tag.val = 144 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00145 (tag : Fin 10000) (htag : tag.val = 145) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 145 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00146 (tag : Fin 10000) (htag : tag.val = 146) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 146 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00147 (tag : Fin 10000) (htag : tag.val = 147) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 147 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00148 (tag : Fin 10000) (htag : tag.val = 148) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 148 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00149 (tag : Fin 10000) (htag : tag.val = 149) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 149 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00150 (tag : Fin 10000) (htag : tag.val = 150) (k : Ring12) : tag.val = 150 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00151 (tag : Fin 10000) (htag : tag.val = 151) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 151 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00152 (tag : Fin 10000) (htag : tag.val = 152) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 152 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00153 (tag : Fin 10000) (htag : tag.val = 153) (x : State) (e : Event) (dr : Ring12) : tag.val = 153 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00154 (tag : Fin 10000) (htag : tag.val = 154) (x : State) (e : Event) (dr : Ring12) : tag.val = 154 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00155 (tag : Fin 10000) (htag : tag.val = 155) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 155 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00156 (tag : Fin 10000) (htag : tag.val = 156) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 156 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00157 (tag : Fin 10000) (htag : tag.val = 157) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 157 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00158 (tag : Fin 10000) (htag : tag.val = 158) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 158 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00159 (tag : Fin 10000) (htag : tag.val = 159) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 159 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00160 (tag : Fin 10000) (htag : tag.val = 160) (k : Ring12) : tag.val = 160 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00161 (tag : Fin 10000) (htag : tag.val = 161) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 161 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00162 (tag : Fin 10000) (htag : tag.val = 162) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 162 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00163 (tag : Fin 10000) (htag : tag.val = 163) (x : State) (e : Event) (dr : Ring12) : tag.val = 163 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00164 (tag : Fin 10000) (htag : tag.val = 164) (x : State) (e : Event) (dr : Ring12) : tag.val = 164 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00165 (tag : Fin 10000) (htag : tag.val = 165) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 165 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00166 (tag : Fin 10000) (htag : tag.val = 166) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 166 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00167 (tag : Fin 10000) (htag : tag.val = 167) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 167 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00168 (tag : Fin 10000) (htag : tag.val = 168) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 168 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00169 (tag : Fin 10000) (htag : tag.val = 169) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 169 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00170 (tag : Fin 10000) (htag : tag.val = 170) (k : Ring12) : tag.val = 170 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00171 (tag : Fin 10000) (htag : tag.val = 171) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 171 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00172 (tag : Fin 10000) (htag : tag.val = 172) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 172 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00173 (tag : Fin 10000) (htag : tag.val = 173) (x : State) (e : Event) (dr : Ring12) : tag.val = 173 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00174 (tag : Fin 10000) (htag : tag.val = 174) (x : State) (e : Event) (dr : Ring12) : tag.val = 174 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00175 (tag : Fin 10000) (htag : tag.val = 175) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 175 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00176 (tag : Fin 10000) (htag : tag.val = 176) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 176 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00177 (tag : Fin 10000) (htag : tag.val = 177) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 177 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00178 (tag : Fin 10000) (htag : tag.val = 178) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 178 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00179 (tag : Fin 10000) (htag : tag.val = 179) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 179 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00180 (tag : Fin 10000) (htag : tag.val = 180) (k : Ring12) : tag.val = 180 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00181 (tag : Fin 10000) (htag : tag.val = 181) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 181 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00182 (tag : Fin 10000) (htag : tag.val = 182) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 182 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00183 (tag : Fin 10000) (htag : tag.val = 183) (x : State) (e : Event) (dr : Ring12) : tag.val = 183 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00184 (tag : Fin 10000) (htag : tag.val = 184) (x : State) (e : Event) (dr : Ring12) : tag.val = 184 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00185 (tag : Fin 10000) (htag : tag.val = 185) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 185 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00186 (tag : Fin 10000) (htag : tag.val = 186) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 186 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00187 (tag : Fin 10000) (htag : tag.val = 187) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 187 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00188 (tag : Fin 10000) (htag : tag.val = 188) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 188 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00189 (tag : Fin 10000) (htag : tag.val = 189) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 189 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00190 (tag : Fin 10000) (htag : tag.val = 190) (k : Ring12) : tag.val = 190 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00191 (tag : Fin 10000) (htag : tag.val = 191) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 191 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00192 (tag : Fin 10000) (htag : tag.val = 192) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 192 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00193 (tag : Fin 10000) (htag : tag.val = 193) (x : State) (e : Event) (dr : Ring12) : tag.val = 193 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00194 (tag : Fin 10000) (htag : tag.val = 194) (x : State) (e : Event) (dr : Ring12) : tag.val = 194 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00195 (tag : Fin 10000) (htag : tag.val = 195) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 195 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00196 (tag : Fin 10000) (htag : tag.val = 196) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 196 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00197 (tag : Fin 10000) (htag : tag.val = 197) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 197 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00198 (tag : Fin 10000) (htag : tag.val = 198) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 198 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00199 (tag : Fin 10000) (htag : tag.val = 199) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 199 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
