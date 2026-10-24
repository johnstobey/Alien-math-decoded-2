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
theorem generated_07100 (tag : Fin 10000) (htag : tag.val = 7100) (k : Ring12) : tag.val = 7100 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07101 (tag : Fin 10000) (htag : tag.val = 7101) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7101 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07102 (tag : Fin 10000) (htag : tag.val = 7102) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7102 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07103 (tag : Fin 10000) (htag : tag.val = 7103) (x : State) (e : Event) (dr : Ring12) : tag.val = 7103 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07104 (tag : Fin 10000) (htag : tag.val = 7104) (x : State) (e : Event) (dr : Ring12) : tag.val = 7104 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07105 (tag : Fin 10000) (htag : tag.val = 7105) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7105 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07106 (tag : Fin 10000) (htag : tag.val = 7106) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7106 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07107 (tag : Fin 10000) (htag : tag.val = 7107) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7107 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07108 (tag : Fin 10000) (htag : tag.val = 7108) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7108 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07109 (tag : Fin 10000) (htag : tag.val = 7109) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7109 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07110 (tag : Fin 10000) (htag : tag.val = 7110) (k : Ring12) : tag.val = 7110 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07111 (tag : Fin 10000) (htag : tag.val = 7111) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7111 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07112 (tag : Fin 10000) (htag : tag.val = 7112) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7112 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07113 (tag : Fin 10000) (htag : tag.val = 7113) (x : State) (e : Event) (dr : Ring12) : tag.val = 7113 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07114 (tag : Fin 10000) (htag : tag.val = 7114) (x : State) (e : Event) (dr : Ring12) : tag.val = 7114 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07115 (tag : Fin 10000) (htag : tag.val = 7115) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7115 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07116 (tag : Fin 10000) (htag : tag.val = 7116) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7116 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07117 (tag : Fin 10000) (htag : tag.val = 7117) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7117 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07118 (tag : Fin 10000) (htag : tag.val = 7118) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7118 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07119 (tag : Fin 10000) (htag : tag.val = 7119) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7119 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07120 (tag : Fin 10000) (htag : tag.val = 7120) (k : Ring12) : tag.val = 7120 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07121 (tag : Fin 10000) (htag : tag.val = 7121) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7121 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07122 (tag : Fin 10000) (htag : tag.val = 7122) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7122 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07123 (tag : Fin 10000) (htag : tag.val = 7123) (x : State) (e : Event) (dr : Ring12) : tag.val = 7123 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07124 (tag : Fin 10000) (htag : tag.val = 7124) (x : State) (e : Event) (dr : Ring12) : tag.val = 7124 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07125 (tag : Fin 10000) (htag : tag.val = 7125) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7125 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07126 (tag : Fin 10000) (htag : tag.val = 7126) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7126 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07127 (tag : Fin 10000) (htag : tag.val = 7127) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7127 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07128 (tag : Fin 10000) (htag : tag.val = 7128) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7128 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07129 (tag : Fin 10000) (htag : tag.val = 7129) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7129 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07130 (tag : Fin 10000) (htag : tag.val = 7130) (k : Ring12) : tag.val = 7130 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07131 (tag : Fin 10000) (htag : tag.val = 7131) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7131 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07132 (tag : Fin 10000) (htag : tag.val = 7132) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7132 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07133 (tag : Fin 10000) (htag : tag.val = 7133) (x : State) (e : Event) (dr : Ring12) : tag.val = 7133 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07134 (tag : Fin 10000) (htag : tag.val = 7134) (x : State) (e : Event) (dr : Ring12) : tag.val = 7134 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07135 (tag : Fin 10000) (htag : tag.val = 7135) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7135 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07136 (tag : Fin 10000) (htag : tag.val = 7136) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7136 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07137 (tag : Fin 10000) (htag : tag.val = 7137) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7137 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07138 (tag : Fin 10000) (htag : tag.val = 7138) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7138 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07139 (tag : Fin 10000) (htag : tag.val = 7139) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7139 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07140 (tag : Fin 10000) (htag : tag.val = 7140) (k : Ring12) : tag.val = 7140 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07141 (tag : Fin 10000) (htag : tag.val = 7141) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7141 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07142 (tag : Fin 10000) (htag : tag.val = 7142) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7142 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07143 (tag : Fin 10000) (htag : tag.val = 7143) (x : State) (e : Event) (dr : Ring12) : tag.val = 7143 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07144 (tag : Fin 10000) (htag : tag.val = 7144) (x : State) (e : Event) (dr : Ring12) : tag.val = 7144 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07145 (tag : Fin 10000) (htag : tag.val = 7145) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7145 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07146 (tag : Fin 10000) (htag : tag.val = 7146) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7146 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07147 (tag : Fin 10000) (htag : tag.val = 7147) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7147 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07148 (tag : Fin 10000) (htag : tag.val = 7148) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7148 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07149 (tag : Fin 10000) (htag : tag.val = 7149) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7149 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07150 (tag : Fin 10000) (htag : tag.val = 7150) (k : Ring12) : tag.val = 7150 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07151 (tag : Fin 10000) (htag : tag.val = 7151) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7151 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07152 (tag : Fin 10000) (htag : tag.val = 7152) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7152 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07153 (tag : Fin 10000) (htag : tag.val = 7153) (x : State) (e : Event) (dr : Ring12) : tag.val = 7153 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07154 (tag : Fin 10000) (htag : tag.val = 7154) (x : State) (e : Event) (dr : Ring12) : tag.val = 7154 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07155 (tag : Fin 10000) (htag : tag.val = 7155) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7155 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07156 (tag : Fin 10000) (htag : tag.val = 7156) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7156 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07157 (tag : Fin 10000) (htag : tag.val = 7157) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7157 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07158 (tag : Fin 10000) (htag : tag.val = 7158) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7158 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07159 (tag : Fin 10000) (htag : tag.val = 7159) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7159 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07160 (tag : Fin 10000) (htag : tag.val = 7160) (k : Ring12) : tag.val = 7160 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07161 (tag : Fin 10000) (htag : tag.val = 7161) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7161 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07162 (tag : Fin 10000) (htag : tag.val = 7162) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7162 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07163 (tag : Fin 10000) (htag : tag.val = 7163) (x : State) (e : Event) (dr : Ring12) : tag.val = 7163 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07164 (tag : Fin 10000) (htag : tag.val = 7164) (x : State) (e : Event) (dr : Ring12) : tag.val = 7164 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07165 (tag : Fin 10000) (htag : tag.val = 7165) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7165 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07166 (tag : Fin 10000) (htag : tag.val = 7166) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7166 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07167 (tag : Fin 10000) (htag : tag.val = 7167) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7167 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07168 (tag : Fin 10000) (htag : tag.val = 7168) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7168 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07169 (tag : Fin 10000) (htag : tag.val = 7169) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7169 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07170 (tag : Fin 10000) (htag : tag.val = 7170) (k : Ring12) : tag.val = 7170 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07171 (tag : Fin 10000) (htag : tag.val = 7171) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7171 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07172 (tag : Fin 10000) (htag : tag.val = 7172) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7172 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07173 (tag : Fin 10000) (htag : tag.val = 7173) (x : State) (e : Event) (dr : Ring12) : tag.val = 7173 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07174 (tag : Fin 10000) (htag : tag.val = 7174) (x : State) (e : Event) (dr : Ring12) : tag.val = 7174 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07175 (tag : Fin 10000) (htag : tag.val = 7175) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7175 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07176 (tag : Fin 10000) (htag : tag.val = 7176) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7176 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07177 (tag : Fin 10000) (htag : tag.val = 7177) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7177 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07178 (tag : Fin 10000) (htag : tag.val = 7178) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7178 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07179 (tag : Fin 10000) (htag : tag.val = 7179) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7179 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07180 (tag : Fin 10000) (htag : tag.val = 7180) (k : Ring12) : tag.val = 7180 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07181 (tag : Fin 10000) (htag : tag.val = 7181) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7181 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07182 (tag : Fin 10000) (htag : tag.val = 7182) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7182 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07183 (tag : Fin 10000) (htag : tag.val = 7183) (x : State) (e : Event) (dr : Ring12) : tag.val = 7183 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07184 (tag : Fin 10000) (htag : tag.val = 7184) (x : State) (e : Event) (dr : Ring12) : tag.val = 7184 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07185 (tag : Fin 10000) (htag : tag.val = 7185) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7185 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07186 (tag : Fin 10000) (htag : tag.val = 7186) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7186 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07187 (tag : Fin 10000) (htag : tag.val = 7187) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7187 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07188 (tag : Fin 10000) (htag : tag.val = 7188) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7188 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07189 (tag : Fin 10000) (htag : tag.val = 7189) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7189 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07190 (tag : Fin 10000) (htag : tag.val = 7190) (k : Ring12) : tag.val = 7190 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07191 (tag : Fin 10000) (htag : tag.val = 7191) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7191 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07192 (tag : Fin 10000) (htag : tag.val = 7192) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7192 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07193 (tag : Fin 10000) (htag : tag.val = 7193) (x : State) (e : Event) (dr : Ring12) : tag.val = 7193 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07194 (tag : Fin 10000) (htag : tag.val = 7194) (x : State) (e : Event) (dr : Ring12) : tag.val = 7194 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07195 (tag : Fin 10000) (htag : tag.val = 7195) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7195 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07196 (tag : Fin 10000) (htag : tag.val = 7196) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7196 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07197 (tag : Fin 10000) (htag : tag.val = 7197) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7197 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07198 (tag : Fin 10000) (htag : tag.val = 7198) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7198 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07199 (tag : Fin 10000) (htag : tag.val = 7199) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7199 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
