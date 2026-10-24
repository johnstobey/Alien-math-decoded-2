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
theorem generated_08100 (tag : Fin 10000) (htag : tag.val = 8100) (k : Ring12) : tag.val = 8100 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08101 (tag : Fin 10000) (htag : tag.val = 8101) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8101 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08102 (tag : Fin 10000) (htag : tag.val = 8102) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8102 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08103 (tag : Fin 10000) (htag : tag.val = 8103) (x : State) (e : Event) (dr : Ring12) : tag.val = 8103 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08104 (tag : Fin 10000) (htag : tag.val = 8104) (x : State) (e : Event) (dr : Ring12) : tag.val = 8104 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08105 (tag : Fin 10000) (htag : tag.val = 8105) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8105 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08106 (tag : Fin 10000) (htag : tag.val = 8106) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8106 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08107 (tag : Fin 10000) (htag : tag.val = 8107) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8107 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08108 (tag : Fin 10000) (htag : tag.val = 8108) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8108 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08109 (tag : Fin 10000) (htag : tag.val = 8109) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8109 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08110 (tag : Fin 10000) (htag : tag.val = 8110) (k : Ring12) : tag.val = 8110 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08111 (tag : Fin 10000) (htag : tag.val = 8111) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8111 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08112 (tag : Fin 10000) (htag : tag.val = 8112) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8112 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08113 (tag : Fin 10000) (htag : tag.val = 8113) (x : State) (e : Event) (dr : Ring12) : tag.val = 8113 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08114 (tag : Fin 10000) (htag : tag.val = 8114) (x : State) (e : Event) (dr : Ring12) : tag.val = 8114 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08115 (tag : Fin 10000) (htag : tag.val = 8115) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8115 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08116 (tag : Fin 10000) (htag : tag.val = 8116) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8116 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08117 (tag : Fin 10000) (htag : tag.val = 8117) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8117 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08118 (tag : Fin 10000) (htag : tag.val = 8118) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8118 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08119 (tag : Fin 10000) (htag : tag.val = 8119) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8119 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08120 (tag : Fin 10000) (htag : tag.val = 8120) (k : Ring12) : tag.val = 8120 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08121 (tag : Fin 10000) (htag : tag.val = 8121) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8121 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08122 (tag : Fin 10000) (htag : tag.val = 8122) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8122 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08123 (tag : Fin 10000) (htag : tag.val = 8123) (x : State) (e : Event) (dr : Ring12) : tag.val = 8123 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08124 (tag : Fin 10000) (htag : tag.val = 8124) (x : State) (e : Event) (dr : Ring12) : tag.val = 8124 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08125 (tag : Fin 10000) (htag : tag.val = 8125) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8125 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08126 (tag : Fin 10000) (htag : tag.val = 8126) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8126 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08127 (tag : Fin 10000) (htag : tag.val = 8127) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8127 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08128 (tag : Fin 10000) (htag : tag.val = 8128) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8128 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08129 (tag : Fin 10000) (htag : tag.val = 8129) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8129 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08130 (tag : Fin 10000) (htag : tag.val = 8130) (k : Ring12) : tag.val = 8130 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08131 (tag : Fin 10000) (htag : tag.val = 8131) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8131 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08132 (tag : Fin 10000) (htag : tag.val = 8132) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8132 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08133 (tag : Fin 10000) (htag : tag.val = 8133) (x : State) (e : Event) (dr : Ring12) : tag.val = 8133 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08134 (tag : Fin 10000) (htag : tag.val = 8134) (x : State) (e : Event) (dr : Ring12) : tag.val = 8134 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08135 (tag : Fin 10000) (htag : tag.val = 8135) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8135 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08136 (tag : Fin 10000) (htag : tag.val = 8136) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8136 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08137 (tag : Fin 10000) (htag : tag.val = 8137) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8137 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08138 (tag : Fin 10000) (htag : tag.val = 8138) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8138 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08139 (tag : Fin 10000) (htag : tag.val = 8139) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8139 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08140 (tag : Fin 10000) (htag : tag.val = 8140) (k : Ring12) : tag.val = 8140 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08141 (tag : Fin 10000) (htag : tag.val = 8141) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8141 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08142 (tag : Fin 10000) (htag : tag.val = 8142) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8142 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08143 (tag : Fin 10000) (htag : tag.val = 8143) (x : State) (e : Event) (dr : Ring12) : tag.val = 8143 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08144 (tag : Fin 10000) (htag : tag.val = 8144) (x : State) (e : Event) (dr : Ring12) : tag.val = 8144 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08145 (tag : Fin 10000) (htag : tag.val = 8145) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8145 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08146 (tag : Fin 10000) (htag : tag.val = 8146) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8146 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08147 (tag : Fin 10000) (htag : tag.val = 8147) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8147 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08148 (tag : Fin 10000) (htag : tag.val = 8148) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8148 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08149 (tag : Fin 10000) (htag : tag.val = 8149) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8149 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08150 (tag : Fin 10000) (htag : tag.val = 8150) (k : Ring12) : tag.val = 8150 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08151 (tag : Fin 10000) (htag : tag.val = 8151) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8151 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08152 (tag : Fin 10000) (htag : tag.val = 8152) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8152 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08153 (tag : Fin 10000) (htag : tag.val = 8153) (x : State) (e : Event) (dr : Ring12) : tag.val = 8153 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08154 (tag : Fin 10000) (htag : tag.val = 8154) (x : State) (e : Event) (dr : Ring12) : tag.val = 8154 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08155 (tag : Fin 10000) (htag : tag.val = 8155) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8155 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08156 (tag : Fin 10000) (htag : tag.val = 8156) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8156 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08157 (tag : Fin 10000) (htag : tag.val = 8157) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8157 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08158 (tag : Fin 10000) (htag : tag.val = 8158) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8158 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08159 (tag : Fin 10000) (htag : tag.val = 8159) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8159 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08160 (tag : Fin 10000) (htag : tag.val = 8160) (k : Ring12) : tag.val = 8160 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08161 (tag : Fin 10000) (htag : tag.val = 8161) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8161 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08162 (tag : Fin 10000) (htag : tag.val = 8162) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8162 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08163 (tag : Fin 10000) (htag : tag.val = 8163) (x : State) (e : Event) (dr : Ring12) : tag.val = 8163 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08164 (tag : Fin 10000) (htag : tag.val = 8164) (x : State) (e : Event) (dr : Ring12) : tag.val = 8164 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08165 (tag : Fin 10000) (htag : tag.val = 8165) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8165 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08166 (tag : Fin 10000) (htag : tag.val = 8166) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8166 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08167 (tag : Fin 10000) (htag : tag.val = 8167) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8167 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08168 (tag : Fin 10000) (htag : tag.val = 8168) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8168 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08169 (tag : Fin 10000) (htag : tag.val = 8169) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8169 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08170 (tag : Fin 10000) (htag : tag.val = 8170) (k : Ring12) : tag.val = 8170 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08171 (tag : Fin 10000) (htag : tag.val = 8171) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8171 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08172 (tag : Fin 10000) (htag : tag.val = 8172) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8172 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08173 (tag : Fin 10000) (htag : tag.val = 8173) (x : State) (e : Event) (dr : Ring12) : tag.val = 8173 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08174 (tag : Fin 10000) (htag : tag.val = 8174) (x : State) (e : Event) (dr : Ring12) : tag.val = 8174 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08175 (tag : Fin 10000) (htag : tag.val = 8175) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8175 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08176 (tag : Fin 10000) (htag : tag.val = 8176) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8176 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08177 (tag : Fin 10000) (htag : tag.val = 8177) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8177 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08178 (tag : Fin 10000) (htag : tag.val = 8178) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8178 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08179 (tag : Fin 10000) (htag : tag.val = 8179) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8179 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08180 (tag : Fin 10000) (htag : tag.val = 8180) (k : Ring12) : tag.val = 8180 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08181 (tag : Fin 10000) (htag : tag.val = 8181) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8181 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08182 (tag : Fin 10000) (htag : tag.val = 8182) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8182 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08183 (tag : Fin 10000) (htag : tag.val = 8183) (x : State) (e : Event) (dr : Ring12) : tag.val = 8183 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08184 (tag : Fin 10000) (htag : tag.val = 8184) (x : State) (e : Event) (dr : Ring12) : tag.val = 8184 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08185 (tag : Fin 10000) (htag : tag.val = 8185) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8185 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08186 (tag : Fin 10000) (htag : tag.val = 8186) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8186 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08187 (tag : Fin 10000) (htag : tag.val = 8187) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8187 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08188 (tag : Fin 10000) (htag : tag.val = 8188) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8188 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08189 (tag : Fin 10000) (htag : tag.val = 8189) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8189 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08190 (tag : Fin 10000) (htag : tag.val = 8190) (k : Ring12) : tag.val = 8190 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08191 (tag : Fin 10000) (htag : tag.val = 8191) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8191 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08192 (tag : Fin 10000) (htag : tag.val = 8192) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8192 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08193 (tag : Fin 10000) (htag : tag.val = 8193) (x : State) (e : Event) (dr : Ring12) : tag.val = 8193 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08194 (tag : Fin 10000) (htag : tag.val = 8194) (x : State) (e : Event) (dr : Ring12) : tag.val = 8194 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08195 (tag : Fin 10000) (htag : tag.val = 8195) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8195 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08196 (tag : Fin 10000) (htag : tag.val = 8196) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8196 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08197 (tag : Fin 10000) (htag : tag.val = 8197) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8197 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08198 (tag : Fin 10000) (htag : tag.val = 8198) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8198 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08199 (tag : Fin 10000) (htag : tag.val = 8199) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8199 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
