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
theorem generated_01100 (tag : Fin 10000) (htag : tag.val = 1100) (k : Ring12) : tag.val = 1100 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01101 (tag : Fin 10000) (htag : tag.val = 1101) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1101 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01102 (tag : Fin 10000) (htag : tag.val = 1102) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1102 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01103 (tag : Fin 10000) (htag : tag.val = 1103) (x : State) (e : Event) (dr : Ring12) : tag.val = 1103 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01104 (tag : Fin 10000) (htag : tag.val = 1104) (x : State) (e : Event) (dr : Ring12) : tag.val = 1104 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01105 (tag : Fin 10000) (htag : tag.val = 1105) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1105 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01106 (tag : Fin 10000) (htag : tag.val = 1106) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1106 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01107 (tag : Fin 10000) (htag : tag.val = 1107) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1107 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01108 (tag : Fin 10000) (htag : tag.val = 1108) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1108 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01109 (tag : Fin 10000) (htag : tag.val = 1109) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1109 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01110 (tag : Fin 10000) (htag : tag.val = 1110) (k : Ring12) : tag.val = 1110 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01111 (tag : Fin 10000) (htag : tag.val = 1111) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1111 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01112 (tag : Fin 10000) (htag : tag.val = 1112) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1112 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01113 (tag : Fin 10000) (htag : tag.val = 1113) (x : State) (e : Event) (dr : Ring12) : tag.val = 1113 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01114 (tag : Fin 10000) (htag : tag.val = 1114) (x : State) (e : Event) (dr : Ring12) : tag.val = 1114 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01115 (tag : Fin 10000) (htag : tag.val = 1115) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1115 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01116 (tag : Fin 10000) (htag : tag.val = 1116) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1116 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01117 (tag : Fin 10000) (htag : tag.val = 1117) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1117 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01118 (tag : Fin 10000) (htag : tag.val = 1118) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1118 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01119 (tag : Fin 10000) (htag : tag.val = 1119) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1119 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01120 (tag : Fin 10000) (htag : tag.val = 1120) (k : Ring12) : tag.val = 1120 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01121 (tag : Fin 10000) (htag : tag.val = 1121) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1121 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01122 (tag : Fin 10000) (htag : tag.val = 1122) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1122 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01123 (tag : Fin 10000) (htag : tag.val = 1123) (x : State) (e : Event) (dr : Ring12) : tag.val = 1123 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01124 (tag : Fin 10000) (htag : tag.val = 1124) (x : State) (e : Event) (dr : Ring12) : tag.val = 1124 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01125 (tag : Fin 10000) (htag : tag.val = 1125) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1125 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01126 (tag : Fin 10000) (htag : tag.val = 1126) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1126 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01127 (tag : Fin 10000) (htag : tag.val = 1127) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1127 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01128 (tag : Fin 10000) (htag : tag.val = 1128) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1128 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01129 (tag : Fin 10000) (htag : tag.val = 1129) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1129 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01130 (tag : Fin 10000) (htag : tag.val = 1130) (k : Ring12) : tag.val = 1130 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01131 (tag : Fin 10000) (htag : tag.val = 1131) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1131 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01132 (tag : Fin 10000) (htag : tag.val = 1132) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1132 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01133 (tag : Fin 10000) (htag : tag.val = 1133) (x : State) (e : Event) (dr : Ring12) : tag.val = 1133 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01134 (tag : Fin 10000) (htag : tag.val = 1134) (x : State) (e : Event) (dr : Ring12) : tag.val = 1134 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01135 (tag : Fin 10000) (htag : tag.val = 1135) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1135 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01136 (tag : Fin 10000) (htag : tag.val = 1136) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1136 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01137 (tag : Fin 10000) (htag : tag.val = 1137) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1137 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01138 (tag : Fin 10000) (htag : tag.val = 1138) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1138 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01139 (tag : Fin 10000) (htag : tag.val = 1139) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1139 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01140 (tag : Fin 10000) (htag : tag.val = 1140) (k : Ring12) : tag.val = 1140 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01141 (tag : Fin 10000) (htag : tag.val = 1141) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1141 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01142 (tag : Fin 10000) (htag : tag.val = 1142) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1142 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01143 (tag : Fin 10000) (htag : tag.val = 1143) (x : State) (e : Event) (dr : Ring12) : tag.val = 1143 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01144 (tag : Fin 10000) (htag : tag.val = 1144) (x : State) (e : Event) (dr : Ring12) : tag.val = 1144 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01145 (tag : Fin 10000) (htag : tag.val = 1145) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1145 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01146 (tag : Fin 10000) (htag : tag.val = 1146) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1146 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01147 (tag : Fin 10000) (htag : tag.val = 1147) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1147 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01148 (tag : Fin 10000) (htag : tag.val = 1148) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1148 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01149 (tag : Fin 10000) (htag : tag.val = 1149) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1149 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01150 (tag : Fin 10000) (htag : tag.val = 1150) (k : Ring12) : tag.val = 1150 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01151 (tag : Fin 10000) (htag : tag.val = 1151) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1151 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01152 (tag : Fin 10000) (htag : tag.val = 1152) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1152 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01153 (tag : Fin 10000) (htag : tag.val = 1153) (x : State) (e : Event) (dr : Ring12) : tag.val = 1153 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01154 (tag : Fin 10000) (htag : tag.val = 1154) (x : State) (e : Event) (dr : Ring12) : tag.val = 1154 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01155 (tag : Fin 10000) (htag : tag.val = 1155) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1155 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01156 (tag : Fin 10000) (htag : tag.val = 1156) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1156 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01157 (tag : Fin 10000) (htag : tag.val = 1157) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1157 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01158 (tag : Fin 10000) (htag : tag.val = 1158) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1158 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01159 (tag : Fin 10000) (htag : tag.val = 1159) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1159 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01160 (tag : Fin 10000) (htag : tag.val = 1160) (k : Ring12) : tag.val = 1160 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01161 (tag : Fin 10000) (htag : tag.val = 1161) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1161 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01162 (tag : Fin 10000) (htag : tag.val = 1162) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1162 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01163 (tag : Fin 10000) (htag : tag.val = 1163) (x : State) (e : Event) (dr : Ring12) : tag.val = 1163 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01164 (tag : Fin 10000) (htag : tag.val = 1164) (x : State) (e : Event) (dr : Ring12) : tag.val = 1164 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01165 (tag : Fin 10000) (htag : tag.val = 1165) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1165 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01166 (tag : Fin 10000) (htag : tag.val = 1166) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1166 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01167 (tag : Fin 10000) (htag : tag.val = 1167) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1167 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01168 (tag : Fin 10000) (htag : tag.val = 1168) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1168 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01169 (tag : Fin 10000) (htag : tag.val = 1169) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1169 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01170 (tag : Fin 10000) (htag : tag.val = 1170) (k : Ring12) : tag.val = 1170 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01171 (tag : Fin 10000) (htag : tag.val = 1171) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1171 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01172 (tag : Fin 10000) (htag : tag.val = 1172) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1172 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01173 (tag : Fin 10000) (htag : tag.val = 1173) (x : State) (e : Event) (dr : Ring12) : tag.val = 1173 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01174 (tag : Fin 10000) (htag : tag.val = 1174) (x : State) (e : Event) (dr : Ring12) : tag.val = 1174 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01175 (tag : Fin 10000) (htag : tag.val = 1175) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1175 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01176 (tag : Fin 10000) (htag : tag.val = 1176) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1176 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01177 (tag : Fin 10000) (htag : tag.val = 1177) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1177 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01178 (tag : Fin 10000) (htag : tag.val = 1178) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1178 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01179 (tag : Fin 10000) (htag : tag.val = 1179) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1179 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01180 (tag : Fin 10000) (htag : tag.val = 1180) (k : Ring12) : tag.val = 1180 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01181 (tag : Fin 10000) (htag : tag.val = 1181) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1181 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01182 (tag : Fin 10000) (htag : tag.val = 1182) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1182 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01183 (tag : Fin 10000) (htag : tag.val = 1183) (x : State) (e : Event) (dr : Ring12) : tag.val = 1183 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01184 (tag : Fin 10000) (htag : tag.val = 1184) (x : State) (e : Event) (dr : Ring12) : tag.val = 1184 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01185 (tag : Fin 10000) (htag : tag.val = 1185) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1185 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01186 (tag : Fin 10000) (htag : tag.val = 1186) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1186 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01187 (tag : Fin 10000) (htag : tag.val = 1187) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1187 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01188 (tag : Fin 10000) (htag : tag.val = 1188) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1188 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01189 (tag : Fin 10000) (htag : tag.val = 1189) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1189 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01190 (tag : Fin 10000) (htag : tag.val = 1190) (k : Ring12) : tag.val = 1190 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01191 (tag : Fin 10000) (htag : tag.val = 1191) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1191 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01192 (tag : Fin 10000) (htag : tag.val = 1192) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1192 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01193 (tag : Fin 10000) (htag : tag.val = 1193) (x : State) (e : Event) (dr : Ring12) : tag.val = 1193 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01194 (tag : Fin 10000) (htag : tag.val = 1194) (x : State) (e : Event) (dr : Ring12) : tag.val = 1194 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01195 (tag : Fin 10000) (htag : tag.val = 1195) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1195 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01196 (tag : Fin 10000) (htag : tag.val = 1196) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1196 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01197 (tag : Fin 10000) (htag : tag.val = 1197) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1197 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01198 (tag : Fin 10000) (htag : tag.val = 1198) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1198 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01199 (tag : Fin 10000) (htag : tag.val = 1199) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1199 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
