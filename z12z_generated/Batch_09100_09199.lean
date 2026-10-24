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
theorem generated_09100 (tag : Fin 10000) (htag : tag.val = 9100) (k : Ring12) : tag.val = 9100 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09101 (tag : Fin 10000) (htag : tag.val = 9101) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9101 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09102 (tag : Fin 10000) (htag : tag.val = 9102) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9102 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09103 (tag : Fin 10000) (htag : tag.val = 9103) (x : State) (e : Event) (dr : Ring12) : tag.val = 9103 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09104 (tag : Fin 10000) (htag : tag.val = 9104) (x : State) (e : Event) (dr : Ring12) : tag.val = 9104 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09105 (tag : Fin 10000) (htag : tag.val = 9105) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9105 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09106 (tag : Fin 10000) (htag : tag.val = 9106) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9106 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09107 (tag : Fin 10000) (htag : tag.val = 9107) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9107 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09108 (tag : Fin 10000) (htag : tag.val = 9108) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9108 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09109 (tag : Fin 10000) (htag : tag.val = 9109) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9109 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09110 (tag : Fin 10000) (htag : tag.val = 9110) (k : Ring12) : tag.val = 9110 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09111 (tag : Fin 10000) (htag : tag.val = 9111) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9111 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09112 (tag : Fin 10000) (htag : tag.val = 9112) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9112 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09113 (tag : Fin 10000) (htag : tag.val = 9113) (x : State) (e : Event) (dr : Ring12) : tag.val = 9113 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09114 (tag : Fin 10000) (htag : tag.val = 9114) (x : State) (e : Event) (dr : Ring12) : tag.val = 9114 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09115 (tag : Fin 10000) (htag : tag.val = 9115) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9115 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09116 (tag : Fin 10000) (htag : tag.val = 9116) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9116 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09117 (tag : Fin 10000) (htag : tag.val = 9117) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9117 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09118 (tag : Fin 10000) (htag : tag.val = 9118) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9118 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09119 (tag : Fin 10000) (htag : tag.val = 9119) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9119 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09120 (tag : Fin 10000) (htag : tag.val = 9120) (k : Ring12) : tag.val = 9120 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09121 (tag : Fin 10000) (htag : tag.val = 9121) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9121 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09122 (tag : Fin 10000) (htag : tag.val = 9122) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9122 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09123 (tag : Fin 10000) (htag : tag.val = 9123) (x : State) (e : Event) (dr : Ring12) : tag.val = 9123 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09124 (tag : Fin 10000) (htag : tag.val = 9124) (x : State) (e : Event) (dr : Ring12) : tag.val = 9124 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09125 (tag : Fin 10000) (htag : tag.val = 9125) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9125 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09126 (tag : Fin 10000) (htag : tag.val = 9126) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9126 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09127 (tag : Fin 10000) (htag : tag.val = 9127) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9127 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09128 (tag : Fin 10000) (htag : tag.val = 9128) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9128 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09129 (tag : Fin 10000) (htag : tag.val = 9129) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9129 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09130 (tag : Fin 10000) (htag : tag.val = 9130) (k : Ring12) : tag.val = 9130 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09131 (tag : Fin 10000) (htag : tag.val = 9131) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9131 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09132 (tag : Fin 10000) (htag : tag.val = 9132) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9132 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09133 (tag : Fin 10000) (htag : tag.val = 9133) (x : State) (e : Event) (dr : Ring12) : tag.val = 9133 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09134 (tag : Fin 10000) (htag : tag.val = 9134) (x : State) (e : Event) (dr : Ring12) : tag.val = 9134 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09135 (tag : Fin 10000) (htag : tag.val = 9135) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9135 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09136 (tag : Fin 10000) (htag : tag.val = 9136) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9136 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09137 (tag : Fin 10000) (htag : tag.val = 9137) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9137 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09138 (tag : Fin 10000) (htag : tag.val = 9138) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9138 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09139 (tag : Fin 10000) (htag : tag.val = 9139) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9139 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09140 (tag : Fin 10000) (htag : tag.val = 9140) (k : Ring12) : tag.val = 9140 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09141 (tag : Fin 10000) (htag : tag.val = 9141) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9141 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09142 (tag : Fin 10000) (htag : tag.val = 9142) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9142 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09143 (tag : Fin 10000) (htag : tag.val = 9143) (x : State) (e : Event) (dr : Ring12) : tag.val = 9143 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09144 (tag : Fin 10000) (htag : tag.val = 9144) (x : State) (e : Event) (dr : Ring12) : tag.val = 9144 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09145 (tag : Fin 10000) (htag : tag.val = 9145) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9145 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09146 (tag : Fin 10000) (htag : tag.val = 9146) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9146 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09147 (tag : Fin 10000) (htag : tag.val = 9147) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9147 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09148 (tag : Fin 10000) (htag : tag.val = 9148) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9148 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09149 (tag : Fin 10000) (htag : tag.val = 9149) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9149 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09150 (tag : Fin 10000) (htag : tag.val = 9150) (k : Ring12) : tag.val = 9150 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09151 (tag : Fin 10000) (htag : tag.val = 9151) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9151 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09152 (tag : Fin 10000) (htag : tag.val = 9152) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9152 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09153 (tag : Fin 10000) (htag : tag.val = 9153) (x : State) (e : Event) (dr : Ring12) : tag.val = 9153 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09154 (tag : Fin 10000) (htag : tag.val = 9154) (x : State) (e : Event) (dr : Ring12) : tag.val = 9154 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09155 (tag : Fin 10000) (htag : tag.val = 9155) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9155 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09156 (tag : Fin 10000) (htag : tag.val = 9156) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9156 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09157 (tag : Fin 10000) (htag : tag.val = 9157) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9157 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09158 (tag : Fin 10000) (htag : tag.val = 9158) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9158 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09159 (tag : Fin 10000) (htag : tag.val = 9159) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9159 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09160 (tag : Fin 10000) (htag : tag.val = 9160) (k : Ring12) : tag.val = 9160 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09161 (tag : Fin 10000) (htag : tag.val = 9161) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9161 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09162 (tag : Fin 10000) (htag : tag.val = 9162) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9162 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09163 (tag : Fin 10000) (htag : tag.val = 9163) (x : State) (e : Event) (dr : Ring12) : tag.val = 9163 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09164 (tag : Fin 10000) (htag : tag.val = 9164) (x : State) (e : Event) (dr : Ring12) : tag.val = 9164 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09165 (tag : Fin 10000) (htag : tag.val = 9165) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9165 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09166 (tag : Fin 10000) (htag : tag.val = 9166) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9166 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09167 (tag : Fin 10000) (htag : tag.val = 9167) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9167 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09168 (tag : Fin 10000) (htag : tag.val = 9168) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9168 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09169 (tag : Fin 10000) (htag : tag.val = 9169) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9169 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09170 (tag : Fin 10000) (htag : tag.val = 9170) (k : Ring12) : tag.val = 9170 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09171 (tag : Fin 10000) (htag : tag.val = 9171) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9171 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09172 (tag : Fin 10000) (htag : tag.val = 9172) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9172 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09173 (tag : Fin 10000) (htag : tag.val = 9173) (x : State) (e : Event) (dr : Ring12) : tag.val = 9173 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09174 (tag : Fin 10000) (htag : tag.val = 9174) (x : State) (e : Event) (dr : Ring12) : tag.val = 9174 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09175 (tag : Fin 10000) (htag : tag.val = 9175) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9175 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09176 (tag : Fin 10000) (htag : tag.val = 9176) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9176 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09177 (tag : Fin 10000) (htag : tag.val = 9177) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9177 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09178 (tag : Fin 10000) (htag : tag.val = 9178) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9178 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09179 (tag : Fin 10000) (htag : tag.val = 9179) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9179 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09180 (tag : Fin 10000) (htag : tag.val = 9180) (k : Ring12) : tag.val = 9180 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09181 (tag : Fin 10000) (htag : tag.val = 9181) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9181 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09182 (tag : Fin 10000) (htag : tag.val = 9182) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9182 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09183 (tag : Fin 10000) (htag : tag.val = 9183) (x : State) (e : Event) (dr : Ring12) : tag.val = 9183 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09184 (tag : Fin 10000) (htag : tag.val = 9184) (x : State) (e : Event) (dr : Ring12) : tag.val = 9184 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09185 (tag : Fin 10000) (htag : tag.val = 9185) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9185 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09186 (tag : Fin 10000) (htag : tag.val = 9186) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9186 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09187 (tag : Fin 10000) (htag : tag.val = 9187) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9187 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09188 (tag : Fin 10000) (htag : tag.val = 9188) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9188 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09189 (tag : Fin 10000) (htag : tag.val = 9189) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9189 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09190 (tag : Fin 10000) (htag : tag.val = 9190) (k : Ring12) : tag.val = 9190 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09191 (tag : Fin 10000) (htag : tag.val = 9191) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9191 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09192 (tag : Fin 10000) (htag : tag.val = 9192) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9192 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09193 (tag : Fin 10000) (htag : tag.val = 9193) (x : State) (e : Event) (dr : Ring12) : tag.val = 9193 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09194 (tag : Fin 10000) (htag : tag.val = 9194) (x : State) (e : Event) (dr : Ring12) : tag.val = 9194 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09195 (tag : Fin 10000) (htag : tag.val = 9195) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9195 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09196 (tag : Fin 10000) (htag : tag.val = 9196) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9196 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09197 (tag : Fin 10000) (htag : tag.val = 9197) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9197 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09198 (tag : Fin 10000) (htag : tag.val = 9198) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9198 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09199 (tag : Fin 10000) (htag : tag.val = 9199) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9199 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
