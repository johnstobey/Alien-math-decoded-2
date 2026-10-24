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
theorem generated_02100 (tag : Fin 10000) (htag : tag.val = 2100) (k : Ring12) : tag.val = 2100 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02101 (tag : Fin 10000) (htag : tag.val = 2101) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2101 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02102 (tag : Fin 10000) (htag : tag.val = 2102) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2102 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02103 (tag : Fin 10000) (htag : tag.val = 2103) (x : State) (e : Event) (dr : Ring12) : tag.val = 2103 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02104 (tag : Fin 10000) (htag : tag.val = 2104) (x : State) (e : Event) (dr : Ring12) : tag.val = 2104 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02105 (tag : Fin 10000) (htag : tag.val = 2105) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2105 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02106 (tag : Fin 10000) (htag : tag.val = 2106) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2106 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02107 (tag : Fin 10000) (htag : tag.val = 2107) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2107 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02108 (tag : Fin 10000) (htag : tag.val = 2108) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2108 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02109 (tag : Fin 10000) (htag : tag.val = 2109) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2109 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02110 (tag : Fin 10000) (htag : tag.val = 2110) (k : Ring12) : tag.val = 2110 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02111 (tag : Fin 10000) (htag : tag.val = 2111) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2111 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02112 (tag : Fin 10000) (htag : tag.val = 2112) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2112 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02113 (tag : Fin 10000) (htag : tag.val = 2113) (x : State) (e : Event) (dr : Ring12) : tag.val = 2113 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02114 (tag : Fin 10000) (htag : tag.val = 2114) (x : State) (e : Event) (dr : Ring12) : tag.val = 2114 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02115 (tag : Fin 10000) (htag : tag.val = 2115) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2115 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02116 (tag : Fin 10000) (htag : tag.val = 2116) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2116 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02117 (tag : Fin 10000) (htag : tag.val = 2117) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2117 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02118 (tag : Fin 10000) (htag : tag.val = 2118) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2118 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02119 (tag : Fin 10000) (htag : tag.val = 2119) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2119 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02120 (tag : Fin 10000) (htag : tag.val = 2120) (k : Ring12) : tag.val = 2120 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02121 (tag : Fin 10000) (htag : tag.val = 2121) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2121 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02122 (tag : Fin 10000) (htag : tag.val = 2122) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2122 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02123 (tag : Fin 10000) (htag : tag.val = 2123) (x : State) (e : Event) (dr : Ring12) : tag.val = 2123 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02124 (tag : Fin 10000) (htag : tag.val = 2124) (x : State) (e : Event) (dr : Ring12) : tag.val = 2124 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02125 (tag : Fin 10000) (htag : tag.val = 2125) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2125 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02126 (tag : Fin 10000) (htag : tag.val = 2126) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2126 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02127 (tag : Fin 10000) (htag : tag.val = 2127) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2127 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02128 (tag : Fin 10000) (htag : tag.val = 2128) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2128 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02129 (tag : Fin 10000) (htag : tag.val = 2129) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2129 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02130 (tag : Fin 10000) (htag : tag.val = 2130) (k : Ring12) : tag.val = 2130 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02131 (tag : Fin 10000) (htag : tag.val = 2131) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2131 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02132 (tag : Fin 10000) (htag : tag.val = 2132) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2132 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02133 (tag : Fin 10000) (htag : tag.val = 2133) (x : State) (e : Event) (dr : Ring12) : tag.val = 2133 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02134 (tag : Fin 10000) (htag : tag.val = 2134) (x : State) (e : Event) (dr : Ring12) : tag.val = 2134 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02135 (tag : Fin 10000) (htag : tag.val = 2135) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2135 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02136 (tag : Fin 10000) (htag : tag.val = 2136) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2136 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02137 (tag : Fin 10000) (htag : tag.val = 2137) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2137 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02138 (tag : Fin 10000) (htag : tag.val = 2138) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2138 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02139 (tag : Fin 10000) (htag : tag.val = 2139) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2139 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02140 (tag : Fin 10000) (htag : tag.val = 2140) (k : Ring12) : tag.val = 2140 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02141 (tag : Fin 10000) (htag : tag.val = 2141) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2141 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02142 (tag : Fin 10000) (htag : tag.val = 2142) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2142 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02143 (tag : Fin 10000) (htag : tag.val = 2143) (x : State) (e : Event) (dr : Ring12) : tag.val = 2143 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02144 (tag : Fin 10000) (htag : tag.val = 2144) (x : State) (e : Event) (dr : Ring12) : tag.val = 2144 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02145 (tag : Fin 10000) (htag : tag.val = 2145) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2145 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02146 (tag : Fin 10000) (htag : tag.val = 2146) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2146 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02147 (tag : Fin 10000) (htag : tag.val = 2147) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2147 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02148 (tag : Fin 10000) (htag : tag.val = 2148) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2148 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02149 (tag : Fin 10000) (htag : tag.val = 2149) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2149 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02150 (tag : Fin 10000) (htag : tag.val = 2150) (k : Ring12) : tag.val = 2150 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02151 (tag : Fin 10000) (htag : tag.val = 2151) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2151 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02152 (tag : Fin 10000) (htag : tag.val = 2152) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2152 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02153 (tag : Fin 10000) (htag : tag.val = 2153) (x : State) (e : Event) (dr : Ring12) : tag.val = 2153 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02154 (tag : Fin 10000) (htag : tag.val = 2154) (x : State) (e : Event) (dr : Ring12) : tag.val = 2154 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02155 (tag : Fin 10000) (htag : tag.val = 2155) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2155 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02156 (tag : Fin 10000) (htag : tag.val = 2156) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2156 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02157 (tag : Fin 10000) (htag : tag.val = 2157) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2157 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02158 (tag : Fin 10000) (htag : tag.val = 2158) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2158 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02159 (tag : Fin 10000) (htag : tag.val = 2159) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2159 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02160 (tag : Fin 10000) (htag : tag.val = 2160) (k : Ring12) : tag.val = 2160 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02161 (tag : Fin 10000) (htag : tag.val = 2161) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2161 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02162 (tag : Fin 10000) (htag : tag.val = 2162) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2162 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02163 (tag : Fin 10000) (htag : tag.val = 2163) (x : State) (e : Event) (dr : Ring12) : tag.val = 2163 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02164 (tag : Fin 10000) (htag : tag.val = 2164) (x : State) (e : Event) (dr : Ring12) : tag.val = 2164 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02165 (tag : Fin 10000) (htag : tag.val = 2165) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2165 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02166 (tag : Fin 10000) (htag : tag.val = 2166) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2166 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02167 (tag : Fin 10000) (htag : tag.val = 2167) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2167 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02168 (tag : Fin 10000) (htag : tag.val = 2168) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2168 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02169 (tag : Fin 10000) (htag : tag.val = 2169) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2169 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02170 (tag : Fin 10000) (htag : tag.val = 2170) (k : Ring12) : tag.val = 2170 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02171 (tag : Fin 10000) (htag : tag.val = 2171) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2171 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02172 (tag : Fin 10000) (htag : tag.val = 2172) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2172 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02173 (tag : Fin 10000) (htag : tag.val = 2173) (x : State) (e : Event) (dr : Ring12) : tag.val = 2173 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02174 (tag : Fin 10000) (htag : tag.val = 2174) (x : State) (e : Event) (dr : Ring12) : tag.val = 2174 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02175 (tag : Fin 10000) (htag : tag.val = 2175) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2175 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02176 (tag : Fin 10000) (htag : tag.val = 2176) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2176 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02177 (tag : Fin 10000) (htag : tag.val = 2177) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2177 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02178 (tag : Fin 10000) (htag : tag.val = 2178) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2178 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02179 (tag : Fin 10000) (htag : tag.val = 2179) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2179 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02180 (tag : Fin 10000) (htag : tag.val = 2180) (k : Ring12) : tag.val = 2180 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02181 (tag : Fin 10000) (htag : tag.val = 2181) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2181 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02182 (tag : Fin 10000) (htag : tag.val = 2182) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2182 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02183 (tag : Fin 10000) (htag : tag.val = 2183) (x : State) (e : Event) (dr : Ring12) : tag.val = 2183 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02184 (tag : Fin 10000) (htag : tag.val = 2184) (x : State) (e : Event) (dr : Ring12) : tag.val = 2184 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02185 (tag : Fin 10000) (htag : tag.val = 2185) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2185 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02186 (tag : Fin 10000) (htag : tag.val = 2186) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2186 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02187 (tag : Fin 10000) (htag : tag.val = 2187) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2187 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02188 (tag : Fin 10000) (htag : tag.val = 2188) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2188 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02189 (tag : Fin 10000) (htag : tag.val = 2189) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2189 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02190 (tag : Fin 10000) (htag : tag.val = 2190) (k : Ring12) : tag.val = 2190 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02191 (tag : Fin 10000) (htag : tag.val = 2191) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2191 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02192 (tag : Fin 10000) (htag : tag.val = 2192) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2192 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02193 (tag : Fin 10000) (htag : tag.val = 2193) (x : State) (e : Event) (dr : Ring12) : tag.val = 2193 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02194 (tag : Fin 10000) (htag : tag.val = 2194) (x : State) (e : Event) (dr : Ring12) : tag.val = 2194 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02195 (tag : Fin 10000) (htag : tag.val = 2195) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2195 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02196 (tag : Fin 10000) (htag : tag.val = 2196) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2196 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02197 (tag : Fin 10000) (htag : tag.val = 2197) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2197 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02198 (tag : Fin 10000) (htag : tag.val = 2198) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2198 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02199 (tag : Fin 10000) (htag : tag.val = 2199) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2199 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
