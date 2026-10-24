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
theorem generated_02200 (tag : Fin 10000) (htag : tag.val = 2200) (k : Ring12) : tag.val = 2200 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02201 (tag : Fin 10000) (htag : tag.val = 2201) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2201 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02202 (tag : Fin 10000) (htag : tag.val = 2202) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2202 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02203 (tag : Fin 10000) (htag : tag.val = 2203) (x : State) (e : Event) (dr : Ring12) : tag.val = 2203 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02204 (tag : Fin 10000) (htag : tag.val = 2204) (x : State) (e : Event) (dr : Ring12) : tag.val = 2204 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02205 (tag : Fin 10000) (htag : tag.val = 2205) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2205 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02206 (tag : Fin 10000) (htag : tag.val = 2206) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2206 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02207 (tag : Fin 10000) (htag : tag.val = 2207) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2207 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02208 (tag : Fin 10000) (htag : tag.val = 2208) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2208 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02209 (tag : Fin 10000) (htag : tag.val = 2209) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2209 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02210 (tag : Fin 10000) (htag : tag.val = 2210) (k : Ring12) : tag.val = 2210 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02211 (tag : Fin 10000) (htag : tag.val = 2211) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2211 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02212 (tag : Fin 10000) (htag : tag.val = 2212) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2212 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02213 (tag : Fin 10000) (htag : tag.val = 2213) (x : State) (e : Event) (dr : Ring12) : tag.val = 2213 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02214 (tag : Fin 10000) (htag : tag.val = 2214) (x : State) (e : Event) (dr : Ring12) : tag.val = 2214 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02215 (tag : Fin 10000) (htag : tag.val = 2215) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2215 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02216 (tag : Fin 10000) (htag : tag.val = 2216) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2216 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02217 (tag : Fin 10000) (htag : tag.val = 2217) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2217 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02218 (tag : Fin 10000) (htag : tag.val = 2218) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2218 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02219 (tag : Fin 10000) (htag : tag.val = 2219) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2219 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02220 (tag : Fin 10000) (htag : tag.val = 2220) (k : Ring12) : tag.val = 2220 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02221 (tag : Fin 10000) (htag : tag.val = 2221) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2221 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02222 (tag : Fin 10000) (htag : tag.val = 2222) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2222 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02223 (tag : Fin 10000) (htag : tag.val = 2223) (x : State) (e : Event) (dr : Ring12) : tag.val = 2223 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02224 (tag : Fin 10000) (htag : tag.val = 2224) (x : State) (e : Event) (dr : Ring12) : tag.val = 2224 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02225 (tag : Fin 10000) (htag : tag.val = 2225) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2225 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02226 (tag : Fin 10000) (htag : tag.val = 2226) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2226 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02227 (tag : Fin 10000) (htag : tag.val = 2227) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2227 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02228 (tag : Fin 10000) (htag : tag.val = 2228) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2228 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02229 (tag : Fin 10000) (htag : tag.val = 2229) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2229 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02230 (tag : Fin 10000) (htag : tag.val = 2230) (k : Ring12) : tag.val = 2230 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02231 (tag : Fin 10000) (htag : tag.val = 2231) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2231 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02232 (tag : Fin 10000) (htag : tag.val = 2232) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2232 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02233 (tag : Fin 10000) (htag : tag.val = 2233) (x : State) (e : Event) (dr : Ring12) : tag.val = 2233 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02234 (tag : Fin 10000) (htag : tag.val = 2234) (x : State) (e : Event) (dr : Ring12) : tag.val = 2234 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02235 (tag : Fin 10000) (htag : tag.val = 2235) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2235 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02236 (tag : Fin 10000) (htag : tag.val = 2236) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2236 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02237 (tag : Fin 10000) (htag : tag.val = 2237) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2237 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02238 (tag : Fin 10000) (htag : tag.val = 2238) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2238 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02239 (tag : Fin 10000) (htag : tag.val = 2239) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2239 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02240 (tag : Fin 10000) (htag : tag.val = 2240) (k : Ring12) : tag.val = 2240 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02241 (tag : Fin 10000) (htag : tag.val = 2241) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2241 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02242 (tag : Fin 10000) (htag : tag.val = 2242) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2242 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02243 (tag : Fin 10000) (htag : tag.val = 2243) (x : State) (e : Event) (dr : Ring12) : tag.val = 2243 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02244 (tag : Fin 10000) (htag : tag.val = 2244) (x : State) (e : Event) (dr : Ring12) : tag.val = 2244 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02245 (tag : Fin 10000) (htag : tag.val = 2245) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2245 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02246 (tag : Fin 10000) (htag : tag.val = 2246) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2246 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02247 (tag : Fin 10000) (htag : tag.val = 2247) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2247 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02248 (tag : Fin 10000) (htag : tag.val = 2248) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2248 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02249 (tag : Fin 10000) (htag : tag.val = 2249) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2249 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02250 (tag : Fin 10000) (htag : tag.val = 2250) (k : Ring12) : tag.val = 2250 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02251 (tag : Fin 10000) (htag : tag.val = 2251) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2251 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02252 (tag : Fin 10000) (htag : tag.val = 2252) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2252 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02253 (tag : Fin 10000) (htag : tag.val = 2253) (x : State) (e : Event) (dr : Ring12) : tag.val = 2253 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02254 (tag : Fin 10000) (htag : tag.val = 2254) (x : State) (e : Event) (dr : Ring12) : tag.val = 2254 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02255 (tag : Fin 10000) (htag : tag.val = 2255) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2255 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02256 (tag : Fin 10000) (htag : tag.val = 2256) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2256 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02257 (tag : Fin 10000) (htag : tag.val = 2257) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2257 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02258 (tag : Fin 10000) (htag : tag.val = 2258) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2258 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02259 (tag : Fin 10000) (htag : tag.val = 2259) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2259 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02260 (tag : Fin 10000) (htag : tag.val = 2260) (k : Ring12) : tag.val = 2260 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02261 (tag : Fin 10000) (htag : tag.val = 2261) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2261 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02262 (tag : Fin 10000) (htag : tag.val = 2262) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2262 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02263 (tag : Fin 10000) (htag : tag.val = 2263) (x : State) (e : Event) (dr : Ring12) : tag.val = 2263 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02264 (tag : Fin 10000) (htag : tag.val = 2264) (x : State) (e : Event) (dr : Ring12) : tag.val = 2264 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02265 (tag : Fin 10000) (htag : tag.val = 2265) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2265 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02266 (tag : Fin 10000) (htag : tag.val = 2266) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2266 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02267 (tag : Fin 10000) (htag : tag.val = 2267) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2267 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02268 (tag : Fin 10000) (htag : tag.val = 2268) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2268 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02269 (tag : Fin 10000) (htag : tag.val = 2269) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2269 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02270 (tag : Fin 10000) (htag : tag.val = 2270) (k : Ring12) : tag.val = 2270 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02271 (tag : Fin 10000) (htag : tag.val = 2271) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2271 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02272 (tag : Fin 10000) (htag : tag.val = 2272) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2272 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02273 (tag : Fin 10000) (htag : tag.val = 2273) (x : State) (e : Event) (dr : Ring12) : tag.val = 2273 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02274 (tag : Fin 10000) (htag : tag.val = 2274) (x : State) (e : Event) (dr : Ring12) : tag.val = 2274 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02275 (tag : Fin 10000) (htag : tag.val = 2275) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2275 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02276 (tag : Fin 10000) (htag : tag.val = 2276) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2276 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02277 (tag : Fin 10000) (htag : tag.val = 2277) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2277 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02278 (tag : Fin 10000) (htag : tag.val = 2278) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2278 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02279 (tag : Fin 10000) (htag : tag.val = 2279) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2279 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02280 (tag : Fin 10000) (htag : tag.val = 2280) (k : Ring12) : tag.val = 2280 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02281 (tag : Fin 10000) (htag : tag.val = 2281) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2281 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02282 (tag : Fin 10000) (htag : tag.val = 2282) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2282 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02283 (tag : Fin 10000) (htag : tag.val = 2283) (x : State) (e : Event) (dr : Ring12) : tag.val = 2283 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02284 (tag : Fin 10000) (htag : tag.val = 2284) (x : State) (e : Event) (dr : Ring12) : tag.val = 2284 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02285 (tag : Fin 10000) (htag : tag.val = 2285) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2285 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02286 (tag : Fin 10000) (htag : tag.val = 2286) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2286 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02287 (tag : Fin 10000) (htag : tag.val = 2287) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2287 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02288 (tag : Fin 10000) (htag : tag.val = 2288) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2288 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02289 (tag : Fin 10000) (htag : tag.val = 2289) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2289 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02290 (tag : Fin 10000) (htag : tag.val = 2290) (k : Ring12) : tag.val = 2290 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02291 (tag : Fin 10000) (htag : tag.val = 2291) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2291 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02292 (tag : Fin 10000) (htag : tag.val = 2292) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2292 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02293 (tag : Fin 10000) (htag : tag.val = 2293) (x : State) (e : Event) (dr : Ring12) : tag.val = 2293 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02294 (tag : Fin 10000) (htag : tag.val = 2294) (x : State) (e : Event) (dr : Ring12) : tag.val = 2294 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02295 (tag : Fin 10000) (htag : tag.val = 2295) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2295 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02296 (tag : Fin 10000) (htag : tag.val = 2296) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2296 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02297 (tag : Fin 10000) (htag : tag.val = 2297) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2297 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02298 (tag : Fin 10000) (htag : tag.val = 2298) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2298 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02299 (tag : Fin 10000) (htag : tag.val = 2299) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2299 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
