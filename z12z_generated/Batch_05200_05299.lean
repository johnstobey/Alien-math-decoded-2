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
theorem generated_05200 (tag : Fin 10000) (htag : tag.val = 5200) (k : Ring12) : tag.val = 5200 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05201 (tag : Fin 10000) (htag : tag.val = 5201) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5201 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05202 (tag : Fin 10000) (htag : tag.val = 5202) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5202 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05203 (tag : Fin 10000) (htag : tag.val = 5203) (x : State) (e : Event) (dr : Ring12) : tag.val = 5203 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05204 (tag : Fin 10000) (htag : tag.val = 5204) (x : State) (e : Event) (dr : Ring12) : tag.val = 5204 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05205 (tag : Fin 10000) (htag : tag.val = 5205) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5205 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05206 (tag : Fin 10000) (htag : tag.val = 5206) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5206 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05207 (tag : Fin 10000) (htag : tag.val = 5207) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5207 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05208 (tag : Fin 10000) (htag : tag.val = 5208) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5208 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05209 (tag : Fin 10000) (htag : tag.val = 5209) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5209 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05210 (tag : Fin 10000) (htag : tag.val = 5210) (k : Ring12) : tag.val = 5210 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05211 (tag : Fin 10000) (htag : tag.val = 5211) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5211 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05212 (tag : Fin 10000) (htag : tag.val = 5212) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5212 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05213 (tag : Fin 10000) (htag : tag.val = 5213) (x : State) (e : Event) (dr : Ring12) : tag.val = 5213 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05214 (tag : Fin 10000) (htag : tag.val = 5214) (x : State) (e : Event) (dr : Ring12) : tag.val = 5214 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05215 (tag : Fin 10000) (htag : tag.val = 5215) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5215 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05216 (tag : Fin 10000) (htag : tag.val = 5216) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5216 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05217 (tag : Fin 10000) (htag : tag.val = 5217) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5217 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05218 (tag : Fin 10000) (htag : tag.val = 5218) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5218 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05219 (tag : Fin 10000) (htag : tag.val = 5219) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5219 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05220 (tag : Fin 10000) (htag : tag.val = 5220) (k : Ring12) : tag.val = 5220 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05221 (tag : Fin 10000) (htag : tag.val = 5221) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5221 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05222 (tag : Fin 10000) (htag : tag.val = 5222) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5222 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05223 (tag : Fin 10000) (htag : tag.val = 5223) (x : State) (e : Event) (dr : Ring12) : tag.val = 5223 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05224 (tag : Fin 10000) (htag : tag.val = 5224) (x : State) (e : Event) (dr : Ring12) : tag.val = 5224 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05225 (tag : Fin 10000) (htag : tag.val = 5225) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5225 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05226 (tag : Fin 10000) (htag : tag.val = 5226) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5226 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05227 (tag : Fin 10000) (htag : tag.val = 5227) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5227 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05228 (tag : Fin 10000) (htag : tag.val = 5228) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5228 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05229 (tag : Fin 10000) (htag : tag.val = 5229) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5229 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05230 (tag : Fin 10000) (htag : tag.val = 5230) (k : Ring12) : tag.val = 5230 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05231 (tag : Fin 10000) (htag : tag.val = 5231) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5231 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05232 (tag : Fin 10000) (htag : tag.val = 5232) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5232 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05233 (tag : Fin 10000) (htag : tag.val = 5233) (x : State) (e : Event) (dr : Ring12) : tag.val = 5233 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05234 (tag : Fin 10000) (htag : tag.val = 5234) (x : State) (e : Event) (dr : Ring12) : tag.val = 5234 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05235 (tag : Fin 10000) (htag : tag.val = 5235) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5235 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05236 (tag : Fin 10000) (htag : tag.val = 5236) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5236 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05237 (tag : Fin 10000) (htag : tag.val = 5237) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5237 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05238 (tag : Fin 10000) (htag : tag.val = 5238) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5238 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05239 (tag : Fin 10000) (htag : tag.val = 5239) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5239 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05240 (tag : Fin 10000) (htag : tag.val = 5240) (k : Ring12) : tag.val = 5240 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05241 (tag : Fin 10000) (htag : tag.val = 5241) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5241 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05242 (tag : Fin 10000) (htag : tag.val = 5242) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5242 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05243 (tag : Fin 10000) (htag : tag.val = 5243) (x : State) (e : Event) (dr : Ring12) : tag.val = 5243 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05244 (tag : Fin 10000) (htag : tag.val = 5244) (x : State) (e : Event) (dr : Ring12) : tag.val = 5244 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05245 (tag : Fin 10000) (htag : tag.val = 5245) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5245 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05246 (tag : Fin 10000) (htag : tag.val = 5246) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5246 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05247 (tag : Fin 10000) (htag : tag.val = 5247) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5247 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05248 (tag : Fin 10000) (htag : tag.val = 5248) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5248 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05249 (tag : Fin 10000) (htag : tag.val = 5249) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5249 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05250 (tag : Fin 10000) (htag : tag.val = 5250) (k : Ring12) : tag.val = 5250 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05251 (tag : Fin 10000) (htag : tag.val = 5251) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5251 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05252 (tag : Fin 10000) (htag : tag.val = 5252) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5252 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05253 (tag : Fin 10000) (htag : tag.val = 5253) (x : State) (e : Event) (dr : Ring12) : tag.val = 5253 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05254 (tag : Fin 10000) (htag : tag.val = 5254) (x : State) (e : Event) (dr : Ring12) : tag.val = 5254 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05255 (tag : Fin 10000) (htag : tag.val = 5255) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5255 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05256 (tag : Fin 10000) (htag : tag.val = 5256) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5256 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05257 (tag : Fin 10000) (htag : tag.val = 5257) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5257 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05258 (tag : Fin 10000) (htag : tag.val = 5258) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5258 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05259 (tag : Fin 10000) (htag : tag.val = 5259) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5259 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05260 (tag : Fin 10000) (htag : tag.val = 5260) (k : Ring12) : tag.val = 5260 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05261 (tag : Fin 10000) (htag : tag.val = 5261) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5261 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05262 (tag : Fin 10000) (htag : tag.val = 5262) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5262 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05263 (tag : Fin 10000) (htag : tag.val = 5263) (x : State) (e : Event) (dr : Ring12) : tag.val = 5263 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05264 (tag : Fin 10000) (htag : tag.val = 5264) (x : State) (e : Event) (dr : Ring12) : tag.val = 5264 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05265 (tag : Fin 10000) (htag : tag.val = 5265) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5265 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05266 (tag : Fin 10000) (htag : tag.val = 5266) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5266 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05267 (tag : Fin 10000) (htag : tag.val = 5267) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5267 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05268 (tag : Fin 10000) (htag : tag.val = 5268) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5268 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05269 (tag : Fin 10000) (htag : tag.val = 5269) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5269 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05270 (tag : Fin 10000) (htag : tag.val = 5270) (k : Ring12) : tag.val = 5270 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05271 (tag : Fin 10000) (htag : tag.val = 5271) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5271 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05272 (tag : Fin 10000) (htag : tag.val = 5272) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5272 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05273 (tag : Fin 10000) (htag : tag.val = 5273) (x : State) (e : Event) (dr : Ring12) : tag.val = 5273 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05274 (tag : Fin 10000) (htag : tag.val = 5274) (x : State) (e : Event) (dr : Ring12) : tag.val = 5274 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05275 (tag : Fin 10000) (htag : tag.val = 5275) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5275 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05276 (tag : Fin 10000) (htag : tag.val = 5276) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5276 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05277 (tag : Fin 10000) (htag : tag.val = 5277) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5277 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05278 (tag : Fin 10000) (htag : tag.val = 5278) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5278 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05279 (tag : Fin 10000) (htag : tag.val = 5279) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5279 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05280 (tag : Fin 10000) (htag : tag.val = 5280) (k : Ring12) : tag.val = 5280 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05281 (tag : Fin 10000) (htag : tag.val = 5281) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5281 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05282 (tag : Fin 10000) (htag : tag.val = 5282) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5282 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05283 (tag : Fin 10000) (htag : tag.val = 5283) (x : State) (e : Event) (dr : Ring12) : tag.val = 5283 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05284 (tag : Fin 10000) (htag : tag.val = 5284) (x : State) (e : Event) (dr : Ring12) : tag.val = 5284 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05285 (tag : Fin 10000) (htag : tag.val = 5285) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5285 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05286 (tag : Fin 10000) (htag : tag.val = 5286) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5286 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05287 (tag : Fin 10000) (htag : tag.val = 5287) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5287 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05288 (tag : Fin 10000) (htag : tag.val = 5288) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5288 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05289 (tag : Fin 10000) (htag : tag.val = 5289) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5289 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05290 (tag : Fin 10000) (htag : tag.val = 5290) (k : Ring12) : tag.val = 5290 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05291 (tag : Fin 10000) (htag : tag.val = 5291) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5291 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05292 (tag : Fin 10000) (htag : tag.val = 5292) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5292 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05293 (tag : Fin 10000) (htag : tag.val = 5293) (x : State) (e : Event) (dr : Ring12) : tag.val = 5293 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05294 (tag : Fin 10000) (htag : tag.val = 5294) (x : State) (e : Event) (dr : Ring12) : tag.val = 5294 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05295 (tag : Fin 10000) (htag : tag.val = 5295) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5295 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05296 (tag : Fin 10000) (htag : tag.val = 5296) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5296 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05297 (tag : Fin 10000) (htag : tag.val = 5297) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5297 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05298 (tag : Fin 10000) (htag : tag.val = 5298) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5298 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05299 (tag : Fin 10000) (htag : tag.val = 5299) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5299 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
