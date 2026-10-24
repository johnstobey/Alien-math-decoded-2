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
theorem generated_06300 (tag : Fin 10000) (htag : tag.val = 6300) (k : Ring12) : tag.val = 6300 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06301 (tag : Fin 10000) (htag : tag.val = 6301) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6301 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06302 (tag : Fin 10000) (htag : tag.val = 6302) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6302 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06303 (tag : Fin 10000) (htag : tag.val = 6303) (x : State) (e : Event) (dr : Ring12) : tag.val = 6303 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06304 (tag : Fin 10000) (htag : tag.val = 6304) (x : State) (e : Event) (dr : Ring12) : tag.val = 6304 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06305 (tag : Fin 10000) (htag : tag.val = 6305) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6305 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06306 (tag : Fin 10000) (htag : tag.val = 6306) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6306 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06307 (tag : Fin 10000) (htag : tag.val = 6307) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6307 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06308 (tag : Fin 10000) (htag : tag.val = 6308) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6308 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06309 (tag : Fin 10000) (htag : tag.val = 6309) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6309 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06310 (tag : Fin 10000) (htag : tag.val = 6310) (k : Ring12) : tag.val = 6310 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06311 (tag : Fin 10000) (htag : tag.val = 6311) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6311 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06312 (tag : Fin 10000) (htag : tag.val = 6312) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6312 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06313 (tag : Fin 10000) (htag : tag.val = 6313) (x : State) (e : Event) (dr : Ring12) : tag.val = 6313 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06314 (tag : Fin 10000) (htag : tag.val = 6314) (x : State) (e : Event) (dr : Ring12) : tag.val = 6314 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06315 (tag : Fin 10000) (htag : tag.val = 6315) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6315 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06316 (tag : Fin 10000) (htag : tag.val = 6316) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6316 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06317 (tag : Fin 10000) (htag : tag.val = 6317) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6317 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06318 (tag : Fin 10000) (htag : tag.val = 6318) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6318 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06319 (tag : Fin 10000) (htag : tag.val = 6319) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6319 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06320 (tag : Fin 10000) (htag : tag.val = 6320) (k : Ring12) : tag.val = 6320 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06321 (tag : Fin 10000) (htag : tag.val = 6321) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6321 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06322 (tag : Fin 10000) (htag : tag.val = 6322) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6322 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06323 (tag : Fin 10000) (htag : tag.val = 6323) (x : State) (e : Event) (dr : Ring12) : tag.val = 6323 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06324 (tag : Fin 10000) (htag : tag.val = 6324) (x : State) (e : Event) (dr : Ring12) : tag.val = 6324 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06325 (tag : Fin 10000) (htag : tag.val = 6325) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6325 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06326 (tag : Fin 10000) (htag : tag.val = 6326) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6326 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06327 (tag : Fin 10000) (htag : tag.val = 6327) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6327 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06328 (tag : Fin 10000) (htag : tag.val = 6328) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6328 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06329 (tag : Fin 10000) (htag : tag.val = 6329) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6329 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06330 (tag : Fin 10000) (htag : tag.val = 6330) (k : Ring12) : tag.val = 6330 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06331 (tag : Fin 10000) (htag : tag.val = 6331) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6331 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06332 (tag : Fin 10000) (htag : tag.val = 6332) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6332 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06333 (tag : Fin 10000) (htag : tag.val = 6333) (x : State) (e : Event) (dr : Ring12) : tag.val = 6333 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06334 (tag : Fin 10000) (htag : tag.val = 6334) (x : State) (e : Event) (dr : Ring12) : tag.val = 6334 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06335 (tag : Fin 10000) (htag : tag.val = 6335) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6335 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06336 (tag : Fin 10000) (htag : tag.val = 6336) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6336 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06337 (tag : Fin 10000) (htag : tag.val = 6337) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6337 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06338 (tag : Fin 10000) (htag : tag.val = 6338) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6338 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06339 (tag : Fin 10000) (htag : tag.val = 6339) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6339 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06340 (tag : Fin 10000) (htag : tag.val = 6340) (k : Ring12) : tag.val = 6340 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06341 (tag : Fin 10000) (htag : tag.val = 6341) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6341 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06342 (tag : Fin 10000) (htag : tag.val = 6342) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6342 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06343 (tag : Fin 10000) (htag : tag.val = 6343) (x : State) (e : Event) (dr : Ring12) : tag.val = 6343 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06344 (tag : Fin 10000) (htag : tag.val = 6344) (x : State) (e : Event) (dr : Ring12) : tag.val = 6344 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06345 (tag : Fin 10000) (htag : tag.val = 6345) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6345 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06346 (tag : Fin 10000) (htag : tag.val = 6346) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6346 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06347 (tag : Fin 10000) (htag : tag.val = 6347) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6347 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06348 (tag : Fin 10000) (htag : tag.val = 6348) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6348 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06349 (tag : Fin 10000) (htag : tag.val = 6349) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6349 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06350 (tag : Fin 10000) (htag : tag.val = 6350) (k : Ring12) : tag.val = 6350 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06351 (tag : Fin 10000) (htag : tag.val = 6351) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6351 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06352 (tag : Fin 10000) (htag : tag.val = 6352) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6352 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06353 (tag : Fin 10000) (htag : tag.val = 6353) (x : State) (e : Event) (dr : Ring12) : tag.val = 6353 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06354 (tag : Fin 10000) (htag : tag.val = 6354) (x : State) (e : Event) (dr : Ring12) : tag.val = 6354 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06355 (tag : Fin 10000) (htag : tag.val = 6355) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6355 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06356 (tag : Fin 10000) (htag : tag.val = 6356) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6356 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06357 (tag : Fin 10000) (htag : tag.val = 6357) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6357 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06358 (tag : Fin 10000) (htag : tag.val = 6358) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6358 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06359 (tag : Fin 10000) (htag : tag.val = 6359) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6359 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06360 (tag : Fin 10000) (htag : tag.val = 6360) (k : Ring12) : tag.val = 6360 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06361 (tag : Fin 10000) (htag : tag.val = 6361) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6361 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06362 (tag : Fin 10000) (htag : tag.val = 6362) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6362 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06363 (tag : Fin 10000) (htag : tag.val = 6363) (x : State) (e : Event) (dr : Ring12) : tag.val = 6363 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06364 (tag : Fin 10000) (htag : tag.val = 6364) (x : State) (e : Event) (dr : Ring12) : tag.val = 6364 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06365 (tag : Fin 10000) (htag : tag.val = 6365) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6365 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06366 (tag : Fin 10000) (htag : tag.val = 6366) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6366 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06367 (tag : Fin 10000) (htag : tag.val = 6367) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6367 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06368 (tag : Fin 10000) (htag : tag.val = 6368) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6368 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06369 (tag : Fin 10000) (htag : tag.val = 6369) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6369 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06370 (tag : Fin 10000) (htag : tag.val = 6370) (k : Ring12) : tag.val = 6370 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06371 (tag : Fin 10000) (htag : tag.val = 6371) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6371 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06372 (tag : Fin 10000) (htag : tag.val = 6372) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6372 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06373 (tag : Fin 10000) (htag : tag.val = 6373) (x : State) (e : Event) (dr : Ring12) : tag.val = 6373 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06374 (tag : Fin 10000) (htag : tag.val = 6374) (x : State) (e : Event) (dr : Ring12) : tag.val = 6374 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06375 (tag : Fin 10000) (htag : tag.val = 6375) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6375 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06376 (tag : Fin 10000) (htag : tag.val = 6376) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6376 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06377 (tag : Fin 10000) (htag : tag.val = 6377) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6377 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06378 (tag : Fin 10000) (htag : tag.val = 6378) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6378 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06379 (tag : Fin 10000) (htag : tag.val = 6379) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6379 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06380 (tag : Fin 10000) (htag : tag.val = 6380) (k : Ring12) : tag.val = 6380 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06381 (tag : Fin 10000) (htag : tag.val = 6381) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6381 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06382 (tag : Fin 10000) (htag : tag.val = 6382) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6382 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06383 (tag : Fin 10000) (htag : tag.val = 6383) (x : State) (e : Event) (dr : Ring12) : tag.val = 6383 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06384 (tag : Fin 10000) (htag : tag.val = 6384) (x : State) (e : Event) (dr : Ring12) : tag.val = 6384 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06385 (tag : Fin 10000) (htag : tag.val = 6385) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6385 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06386 (tag : Fin 10000) (htag : tag.val = 6386) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6386 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06387 (tag : Fin 10000) (htag : tag.val = 6387) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6387 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06388 (tag : Fin 10000) (htag : tag.val = 6388) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6388 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06389 (tag : Fin 10000) (htag : tag.val = 6389) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6389 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06390 (tag : Fin 10000) (htag : tag.val = 6390) (k : Ring12) : tag.val = 6390 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06391 (tag : Fin 10000) (htag : tag.val = 6391) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6391 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06392 (tag : Fin 10000) (htag : tag.val = 6392) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6392 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06393 (tag : Fin 10000) (htag : tag.val = 6393) (x : State) (e : Event) (dr : Ring12) : tag.val = 6393 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06394 (tag : Fin 10000) (htag : tag.val = 6394) (x : State) (e : Event) (dr : Ring12) : tag.val = 6394 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06395 (tag : Fin 10000) (htag : tag.val = 6395) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6395 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06396 (tag : Fin 10000) (htag : tag.val = 6396) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6396 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06397 (tag : Fin 10000) (htag : tag.val = 6397) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6397 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06398 (tag : Fin 10000) (htag : tag.val = 6398) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6398 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06399 (tag : Fin 10000) (htag : tag.val = 6399) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6399 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
