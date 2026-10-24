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
theorem generated_05300 (tag : Fin 10000) (htag : tag.val = 5300) (k : Ring12) : tag.val = 5300 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05301 (tag : Fin 10000) (htag : tag.val = 5301) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5301 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05302 (tag : Fin 10000) (htag : tag.val = 5302) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5302 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05303 (tag : Fin 10000) (htag : tag.val = 5303) (x : State) (e : Event) (dr : Ring12) : tag.val = 5303 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05304 (tag : Fin 10000) (htag : tag.val = 5304) (x : State) (e : Event) (dr : Ring12) : tag.val = 5304 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05305 (tag : Fin 10000) (htag : tag.val = 5305) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5305 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05306 (tag : Fin 10000) (htag : tag.val = 5306) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5306 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05307 (tag : Fin 10000) (htag : tag.val = 5307) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5307 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05308 (tag : Fin 10000) (htag : tag.val = 5308) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5308 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05309 (tag : Fin 10000) (htag : tag.val = 5309) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5309 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05310 (tag : Fin 10000) (htag : tag.val = 5310) (k : Ring12) : tag.val = 5310 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05311 (tag : Fin 10000) (htag : tag.val = 5311) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5311 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05312 (tag : Fin 10000) (htag : tag.val = 5312) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5312 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05313 (tag : Fin 10000) (htag : tag.val = 5313) (x : State) (e : Event) (dr : Ring12) : tag.val = 5313 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05314 (tag : Fin 10000) (htag : tag.val = 5314) (x : State) (e : Event) (dr : Ring12) : tag.val = 5314 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05315 (tag : Fin 10000) (htag : tag.val = 5315) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5315 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05316 (tag : Fin 10000) (htag : tag.val = 5316) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5316 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05317 (tag : Fin 10000) (htag : tag.val = 5317) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5317 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05318 (tag : Fin 10000) (htag : tag.val = 5318) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5318 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05319 (tag : Fin 10000) (htag : tag.val = 5319) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5319 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05320 (tag : Fin 10000) (htag : tag.val = 5320) (k : Ring12) : tag.val = 5320 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05321 (tag : Fin 10000) (htag : tag.val = 5321) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5321 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05322 (tag : Fin 10000) (htag : tag.val = 5322) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5322 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05323 (tag : Fin 10000) (htag : tag.val = 5323) (x : State) (e : Event) (dr : Ring12) : tag.val = 5323 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05324 (tag : Fin 10000) (htag : tag.val = 5324) (x : State) (e : Event) (dr : Ring12) : tag.val = 5324 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05325 (tag : Fin 10000) (htag : tag.val = 5325) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5325 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05326 (tag : Fin 10000) (htag : tag.val = 5326) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5326 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05327 (tag : Fin 10000) (htag : tag.val = 5327) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5327 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05328 (tag : Fin 10000) (htag : tag.val = 5328) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5328 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05329 (tag : Fin 10000) (htag : tag.val = 5329) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5329 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05330 (tag : Fin 10000) (htag : tag.val = 5330) (k : Ring12) : tag.val = 5330 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05331 (tag : Fin 10000) (htag : tag.val = 5331) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5331 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05332 (tag : Fin 10000) (htag : tag.val = 5332) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5332 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05333 (tag : Fin 10000) (htag : tag.val = 5333) (x : State) (e : Event) (dr : Ring12) : tag.val = 5333 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05334 (tag : Fin 10000) (htag : tag.val = 5334) (x : State) (e : Event) (dr : Ring12) : tag.val = 5334 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05335 (tag : Fin 10000) (htag : tag.val = 5335) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5335 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05336 (tag : Fin 10000) (htag : tag.val = 5336) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5336 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05337 (tag : Fin 10000) (htag : tag.val = 5337) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5337 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05338 (tag : Fin 10000) (htag : tag.val = 5338) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5338 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05339 (tag : Fin 10000) (htag : tag.val = 5339) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5339 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05340 (tag : Fin 10000) (htag : tag.val = 5340) (k : Ring12) : tag.val = 5340 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05341 (tag : Fin 10000) (htag : tag.val = 5341) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5341 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05342 (tag : Fin 10000) (htag : tag.val = 5342) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5342 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05343 (tag : Fin 10000) (htag : tag.val = 5343) (x : State) (e : Event) (dr : Ring12) : tag.val = 5343 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05344 (tag : Fin 10000) (htag : tag.val = 5344) (x : State) (e : Event) (dr : Ring12) : tag.val = 5344 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05345 (tag : Fin 10000) (htag : tag.val = 5345) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5345 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05346 (tag : Fin 10000) (htag : tag.val = 5346) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5346 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05347 (tag : Fin 10000) (htag : tag.val = 5347) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5347 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05348 (tag : Fin 10000) (htag : tag.val = 5348) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5348 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05349 (tag : Fin 10000) (htag : tag.val = 5349) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5349 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05350 (tag : Fin 10000) (htag : tag.val = 5350) (k : Ring12) : tag.val = 5350 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05351 (tag : Fin 10000) (htag : tag.val = 5351) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5351 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05352 (tag : Fin 10000) (htag : tag.val = 5352) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5352 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05353 (tag : Fin 10000) (htag : tag.val = 5353) (x : State) (e : Event) (dr : Ring12) : tag.val = 5353 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05354 (tag : Fin 10000) (htag : tag.val = 5354) (x : State) (e : Event) (dr : Ring12) : tag.val = 5354 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05355 (tag : Fin 10000) (htag : tag.val = 5355) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5355 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05356 (tag : Fin 10000) (htag : tag.val = 5356) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5356 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05357 (tag : Fin 10000) (htag : tag.val = 5357) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5357 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05358 (tag : Fin 10000) (htag : tag.val = 5358) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5358 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05359 (tag : Fin 10000) (htag : tag.val = 5359) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5359 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05360 (tag : Fin 10000) (htag : tag.val = 5360) (k : Ring12) : tag.val = 5360 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05361 (tag : Fin 10000) (htag : tag.val = 5361) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5361 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05362 (tag : Fin 10000) (htag : tag.val = 5362) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5362 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05363 (tag : Fin 10000) (htag : tag.val = 5363) (x : State) (e : Event) (dr : Ring12) : tag.val = 5363 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05364 (tag : Fin 10000) (htag : tag.val = 5364) (x : State) (e : Event) (dr : Ring12) : tag.val = 5364 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05365 (tag : Fin 10000) (htag : tag.val = 5365) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5365 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05366 (tag : Fin 10000) (htag : tag.val = 5366) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5366 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05367 (tag : Fin 10000) (htag : tag.val = 5367) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5367 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05368 (tag : Fin 10000) (htag : tag.val = 5368) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5368 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05369 (tag : Fin 10000) (htag : tag.val = 5369) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5369 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05370 (tag : Fin 10000) (htag : tag.val = 5370) (k : Ring12) : tag.val = 5370 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05371 (tag : Fin 10000) (htag : tag.val = 5371) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5371 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05372 (tag : Fin 10000) (htag : tag.val = 5372) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5372 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05373 (tag : Fin 10000) (htag : tag.val = 5373) (x : State) (e : Event) (dr : Ring12) : tag.val = 5373 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05374 (tag : Fin 10000) (htag : tag.val = 5374) (x : State) (e : Event) (dr : Ring12) : tag.val = 5374 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05375 (tag : Fin 10000) (htag : tag.val = 5375) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5375 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05376 (tag : Fin 10000) (htag : tag.val = 5376) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5376 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05377 (tag : Fin 10000) (htag : tag.val = 5377) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5377 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05378 (tag : Fin 10000) (htag : tag.val = 5378) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5378 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05379 (tag : Fin 10000) (htag : tag.val = 5379) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5379 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05380 (tag : Fin 10000) (htag : tag.val = 5380) (k : Ring12) : tag.val = 5380 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05381 (tag : Fin 10000) (htag : tag.val = 5381) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5381 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05382 (tag : Fin 10000) (htag : tag.val = 5382) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5382 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05383 (tag : Fin 10000) (htag : tag.val = 5383) (x : State) (e : Event) (dr : Ring12) : tag.val = 5383 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05384 (tag : Fin 10000) (htag : tag.val = 5384) (x : State) (e : Event) (dr : Ring12) : tag.val = 5384 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05385 (tag : Fin 10000) (htag : tag.val = 5385) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5385 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05386 (tag : Fin 10000) (htag : tag.val = 5386) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5386 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05387 (tag : Fin 10000) (htag : tag.val = 5387) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5387 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05388 (tag : Fin 10000) (htag : tag.val = 5388) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5388 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05389 (tag : Fin 10000) (htag : tag.val = 5389) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5389 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05390 (tag : Fin 10000) (htag : tag.val = 5390) (k : Ring12) : tag.val = 5390 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05391 (tag : Fin 10000) (htag : tag.val = 5391) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5391 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05392 (tag : Fin 10000) (htag : tag.val = 5392) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5392 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05393 (tag : Fin 10000) (htag : tag.val = 5393) (x : State) (e : Event) (dr : Ring12) : tag.val = 5393 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05394 (tag : Fin 10000) (htag : tag.val = 5394) (x : State) (e : Event) (dr : Ring12) : tag.val = 5394 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05395 (tag : Fin 10000) (htag : tag.val = 5395) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5395 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05396 (tag : Fin 10000) (htag : tag.val = 5396) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5396 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05397 (tag : Fin 10000) (htag : tag.val = 5397) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5397 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05398 (tag : Fin 10000) (htag : tag.val = 5398) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5398 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05399 (tag : Fin 10000) (htag : tag.val = 5399) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5399 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
