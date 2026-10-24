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
theorem generated_04300 (tag : Fin 10000) (htag : tag.val = 4300) (k : Ring12) : tag.val = 4300 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04301 (tag : Fin 10000) (htag : tag.val = 4301) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4301 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04302 (tag : Fin 10000) (htag : tag.val = 4302) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4302 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04303 (tag : Fin 10000) (htag : tag.val = 4303) (x : State) (e : Event) (dr : Ring12) : tag.val = 4303 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04304 (tag : Fin 10000) (htag : tag.val = 4304) (x : State) (e : Event) (dr : Ring12) : tag.val = 4304 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04305 (tag : Fin 10000) (htag : tag.val = 4305) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4305 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04306 (tag : Fin 10000) (htag : tag.val = 4306) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4306 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04307 (tag : Fin 10000) (htag : tag.val = 4307) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4307 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04308 (tag : Fin 10000) (htag : tag.val = 4308) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4308 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04309 (tag : Fin 10000) (htag : tag.val = 4309) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4309 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04310 (tag : Fin 10000) (htag : tag.val = 4310) (k : Ring12) : tag.val = 4310 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04311 (tag : Fin 10000) (htag : tag.val = 4311) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4311 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04312 (tag : Fin 10000) (htag : tag.val = 4312) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4312 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04313 (tag : Fin 10000) (htag : tag.val = 4313) (x : State) (e : Event) (dr : Ring12) : tag.val = 4313 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04314 (tag : Fin 10000) (htag : tag.val = 4314) (x : State) (e : Event) (dr : Ring12) : tag.val = 4314 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04315 (tag : Fin 10000) (htag : tag.val = 4315) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4315 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04316 (tag : Fin 10000) (htag : tag.val = 4316) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4316 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04317 (tag : Fin 10000) (htag : tag.val = 4317) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4317 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04318 (tag : Fin 10000) (htag : tag.val = 4318) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4318 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04319 (tag : Fin 10000) (htag : tag.val = 4319) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4319 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04320 (tag : Fin 10000) (htag : tag.val = 4320) (k : Ring12) : tag.val = 4320 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04321 (tag : Fin 10000) (htag : tag.val = 4321) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4321 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04322 (tag : Fin 10000) (htag : tag.val = 4322) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4322 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04323 (tag : Fin 10000) (htag : tag.val = 4323) (x : State) (e : Event) (dr : Ring12) : tag.val = 4323 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04324 (tag : Fin 10000) (htag : tag.val = 4324) (x : State) (e : Event) (dr : Ring12) : tag.val = 4324 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04325 (tag : Fin 10000) (htag : tag.val = 4325) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4325 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04326 (tag : Fin 10000) (htag : tag.val = 4326) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4326 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04327 (tag : Fin 10000) (htag : tag.val = 4327) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4327 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04328 (tag : Fin 10000) (htag : tag.val = 4328) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4328 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04329 (tag : Fin 10000) (htag : tag.val = 4329) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4329 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04330 (tag : Fin 10000) (htag : tag.val = 4330) (k : Ring12) : tag.val = 4330 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04331 (tag : Fin 10000) (htag : tag.val = 4331) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4331 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04332 (tag : Fin 10000) (htag : tag.val = 4332) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4332 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04333 (tag : Fin 10000) (htag : tag.val = 4333) (x : State) (e : Event) (dr : Ring12) : tag.val = 4333 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04334 (tag : Fin 10000) (htag : tag.val = 4334) (x : State) (e : Event) (dr : Ring12) : tag.val = 4334 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04335 (tag : Fin 10000) (htag : tag.val = 4335) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4335 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04336 (tag : Fin 10000) (htag : tag.val = 4336) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4336 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04337 (tag : Fin 10000) (htag : tag.val = 4337) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4337 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04338 (tag : Fin 10000) (htag : tag.val = 4338) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4338 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04339 (tag : Fin 10000) (htag : tag.val = 4339) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4339 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04340 (tag : Fin 10000) (htag : tag.val = 4340) (k : Ring12) : tag.val = 4340 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04341 (tag : Fin 10000) (htag : tag.val = 4341) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4341 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04342 (tag : Fin 10000) (htag : tag.val = 4342) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4342 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04343 (tag : Fin 10000) (htag : tag.val = 4343) (x : State) (e : Event) (dr : Ring12) : tag.val = 4343 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04344 (tag : Fin 10000) (htag : tag.val = 4344) (x : State) (e : Event) (dr : Ring12) : tag.val = 4344 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04345 (tag : Fin 10000) (htag : tag.val = 4345) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4345 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04346 (tag : Fin 10000) (htag : tag.val = 4346) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4346 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04347 (tag : Fin 10000) (htag : tag.val = 4347) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4347 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04348 (tag : Fin 10000) (htag : tag.val = 4348) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4348 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04349 (tag : Fin 10000) (htag : tag.val = 4349) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4349 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04350 (tag : Fin 10000) (htag : tag.val = 4350) (k : Ring12) : tag.val = 4350 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04351 (tag : Fin 10000) (htag : tag.val = 4351) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4351 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04352 (tag : Fin 10000) (htag : tag.val = 4352) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4352 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04353 (tag : Fin 10000) (htag : tag.val = 4353) (x : State) (e : Event) (dr : Ring12) : tag.val = 4353 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04354 (tag : Fin 10000) (htag : tag.val = 4354) (x : State) (e : Event) (dr : Ring12) : tag.val = 4354 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04355 (tag : Fin 10000) (htag : tag.val = 4355) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4355 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04356 (tag : Fin 10000) (htag : tag.val = 4356) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4356 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04357 (tag : Fin 10000) (htag : tag.val = 4357) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4357 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04358 (tag : Fin 10000) (htag : tag.val = 4358) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4358 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04359 (tag : Fin 10000) (htag : tag.val = 4359) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4359 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04360 (tag : Fin 10000) (htag : tag.val = 4360) (k : Ring12) : tag.val = 4360 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04361 (tag : Fin 10000) (htag : tag.val = 4361) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4361 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04362 (tag : Fin 10000) (htag : tag.val = 4362) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4362 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04363 (tag : Fin 10000) (htag : tag.val = 4363) (x : State) (e : Event) (dr : Ring12) : tag.val = 4363 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04364 (tag : Fin 10000) (htag : tag.val = 4364) (x : State) (e : Event) (dr : Ring12) : tag.val = 4364 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04365 (tag : Fin 10000) (htag : tag.val = 4365) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4365 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04366 (tag : Fin 10000) (htag : tag.val = 4366) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4366 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04367 (tag : Fin 10000) (htag : tag.val = 4367) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4367 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04368 (tag : Fin 10000) (htag : tag.val = 4368) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4368 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04369 (tag : Fin 10000) (htag : tag.val = 4369) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4369 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04370 (tag : Fin 10000) (htag : tag.val = 4370) (k : Ring12) : tag.val = 4370 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04371 (tag : Fin 10000) (htag : tag.val = 4371) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4371 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04372 (tag : Fin 10000) (htag : tag.val = 4372) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4372 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04373 (tag : Fin 10000) (htag : tag.val = 4373) (x : State) (e : Event) (dr : Ring12) : tag.val = 4373 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04374 (tag : Fin 10000) (htag : tag.val = 4374) (x : State) (e : Event) (dr : Ring12) : tag.val = 4374 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04375 (tag : Fin 10000) (htag : tag.val = 4375) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4375 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04376 (tag : Fin 10000) (htag : tag.val = 4376) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4376 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04377 (tag : Fin 10000) (htag : tag.val = 4377) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4377 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04378 (tag : Fin 10000) (htag : tag.val = 4378) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4378 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04379 (tag : Fin 10000) (htag : tag.val = 4379) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4379 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04380 (tag : Fin 10000) (htag : tag.val = 4380) (k : Ring12) : tag.val = 4380 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04381 (tag : Fin 10000) (htag : tag.val = 4381) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4381 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04382 (tag : Fin 10000) (htag : tag.val = 4382) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4382 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04383 (tag : Fin 10000) (htag : tag.val = 4383) (x : State) (e : Event) (dr : Ring12) : tag.val = 4383 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04384 (tag : Fin 10000) (htag : tag.val = 4384) (x : State) (e : Event) (dr : Ring12) : tag.val = 4384 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04385 (tag : Fin 10000) (htag : tag.val = 4385) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4385 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04386 (tag : Fin 10000) (htag : tag.val = 4386) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4386 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04387 (tag : Fin 10000) (htag : tag.val = 4387) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4387 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04388 (tag : Fin 10000) (htag : tag.val = 4388) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4388 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04389 (tag : Fin 10000) (htag : tag.val = 4389) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4389 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04390 (tag : Fin 10000) (htag : tag.val = 4390) (k : Ring12) : tag.val = 4390 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04391 (tag : Fin 10000) (htag : tag.val = 4391) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4391 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04392 (tag : Fin 10000) (htag : tag.val = 4392) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4392 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04393 (tag : Fin 10000) (htag : tag.val = 4393) (x : State) (e : Event) (dr : Ring12) : tag.val = 4393 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04394 (tag : Fin 10000) (htag : tag.val = 4394) (x : State) (e : Event) (dr : Ring12) : tag.val = 4394 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04395 (tag : Fin 10000) (htag : tag.val = 4395) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4395 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04396 (tag : Fin 10000) (htag : tag.val = 4396) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4396 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04397 (tag : Fin 10000) (htag : tag.val = 4397) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4397 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04398 (tag : Fin 10000) (htag : tag.val = 4398) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4398 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04399 (tag : Fin 10000) (htag : tag.val = 4399) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4399 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
