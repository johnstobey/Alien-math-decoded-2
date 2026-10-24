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
theorem generated_00300 (tag : Fin 10000) (htag : tag.val = 300) (k : Ring12) : tag.val = 300 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00301 (tag : Fin 10000) (htag : tag.val = 301) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 301 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00302 (tag : Fin 10000) (htag : tag.val = 302) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 302 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00303 (tag : Fin 10000) (htag : tag.val = 303) (x : State) (e : Event) (dr : Ring12) : tag.val = 303 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00304 (tag : Fin 10000) (htag : tag.val = 304) (x : State) (e : Event) (dr : Ring12) : tag.val = 304 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00305 (tag : Fin 10000) (htag : tag.val = 305) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 305 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00306 (tag : Fin 10000) (htag : tag.val = 306) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 306 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00307 (tag : Fin 10000) (htag : tag.val = 307) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 307 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00308 (tag : Fin 10000) (htag : tag.val = 308) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 308 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00309 (tag : Fin 10000) (htag : tag.val = 309) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 309 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00310 (tag : Fin 10000) (htag : tag.val = 310) (k : Ring12) : tag.val = 310 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00311 (tag : Fin 10000) (htag : tag.val = 311) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 311 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00312 (tag : Fin 10000) (htag : tag.val = 312) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 312 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00313 (tag : Fin 10000) (htag : tag.val = 313) (x : State) (e : Event) (dr : Ring12) : tag.val = 313 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00314 (tag : Fin 10000) (htag : tag.val = 314) (x : State) (e : Event) (dr : Ring12) : tag.val = 314 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00315 (tag : Fin 10000) (htag : tag.val = 315) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 315 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00316 (tag : Fin 10000) (htag : tag.val = 316) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 316 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00317 (tag : Fin 10000) (htag : tag.val = 317) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 317 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00318 (tag : Fin 10000) (htag : tag.val = 318) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 318 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00319 (tag : Fin 10000) (htag : tag.val = 319) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 319 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00320 (tag : Fin 10000) (htag : tag.val = 320) (k : Ring12) : tag.val = 320 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00321 (tag : Fin 10000) (htag : tag.val = 321) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 321 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00322 (tag : Fin 10000) (htag : tag.val = 322) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 322 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00323 (tag : Fin 10000) (htag : tag.val = 323) (x : State) (e : Event) (dr : Ring12) : tag.val = 323 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00324 (tag : Fin 10000) (htag : tag.val = 324) (x : State) (e : Event) (dr : Ring12) : tag.val = 324 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00325 (tag : Fin 10000) (htag : tag.val = 325) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 325 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00326 (tag : Fin 10000) (htag : tag.val = 326) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 326 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00327 (tag : Fin 10000) (htag : tag.val = 327) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 327 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00328 (tag : Fin 10000) (htag : tag.val = 328) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 328 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00329 (tag : Fin 10000) (htag : tag.val = 329) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 329 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00330 (tag : Fin 10000) (htag : tag.val = 330) (k : Ring12) : tag.val = 330 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00331 (tag : Fin 10000) (htag : tag.val = 331) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 331 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00332 (tag : Fin 10000) (htag : tag.val = 332) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 332 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00333 (tag : Fin 10000) (htag : tag.val = 333) (x : State) (e : Event) (dr : Ring12) : tag.val = 333 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00334 (tag : Fin 10000) (htag : tag.val = 334) (x : State) (e : Event) (dr : Ring12) : tag.val = 334 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00335 (tag : Fin 10000) (htag : tag.val = 335) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 335 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00336 (tag : Fin 10000) (htag : tag.val = 336) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 336 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00337 (tag : Fin 10000) (htag : tag.val = 337) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 337 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00338 (tag : Fin 10000) (htag : tag.val = 338) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 338 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00339 (tag : Fin 10000) (htag : tag.val = 339) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 339 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00340 (tag : Fin 10000) (htag : tag.val = 340) (k : Ring12) : tag.val = 340 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00341 (tag : Fin 10000) (htag : tag.val = 341) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 341 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00342 (tag : Fin 10000) (htag : tag.val = 342) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 342 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00343 (tag : Fin 10000) (htag : tag.val = 343) (x : State) (e : Event) (dr : Ring12) : tag.val = 343 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00344 (tag : Fin 10000) (htag : tag.val = 344) (x : State) (e : Event) (dr : Ring12) : tag.val = 344 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00345 (tag : Fin 10000) (htag : tag.val = 345) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 345 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00346 (tag : Fin 10000) (htag : tag.val = 346) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 346 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00347 (tag : Fin 10000) (htag : tag.val = 347) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 347 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00348 (tag : Fin 10000) (htag : tag.val = 348) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 348 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00349 (tag : Fin 10000) (htag : tag.val = 349) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 349 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00350 (tag : Fin 10000) (htag : tag.val = 350) (k : Ring12) : tag.val = 350 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00351 (tag : Fin 10000) (htag : tag.val = 351) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 351 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00352 (tag : Fin 10000) (htag : tag.val = 352) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 352 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00353 (tag : Fin 10000) (htag : tag.val = 353) (x : State) (e : Event) (dr : Ring12) : tag.val = 353 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00354 (tag : Fin 10000) (htag : tag.val = 354) (x : State) (e : Event) (dr : Ring12) : tag.val = 354 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00355 (tag : Fin 10000) (htag : tag.val = 355) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 355 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00356 (tag : Fin 10000) (htag : tag.val = 356) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 356 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00357 (tag : Fin 10000) (htag : tag.val = 357) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 357 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00358 (tag : Fin 10000) (htag : tag.val = 358) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 358 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00359 (tag : Fin 10000) (htag : tag.val = 359) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 359 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00360 (tag : Fin 10000) (htag : tag.val = 360) (k : Ring12) : tag.val = 360 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00361 (tag : Fin 10000) (htag : tag.val = 361) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 361 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00362 (tag : Fin 10000) (htag : tag.val = 362) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 362 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00363 (tag : Fin 10000) (htag : tag.val = 363) (x : State) (e : Event) (dr : Ring12) : tag.val = 363 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00364 (tag : Fin 10000) (htag : tag.val = 364) (x : State) (e : Event) (dr : Ring12) : tag.val = 364 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00365 (tag : Fin 10000) (htag : tag.val = 365) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 365 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00366 (tag : Fin 10000) (htag : tag.val = 366) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 366 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00367 (tag : Fin 10000) (htag : tag.val = 367) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 367 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00368 (tag : Fin 10000) (htag : tag.val = 368) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 368 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00369 (tag : Fin 10000) (htag : tag.val = 369) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 369 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00370 (tag : Fin 10000) (htag : tag.val = 370) (k : Ring12) : tag.val = 370 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00371 (tag : Fin 10000) (htag : tag.val = 371) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 371 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00372 (tag : Fin 10000) (htag : tag.val = 372) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 372 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00373 (tag : Fin 10000) (htag : tag.val = 373) (x : State) (e : Event) (dr : Ring12) : tag.val = 373 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00374 (tag : Fin 10000) (htag : tag.val = 374) (x : State) (e : Event) (dr : Ring12) : tag.val = 374 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00375 (tag : Fin 10000) (htag : tag.val = 375) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 375 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00376 (tag : Fin 10000) (htag : tag.val = 376) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 376 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00377 (tag : Fin 10000) (htag : tag.val = 377) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 377 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00378 (tag : Fin 10000) (htag : tag.val = 378) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 378 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00379 (tag : Fin 10000) (htag : tag.val = 379) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 379 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00380 (tag : Fin 10000) (htag : tag.val = 380) (k : Ring12) : tag.val = 380 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00381 (tag : Fin 10000) (htag : tag.val = 381) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 381 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00382 (tag : Fin 10000) (htag : tag.val = 382) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 382 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00383 (tag : Fin 10000) (htag : tag.val = 383) (x : State) (e : Event) (dr : Ring12) : tag.val = 383 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00384 (tag : Fin 10000) (htag : tag.val = 384) (x : State) (e : Event) (dr : Ring12) : tag.val = 384 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00385 (tag : Fin 10000) (htag : tag.val = 385) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 385 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00386 (tag : Fin 10000) (htag : tag.val = 386) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 386 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00387 (tag : Fin 10000) (htag : tag.val = 387) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 387 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00388 (tag : Fin 10000) (htag : tag.val = 388) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 388 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00389 (tag : Fin 10000) (htag : tag.val = 389) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 389 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00390 (tag : Fin 10000) (htag : tag.val = 390) (k : Ring12) : tag.val = 390 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00391 (tag : Fin 10000) (htag : tag.val = 391) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 391 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00392 (tag : Fin 10000) (htag : tag.val = 392) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 392 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00393 (tag : Fin 10000) (htag : tag.val = 393) (x : State) (e : Event) (dr : Ring12) : tag.val = 393 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00394 (tag : Fin 10000) (htag : tag.val = 394) (x : State) (e : Event) (dr : Ring12) : tag.val = 394 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00395 (tag : Fin 10000) (htag : tag.val = 395) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 395 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00396 (tag : Fin 10000) (htag : tag.val = 396) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 396 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00397 (tag : Fin 10000) (htag : tag.val = 397) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 397 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00398 (tag : Fin 10000) (htag : tag.val = 398) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 398 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00399 (tag : Fin 10000) (htag : tag.val = 399) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 399 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
