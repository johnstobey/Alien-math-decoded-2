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
theorem generated_00400 (tag : Fin 10000) (htag : tag.val = 400) (k : Ring12) : tag.val = 400 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00401 (tag : Fin 10000) (htag : tag.val = 401) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 401 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00402 (tag : Fin 10000) (htag : tag.val = 402) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 402 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00403 (tag : Fin 10000) (htag : tag.val = 403) (x : State) (e : Event) (dr : Ring12) : tag.val = 403 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00404 (tag : Fin 10000) (htag : tag.val = 404) (x : State) (e : Event) (dr : Ring12) : tag.val = 404 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00405 (tag : Fin 10000) (htag : tag.val = 405) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 405 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00406 (tag : Fin 10000) (htag : tag.val = 406) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 406 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00407 (tag : Fin 10000) (htag : tag.val = 407) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 407 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00408 (tag : Fin 10000) (htag : tag.val = 408) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 408 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00409 (tag : Fin 10000) (htag : tag.val = 409) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 409 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00410 (tag : Fin 10000) (htag : tag.val = 410) (k : Ring12) : tag.val = 410 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00411 (tag : Fin 10000) (htag : tag.val = 411) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 411 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00412 (tag : Fin 10000) (htag : tag.val = 412) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 412 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00413 (tag : Fin 10000) (htag : tag.val = 413) (x : State) (e : Event) (dr : Ring12) : tag.val = 413 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00414 (tag : Fin 10000) (htag : tag.val = 414) (x : State) (e : Event) (dr : Ring12) : tag.val = 414 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00415 (tag : Fin 10000) (htag : tag.val = 415) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 415 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00416 (tag : Fin 10000) (htag : tag.val = 416) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 416 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00417 (tag : Fin 10000) (htag : tag.val = 417) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 417 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00418 (tag : Fin 10000) (htag : tag.val = 418) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 418 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00419 (tag : Fin 10000) (htag : tag.val = 419) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 419 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00420 (tag : Fin 10000) (htag : tag.val = 420) (k : Ring12) : tag.val = 420 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00421 (tag : Fin 10000) (htag : tag.val = 421) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 421 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00422 (tag : Fin 10000) (htag : tag.val = 422) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 422 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00423 (tag : Fin 10000) (htag : tag.val = 423) (x : State) (e : Event) (dr : Ring12) : tag.val = 423 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00424 (tag : Fin 10000) (htag : tag.val = 424) (x : State) (e : Event) (dr : Ring12) : tag.val = 424 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00425 (tag : Fin 10000) (htag : tag.val = 425) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 425 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00426 (tag : Fin 10000) (htag : tag.val = 426) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 426 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00427 (tag : Fin 10000) (htag : tag.val = 427) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 427 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00428 (tag : Fin 10000) (htag : tag.val = 428) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 428 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00429 (tag : Fin 10000) (htag : tag.val = 429) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 429 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00430 (tag : Fin 10000) (htag : tag.val = 430) (k : Ring12) : tag.val = 430 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00431 (tag : Fin 10000) (htag : tag.val = 431) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 431 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00432 (tag : Fin 10000) (htag : tag.val = 432) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 432 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00433 (tag : Fin 10000) (htag : tag.val = 433) (x : State) (e : Event) (dr : Ring12) : tag.val = 433 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00434 (tag : Fin 10000) (htag : tag.val = 434) (x : State) (e : Event) (dr : Ring12) : tag.val = 434 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00435 (tag : Fin 10000) (htag : tag.val = 435) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 435 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00436 (tag : Fin 10000) (htag : tag.val = 436) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 436 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00437 (tag : Fin 10000) (htag : tag.val = 437) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 437 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00438 (tag : Fin 10000) (htag : tag.val = 438) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 438 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00439 (tag : Fin 10000) (htag : tag.val = 439) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 439 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00440 (tag : Fin 10000) (htag : tag.val = 440) (k : Ring12) : tag.val = 440 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00441 (tag : Fin 10000) (htag : tag.val = 441) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 441 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00442 (tag : Fin 10000) (htag : tag.val = 442) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 442 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00443 (tag : Fin 10000) (htag : tag.val = 443) (x : State) (e : Event) (dr : Ring12) : tag.val = 443 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00444 (tag : Fin 10000) (htag : tag.val = 444) (x : State) (e : Event) (dr : Ring12) : tag.val = 444 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00445 (tag : Fin 10000) (htag : tag.val = 445) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 445 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00446 (tag : Fin 10000) (htag : tag.val = 446) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 446 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00447 (tag : Fin 10000) (htag : tag.val = 447) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 447 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00448 (tag : Fin 10000) (htag : tag.val = 448) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 448 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00449 (tag : Fin 10000) (htag : tag.val = 449) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 449 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00450 (tag : Fin 10000) (htag : tag.val = 450) (k : Ring12) : tag.val = 450 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00451 (tag : Fin 10000) (htag : tag.val = 451) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 451 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00452 (tag : Fin 10000) (htag : tag.val = 452) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 452 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00453 (tag : Fin 10000) (htag : tag.val = 453) (x : State) (e : Event) (dr : Ring12) : tag.val = 453 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00454 (tag : Fin 10000) (htag : tag.val = 454) (x : State) (e : Event) (dr : Ring12) : tag.val = 454 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00455 (tag : Fin 10000) (htag : tag.val = 455) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 455 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00456 (tag : Fin 10000) (htag : tag.val = 456) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 456 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00457 (tag : Fin 10000) (htag : tag.val = 457) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 457 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00458 (tag : Fin 10000) (htag : tag.val = 458) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 458 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00459 (tag : Fin 10000) (htag : tag.val = 459) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 459 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00460 (tag : Fin 10000) (htag : tag.val = 460) (k : Ring12) : tag.val = 460 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00461 (tag : Fin 10000) (htag : tag.val = 461) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 461 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00462 (tag : Fin 10000) (htag : tag.val = 462) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 462 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00463 (tag : Fin 10000) (htag : tag.val = 463) (x : State) (e : Event) (dr : Ring12) : tag.val = 463 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00464 (tag : Fin 10000) (htag : tag.val = 464) (x : State) (e : Event) (dr : Ring12) : tag.val = 464 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00465 (tag : Fin 10000) (htag : tag.val = 465) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 465 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00466 (tag : Fin 10000) (htag : tag.val = 466) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 466 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00467 (tag : Fin 10000) (htag : tag.val = 467) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 467 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00468 (tag : Fin 10000) (htag : tag.val = 468) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 468 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00469 (tag : Fin 10000) (htag : tag.val = 469) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 469 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00470 (tag : Fin 10000) (htag : tag.val = 470) (k : Ring12) : tag.val = 470 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00471 (tag : Fin 10000) (htag : tag.val = 471) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 471 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00472 (tag : Fin 10000) (htag : tag.val = 472) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 472 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00473 (tag : Fin 10000) (htag : tag.val = 473) (x : State) (e : Event) (dr : Ring12) : tag.val = 473 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00474 (tag : Fin 10000) (htag : tag.val = 474) (x : State) (e : Event) (dr : Ring12) : tag.val = 474 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00475 (tag : Fin 10000) (htag : tag.val = 475) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 475 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00476 (tag : Fin 10000) (htag : tag.val = 476) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 476 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00477 (tag : Fin 10000) (htag : tag.val = 477) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 477 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00478 (tag : Fin 10000) (htag : tag.val = 478) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 478 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00479 (tag : Fin 10000) (htag : tag.val = 479) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 479 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00480 (tag : Fin 10000) (htag : tag.val = 480) (k : Ring12) : tag.val = 480 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00481 (tag : Fin 10000) (htag : tag.val = 481) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 481 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00482 (tag : Fin 10000) (htag : tag.val = 482) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 482 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00483 (tag : Fin 10000) (htag : tag.val = 483) (x : State) (e : Event) (dr : Ring12) : tag.val = 483 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00484 (tag : Fin 10000) (htag : tag.val = 484) (x : State) (e : Event) (dr : Ring12) : tag.val = 484 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00485 (tag : Fin 10000) (htag : tag.val = 485) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 485 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00486 (tag : Fin 10000) (htag : tag.val = 486) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 486 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00487 (tag : Fin 10000) (htag : tag.val = 487) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 487 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00488 (tag : Fin 10000) (htag : tag.val = 488) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 488 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00489 (tag : Fin 10000) (htag : tag.val = 489) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 489 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00490 (tag : Fin 10000) (htag : tag.val = 490) (k : Ring12) : tag.val = 490 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00491 (tag : Fin 10000) (htag : tag.val = 491) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 491 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00492 (tag : Fin 10000) (htag : tag.val = 492) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 492 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00493 (tag : Fin 10000) (htag : tag.val = 493) (x : State) (e : Event) (dr : Ring12) : tag.val = 493 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00494 (tag : Fin 10000) (htag : tag.val = 494) (x : State) (e : Event) (dr : Ring12) : tag.val = 494 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00495 (tag : Fin 10000) (htag : tag.val = 495) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 495 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00496 (tag : Fin 10000) (htag : tag.val = 496) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 496 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00497 (tag : Fin 10000) (htag : tag.val = 497) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 497 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00498 (tag : Fin 10000) (htag : tag.val = 498) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 498 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00499 (tag : Fin 10000) (htag : tag.val = 499) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 499 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
