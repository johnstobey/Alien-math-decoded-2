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
theorem generated_04500 (tag : Fin 10000) (htag : tag.val = 4500) (k : Ring12) : tag.val = 4500 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04501 (tag : Fin 10000) (htag : tag.val = 4501) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4501 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04502 (tag : Fin 10000) (htag : tag.val = 4502) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4502 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04503 (tag : Fin 10000) (htag : tag.val = 4503) (x : State) (e : Event) (dr : Ring12) : tag.val = 4503 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04504 (tag : Fin 10000) (htag : tag.val = 4504) (x : State) (e : Event) (dr : Ring12) : tag.val = 4504 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04505 (tag : Fin 10000) (htag : tag.val = 4505) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4505 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04506 (tag : Fin 10000) (htag : tag.val = 4506) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4506 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04507 (tag : Fin 10000) (htag : tag.val = 4507) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4507 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04508 (tag : Fin 10000) (htag : tag.val = 4508) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4508 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04509 (tag : Fin 10000) (htag : tag.val = 4509) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4509 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04510 (tag : Fin 10000) (htag : tag.val = 4510) (k : Ring12) : tag.val = 4510 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04511 (tag : Fin 10000) (htag : tag.val = 4511) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4511 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04512 (tag : Fin 10000) (htag : tag.val = 4512) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4512 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04513 (tag : Fin 10000) (htag : tag.val = 4513) (x : State) (e : Event) (dr : Ring12) : tag.val = 4513 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04514 (tag : Fin 10000) (htag : tag.val = 4514) (x : State) (e : Event) (dr : Ring12) : tag.val = 4514 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04515 (tag : Fin 10000) (htag : tag.val = 4515) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4515 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04516 (tag : Fin 10000) (htag : tag.val = 4516) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4516 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04517 (tag : Fin 10000) (htag : tag.val = 4517) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4517 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04518 (tag : Fin 10000) (htag : tag.val = 4518) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4518 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04519 (tag : Fin 10000) (htag : tag.val = 4519) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4519 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04520 (tag : Fin 10000) (htag : tag.val = 4520) (k : Ring12) : tag.val = 4520 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04521 (tag : Fin 10000) (htag : tag.val = 4521) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4521 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04522 (tag : Fin 10000) (htag : tag.val = 4522) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4522 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04523 (tag : Fin 10000) (htag : tag.val = 4523) (x : State) (e : Event) (dr : Ring12) : tag.val = 4523 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04524 (tag : Fin 10000) (htag : tag.val = 4524) (x : State) (e : Event) (dr : Ring12) : tag.val = 4524 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04525 (tag : Fin 10000) (htag : tag.val = 4525) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4525 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04526 (tag : Fin 10000) (htag : tag.val = 4526) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4526 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04527 (tag : Fin 10000) (htag : tag.val = 4527) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4527 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04528 (tag : Fin 10000) (htag : tag.val = 4528) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4528 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04529 (tag : Fin 10000) (htag : tag.val = 4529) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4529 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04530 (tag : Fin 10000) (htag : tag.val = 4530) (k : Ring12) : tag.val = 4530 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04531 (tag : Fin 10000) (htag : tag.val = 4531) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4531 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04532 (tag : Fin 10000) (htag : tag.val = 4532) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4532 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04533 (tag : Fin 10000) (htag : tag.val = 4533) (x : State) (e : Event) (dr : Ring12) : tag.val = 4533 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04534 (tag : Fin 10000) (htag : tag.val = 4534) (x : State) (e : Event) (dr : Ring12) : tag.val = 4534 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04535 (tag : Fin 10000) (htag : tag.val = 4535) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4535 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04536 (tag : Fin 10000) (htag : tag.val = 4536) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4536 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04537 (tag : Fin 10000) (htag : tag.val = 4537) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4537 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04538 (tag : Fin 10000) (htag : tag.val = 4538) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4538 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04539 (tag : Fin 10000) (htag : tag.val = 4539) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4539 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04540 (tag : Fin 10000) (htag : tag.val = 4540) (k : Ring12) : tag.val = 4540 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04541 (tag : Fin 10000) (htag : tag.val = 4541) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4541 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04542 (tag : Fin 10000) (htag : tag.val = 4542) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4542 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04543 (tag : Fin 10000) (htag : tag.val = 4543) (x : State) (e : Event) (dr : Ring12) : tag.val = 4543 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04544 (tag : Fin 10000) (htag : tag.val = 4544) (x : State) (e : Event) (dr : Ring12) : tag.val = 4544 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04545 (tag : Fin 10000) (htag : tag.val = 4545) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4545 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04546 (tag : Fin 10000) (htag : tag.val = 4546) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4546 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04547 (tag : Fin 10000) (htag : tag.val = 4547) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4547 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04548 (tag : Fin 10000) (htag : tag.val = 4548) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4548 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04549 (tag : Fin 10000) (htag : tag.val = 4549) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4549 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04550 (tag : Fin 10000) (htag : tag.val = 4550) (k : Ring12) : tag.val = 4550 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04551 (tag : Fin 10000) (htag : tag.val = 4551) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4551 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04552 (tag : Fin 10000) (htag : tag.val = 4552) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4552 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04553 (tag : Fin 10000) (htag : tag.val = 4553) (x : State) (e : Event) (dr : Ring12) : tag.val = 4553 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04554 (tag : Fin 10000) (htag : tag.val = 4554) (x : State) (e : Event) (dr : Ring12) : tag.val = 4554 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04555 (tag : Fin 10000) (htag : tag.val = 4555) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4555 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04556 (tag : Fin 10000) (htag : tag.val = 4556) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4556 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04557 (tag : Fin 10000) (htag : tag.val = 4557) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4557 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04558 (tag : Fin 10000) (htag : tag.val = 4558) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4558 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04559 (tag : Fin 10000) (htag : tag.val = 4559) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4559 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04560 (tag : Fin 10000) (htag : tag.val = 4560) (k : Ring12) : tag.val = 4560 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04561 (tag : Fin 10000) (htag : tag.val = 4561) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4561 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04562 (tag : Fin 10000) (htag : tag.val = 4562) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4562 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04563 (tag : Fin 10000) (htag : tag.val = 4563) (x : State) (e : Event) (dr : Ring12) : tag.val = 4563 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04564 (tag : Fin 10000) (htag : tag.val = 4564) (x : State) (e : Event) (dr : Ring12) : tag.val = 4564 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04565 (tag : Fin 10000) (htag : tag.val = 4565) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4565 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04566 (tag : Fin 10000) (htag : tag.val = 4566) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4566 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04567 (tag : Fin 10000) (htag : tag.val = 4567) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4567 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04568 (tag : Fin 10000) (htag : tag.val = 4568) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4568 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04569 (tag : Fin 10000) (htag : tag.val = 4569) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4569 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04570 (tag : Fin 10000) (htag : tag.val = 4570) (k : Ring12) : tag.val = 4570 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04571 (tag : Fin 10000) (htag : tag.val = 4571) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4571 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04572 (tag : Fin 10000) (htag : tag.val = 4572) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4572 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04573 (tag : Fin 10000) (htag : tag.val = 4573) (x : State) (e : Event) (dr : Ring12) : tag.val = 4573 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04574 (tag : Fin 10000) (htag : tag.val = 4574) (x : State) (e : Event) (dr : Ring12) : tag.val = 4574 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04575 (tag : Fin 10000) (htag : tag.val = 4575) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4575 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04576 (tag : Fin 10000) (htag : tag.val = 4576) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4576 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04577 (tag : Fin 10000) (htag : tag.val = 4577) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4577 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04578 (tag : Fin 10000) (htag : tag.val = 4578) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4578 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04579 (tag : Fin 10000) (htag : tag.val = 4579) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4579 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04580 (tag : Fin 10000) (htag : tag.val = 4580) (k : Ring12) : tag.val = 4580 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04581 (tag : Fin 10000) (htag : tag.val = 4581) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4581 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04582 (tag : Fin 10000) (htag : tag.val = 4582) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4582 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04583 (tag : Fin 10000) (htag : tag.val = 4583) (x : State) (e : Event) (dr : Ring12) : tag.val = 4583 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04584 (tag : Fin 10000) (htag : tag.val = 4584) (x : State) (e : Event) (dr : Ring12) : tag.val = 4584 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04585 (tag : Fin 10000) (htag : tag.val = 4585) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4585 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04586 (tag : Fin 10000) (htag : tag.val = 4586) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4586 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04587 (tag : Fin 10000) (htag : tag.val = 4587) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4587 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04588 (tag : Fin 10000) (htag : tag.val = 4588) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4588 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04589 (tag : Fin 10000) (htag : tag.val = 4589) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4589 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04590 (tag : Fin 10000) (htag : tag.val = 4590) (k : Ring12) : tag.val = 4590 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04591 (tag : Fin 10000) (htag : tag.val = 4591) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4591 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04592 (tag : Fin 10000) (htag : tag.val = 4592) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4592 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04593 (tag : Fin 10000) (htag : tag.val = 4593) (x : State) (e : Event) (dr : Ring12) : tag.val = 4593 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04594 (tag : Fin 10000) (htag : tag.val = 4594) (x : State) (e : Event) (dr : Ring12) : tag.val = 4594 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04595 (tag : Fin 10000) (htag : tag.val = 4595) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4595 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04596 (tag : Fin 10000) (htag : tag.val = 4596) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4596 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04597 (tag : Fin 10000) (htag : tag.val = 4597) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4597 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04598 (tag : Fin 10000) (htag : tag.val = 4598) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4598 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04599 (tag : Fin 10000) (htag : tag.val = 4599) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4599 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
