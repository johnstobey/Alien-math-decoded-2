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
theorem generated_03500 (tag : Fin 10000) (htag : tag.val = 3500) (k : Ring12) : tag.val = 3500 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03501 (tag : Fin 10000) (htag : tag.val = 3501) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3501 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03502 (tag : Fin 10000) (htag : tag.val = 3502) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3502 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03503 (tag : Fin 10000) (htag : tag.val = 3503) (x : State) (e : Event) (dr : Ring12) : tag.val = 3503 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03504 (tag : Fin 10000) (htag : tag.val = 3504) (x : State) (e : Event) (dr : Ring12) : tag.val = 3504 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03505 (tag : Fin 10000) (htag : tag.val = 3505) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3505 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03506 (tag : Fin 10000) (htag : tag.val = 3506) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3506 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03507 (tag : Fin 10000) (htag : tag.val = 3507) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3507 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03508 (tag : Fin 10000) (htag : tag.val = 3508) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3508 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03509 (tag : Fin 10000) (htag : tag.val = 3509) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3509 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03510 (tag : Fin 10000) (htag : tag.val = 3510) (k : Ring12) : tag.val = 3510 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03511 (tag : Fin 10000) (htag : tag.val = 3511) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3511 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03512 (tag : Fin 10000) (htag : tag.val = 3512) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3512 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03513 (tag : Fin 10000) (htag : tag.val = 3513) (x : State) (e : Event) (dr : Ring12) : tag.val = 3513 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03514 (tag : Fin 10000) (htag : tag.val = 3514) (x : State) (e : Event) (dr : Ring12) : tag.val = 3514 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03515 (tag : Fin 10000) (htag : tag.val = 3515) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3515 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03516 (tag : Fin 10000) (htag : tag.val = 3516) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3516 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03517 (tag : Fin 10000) (htag : tag.val = 3517) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3517 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03518 (tag : Fin 10000) (htag : tag.val = 3518) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3518 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03519 (tag : Fin 10000) (htag : tag.val = 3519) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3519 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03520 (tag : Fin 10000) (htag : tag.val = 3520) (k : Ring12) : tag.val = 3520 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03521 (tag : Fin 10000) (htag : tag.val = 3521) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3521 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03522 (tag : Fin 10000) (htag : tag.val = 3522) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3522 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03523 (tag : Fin 10000) (htag : tag.val = 3523) (x : State) (e : Event) (dr : Ring12) : tag.val = 3523 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03524 (tag : Fin 10000) (htag : tag.val = 3524) (x : State) (e : Event) (dr : Ring12) : tag.val = 3524 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03525 (tag : Fin 10000) (htag : tag.val = 3525) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3525 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03526 (tag : Fin 10000) (htag : tag.val = 3526) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3526 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03527 (tag : Fin 10000) (htag : tag.val = 3527) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3527 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03528 (tag : Fin 10000) (htag : tag.val = 3528) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3528 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03529 (tag : Fin 10000) (htag : tag.val = 3529) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3529 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03530 (tag : Fin 10000) (htag : tag.val = 3530) (k : Ring12) : tag.val = 3530 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03531 (tag : Fin 10000) (htag : tag.val = 3531) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3531 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03532 (tag : Fin 10000) (htag : tag.val = 3532) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3532 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03533 (tag : Fin 10000) (htag : tag.val = 3533) (x : State) (e : Event) (dr : Ring12) : tag.val = 3533 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03534 (tag : Fin 10000) (htag : tag.val = 3534) (x : State) (e : Event) (dr : Ring12) : tag.val = 3534 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03535 (tag : Fin 10000) (htag : tag.val = 3535) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3535 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03536 (tag : Fin 10000) (htag : tag.val = 3536) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3536 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03537 (tag : Fin 10000) (htag : tag.val = 3537) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3537 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03538 (tag : Fin 10000) (htag : tag.val = 3538) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3538 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03539 (tag : Fin 10000) (htag : tag.val = 3539) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3539 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03540 (tag : Fin 10000) (htag : tag.val = 3540) (k : Ring12) : tag.val = 3540 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03541 (tag : Fin 10000) (htag : tag.val = 3541) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3541 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03542 (tag : Fin 10000) (htag : tag.val = 3542) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3542 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03543 (tag : Fin 10000) (htag : tag.val = 3543) (x : State) (e : Event) (dr : Ring12) : tag.val = 3543 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03544 (tag : Fin 10000) (htag : tag.val = 3544) (x : State) (e : Event) (dr : Ring12) : tag.val = 3544 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03545 (tag : Fin 10000) (htag : tag.val = 3545) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3545 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03546 (tag : Fin 10000) (htag : tag.val = 3546) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3546 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03547 (tag : Fin 10000) (htag : tag.val = 3547) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3547 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03548 (tag : Fin 10000) (htag : tag.val = 3548) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3548 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03549 (tag : Fin 10000) (htag : tag.val = 3549) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3549 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03550 (tag : Fin 10000) (htag : tag.val = 3550) (k : Ring12) : tag.val = 3550 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03551 (tag : Fin 10000) (htag : tag.val = 3551) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3551 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03552 (tag : Fin 10000) (htag : tag.val = 3552) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3552 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03553 (tag : Fin 10000) (htag : tag.val = 3553) (x : State) (e : Event) (dr : Ring12) : tag.val = 3553 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03554 (tag : Fin 10000) (htag : tag.val = 3554) (x : State) (e : Event) (dr : Ring12) : tag.val = 3554 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03555 (tag : Fin 10000) (htag : tag.val = 3555) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3555 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03556 (tag : Fin 10000) (htag : tag.val = 3556) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3556 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03557 (tag : Fin 10000) (htag : tag.val = 3557) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3557 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03558 (tag : Fin 10000) (htag : tag.val = 3558) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3558 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03559 (tag : Fin 10000) (htag : tag.val = 3559) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3559 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03560 (tag : Fin 10000) (htag : tag.val = 3560) (k : Ring12) : tag.val = 3560 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03561 (tag : Fin 10000) (htag : tag.val = 3561) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3561 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03562 (tag : Fin 10000) (htag : tag.val = 3562) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3562 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03563 (tag : Fin 10000) (htag : tag.val = 3563) (x : State) (e : Event) (dr : Ring12) : tag.val = 3563 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03564 (tag : Fin 10000) (htag : tag.val = 3564) (x : State) (e : Event) (dr : Ring12) : tag.val = 3564 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03565 (tag : Fin 10000) (htag : tag.val = 3565) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3565 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03566 (tag : Fin 10000) (htag : tag.val = 3566) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3566 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03567 (tag : Fin 10000) (htag : tag.val = 3567) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3567 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03568 (tag : Fin 10000) (htag : tag.val = 3568) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3568 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03569 (tag : Fin 10000) (htag : tag.val = 3569) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3569 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03570 (tag : Fin 10000) (htag : tag.val = 3570) (k : Ring12) : tag.val = 3570 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03571 (tag : Fin 10000) (htag : tag.val = 3571) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3571 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03572 (tag : Fin 10000) (htag : tag.val = 3572) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3572 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03573 (tag : Fin 10000) (htag : tag.val = 3573) (x : State) (e : Event) (dr : Ring12) : tag.val = 3573 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03574 (tag : Fin 10000) (htag : tag.val = 3574) (x : State) (e : Event) (dr : Ring12) : tag.val = 3574 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03575 (tag : Fin 10000) (htag : tag.val = 3575) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3575 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03576 (tag : Fin 10000) (htag : tag.val = 3576) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3576 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03577 (tag : Fin 10000) (htag : tag.val = 3577) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3577 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03578 (tag : Fin 10000) (htag : tag.val = 3578) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3578 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03579 (tag : Fin 10000) (htag : tag.val = 3579) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3579 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03580 (tag : Fin 10000) (htag : tag.val = 3580) (k : Ring12) : tag.val = 3580 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03581 (tag : Fin 10000) (htag : tag.val = 3581) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3581 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03582 (tag : Fin 10000) (htag : tag.val = 3582) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3582 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03583 (tag : Fin 10000) (htag : tag.val = 3583) (x : State) (e : Event) (dr : Ring12) : tag.val = 3583 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03584 (tag : Fin 10000) (htag : tag.val = 3584) (x : State) (e : Event) (dr : Ring12) : tag.val = 3584 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03585 (tag : Fin 10000) (htag : tag.val = 3585) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3585 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03586 (tag : Fin 10000) (htag : tag.val = 3586) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3586 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03587 (tag : Fin 10000) (htag : tag.val = 3587) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3587 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03588 (tag : Fin 10000) (htag : tag.val = 3588) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3588 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03589 (tag : Fin 10000) (htag : tag.val = 3589) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3589 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03590 (tag : Fin 10000) (htag : tag.val = 3590) (k : Ring12) : tag.val = 3590 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03591 (tag : Fin 10000) (htag : tag.val = 3591) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3591 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03592 (tag : Fin 10000) (htag : tag.val = 3592) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3592 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03593 (tag : Fin 10000) (htag : tag.val = 3593) (x : State) (e : Event) (dr : Ring12) : tag.val = 3593 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03594 (tag : Fin 10000) (htag : tag.val = 3594) (x : State) (e : Event) (dr : Ring12) : tag.val = 3594 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03595 (tag : Fin 10000) (htag : tag.val = 3595) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3595 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03596 (tag : Fin 10000) (htag : tag.val = 3596) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3596 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03597 (tag : Fin 10000) (htag : tag.val = 3597) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3597 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03598 (tag : Fin 10000) (htag : tag.val = 3598) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3598 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03599 (tag : Fin 10000) (htag : tag.val = 3599) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3599 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
