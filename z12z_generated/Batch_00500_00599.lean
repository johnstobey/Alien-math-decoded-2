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
theorem generated_00500 (tag : Fin 10000) (htag : tag.val = 500) (k : Ring12) : tag.val = 500 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00501 (tag : Fin 10000) (htag : tag.val = 501) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 501 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00502 (tag : Fin 10000) (htag : tag.val = 502) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 502 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00503 (tag : Fin 10000) (htag : tag.val = 503) (x : State) (e : Event) (dr : Ring12) : tag.val = 503 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00504 (tag : Fin 10000) (htag : tag.val = 504) (x : State) (e : Event) (dr : Ring12) : tag.val = 504 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00505 (tag : Fin 10000) (htag : tag.val = 505) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 505 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00506 (tag : Fin 10000) (htag : tag.val = 506) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 506 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00507 (tag : Fin 10000) (htag : tag.val = 507) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 507 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00508 (tag : Fin 10000) (htag : tag.val = 508) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 508 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00509 (tag : Fin 10000) (htag : tag.val = 509) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 509 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00510 (tag : Fin 10000) (htag : tag.val = 510) (k : Ring12) : tag.val = 510 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00511 (tag : Fin 10000) (htag : tag.val = 511) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 511 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00512 (tag : Fin 10000) (htag : tag.val = 512) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 512 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00513 (tag : Fin 10000) (htag : tag.val = 513) (x : State) (e : Event) (dr : Ring12) : tag.val = 513 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00514 (tag : Fin 10000) (htag : tag.val = 514) (x : State) (e : Event) (dr : Ring12) : tag.val = 514 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00515 (tag : Fin 10000) (htag : tag.val = 515) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 515 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00516 (tag : Fin 10000) (htag : tag.val = 516) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 516 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00517 (tag : Fin 10000) (htag : tag.val = 517) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 517 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00518 (tag : Fin 10000) (htag : tag.val = 518) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 518 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00519 (tag : Fin 10000) (htag : tag.val = 519) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 519 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00520 (tag : Fin 10000) (htag : tag.val = 520) (k : Ring12) : tag.val = 520 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00521 (tag : Fin 10000) (htag : tag.val = 521) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 521 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00522 (tag : Fin 10000) (htag : tag.val = 522) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 522 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00523 (tag : Fin 10000) (htag : tag.val = 523) (x : State) (e : Event) (dr : Ring12) : tag.val = 523 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00524 (tag : Fin 10000) (htag : tag.val = 524) (x : State) (e : Event) (dr : Ring12) : tag.val = 524 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00525 (tag : Fin 10000) (htag : tag.val = 525) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 525 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00526 (tag : Fin 10000) (htag : tag.val = 526) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 526 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00527 (tag : Fin 10000) (htag : tag.val = 527) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 527 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00528 (tag : Fin 10000) (htag : tag.val = 528) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 528 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00529 (tag : Fin 10000) (htag : tag.val = 529) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 529 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00530 (tag : Fin 10000) (htag : tag.val = 530) (k : Ring12) : tag.val = 530 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00531 (tag : Fin 10000) (htag : tag.val = 531) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 531 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00532 (tag : Fin 10000) (htag : tag.val = 532) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 532 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00533 (tag : Fin 10000) (htag : tag.val = 533) (x : State) (e : Event) (dr : Ring12) : tag.val = 533 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00534 (tag : Fin 10000) (htag : tag.val = 534) (x : State) (e : Event) (dr : Ring12) : tag.val = 534 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00535 (tag : Fin 10000) (htag : tag.val = 535) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 535 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00536 (tag : Fin 10000) (htag : tag.val = 536) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 536 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00537 (tag : Fin 10000) (htag : tag.val = 537) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 537 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00538 (tag : Fin 10000) (htag : tag.val = 538) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 538 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00539 (tag : Fin 10000) (htag : tag.val = 539) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 539 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00540 (tag : Fin 10000) (htag : tag.val = 540) (k : Ring12) : tag.val = 540 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00541 (tag : Fin 10000) (htag : tag.val = 541) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 541 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00542 (tag : Fin 10000) (htag : tag.val = 542) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 542 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00543 (tag : Fin 10000) (htag : tag.val = 543) (x : State) (e : Event) (dr : Ring12) : tag.val = 543 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00544 (tag : Fin 10000) (htag : tag.val = 544) (x : State) (e : Event) (dr : Ring12) : tag.val = 544 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00545 (tag : Fin 10000) (htag : tag.val = 545) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 545 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00546 (tag : Fin 10000) (htag : tag.val = 546) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 546 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00547 (tag : Fin 10000) (htag : tag.val = 547) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 547 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00548 (tag : Fin 10000) (htag : tag.val = 548) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 548 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00549 (tag : Fin 10000) (htag : tag.val = 549) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 549 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00550 (tag : Fin 10000) (htag : tag.val = 550) (k : Ring12) : tag.val = 550 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00551 (tag : Fin 10000) (htag : tag.val = 551) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 551 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00552 (tag : Fin 10000) (htag : tag.val = 552) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 552 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00553 (tag : Fin 10000) (htag : tag.val = 553) (x : State) (e : Event) (dr : Ring12) : tag.val = 553 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00554 (tag : Fin 10000) (htag : tag.val = 554) (x : State) (e : Event) (dr : Ring12) : tag.val = 554 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00555 (tag : Fin 10000) (htag : tag.val = 555) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 555 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00556 (tag : Fin 10000) (htag : tag.val = 556) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 556 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00557 (tag : Fin 10000) (htag : tag.val = 557) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 557 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00558 (tag : Fin 10000) (htag : tag.val = 558) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 558 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00559 (tag : Fin 10000) (htag : tag.val = 559) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 559 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00560 (tag : Fin 10000) (htag : tag.val = 560) (k : Ring12) : tag.val = 560 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00561 (tag : Fin 10000) (htag : tag.val = 561) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 561 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00562 (tag : Fin 10000) (htag : tag.val = 562) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 562 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00563 (tag : Fin 10000) (htag : tag.val = 563) (x : State) (e : Event) (dr : Ring12) : tag.val = 563 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00564 (tag : Fin 10000) (htag : tag.val = 564) (x : State) (e : Event) (dr : Ring12) : tag.val = 564 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00565 (tag : Fin 10000) (htag : tag.val = 565) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 565 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00566 (tag : Fin 10000) (htag : tag.val = 566) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 566 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00567 (tag : Fin 10000) (htag : tag.val = 567) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 567 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00568 (tag : Fin 10000) (htag : tag.val = 568) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 568 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00569 (tag : Fin 10000) (htag : tag.val = 569) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 569 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00570 (tag : Fin 10000) (htag : tag.val = 570) (k : Ring12) : tag.val = 570 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00571 (tag : Fin 10000) (htag : tag.val = 571) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 571 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00572 (tag : Fin 10000) (htag : tag.val = 572) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 572 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00573 (tag : Fin 10000) (htag : tag.val = 573) (x : State) (e : Event) (dr : Ring12) : tag.val = 573 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00574 (tag : Fin 10000) (htag : tag.val = 574) (x : State) (e : Event) (dr : Ring12) : tag.val = 574 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00575 (tag : Fin 10000) (htag : tag.val = 575) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 575 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00576 (tag : Fin 10000) (htag : tag.val = 576) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 576 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00577 (tag : Fin 10000) (htag : tag.val = 577) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 577 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00578 (tag : Fin 10000) (htag : tag.val = 578) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 578 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00579 (tag : Fin 10000) (htag : tag.val = 579) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 579 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00580 (tag : Fin 10000) (htag : tag.val = 580) (k : Ring12) : tag.val = 580 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00581 (tag : Fin 10000) (htag : tag.val = 581) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 581 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00582 (tag : Fin 10000) (htag : tag.val = 582) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 582 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00583 (tag : Fin 10000) (htag : tag.val = 583) (x : State) (e : Event) (dr : Ring12) : tag.val = 583 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00584 (tag : Fin 10000) (htag : tag.val = 584) (x : State) (e : Event) (dr : Ring12) : tag.val = 584 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00585 (tag : Fin 10000) (htag : tag.val = 585) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 585 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00586 (tag : Fin 10000) (htag : tag.val = 586) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 586 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00587 (tag : Fin 10000) (htag : tag.val = 587) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 587 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00588 (tag : Fin 10000) (htag : tag.val = 588) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 588 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00589 (tag : Fin 10000) (htag : tag.val = 589) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 589 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00590 (tag : Fin 10000) (htag : tag.val = 590) (k : Ring12) : tag.val = 590 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00591 (tag : Fin 10000) (htag : tag.val = 591) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 591 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00592 (tag : Fin 10000) (htag : tag.val = 592) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 592 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00593 (tag : Fin 10000) (htag : tag.val = 593) (x : State) (e : Event) (dr : Ring12) : tag.val = 593 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00594 (tag : Fin 10000) (htag : tag.val = 594) (x : State) (e : Event) (dr : Ring12) : tag.val = 594 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00595 (tag : Fin 10000) (htag : tag.val = 595) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 595 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00596 (tag : Fin 10000) (htag : tag.val = 596) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 596 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00597 (tag : Fin 10000) (htag : tag.val = 597) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 597 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00598 (tag : Fin 10000) (htag : tag.val = 598) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 598 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00599 (tag : Fin 10000) (htag : tag.val = 599) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 599 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
