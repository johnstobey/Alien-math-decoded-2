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
theorem generated_00600 (tag : Fin 10000) (htag : tag.val = 600) (k : Ring12) : tag.val = 600 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00601 (tag : Fin 10000) (htag : tag.val = 601) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 601 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00602 (tag : Fin 10000) (htag : tag.val = 602) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 602 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00603 (tag : Fin 10000) (htag : tag.val = 603) (x : State) (e : Event) (dr : Ring12) : tag.val = 603 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00604 (tag : Fin 10000) (htag : tag.val = 604) (x : State) (e : Event) (dr : Ring12) : tag.val = 604 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00605 (tag : Fin 10000) (htag : tag.val = 605) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 605 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00606 (tag : Fin 10000) (htag : tag.val = 606) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 606 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00607 (tag : Fin 10000) (htag : tag.val = 607) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 607 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00608 (tag : Fin 10000) (htag : tag.val = 608) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 608 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00609 (tag : Fin 10000) (htag : tag.val = 609) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 609 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00610 (tag : Fin 10000) (htag : tag.val = 610) (k : Ring12) : tag.val = 610 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00611 (tag : Fin 10000) (htag : tag.val = 611) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 611 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00612 (tag : Fin 10000) (htag : tag.val = 612) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 612 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00613 (tag : Fin 10000) (htag : tag.val = 613) (x : State) (e : Event) (dr : Ring12) : tag.val = 613 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00614 (tag : Fin 10000) (htag : tag.val = 614) (x : State) (e : Event) (dr : Ring12) : tag.val = 614 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00615 (tag : Fin 10000) (htag : tag.val = 615) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 615 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00616 (tag : Fin 10000) (htag : tag.val = 616) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 616 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00617 (tag : Fin 10000) (htag : tag.val = 617) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 617 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00618 (tag : Fin 10000) (htag : tag.val = 618) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 618 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00619 (tag : Fin 10000) (htag : tag.val = 619) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 619 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00620 (tag : Fin 10000) (htag : tag.val = 620) (k : Ring12) : tag.val = 620 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00621 (tag : Fin 10000) (htag : tag.val = 621) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 621 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00622 (tag : Fin 10000) (htag : tag.val = 622) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 622 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00623 (tag : Fin 10000) (htag : tag.val = 623) (x : State) (e : Event) (dr : Ring12) : tag.val = 623 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00624 (tag : Fin 10000) (htag : tag.val = 624) (x : State) (e : Event) (dr : Ring12) : tag.val = 624 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00625 (tag : Fin 10000) (htag : tag.val = 625) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 625 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00626 (tag : Fin 10000) (htag : tag.val = 626) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 626 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00627 (tag : Fin 10000) (htag : tag.val = 627) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 627 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00628 (tag : Fin 10000) (htag : tag.val = 628) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 628 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00629 (tag : Fin 10000) (htag : tag.val = 629) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 629 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00630 (tag : Fin 10000) (htag : tag.val = 630) (k : Ring12) : tag.val = 630 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00631 (tag : Fin 10000) (htag : tag.val = 631) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 631 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00632 (tag : Fin 10000) (htag : tag.val = 632) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 632 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00633 (tag : Fin 10000) (htag : tag.val = 633) (x : State) (e : Event) (dr : Ring12) : tag.val = 633 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00634 (tag : Fin 10000) (htag : tag.val = 634) (x : State) (e : Event) (dr : Ring12) : tag.val = 634 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00635 (tag : Fin 10000) (htag : tag.val = 635) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 635 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00636 (tag : Fin 10000) (htag : tag.val = 636) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 636 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00637 (tag : Fin 10000) (htag : tag.val = 637) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 637 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00638 (tag : Fin 10000) (htag : tag.val = 638) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 638 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00639 (tag : Fin 10000) (htag : tag.val = 639) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 639 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00640 (tag : Fin 10000) (htag : tag.val = 640) (k : Ring12) : tag.val = 640 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00641 (tag : Fin 10000) (htag : tag.val = 641) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 641 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00642 (tag : Fin 10000) (htag : tag.val = 642) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 642 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00643 (tag : Fin 10000) (htag : tag.val = 643) (x : State) (e : Event) (dr : Ring12) : tag.val = 643 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00644 (tag : Fin 10000) (htag : tag.val = 644) (x : State) (e : Event) (dr : Ring12) : tag.val = 644 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00645 (tag : Fin 10000) (htag : tag.val = 645) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 645 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00646 (tag : Fin 10000) (htag : tag.val = 646) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 646 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00647 (tag : Fin 10000) (htag : tag.val = 647) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 647 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00648 (tag : Fin 10000) (htag : tag.val = 648) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 648 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00649 (tag : Fin 10000) (htag : tag.val = 649) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 649 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00650 (tag : Fin 10000) (htag : tag.val = 650) (k : Ring12) : tag.val = 650 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00651 (tag : Fin 10000) (htag : tag.val = 651) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 651 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00652 (tag : Fin 10000) (htag : tag.val = 652) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 652 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00653 (tag : Fin 10000) (htag : tag.val = 653) (x : State) (e : Event) (dr : Ring12) : tag.val = 653 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00654 (tag : Fin 10000) (htag : tag.val = 654) (x : State) (e : Event) (dr : Ring12) : tag.val = 654 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00655 (tag : Fin 10000) (htag : tag.val = 655) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 655 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00656 (tag : Fin 10000) (htag : tag.val = 656) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 656 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00657 (tag : Fin 10000) (htag : tag.val = 657) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 657 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00658 (tag : Fin 10000) (htag : tag.val = 658) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 658 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00659 (tag : Fin 10000) (htag : tag.val = 659) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 659 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00660 (tag : Fin 10000) (htag : tag.val = 660) (k : Ring12) : tag.val = 660 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00661 (tag : Fin 10000) (htag : tag.val = 661) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 661 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00662 (tag : Fin 10000) (htag : tag.val = 662) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 662 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00663 (tag : Fin 10000) (htag : tag.val = 663) (x : State) (e : Event) (dr : Ring12) : tag.val = 663 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00664 (tag : Fin 10000) (htag : tag.val = 664) (x : State) (e : Event) (dr : Ring12) : tag.val = 664 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00665 (tag : Fin 10000) (htag : tag.val = 665) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 665 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00666 (tag : Fin 10000) (htag : tag.val = 666) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 666 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00667 (tag : Fin 10000) (htag : tag.val = 667) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 667 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00668 (tag : Fin 10000) (htag : tag.val = 668) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 668 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00669 (tag : Fin 10000) (htag : tag.val = 669) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 669 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00670 (tag : Fin 10000) (htag : tag.val = 670) (k : Ring12) : tag.val = 670 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00671 (tag : Fin 10000) (htag : tag.val = 671) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 671 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00672 (tag : Fin 10000) (htag : tag.val = 672) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 672 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00673 (tag : Fin 10000) (htag : tag.val = 673) (x : State) (e : Event) (dr : Ring12) : tag.val = 673 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00674 (tag : Fin 10000) (htag : tag.val = 674) (x : State) (e : Event) (dr : Ring12) : tag.val = 674 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00675 (tag : Fin 10000) (htag : tag.val = 675) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 675 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00676 (tag : Fin 10000) (htag : tag.val = 676) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 676 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00677 (tag : Fin 10000) (htag : tag.val = 677) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 677 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00678 (tag : Fin 10000) (htag : tag.val = 678) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 678 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00679 (tag : Fin 10000) (htag : tag.val = 679) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 679 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00680 (tag : Fin 10000) (htag : tag.val = 680) (k : Ring12) : tag.val = 680 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00681 (tag : Fin 10000) (htag : tag.val = 681) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 681 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00682 (tag : Fin 10000) (htag : tag.val = 682) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 682 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00683 (tag : Fin 10000) (htag : tag.val = 683) (x : State) (e : Event) (dr : Ring12) : tag.val = 683 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00684 (tag : Fin 10000) (htag : tag.val = 684) (x : State) (e : Event) (dr : Ring12) : tag.val = 684 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00685 (tag : Fin 10000) (htag : tag.val = 685) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 685 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00686 (tag : Fin 10000) (htag : tag.val = 686) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 686 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00687 (tag : Fin 10000) (htag : tag.val = 687) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 687 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00688 (tag : Fin 10000) (htag : tag.val = 688) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 688 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00689 (tag : Fin 10000) (htag : tag.val = 689) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 689 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00690 (tag : Fin 10000) (htag : tag.val = 690) (k : Ring12) : tag.val = 690 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00691 (tag : Fin 10000) (htag : tag.val = 691) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 691 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00692 (tag : Fin 10000) (htag : tag.val = 692) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 692 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00693 (tag : Fin 10000) (htag : tag.val = 693) (x : State) (e : Event) (dr : Ring12) : tag.val = 693 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00694 (tag : Fin 10000) (htag : tag.val = 694) (x : State) (e : Event) (dr : Ring12) : tag.val = 694 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00695 (tag : Fin 10000) (htag : tag.val = 695) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 695 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00696 (tag : Fin 10000) (htag : tag.val = 696) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 696 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00697 (tag : Fin 10000) (htag : tag.val = 697) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 697 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00698 (tag : Fin 10000) (htag : tag.val = 698) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 698 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00699 (tag : Fin 10000) (htag : tag.val = 699) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 699 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
