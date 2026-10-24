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
theorem generated_06600 (tag : Fin 10000) (htag : tag.val = 6600) (k : Ring12) : tag.val = 6600 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06601 (tag : Fin 10000) (htag : tag.val = 6601) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6601 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06602 (tag : Fin 10000) (htag : tag.val = 6602) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6602 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06603 (tag : Fin 10000) (htag : tag.val = 6603) (x : State) (e : Event) (dr : Ring12) : tag.val = 6603 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06604 (tag : Fin 10000) (htag : tag.val = 6604) (x : State) (e : Event) (dr : Ring12) : tag.val = 6604 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06605 (tag : Fin 10000) (htag : tag.val = 6605) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6605 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06606 (tag : Fin 10000) (htag : tag.val = 6606) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6606 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06607 (tag : Fin 10000) (htag : tag.val = 6607) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6607 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06608 (tag : Fin 10000) (htag : tag.val = 6608) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6608 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06609 (tag : Fin 10000) (htag : tag.val = 6609) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6609 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06610 (tag : Fin 10000) (htag : tag.val = 6610) (k : Ring12) : tag.val = 6610 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06611 (tag : Fin 10000) (htag : tag.val = 6611) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6611 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06612 (tag : Fin 10000) (htag : tag.val = 6612) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6612 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06613 (tag : Fin 10000) (htag : tag.val = 6613) (x : State) (e : Event) (dr : Ring12) : tag.val = 6613 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06614 (tag : Fin 10000) (htag : tag.val = 6614) (x : State) (e : Event) (dr : Ring12) : tag.val = 6614 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06615 (tag : Fin 10000) (htag : tag.val = 6615) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6615 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06616 (tag : Fin 10000) (htag : tag.val = 6616) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6616 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06617 (tag : Fin 10000) (htag : tag.val = 6617) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6617 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06618 (tag : Fin 10000) (htag : tag.val = 6618) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6618 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06619 (tag : Fin 10000) (htag : tag.val = 6619) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6619 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06620 (tag : Fin 10000) (htag : tag.val = 6620) (k : Ring12) : tag.val = 6620 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06621 (tag : Fin 10000) (htag : tag.val = 6621) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6621 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06622 (tag : Fin 10000) (htag : tag.val = 6622) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6622 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06623 (tag : Fin 10000) (htag : tag.val = 6623) (x : State) (e : Event) (dr : Ring12) : tag.val = 6623 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06624 (tag : Fin 10000) (htag : tag.val = 6624) (x : State) (e : Event) (dr : Ring12) : tag.val = 6624 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06625 (tag : Fin 10000) (htag : tag.val = 6625) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6625 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06626 (tag : Fin 10000) (htag : tag.val = 6626) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6626 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06627 (tag : Fin 10000) (htag : tag.val = 6627) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6627 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06628 (tag : Fin 10000) (htag : tag.val = 6628) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6628 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06629 (tag : Fin 10000) (htag : tag.val = 6629) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6629 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06630 (tag : Fin 10000) (htag : tag.val = 6630) (k : Ring12) : tag.val = 6630 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06631 (tag : Fin 10000) (htag : tag.val = 6631) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6631 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06632 (tag : Fin 10000) (htag : tag.val = 6632) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6632 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06633 (tag : Fin 10000) (htag : tag.val = 6633) (x : State) (e : Event) (dr : Ring12) : tag.val = 6633 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06634 (tag : Fin 10000) (htag : tag.val = 6634) (x : State) (e : Event) (dr : Ring12) : tag.val = 6634 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06635 (tag : Fin 10000) (htag : tag.val = 6635) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6635 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06636 (tag : Fin 10000) (htag : tag.val = 6636) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6636 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06637 (tag : Fin 10000) (htag : tag.val = 6637) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6637 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06638 (tag : Fin 10000) (htag : tag.val = 6638) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6638 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06639 (tag : Fin 10000) (htag : tag.val = 6639) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6639 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06640 (tag : Fin 10000) (htag : tag.val = 6640) (k : Ring12) : tag.val = 6640 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06641 (tag : Fin 10000) (htag : tag.val = 6641) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6641 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06642 (tag : Fin 10000) (htag : tag.val = 6642) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6642 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06643 (tag : Fin 10000) (htag : tag.val = 6643) (x : State) (e : Event) (dr : Ring12) : tag.val = 6643 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06644 (tag : Fin 10000) (htag : tag.val = 6644) (x : State) (e : Event) (dr : Ring12) : tag.val = 6644 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06645 (tag : Fin 10000) (htag : tag.val = 6645) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6645 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06646 (tag : Fin 10000) (htag : tag.val = 6646) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6646 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06647 (tag : Fin 10000) (htag : tag.val = 6647) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6647 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06648 (tag : Fin 10000) (htag : tag.val = 6648) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6648 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06649 (tag : Fin 10000) (htag : tag.val = 6649) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6649 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06650 (tag : Fin 10000) (htag : tag.val = 6650) (k : Ring12) : tag.val = 6650 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06651 (tag : Fin 10000) (htag : tag.val = 6651) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6651 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06652 (tag : Fin 10000) (htag : tag.val = 6652) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6652 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06653 (tag : Fin 10000) (htag : tag.val = 6653) (x : State) (e : Event) (dr : Ring12) : tag.val = 6653 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06654 (tag : Fin 10000) (htag : tag.val = 6654) (x : State) (e : Event) (dr : Ring12) : tag.val = 6654 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06655 (tag : Fin 10000) (htag : tag.val = 6655) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6655 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06656 (tag : Fin 10000) (htag : tag.val = 6656) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6656 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06657 (tag : Fin 10000) (htag : tag.val = 6657) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6657 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06658 (tag : Fin 10000) (htag : tag.val = 6658) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6658 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06659 (tag : Fin 10000) (htag : tag.val = 6659) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6659 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06660 (tag : Fin 10000) (htag : tag.val = 6660) (k : Ring12) : tag.val = 6660 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06661 (tag : Fin 10000) (htag : tag.val = 6661) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6661 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06662 (tag : Fin 10000) (htag : tag.val = 6662) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6662 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06663 (tag : Fin 10000) (htag : tag.val = 6663) (x : State) (e : Event) (dr : Ring12) : tag.val = 6663 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06664 (tag : Fin 10000) (htag : tag.val = 6664) (x : State) (e : Event) (dr : Ring12) : tag.val = 6664 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06665 (tag : Fin 10000) (htag : tag.val = 6665) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6665 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06666 (tag : Fin 10000) (htag : tag.val = 6666) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6666 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06667 (tag : Fin 10000) (htag : tag.val = 6667) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6667 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06668 (tag : Fin 10000) (htag : tag.val = 6668) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6668 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06669 (tag : Fin 10000) (htag : tag.val = 6669) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6669 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06670 (tag : Fin 10000) (htag : tag.val = 6670) (k : Ring12) : tag.val = 6670 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06671 (tag : Fin 10000) (htag : tag.val = 6671) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6671 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06672 (tag : Fin 10000) (htag : tag.val = 6672) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6672 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06673 (tag : Fin 10000) (htag : tag.val = 6673) (x : State) (e : Event) (dr : Ring12) : tag.val = 6673 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06674 (tag : Fin 10000) (htag : tag.val = 6674) (x : State) (e : Event) (dr : Ring12) : tag.val = 6674 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06675 (tag : Fin 10000) (htag : tag.val = 6675) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6675 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06676 (tag : Fin 10000) (htag : tag.val = 6676) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6676 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06677 (tag : Fin 10000) (htag : tag.val = 6677) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6677 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06678 (tag : Fin 10000) (htag : tag.val = 6678) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6678 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06679 (tag : Fin 10000) (htag : tag.val = 6679) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6679 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06680 (tag : Fin 10000) (htag : tag.val = 6680) (k : Ring12) : tag.val = 6680 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06681 (tag : Fin 10000) (htag : tag.val = 6681) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6681 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06682 (tag : Fin 10000) (htag : tag.val = 6682) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6682 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06683 (tag : Fin 10000) (htag : tag.val = 6683) (x : State) (e : Event) (dr : Ring12) : tag.val = 6683 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06684 (tag : Fin 10000) (htag : tag.val = 6684) (x : State) (e : Event) (dr : Ring12) : tag.val = 6684 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06685 (tag : Fin 10000) (htag : tag.val = 6685) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6685 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06686 (tag : Fin 10000) (htag : tag.val = 6686) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6686 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06687 (tag : Fin 10000) (htag : tag.val = 6687) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6687 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06688 (tag : Fin 10000) (htag : tag.val = 6688) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6688 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06689 (tag : Fin 10000) (htag : tag.val = 6689) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6689 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06690 (tag : Fin 10000) (htag : tag.val = 6690) (k : Ring12) : tag.val = 6690 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06691 (tag : Fin 10000) (htag : tag.val = 6691) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6691 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06692 (tag : Fin 10000) (htag : tag.val = 6692) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6692 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06693 (tag : Fin 10000) (htag : tag.val = 6693) (x : State) (e : Event) (dr : Ring12) : tag.val = 6693 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06694 (tag : Fin 10000) (htag : tag.val = 6694) (x : State) (e : Event) (dr : Ring12) : tag.val = 6694 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06695 (tag : Fin 10000) (htag : tag.val = 6695) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6695 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06696 (tag : Fin 10000) (htag : tag.val = 6696) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6696 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06697 (tag : Fin 10000) (htag : tag.val = 6697) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6697 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06698 (tag : Fin 10000) (htag : tag.val = 6698) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6698 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06699 (tag : Fin 10000) (htag : tag.val = 6699) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6699 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
