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
theorem generated_01600 (tag : Fin 10000) (htag : tag.val = 1600) (k : Ring12) : tag.val = 1600 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01601 (tag : Fin 10000) (htag : tag.val = 1601) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1601 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01602 (tag : Fin 10000) (htag : tag.val = 1602) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1602 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01603 (tag : Fin 10000) (htag : tag.val = 1603) (x : State) (e : Event) (dr : Ring12) : tag.val = 1603 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01604 (tag : Fin 10000) (htag : tag.val = 1604) (x : State) (e : Event) (dr : Ring12) : tag.val = 1604 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01605 (tag : Fin 10000) (htag : tag.val = 1605) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1605 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01606 (tag : Fin 10000) (htag : tag.val = 1606) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1606 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01607 (tag : Fin 10000) (htag : tag.val = 1607) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1607 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01608 (tag : Fin 10000) (htag : tag.val = 1608) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1608 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01609 (tag : Fin 10000) (htag : tag.val = 1609) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1609 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01610 (tag : Fin 10000) (htag : tag.val = 1610) (k : Ring12) : tag.val = 1610 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01611 (tag : Fin 10000) (htag : tag.val = 1611) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1611 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01612 (tag : Fin 10000) (htag : tag.val = 1612) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1612 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01613 (tag : Fin 10000) (htag : tag.val = 1613) (x : State) (e : Event) (dr : Ring12) : tag.val = 1613 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01614 (tag : Fin 10000) (htag : tag.val = 1614) (x : State) (e : Event) (dr : Ring12) : tag.val = 1614 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01615 (tag : Fin 10000) (htag : tag.val = 1615) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1615 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01616 (tag : Fin 10000) (htag : tag.val = 1616) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1616 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01617 (tag : Fin 10000) (htag : tag.val = 1617) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1617 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01618 (tag : Fin 10000) (htag : tag.val = 1618) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1618 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01619 (tag : Fin 10000) (htag : tag.val = 1619) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1619 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01620 (tag : Fin 10000) (htag : tag.val = 1620) (k : Ring12) : tag.val = 1620 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01621 (tag : Fin 10000) (htag : tag.val = 1621) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1621 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01622 (tag : Fin 10000) (htag : tag.val = 1622) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1622 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01623 (tag : Fin 10000) (htag : tag.val = 1623) (x : State) (e : Event) (dr : Ring12) : tag.val = 1623 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01624 (tag : Fin 10000) (htag : tag.val = 1624) (x : State) (e : Event) (dr : Ring12) : tag.val = 1624 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01625 (tag : Fin 10000) (htag : tag.val = 1625) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1625 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01626 (tag : Fin 10000) (htag : tag.val = 1626) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1626 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01627 (tag : Fin 10000) (htag : tag.val = 1627) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1627 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01628 (tag : Fin 10000) (htag : tag.val = 1628) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1628 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01629 (tag : Fin 10000) (htag : tag.val = 1629) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1629 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01630 (tag : Fin 10000) (htag : tag.val = 1630) (k : Ring12) : tag.val = 1630 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01631 (tag : Fin 10000) (htag : tag.val = 1631) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1631 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01632 (tag : Fin 10000) (htag : tag.val = 1632) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1632 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01633 (tag : Fin 10000) (htag : tag.val = 1633) (x : State) (e : Event) (dr : Ring12) : tag.val = 1633 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01634 (tag : Fin 10000) (htag : tag.val = 1634) (x : State) (e : Event) (dr : Ring12) : tag.val = 1634 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01635 (tag : Fin 10000) (htag : tag.val = 1635) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1635 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01636 (tag : Fin 10000) (htag : tag.val = 1636) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1636 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01637 (tag : Fin 10000) (htag : tag.val = 1637) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1637 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01638 (tag : Fin 10000) (htag : tag.val = 1638) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1638 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01639 (tag : Fin 10000) (htag : tag.val = 1639) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1639 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01640 (tag : Fin 10000) (htag : tag.val = 1640) (k : Ring12) : tag.val = 1640 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01641 (tag : Fin 10000) (htag : tag.val = 1641) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1641 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01642 (tag : Fin 10000) (htag : tag.val = 1642) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1642 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01643 (tag : Fin 10000) (htag : tag.val = 1643) (x : State) (e : Event) (dr : Ring12) : tag.val = 1643 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01644 (tag : Fin 10000) (htag : tag.val = 1644) (x : State) (e : Event) (dr : Ring12) : tag.val = 1644 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01645 (tag : Fin 10000) (htag : tag.val = 1645) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1645 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01646 (tag : Fin 10000) (htag : tag.val = 1646) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1646 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01647 (tag : Fin 10000) (htag : tag.val = 1647) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1647 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01648 (tag : Fin 10000) (htag : tag.val = 1648) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1648 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01649 (tag : Fin 10000) (htag : tag.val = 1649) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1649 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01650 (tag : Fin 10000) (htag : tag.val = 1650) (k : Ring12) : tag.val = 1650 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01651 (tag : Fin 10000) (htag : tag.val = 1651) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1651 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01652 (tag : Fin 10000) (htag : tag.val = 1652) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1652 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01653 (tag : Fin 10000) (htag : tag.val = 1653) (x : State) (e : Event) (dr : Ring12) : tag.val = 1653 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01654 (tag : Fin 10000) (htag : tag.val = 1654) (x : State) (e : Event) (dr : Ring12) : tag.val = 1654 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01655 (tag : Fin 10000) (htag : tag.val = 1655) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1655 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01656 (tag : Fin 10000) (htag : tag.val = 1656) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1656 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01657 (tag : Fin 10000) (htag : tag.val = 1657) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1657 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01658 (tag : Fin 10000) (htag : tag.val = 1658) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1658 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01659 (tag : Fin 10000) (htag : tag.val = 1659) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1659 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01660 (tag : Fin 10000) (htag : tag.val = 1660) (k : Ring12) : tag.val = 1660 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01661 (tag : Fin 10000) (htag : tag.val = 1661) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1661 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01662 (tag : Fin 10000) (htag : tag.val = 1662) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1662 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01663 (tag : Fin 10000) (htag : tag.val = 1663) (x : State) (e : Event) (dr : Ring12) : tag.val = 1663 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01664 (tag : Fin 10000) (htag : tag.val = 1664) (x : State) (e : Event) (dr : Ring12) : tag.val = 1664 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01665 (tag : Fin 10000) (htag : tag.val = 1665) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1665 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01666 (tag : Fin 10000) (htag : tag.val = 1666) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1666 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01667 (tag : Fin 10000) (htag : tag.val = 1667) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1667 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01668 (tag : Fin 10000) (htag : tag.val = 1668) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1668 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01669 (tag : Fin 10000) (htag : tag.val = 1669) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1669 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01670 (tag : Fin 10000) (htag : tag.val = 1670) (k : Ring12) : tag.val = 1670 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01671 (tag : Fin 10000) (htag : tag.val = 1671) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1671 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01672 (tag : Fin 10000) (htag : tag.val = 1672) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1672 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01673 (tag : Fin 10000) (htag : tag.val = 1673) (x : State) (e : Event) (dr : Ring12) : tag.val = 1673 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01674 (tag : Fin 10000) (htag : tag.val = 1674) (x : State) (e : Event) (dr : Ring12) : tag.val = 1674 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01675 (tag : Fin 10000) (htag : tag.val = 1675) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1675 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01676 (tag : Fin 10000) (htag : tag.val = 1676) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1676 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01677 (tag : Fin 10000) (htag : tag.val = 1677) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1677 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01678 (tag : Fin 10000) (htag : tag.val = 1678) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1678 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01679 (tag : Fin 10000) (htag : tag.val = 1679) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1679 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01680 (tag : Fin 10000) (htag : tag.val = 1680) (k : Ring12) : tag.val = 1680 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01681 (tag : Fin 10000) (htag : tag.val = 1681) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1681 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01682 (tag : Fin 10000) (htag : tag.val = 1682) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1682 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01683 (tag : Fin 10000) (htag : tag.val = 1683) (x : State) (e : Event) (dr : Ring12) : tag.val = 1683 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01684 (tag : Fin 10000) (htag : tag.val = 1684) (x : State) (e : Event) (dr : Ring12) : tag.val = 1684 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01685 (tag : Fin 10000) (htag : tag.val = 1685) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1685 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01686 (tag : Fin 10000) (htag : tag.val = 1686) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1686 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01687 (tag : Fin 10000) (htag : tag.val = 1687) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1687 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01688 (tag : Fin 10000) (htag : tag.val = 1688) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1688 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01689 (tag : Fin 10000) (htag : tag.val = 1689) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1689 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01690 (tag : Fin 10000) (htag : tag.val = 1690) (k : Ring12) : tag.val = 1690 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01691 (tag : Fin 10000) (htag : tag.val = 1691) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1691 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01692 (tag : Fin 10000) (htag : tag.val = 1692) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1692 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01693 (tag : Fin 10000) (htag : tag.val = 1693) (x : State) (e : Event) (dr : Ring12) : tag.val = 1693 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01694 (tag : Fin 10000) (htag : tag.val = 1694) (x : State) (e : Event) (dr : Ring12) : tag.val = 1694 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01695 (tag : Fin 10000) (htag : tag.val = 1695) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1695 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01696 (tag : Fin 10000) (htag : tag.val = 1696) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1696 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01697 (tag : Fin 10000) (htag : tag.val = 1697) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1697 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01698 (tag : Fin 10000) (htag : tag.val = 1698) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1698 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01699 (tag : Fin 10000) (htag : tag.val = 1699) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1699 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
