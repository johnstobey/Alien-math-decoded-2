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
theorem generated_01700 (tag : Fin 10000) (htag : tag.val = 1700) (k : Ring12) : tag.val = 1700 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01701 (tag : Fin 10000) (htag : tag.val = 1701) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1701 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01702 (tag : Fin 10000) (htag : tag.val = 1702) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1702 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01703 (tag : Fin 10000) (htag : tag.val = 1703) (x : State) (e : Event) (dr : Ring12) : tag.val = 1703 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01704 (tag : Fin 10000) (htag : tag.val = 1704) (x : State) (e : Event) (dr : Ring12) : tag.val = 1704 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01705 (tag : Fin 10000) (htag : tag.val = 1705) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1705 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01706 (tag : Fin 10000) (htag : tag.val = 1706) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1706 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01707 (tag : Fin 10000) (htag : tag.val = 1707) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1707 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01708 (tag : Fin 10000) (htag : tag.val = 1708) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1708 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01709 (tag : Fin 10000) (htag : tag.val = 1709) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1709 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01710 (tag : Fin 10000) (htag : tag.val = 1710) (k : Ring12) : tag.val = 1710 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01711 (tag : Fin 10000) (htag : tag.val = 1711) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1711 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01712 (tag : Fin 10000) (htag : tag.val = 1712) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1712 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01713 (tag : Fin 10000) (htag : tag.val = 1713) (x : State) (e : Event) (dr : Ring12) : tag.val = 1713 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01714 (tag : Fin 10000) (htag : tag.val = 1714) (x : State) (e : Event) (dr : Ring12) : tag.val = 1714 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01715 (tag : Fin 10000) (htag : tag.val = 1715) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1715 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01716 (tag : Fin 10000) (htag : tag.val = 1716) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1716 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01717 (tag : Fin 10000) (htag : tag.val = 1717) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1717 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01718 (tag : Fin 10000) (htag : tag.val = 1718) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1718 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01719 (tag : Fin 10000) (htag : tag.val = 1719) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1719 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01720 (tag : Fin 10000) (htag : tag.val = 1720) (k : Ring12) : tag.val = 1720 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01721 (tag : Fin 10000) (htag : tag.val = 1721) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1721 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01722 (tag : Fin 10000) (htag : tag.val = 1722) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1722 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01723 (tag : Fin 10000) (htag : tag.val = 1723) (x : State) (e : Event) (dr : Ring12) : tag.val = 1723 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01724 (tag : Fin 10000) (htag : tag.val = 1724) (x : State) (e : Event) (dr : Ring12) : tag.val = 1724 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01725 (tag : Fin 10000) (htag : tag.val = 1725) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1725 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01726 (tag : Fin 10000) (htag : tag.val = 1726) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1726 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01727 (tag : Fin 10000) (htag : tag.val = 1727) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1727 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01728 (tag : Fin 10000) (htag : tag.val = 1728) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1728 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01729 (tag : Fin 10000) (htag : tag.val = 1729) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1729 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01730 (tag : Fin 10000) (htag : tag.val = 1730) (k : Ring12) : tag.val = 1730 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01731 (tag : Fin 10000) (htag : tag.val = 1731) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1731 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01732 (tag : Fin 10000) (htag : tag.val = 1732) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1732 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01733 (tag : Fin 10000) (htag : tag.val = 1733) (x : State) (e : Event) (dr : Ring12) : tag.val = 1733 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01734 (tag : Fin 10000) (htag : tag.val = 1734) (x : State) (e : Event) (dr : Ring12) : tag.val = 1734 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01735 (tag : Fin 10000) (htag : tag.val = 1735) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1735 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01736 (tag : Fin 10000) (htag : tag.val = 1736) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1736 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01737 (tag : Fin 10000) (htag : tag.val = 1737) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1737 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01738 (tag : Fin 10000) (htag : tag.val = 1738) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1738 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01739 (tag : Fin 10000) (htag : tag.val = 1739) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1739 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01740 (tag : Fin 10000) (htag : tag.val = 1740) (k : Ring12) : tag.val = 1740 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01741 (tag : Fin 10000) (htag : tag.val = 1741) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1741 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01742 (tag : Fin 10000) (htag : tag.val = 1742) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1742 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01743 (tag : Fin 10000) (htag : tag.val = 1743) (x : State) (e : Event) (dr : Ring12) : tag.val = 1743 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01744 (tag : Fin 10000) (htag : tag.val = 1744) (x : State) (e : Event) (dr : Ring12) : tag.val = 1744 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01745 (tag : Fin 10000) (htag : tag.val = 1745) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1745 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01746 (tag : Fin 10000) (htag : tag.val = 1746) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1746 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01747 (tag : Fin 10000) (htag : tag.val = 1747) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1747 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01748 (tag : Fin 10000) (htag : tag.val = 1748) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1748 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01749 (tag : Fin 10000) (htag : tag.val = 1749) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1749 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01750 (tag : Fin 10000) (htag : tag.val = 1750) (k : Ring12) : tag.val = 1750 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01751 (tag : Fin 10000) (htag : tag.val = 1751) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1751 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01752 (tag : Fin 10000) (htag : tag.val = 1752) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1752 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01753 (tag : Fin 10000) (htag : tag.val = 1753) (x : State) (e : Event) (dr : Ring12) : tag.val = 1753 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01754 (tag : Fin 10000) (htag : tag.val = 1754) (x : State) (e : Event) (dr : Ring12) : tag.val = 1754 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01755 (tag : Fin 10000) (htag : tag.val = 1755) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1755 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01756 (tag : Fin 10000) (htag : tag.val = 1756) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1756 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01757 (tag : Fin 10000) (htag : tag.val = 1757) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1757 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01758 (tag : Fin 10000) (htag : tag.val = 1758) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1758 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01759 (tag : Fin 10000) (htag : tag.val = 1759) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1759 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01760 (tag : Fin 10000) (htag : tag.val = 1760) (k : Ring12) : tag.val = 1760 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01761 (tag : Fin 10000) (htag : tag.val = 1761) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1761 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01762 (tag : Fin 10000) (htag : tag.val = 1762) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1762 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01763 (tag : Fin 10000) (htag : tag.val = 1763) (x : State) (e : Event) (dr : Ring12) : tag.val = 1763 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01764 (tag : Fin 10000) (htag : tag.val = 1764) (x : State) (e : Event) (dr : Ring12) : tag.val = 1764 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01765 (tag : Fin 10000) (htag : tag.val = 1765) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1765 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01766 (tag : Fin 10000) (htag : tag.val = 1766) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1766 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01767 (tag : Fin 10000) (htag : tag.val = 1767) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1767 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01768 (tag : Fin 10000) (htag : tag.val = 1768) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1768 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01769 (tag : Fin 10000) (htag : tag.val = 1769) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1769 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01770 (tag : Fin 10000) (htag : tag.val = 1770) (k : Ring12) : tag.val = 1770 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01771 (tag : Fin 10000) (htag : tag.val = 1771) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1771 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01772 (tag : Fin 10000) (htag : tag.val = 1772) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1772 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01773 (tag : Fin 10000) (htag : tag.val = 1773) (x : State) (e : Event) (dr : Ring12) : tag.val = 1773 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01774 (tag : Fin 10000) (htag : tag.val = 1774) (x : State) (e : Event) (dr : Ring12) : tag.val = 1774 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01775 (tag : Fin 10000) (htag : tag.val = 1775) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1775 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01776 (tag : Fin 10000) (htag : tag.val = 1776) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1776 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01777 (tag : Fin 10000) (htag : tag.val = 1777) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1777 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01778 (tag : Fin 10000) (htag : tag.val = 1778) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1778 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01779 (tag : Fin 10000) (htag : tag.val = 1779) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1779 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01780 (tag : Fin 10000) (htag : tag.val = 1780) (k : Ring12) : tag.val = 1780 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01781 (tag : Fin 10000) (htag : tag.val = 1781) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1781 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01782 (tag : Fin 10000) (htag : tag.val = 1782) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1782 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01783 (tag : Fin 10000) (htag : tag.val = 1783) (x : State) (e : Event) (dr : Ring12) : tag.val = 1783 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01784 (tag : Fin 10000) (htag : tag.val = 1784) (x : State) (e : Event) (dr : Ring12) : tag.val = 1784 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01785 (tag : Fin 10000) (htag : tag.val = 1785) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1785 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01786 (tag : Fin 10000) (htag : tag.val = 1786) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1786 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01787 (tag : Fin 10000) (htag : tag.val = 1787) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1787 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01788 (tag : Fin 10000) (htag : tag.val = 1788) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1788 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01789 (tag : Fin 10000) (htag : tag.val = 1789) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1789 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01790 (tag : Fin 10000) (htag : tag.val = 1790) (k : Ring12) : tag.val = 1790 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01791 (tag : Fin 10000) (htag : tag.val = 1791) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1791 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01792 (tag : Fin 10000) (htag : tag.val = 1792) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1792 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01793 (tag : Fin 10000) (htag : tag.val = 1793) (x : State) (e : Event) (dr : Ring12) : tag.val = 1793 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01794 (tag : Fin 10000) (htag : tag.val = 1794) (x : State) (e : Event) (dr : Ring12) : tag.val = 1794 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01795 (tag : Fin 10000) (htag : tag.val = 1795) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1795 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01796 (tag : Fin 10000) (htag : tag.val = 1796) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1796 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01797 (tag : Fin 10000) (htag : tag.val = 1797) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1797 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01798 (tag : Fin 10000) (htag : tag.val = 1798) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1798 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01799 (tag : Fin 10000) (htag : tag.val = 1799) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1799 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
