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
theorem generated_00700 (tag : Fin 10000) (htag : tag.val = 700) (k : Ring12) : tag.val = 700 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00701 (tag : Fin 10000) (htag : tag.val = 701) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 701 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00702 (tag : Fin 10000) (htag : tag.val = 702) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 702 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00703 (tag : Fin 10000) (htag : tag.val = 703) (x : State) (e : Event) (dr : Ring12) : tag.val = 703 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00704 (tag : Fin 10000) (htag : tag.val = 704) (x : State) (e : Event) (dr : Ring12) : tag.val = 704 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00705 (tag : Fin 10000) (htag : tag.val = 705) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 705 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00706 (tag : Fin 10000) (htag : tag.val = 706) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 706 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00707 (tag : Fin 10000) (htag : tag.val = 707) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 707 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00708 (tag : Fin 10000) (htag : tag.val = 708) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 708 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00709 (tag : Fin 10000) (htag : tag.val = 709) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 709 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00710 (tag : Fin 10000) (htag : tag.val = 710) (k : Ring12) : tag.val = 710 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00711 (tag : Fin 10000) (htag : tag.val = 711) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 711 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00712 (tag : Fin 10000) (htag : tag.val = 712) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 712 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00713 (tag : Fin 10000) (htag : tag.val = 713) (x : State) (e : Event) (dr : Ring12) : tag.val = 713 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00714 (tag : Fin 10000) (htag : tag.val = 714) (x : State) (e : Event) (dr : Ring12) : tag.val = 714 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00715 (tag : Fin 10000) (htag : tag.val = 715) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 715 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00716 (tag : Fin 10000) (htag : tag.val = 716) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 716 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00717 (tag : Fin 10000) (htag : tag.val = 717) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 717 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00718 (tag : Fin 10000) (htag : tag.val = 718) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 718 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00719 (tag : Fin 10000) (htag : tag.val = 719) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 719 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00720 (tag : Fin 10000) (htag : tag.val = 720) (k : Ring12) : tag.val = 720 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00721 (tag : Fin 10000) (htag : tag.val = 721) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 721 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00722 (tag : Fin 10000) (htag : tag.val = 722) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 722 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00723 (tag : Fin 10000) (htag : tag.val = 723) (x : State) (e : Event) (dr : Ring12) : tag.val = 723 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00724 (tag : Fin 10000) (htag : tag.val = 724) (x : State) (e : Event) (dr : Ring12) : tag.val = 724 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00725 (tag : Fin 10000) (htag : tag.val = 725) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 725 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00726 (tag : Fin 10000) (htag : tag.val = 726) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 726 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00727 (tag : Fin 10000) (htag : tag.val = 727) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 727 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00728 (tag : Fin 10000) (htag : tag.val = 728) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 728 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00729 (tag : Fin 10000) (htag : tag.val = 729) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 729 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00730 (tag : Fin 10000) (htag : tag.val = 730) (k : Ring12) : tag.val = 730 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00731 (tag : Fin 10000) (htag : tag.val = 731) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 731 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00732 (tag : Fin 10000) (htag : tag.val = 732) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 732 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00733 (tag : Fin 10000) (htag : tag.val = 733) (x : State) (e : Event) (dr : Ring12) : tag.val = 733 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00734 (tag : Fin 10000) (htag : tag.val = 734) (x : State) (e : Event) (dr : Ring12) : tag.val = 734 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00735 (tag : Fin 10000) (htag : tag.val = 735) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 735 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00736 (tag : Fin 10000) (htag : tag.val = 736) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 736 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00737 (tag : Fin 10000) (htag : tag.val = 737) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 737 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00738 (tag : Fin 10000) (htag : tag.val = 738) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 738 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00739 (tag : Fin 10000) (htag : tag.val = 739) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 739 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00740 (tag : Fin 10000) (htag : tag.val = 740) (k : Ring12) : tag.val = 740 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00741 (tag : Fin 10000) (htag : tag.val = 741) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 741 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00742 (tag : Fin 10000) (htag : tag.val = 742) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 742 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00743 (tag : Fin 10000) (htag : tag.val = 743) (x : State) (e : Event) (dr : Ring12) : tag.val = 743 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00744 (tag : Fin 10000) (htag : tag.val = 744) (x : State) (e : Event) (dr : Ring12) : tag.val = 744 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00745 (tag : Fin 10000) (htag : tag.val = 745) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 745 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00746 (tag : Fin 10000) (htag : tag.val = 746) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 746 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00747 (tag : Fin 10000) (htag : tag.val = 747) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 747 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00748 (tag : Fin 10000) (htag : tag.val = 748) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 748 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00749 (tag : Fin 10000) (htag : tag.val = 749) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 749 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00750 (tag : Fin 10000) (htag : tag.val = 750) (k : Ring12) : tag.val = 750 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00751 (tag : Fin 10000) (htag : tag.val = 751) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 751 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00752 (tag : Fin 10000) (htag : tag.val = 752) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 752 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00753 (tag : Fin 10000) (htag : tag.val = 753) (x : State) (e : Event) (dr : Ring12) : tag.val = 753 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00754 (tag : Fin 10000) (htag : tag.val = 754) (x : State) (e : Event) (dr : Ring12) : tag.val = 754 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00755 (tag : Fin 10000) (htag : tag.val = 755) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 755 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00756 (tag : Fin 10000) (htag : tag.val = 756) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 756 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00757 (tag : Fin 10000) (htag : tag.val = 757) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 757 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00758 (tag : Fin 10000) (htag : tag.val = 758) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 758 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00759 (tag : Fin 10000) (htag : tag.val = 759) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 759 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00760 (tag : Fin 10000) (htag : tag.val = 760) (k : Ring12) : tag.val = 760 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00761 (tag : Fin 10000) (htag : tag.val = 761) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 761 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00762 (tag : Fin 10000) (htag : tag.val = 762) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 762 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00763 (tag : Fin 10000) (htag : tag.val = 763) (x : State) (e : Event) (dr : Ring12) : tag.val = 763 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00764 (tag : Fin 10000) (htag : tag.val = 764) (x : State) (e : Event) (dr : Ring12) : tag.val = 764 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00765 (tag : Fin 10000) (htag : tag.val = 765) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 765 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00766 (tag : Fin 10000) (htag : tag.val = 766) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 766 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00767 (tag : Fin 10000) (htag : tag.val = 767) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 767 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00768 (tag : Fin 10000) (htag : tag.val = 768) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 768 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00769 (tag : Fin 10000) (htag : tag.val = 769) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 769 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00770 (tag : Fin 10000) (htag : tag.val = 770) (k : Ring12) : tag.val = 770 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00771 (tag : Fin 10000) (htag : tag.val = 771) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 771 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00772 (tag : Fin 10000) (htag : tag.val = 772) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 772 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00773 (tag : Fin 10000) (htag : tag.val = 773) (x : State) (e : Event) (dr : Ring12) : tag.val = 773 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00774 (tag : Fin 10000) (htag : tag.val = 774) (x : State) (e : Event) (dr : Ring12) : tag.val = 774 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00775 (tag : Fin 10000) (htag : tag.val = 775) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 775 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00776 (tag : Fin 10000) (htag : tag.val = 776) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 776 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00777 (tag : Fin 10000) (htag : tag.val = 777) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 777 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00778 (tag : Fin 10000) (htag : tag.val = 778) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 778 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00779 (tag : Fin 10000) (htag : tag.val = 779) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 779 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00780 (tag : Fin 10000) (htag : tag.val = 780) (k : Ring12) : tag.val = 780 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00781 (tag : Fin 10000) (htag : tag.val = 781) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 781 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00782 (tag : Fin 10000) (htag : tag.val = 782) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 782 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00783 (tag : Fin 10000) (htag : tag.val = 783) (x : State) (e : Event) (dr : Ring12) : tag.val = 783 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00784 (tag : Fin 10000) (htag : tag.val = 784) (x : State) (e : Event) (dr : Ring12) : tag.val = 784 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00785 (tag : Fin 10000) (htag : tag.val = 785) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 785 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00786 (tag : Fin 10000) (htag : tag.val = 786) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 786 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00787 (tag : Fin 10000) (htag : tag.val = 787) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 787 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00788 (tag : Fin 10000) (htag : tag.val = 788) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 788 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00789 (tag : Fin 10000) (htag : tag.val = 789) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 789 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00790 (tag : Fin 10000) (htag : tag.val = 790) (k : Ring12) : tag.val = 790 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00791 (tag : Fin 10000) (htag : tag.val = 791) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 791 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00792 (tag : Fin 10000) (htag : tag.val = 792) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 792 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00793 (tag : Fin 10000) (htag : tag.val = 793) (x : State) (e : Event) (dr : Ring12) : tag.val = 793 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00794 (tag : Fin 10000) (htag : tag.val = 794) (x : State) (e : Event) (dr : Ring12) : tag.val = 794 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00795 (tag : Fin 10000) (htag : tag.val = 795) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 795 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00796 (tag : Fin 10000) (htag : tag.val = 796) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 796 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00797 (tag : Fin 10000) (htag : tag.val = 797) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 797 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00798 (tag : Fin 10000) (htag : tag.val = 798) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 798 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00799 (tag : Fin 10000) (htag : tag.val = 799) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 799 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
