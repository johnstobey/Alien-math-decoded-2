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
theorem generated_06700 (tag : Fin 10000) (htag : tag.val = 6700) (k : Ring12) : tag.val = 6700 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06701 (tag : Fin 10000) (htag : tag.val = 6701) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6701 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06702 (tag : Fin 10000) (htag : tag.val = 6702) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6702 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06703 (tag : Fin 10000) (htag : tag.val = 6703) (x : State) (e : Event) (dr : Ring12) : tag.val = 6703 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06704 (tag : Fin 10000) (htag : tag.val = 6704) (x : State) (e : Event) (dr : Ring12) : tag.val = 6704 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06705 (tag : Fin 10000) (htag : tag.val = 6705) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6705 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06706 (tag : Fin 10000) (htag : tag.val = 6706) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6706 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06707 (tag : Fin 10000) (htag : tag.val = 6707) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6707 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06708 (tag : Fin 10000) (htag : tag.val = 6708) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6708 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06709 (tag : Fin 10000) (htag : tag.val = 6709) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6709 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06710 (tag : Fin 10000) (htag : tag.val = 6710) (k : Ring12) : tag.val = 6710 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06711 (tag : Fin 10000) (htag : tag.val = 6711) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6711 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06712 (tag : Fin 10000) (htag : tag.val = 6712) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6712 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06713 (tag : Fin 10000) (htag : tag.val = 6713) (x : State) (e : Event) (dr : Ring12) : tag.val = 6713 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06714 (tag : Fin 10000) (htag : tag.val = 6714) (x : State) (e : Event) (dr : Ring12) : tag.val = 6714 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06715 (tag : Fin 10000) (htag : tag.val = 6715) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6715 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06716 (tag : Fin 10000) (htag : tag.val = 6716) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6716 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06717 (tag : Fin 10000) (htag : tag.val = 6717) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6717 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06718 (tag : Fin 10000) (htag : tag.val = 6718) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6718 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06719 (tag : Fin 10000) (htag : tag.val = 6719) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6719 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06720 (tag : Fin 10000) (htag : tag.val = 6720) (k : Ring12) : tag.val = 6720 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06721 (tag : Fin 10000) (htag : tag.val = 6721) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6721 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06722 (tag : Fin 10000) (htag : tag.val = 6722) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6722 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06723 (tag : Fin 10000) (htag : tag.val = 6723) (x : State) (e : Event) (dr : Ring12) : tag.val = 6723 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06724 (tag : Fin 10000) (htag : tag.val = 6724) (x : State) (e : Event) (dr : Ring12) : tag.val = 6724 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06725 (tag : Fin 10000) (htag : tag.val = 6725) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6725 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06726 (tag : Fin 10000) (htag : tag.val = 6726) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6726 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06727 (tag : Fin 10000) (htag : tag.val = 6727) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6727 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06728 (tag : Fin 10000) (htag : tag.val = 6728) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6728 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06729 (tag : Fin 10000) (htag : tag.val = 6729) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6729 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06730 (tag : Fin 10000) (htag : tag.val = 6730) (k : Ring12) : tag.val = 6730 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06731 (tag : Fin 10000) (htag : tag.val = 6731) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6731 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06732 (tag : Fin 10000) (htag : tag.val = 6732) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6732 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06733 (tag : Fin 10000) (htag : tag.val = 6733) (x : State) (e : Event) (dr : Ring12) : tag.val = 6733 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06734 (tag : Fin 10000) (htag : tag.val = 6734) (x : State) (e : Event) (dr : Ring12) : tag.val = 6734 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06735 (tag : Fin 10000) (htag : tag.val = 6735) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6735 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06736 (tag : Fin 10000) (htag : tag.val = 6736) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6736 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06737 (tag : Fin 10000) (htag : tag.val = 6737) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6737 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06738 (tag : Fin 10000) (htag : tag.val = 6738) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6738 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06739 (tag : Fin 10000) (htag : tag.val = 6739) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6739 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06740 (tag : Fin 10000) (htag : tag.val = 6740) (k : Ring12) : tag.val = 6740 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06741 (tag : Fin 10000) (htag : tag.val = 6741) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6741 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06742 (tag : Fin 10000) (htag : tag.val = 6742) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6742 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06743 (tag : Fin 10000) (htag : tag.val = 6743) (x : State) (e : Event) (dr : Ring12) : tag.val = 6743 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06744 (tag : Fin 10000) (htag : tag.val = 6744) (x : State) (e : Event) (dr : Ring12) : tag.val = 6744 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06745 (tag : Fin 10000) (htag : tag.val = 6745) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6745 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06746 (tag : Fin 10000) (htag : tag.val = 6746) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6746 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06747 (tag : Fin 10000) (htag : tag.val = 6747) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6747 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06748 (tag : Fin 10000) (htag : tag.val = 6748) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6748 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06749 (tag : Fin 10000) (htag : tag.val = 6749) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6749 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06750 (tag : Fin 10000) (htag : tag.val = 6750) (k : Ring12) : tag.val = 6750 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06751 (tag : Fin 10000) (htag : tag.val = 6751) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6751 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06752 (tag : Fin 10000) (htag : tag.val = 6752) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6752 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06753 (tag : Fin 10000) (htag : tag.val = 6753) (x : State) (e : Event) (dr : Ring12) : tag.val = 6753 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06754 (tag : Fin 10000) (htag : tag.val = 6754) (x : State) (e : Event) (dr : Ring12) : tag.val = 6754 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06755 (tag : Fin 10000) (htag : tag.val = 6755) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6755 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06756 (tag : Fin 10000) (htag : tag.val = 6756) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6756 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06757 (tag : Fin 10000) (htag : tag.val = 6757) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6757 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06758 (tag : Fin 10000) (htag : tag.val = 6758) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6758 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06759 (tag : Fin 10000) (htag : tag.val = 6759) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6759 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06760 (tag : Fin 10000) (htag : tag.val = 6760) (k : Ring12) : tag.val = 6760 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06761 (tag : Fin 10000) (htag : tag.val = 6761) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6761 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06762 (tag : Fin 10000) (htag : tag.val = 6762) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6762 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06763 (tag : Fin 10000) (htag : tag.val = 6763) (x : State) (e : Event) (dr : Ring12) : tag.val = 6763 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06764 (tag : Fin 10000) (htag : tag.val = 6764) (x : State) (e : Event) (dr : Ring12) : tag.val = 6764 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06765 (tag : Fin 10000) (htag : tag.val = 6765) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6765 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06766 (tag : Fin 10000) (htag : tag.val = 6766) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6766 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06767 (tag : Fin 10000) (htag : tag.val = 6767) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6767 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06768 (tag : Fin 10000) (htag : tag.val = 6768) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6768 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06769 (tag : Fin 10000) (htag : tag.val = 6769) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6769 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06770 (tag : Fin 10000) (htag : tag.val = 6770) (k : Ring12) : tag.val = 6770 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06771 (tag : Fin 10000) (htag : tag.val = 6771) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6771 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06772 (tag : Fin 10000) (htag : tag.val = 6772) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6772 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06773 (tag : Fin 10000) (htag : tag.val = 6773) (x : State) (e : Event) (dr : Ring12) : tag.val = 6773 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06774 (tag : Fin 10000) (htag : tag.val = 6774) (x : State) (e : Event) (dr : Ring12) : tag.val = 6774 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06775 (tag : Fin 10000) (htag : tag.val = 6775) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6775 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06776 (tag : Fin 10000) (htag : tag.val = 6776) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6776 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06777 (tag : Fin 10000) (htag : tag.val = 6777) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6777 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06778 (tag : Fin 10000) (htag : tag.val = 6778) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6778 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06779 (tag : Fin 10000) (htag : tag.val = 6779) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6779 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06780 (tag : Fin 10000) (htag : tag.val = 6780) (k : Ring12) : tag.val = 6780 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06781 (tag : Fin 10000) (htag : tag.val = 6781) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6781 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06782 (tag : Fin 10000) (htag : tag.val = 6782) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6782 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06783 (tag : Fin 10000) (htag : tag.val = 6783) (x : State) (e : Event) (dr : Ring12) : tag.val = 6783 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06784 (tag : Fin 10000) (htag : tag.val = 6784) (x : State) (e : Event) (dr : Ring12) : tag.val = 6784 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06785 (tag : Fin 10000) (htag : tag.val = 6785) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6785 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06786 (tag : Fin 10000) (htag : tag.val = 6786) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6786 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06787 (tag : Fin 10000) (htag : tag.val = 6787) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6787 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06788 (tag : Fin 10000) (htag : tag.val = 6788) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6788 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06789 (tag : Fin 10000) (htag : tag.val = 6789) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6789 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06790 (tag : Fin 10000) (htag : tag.val = 6790) (k : Ring12) : tag.val = 6790 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06791 (tag : Fin 10000) (htag : tag.val = 6791) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6791 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06792 (tag : Fin 10000) (htag : tag.val = 6792) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6792 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06793 (tag : Fin 10000) (htag : tag.val = 6793) (x : State) (e : Event) (dr : Ring12) : tag.val = 6793 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06794 (tag : Fin 10000) (htag : tag.val = 6794) (x : State) (e : Event) (dr : Ring12) : tag.val = 6794 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06795 (tag : Fin 10000) (htag : tag.val = 6795) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6795 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06796 (tag : Fin 10000) (htag : tag.val = 6796) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6796 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06797 (tag : Fin 10000) (htag : tag.val = 6797) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6797 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06798 (tag : Fin 10000) (htag : tag.val = 6798) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6798 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06799 (tag : Fin 10000) (htag : tag.val = 6799) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6799 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
