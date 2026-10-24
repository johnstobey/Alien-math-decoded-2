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
theorem generated_09700 (tag : Fin 10000) (htag : tag.val = 9700) (k : Ring12) : tag.val = 9700 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09701 (tag : Fin 10000) (htag : tag.val = 9701) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9701 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09702 (tag : Fin 10000) (htag : tag.val = 9702) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9702 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09703 (tag : Fin 10000) (htag : tag.val = 9703) (x : State) (e : Event) (dr : Ring12) : tag.val = 9703 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09704 (tag : Fin 10000) (htag : tag.val = 9704) (x : State) (e : Event) (dr : Ring12) : tag.val = 9704 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09705 (tag : Fin 10000) (htag : tag.val = 9705) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9705 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09706 (tag : Fin 10000) (htag : tag.val = 9706) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9706 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09707 (tag : Fin 10000) (htag : tag.val = 9707) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9707 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09708 (tag : Fin 10000) (htag : tag.val = 9708) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9708 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09709 (tag : Fin 10000) (htag : tag.val = 9709) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9709 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09710 (tag : Fin 10000) (htag : tag.val = 9710) (k : Ring12) : tag.val = 9710 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09711 (tag : Fin 10000) (htag : tag.val = 9711) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9711 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09712 (tag : Fin 10000) (htag : tag.val = 9712) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9712 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09713 (tag : Fin 10000) (htag : tag.val = 9713) (x : State) (e : Event) (dr : Ring12) : tag.val = 9713 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09714 (tag : Fin 10000) (htag : tag.val = 9714) (x : State) (e : Event) (dr : Ring12) : tag.val = 9714 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09715 (tag : Fin 10000) (htag : tag.val = 9715) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9715 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09716 (tag : Fin 10000) (htag : tag.val = 9716) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9716 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09717 (tag : Fin 10000) (htag : tag.val = 9717) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9717 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09718 (tag : Fin 10000) (htag : tag.val = 9718) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9718 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09719 (tag : Fin 10000) (htag : tag.val = 9719) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9719 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09720 (tag : Fin 10000) (htag : tag.val = 9720) (k : Ring12) : tag.val = 9720 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09721 (tag : Fin 10000) (htag : tag.val = 9721) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9721 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09722 (tag : Fin 10000) (htag : tag.val = 9722) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9722 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09723 (tag : Fin 10000) (htag : tag.val = 9723) (x : State) (e : Event) (dr : Ring12) : tag.val = 9723 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09724 (tag : Fin 10000) (htag : tag.val = 9724) (x : State) (e : Event) (dr : Ring12) : tag.val = 9724 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09725 (tag : Fin 10000) (htag : tag.val = 9725) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9725 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09726 (tag : Fin 10000) (htag : tag.val = 9726) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9726 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09727 (tag : Fin 10000) (htag : tag.val = 9727) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9727 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09728 (tag : Fin 10000) (htag : tag.val = 9728) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9728 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09729 (tag : Fin 10000) (htag : tag.val = 9729) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9729 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09730 (tag : Fin 10000) (htag : tag.val = 9730) (k : Ring12) : tag.val = 9730 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09731 (tag : Fin 10000) (htag : tag.val = 9731) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9731 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09732 (tag : Fin 10000) (htag : tag.val = 9732) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9732 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09733 (tag : Fin 10000) (htag : tag.val = 9733) (x : State) (e : Event) (dr : Ring12) : tag.val = 9733 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09734 (tag : Fin 10000) (htag : tag.val = 9734) (x : State) (e : Event) (dr : Ring12) : tag.val = 9734 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09735 (tag : Fin 10000) (htag : tag.val = 9735) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9735 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09736 (tag : Fin 10000) (htag : tag.val = 9736) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9736 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09737 (tag : Fin 10000) (htag : tag.val = 9737) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9737 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09738 (tag : Fin 10000) (htag : tag.val = 9738) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9738 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09739 (tag : Fin 10000) (htag : tag.val = 9739) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9739 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09740 (tag : Fin 10000) (htag : tag.val = 9740) (k : Ring12) : tag.val = 9740 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09741 (tag : Fin 10000) (htag : tag.val = 9741) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9741 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09742 (tag : Fin 10000) (htag : tag.val = 9742) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9742 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09743 (tag : Fin 10000) (htag : tag.val = 9743) (x : State) (e : Event) (dr : Ring12) : tag.val = 9743 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09744 (tag : Fin 10000) (htag : tag.val = 9744) (x : State) (e : Event) (dr : Ring12) : tag.val = 9744 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09745 (tag : Fin 10000) (htag : tag.val = 9745) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9745 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09746 (tag : Fin 10000) (htag : tag.val = 9746) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9746 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09747 (tag : Fin 10000) (htag : tag.val = 9747) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9747 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09748 (tag : Fin 10000) (htag : tag.val = 9748) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9748 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09749 (tag : Fin 10000) (htag : tag.val = 9749) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9749 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09750 (tag : Fin 10000) (htag : tag.val = 9750) (k : Ring12) : tag.val = 9750 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09751 (tag : Fin 10000) (htag : tag.val = 9751) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9751 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09752 (tag : Fin 10000) (htag : tag.val = 9752) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9752 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09753 (tag : Fin 10000) (htag : tag.val = 9753) (x : State) (e : Event) (dr : Ring12) : tag.val = 9753 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09754 (tag : Fin 10000) (htag : tag.val = 9754) (x : State) (e : Event) (dr : Ring12) : tag.val = 9754 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09755 (tag : Fin 10000) (htag : tag.val = 9755) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9755 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09756 (tag : Fin 10000) (htag : tag.val = 9756) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9756 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09757 (tag : Fin 10000) (htag : tag.val = 9757) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9757 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09758 (tag : Fin 10000) (htag : tag.val = 9758) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9758 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09759 (tag : Fin 10000) (htag : tag.val = 9759) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9759 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09760 (tag : Fin 10000) (htag : tag.val = 9760) (k : Ring12) : tag.val = 9760 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09761 (tag : Fin 10000) (htag : tag.val = 9761) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9761 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09762 (tag : Fin 10000) (htag : tag.val = 9762) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9762 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09763 (tag : Fin 10000) (htag : tag.val = 9763) (x : State) (e : Event) (dr : Ring12) : tag.val = 9763 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09764 (tag : Fin 10000) (htag : tag.val = 9764) (x : State) (e : Event) (dr : Ring12) : tag.val = 9764 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09765 (tag : Fin 10000) (htag : tag.val = 9765) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9765 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09766 (tag : Fin 10000) (htag : tag.val = 9766) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9766 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09767 (tag : Fin 10000) (htag : tag.val = 9767) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9767 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09768 (tag : Fin 10000) (htag : tag.val = 9768) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9768 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09769 (tag : Fin 10000) (htag : tag.val = 9769) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9769 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09770 (tag : Fin 10000) (htag : tag.val = 9770) (k : Ring12) : tag.val = 9770 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09771 (tag : Fin 10000) (htag : tag.val = 9771) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9771 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09772 (tag : Fin 10000) (htag : tag.val = 9772) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9772 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09773 (tag : Fin 10000) (htag : tag.val = 9773) (x : State) (e : Event) (dr : Ring12) : tag.val = 9773 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09774 (tag : Fin 10000) (htag : tag.val = 9774) (x : State) (e : Event) (dr : Ring12) : tag.val = 9774 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09775 (tag : Fin 10000) (htag : tag.val = 9775) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9775 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09776 (tag : Fin 10000) (htag : tag.val = 9776) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9776 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09777 (tag : Fin 10000) (htag : tag.val = 9777) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9777 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09778 (tag : Fin 10000) (htag : tag.val = 9778) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9778 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09779 (tag : Fin 10000) (htag : tag.val = 9779) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9779 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09780 (tag : Fin 10000) (htag : tag.val = 9780) (k : Ring12) : tag.val = 9780 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09781 (tag : Fin 10000) (htag : tag.val = 9781) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9781 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09782 (tag : Fin 10000) (htag : tag.val = 9782) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9782 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09783 (tag : Fin 10000) (htag : tag.val = 9783) (x : State) (e : Event) (dr : Ring12) : tag.val = 9783 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09784 (tag : Fin 10000) (htag : tag.val = 9784) (x : State) (e : Event) (dr : Ring12) : tag.val = 9784 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09785 (tag : Fin 10000) (htag : tag.val = 9785) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9785 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09786 (tag : Fin 10000) (htag : tag.val = 9786) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9786 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09787 (tag : Fin 10000) (htag : tag.val = 9787) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9787 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09788 (tag : Fin 10000) (htag : tag.val = 9788) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9788 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09789 (tag : Fin 10000) (htag : tag.val = 9789) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9789 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09790 (tag : Fin 10000) (htag : tag.val = 9790) (k : Ring12) : tag.val = 9790 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09791 (tag : Fin 10000) (htag : tag.val = 9791) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9791 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09792 (tag : Fin 10000) (htag : tag.val = 9792) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9792 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09793 (tag : Fin 10000) (htag : tag.val = 9793) (x : State) (e : Event) (dr : Ring12) : tag.val = 9793 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09794 (tag : Fin 10000) (htag : tag.val = 9794) (x : State) (e : Event) (dr : Ring12) : tag.val = 9794 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09795 (tag : Fin 10000) (htag : tag.val = 9795) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9795 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09796 (tag : Fin 10000) (htag : tag.val = 9796) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9796 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09797 (tag : Fin 10000) (htag : tag.val = 9797) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9797 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09798 (tag : Fin 10000) (htag : tag.val = 9798) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9798 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09799 (tag : Fin 10000) (htag : tag.val = 9799) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9799 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
