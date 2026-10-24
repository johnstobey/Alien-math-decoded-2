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
theorem generated_08700 (tag : Fin 10000) (htag : tag.val = 8700) (k : Ring12) : tag.val = 8700 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08701 (tag : Fin 10000) (htag : tag.val = 8701) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8701 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08702 (tag : Fin 10000) (htag : tag.val = 8702) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8702 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08703 (tag : Fin 10000) (htag : tag.val = 8703) (x : State) (e : Event) (dr : Ring12) : tag.val = 8703 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08704 (tag : Fin 10000) (htag : tag.val = 8704) (x : State) (e : Event) (dr : Ring12) : tag.val = 8704 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08705 (tag : Fin 10000) (htag : tag.val = 8705) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8705 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08706 (tag : Fin 10000) (htag : tag.val = 8706) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8706 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08707 (tag : Fin 10000) (htag : tag.val = 8707) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8707 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08708 (tag : Fin 10000) (htag : tag.val = 8708) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8708 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08709 (tag : Fin 10000) (htag : tag.val = 8709) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8709 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08710 (tag : Fin 10000) (htag : tag.val = 8710) (k : Ring12) : tag.val = 8710 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08711 (tag : Fin 10000) (htag : tag.val = 8711) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8711 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08712 (tag : Fin 10000) (htag : tag.val = 8712) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8712 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08713 (tag : Fin 10000) (htag : tag.val = 8713) (x : State) (e : Event) (dr : Ring12) : tag.val = 8713 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08714 (tag : Fin 10000) (htag : tag.val = 8714) (x : State) (e : Event) (dr : Ring12) : tag.val = 8714 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08715 (tag : Fin 10000) (htag : tag.val = 8715) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8715 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08716 (tag : Fin 10000) (htag : tag.val = 8716) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8716 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08717 (tag : Fin 10000) (htag : tag.val = 8717) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8717 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08718 (tag : Fin 10000) (htag : tag.val = 8718) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8718 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08719 (tag : Fin 10000) (htag : tag.val = 8719) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8719 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08720 (tag : Fin 10000) (htag : tag.val = 8720) (k : Ring12) : tag.val = 8720 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08721 (tag : Fin 10000) (htag : tag.val = 8721) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8721 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08722 (tag : Fin 10000) (htag : tag.val = 8722) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8722 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08723 (tag : Fin 10000) (htag : tag.val = 8723) (x : State) (e : Event) (dr : Ring12) : tag.val = 8723 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08724 (tag : Fin 10000) (htag : tag.val = 8724) (x : State) (e : Event) (dr : Ring12) : tag.val = 8724 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08725 (tag : Fin 10000) (htag : tag.val = 8725) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8725 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08726 (tag : Fin 10000) (htag : tag.val = 8726) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8726 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08727 (tag : Fin 10000) (htag : tag.val = 8727) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8727 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08728 (tag : Fin 10000) (htag : tag.val = 8728) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8728 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08729 (tag : Fin 10000) (htag : tag.val = 8729) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8729 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08730 (tag : Fin 10000) (htag : tag.val = 8730) (k : Ring12) : tag.val = 8730 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08731 (tag : Fin 10000) (htag : tag.val = 8731) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8731 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08732 (tag : Fin 10000) (htag : tag.val = 8732) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8732 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08733 (tag : Fin 10000) (htag : tag.val = 8733) (x : State) (e : Event) (dr : Ring12) : tag.val = 8733 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08734 (tag : Fin 10000) (htag : tag.val = 8734) (x : State) (e : Event) (dr : Ring12) : tag.val = 8734 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08735 (tag : Fin 10000) (htag : tag.val = 8735) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8735 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08736 (tag : Fin 10000) (htag : tag.val = 8736) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8736 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08737 (tag : Fin 10000) (htag : tag.val = 8737) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8737 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08738 (tag : Fin 10000) (htag : tag.val = 8738) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8738 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08739 (tag : Fin 10000) (htag : tag.val = 8739) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8739 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08740 (tag : Fin 10000) (htag : tag.val = 8740) (k : Ring12) : tag.val = 8740 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08741 (tag : Fin 10000) (htag : tag.val = 8741) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8741 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08742 (tag : Fin 10000) (htag : tag.val = 8742) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8742 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08743 (tag : Fin 10000) (htag : tag.val = 8743) (x : State) (e : Event) (dr : Ring12) : tag.val = 8743 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08744 (tag : Fin 10000) (htag : tag.val = 8744) (x : State) (e : Event) (dr : Ring12) : tag.val = 8744 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08745 (tag : Fin 10000) (htag : tag.val = 8745) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8745 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08746 (tag : Fin 10000) (htag : tag.val = 8746) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8746 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08747 (tag : Fin 10000) (htag : tag.val = 8747) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8747 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08748 (tag : Fin 10000) (htag : tag.val = 8748) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8748 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08749 (tag : Fin 10000) (htag : tag.val = 8749) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8749 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08750 (tag : Fin 10000) (htag : tag.val = 8750) (k : Ring12) : tag.val = 8750 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08751 (tag : Fin 10000) (htag : tag.val = 8751) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8751 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08752 (tag : Fin 10000) (htag : tag.val = 8752) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8752 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08753 (tag : Fin 10000) (htag : tag.val = 8753) (x : State) (e : Event) (dr : Ring12) : tag.val = 8753 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08754 (tag : Fin 10000) (htag : tag.val = 8754) (x : State) (e : Event) (dr : Ring12) : tag.val = 8754 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08755 (tag : Fin 10000) (htag : tag.val = 8755) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8755 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08756 (tag : Fin 10000) (htag : tag.val = 8756) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8756 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08757 (tag : Fin 10000) (htag : tag.val = 8757) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8757 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08758 (tag : Fin 10000) (htag : tag.val = 8758) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8758 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08759 (tag : Fin 10000) (htag : tag.val = 8759) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8759 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08760 (tag : Fin 10000) (htag : tag.val = 8760) (k : Ring12) : tag.val = 8760 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08761 (tag : Fin 10000) (htag : tag.val = 8761) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8761 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08762 (tag : Fin 10000) (htag : tag.val = 8762) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8762 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08763 (tag : Fin 10000) (htag : tag.val = 8763) (x : State) (e : Event) (dr : Ring12) : tag.val = 8763 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08764 (tag : Fin 10000) (htag : tag.val = 8764) (x : State) (e : Event) (dr : Ring12) : tag.val = 8764 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08765 (tag : Fin 10000) (htag : tag.val = 8765) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8765 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08766 (tag : Fin 10000) (htag : tag.val = 8766) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8766 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08767 (tag : Fin 10000) (htag : tag.val = 8767) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8767 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08768 (tag : Fin 10000) (htag : tag.val = 8768) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8768 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08769 (tag : Fin 10000) (htag : tag.val = 8769) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8769 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08770 (tag : Fin 10000) (htag : tag.val = 8770) (k : Ring12) : tag.val = 8770 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08771 (tag : Fin 10000) (htag : tag.val = 8771) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8771 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08772 (tag : Fin 10000) (htag : tag.val = 8772) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8772 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08773 (tag : Fin 10000) (htag : tag.val = 8773) (x : State) (e : Event) (dr : Ring12) : tag.val = 8773 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08774 (tag : Fin 10000) (htag : tag.val = 8774) (x : State) (e : Event) (dr : Ring12) : tag.val = 8774 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08775 (tag : Fin 10000) (htag : tag.val = 8775) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8775 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08776 (tag : Fin 10000) (htag : tag.val = 8776) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8776 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08777 (tag : Fin 10000) (htag : tag.val = 8777) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8777 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08778 (tag : Fin 10000) (htag : tag.val = 8778) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8778 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08779 (tag : Fin 10000) (htag : tag.val = 8779) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8779 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08780 (tag : Fin 10000) (htag : tag.val = 8780) (k : Ring12) : tag.val = 8780 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08781 (tag : Fin 10000) (htag : tag.val = 8781) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8781 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08782 (tag : Fin 10000) (htag : tag.val = 8782) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8782 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08783 (tag : Fin 10000) (htag : tag.val = 8783) (x : State) (e : Event) (dr : Ring12) : tag.val = 8783 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08784 (tag : Fin 10000) (htag : tag.val = 8784) (x : State) (e : Event) (dr : Ring12) : tag.val = 8784 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08785 (tag : Fin 10000) (htag : tag.val = 8785) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8785 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08786 (tag : Fin 10000) (htag : tag.val = 8786) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8786 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08787 (tag : Fin 10000) (htag : tag.val = 8787) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8787 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08788 (tag : Fin 10000) (htag : tag.val = 8788) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8788 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08789 (tag : Fin 10000) (htag : tag.val = 8789) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8789 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08790 (tag : Fin 10000) (htag : tag.val = 8790) (k : Ring12) : tag.val = 8790 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08791 (tag : Fin 10000) (htag : tag.val = 8791) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8791 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08792 (tag : Fin 10000) (htag : tag.val = 8792) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8792 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08793 (tag : Fin 10000) (htag : tag.val = 8793) (x : State) (e : Event) (dr : Ring12) : tag.val = 8793 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08794 (tag : Fin 10000) (htag : tag.val = 8794) (x : State) (e : Event) (dr : Ring12) : tag.val = 8794 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08795 (tag : Fin 10000) (htag : tag.val = 8795) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8795 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08796 (tag : Fin 10000) (htag : tag.val = 8796) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8796 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08797 (tag : Fin 10000) (htag : tag.val = 8797) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8797 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08798 (tag : Fin 10000) (htag : tag.val = 8798) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8798 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08799 (tag : Fin 10000) (htag : tag.val = 8799) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8799 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
