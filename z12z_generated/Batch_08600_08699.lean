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
theorem generated_08600 (tag : Fin 10000) (htag : tag.val = 8600) (k : Ring12) : tag.val = 8600 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08601 (tag : Fin 10000) (htag : tag.val = 8601) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8601 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08602 (tag : Fin 10000) (htag : tag.val = 8602) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8602 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08603 (tag : Fin 10000) (htag : tag.val = 8603) (x : State) (e : Event) (dr : Ring12) : tag.val = 8603 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08604 (tag : Fin 10000) (htag : tag.val = 8604) (x : State) (e : Event) (dr : Ring12) : tag.val = 8604 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08605 (tag : Fin 10000) (htag : tag.val = 8605) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8605 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08606 (tag : Fin 10000) (htag : tag.val = 8606) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8606 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08607 (tag : Fin 10000) (htag : tag.val = 8607) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8607 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08608 (tag : Fin 10000) (htag : tag.val = 8608) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8608 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08609 (tag : Fin 10000) (htag : tag.val = 8609) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8609 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08610 (tag : Fin 10000) (htag : tag.val = 8610) (k : Ring12) : tag.val = 8610 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08611 (tag : Fin 10000) (htag : tag.val = 8611) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8611 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08612 (tag : Fin 10000) (htag : tag.val = 8612) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8612 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08613 (tag : Fin 10000) (htag : tag.val = 8613) (x : State) (e : Event) (dr : Ring12) : tag.val = 8613 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08614 (tag : Fin 10000) (htag : tag.val = 8614) (x : State) (e : Event) (dr : Ring12) : tag.val = 8614 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08615 (tag : Fin 10000) (htag : tag.val = 8615) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8615 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08616 (tag : Fin 10000) (htag : tag.val = 8616) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8616 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08617 (tag : Fin 10000) (htag : tag.val = 8617) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8617 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08618 (tag : Fin 10000) (htag : tag.val = 8618) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8618 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08619 (tag : Fin 10000) (htag : tag.val = 8619) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8619 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08620 (tag : Fin 10000) (htag : tag.val = 8620) (k : Ring12) : tag.val = 8620 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08621 (tag : Fin 10000) (htag : tag.val = 8621) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8621 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08622 (tag : Fin 10000) (htag : tag.val = 8622) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8622 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08623 (tag : Fin 10000) (htag : tag.val = 8623) (x : State) (e : Event) (dr : Ring12) : tag.val = 8623 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08624 (tag : Fin 10000) (htag : tag.val = 8624) (x : State) (e : Event) (dr : Ring12) : tag.val = 8624 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08625 (tag : Fin 10000) (htag : tag.val = 8625) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8625 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08626 (tag : Fin 10000) (htag : tag.val = 8626) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8626 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08627 (tag : Fin 10000) (htag : tag.val = 8627) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8627 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08628 (tag : Fin 10000) (htag : tag.val = 8628) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8628 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08629 (tag : Fin 10000) (htag : tag.val = 8629) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8629 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08630 (tag : Fin 10000) (htag : tag.val = 8630) (k : Ring12) : tag.val = 8630 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08631 (tag : Fin 10000) (htag : tag.val = 8631) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8631 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08632 (tag : Fin 10000) (htag : tag.val = 8632) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8632 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08633 (tag : Fin 10000) (htag : tag.val = 8633) (x : State) (e : Event) (dr : Ring12) : tag.val = 8633 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08634 (tag : Fin 10000) (htag : tag.val = 8634) (x : State) (e : Event) (dr : Ring12) : tag.val = 8634 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08635 (tag : Fin 10000) (htag : tag.val = 8635) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8635 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08636 (tag : Fin 10000) (htag : tag.val = 8636) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8636 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08637 (tag : Fin 10000) (htag : tag.val = 8637) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8637 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08638 (tag : Fin 10000) (htag : tag.val = 8638) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8638 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08639 (tag : Fin 10000) (htag : tag.val = 8639) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8639 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08640 (tag : Fin 10000) (htag : tag.val = 8640) (k : Ring12) : tag.val = 8640 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08641 (tag : Fin 10000) (htag : tag.val = 8641) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8641 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08642 (tag : Fin 10000) (htag : tag.val = 8642) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8642 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08643 (tag : Fin 10000) (htag : tag.val = 8643) (x : State) (e : Event) (dr : Ring12) : tag.val = 8643 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08644 (tag : Fin 10000) (htag : tag.val = 8644) (x : State) (e : Event) (dr : Ring12) : tag.val = 8644 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08645 (tag : Fin 10000) (htag : tag.val = 8645) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8645 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08646 (tag : Fin 10000) (htag : tag.val = 8646) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8646 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08647 (tag : Fin 10000) (htag : tag.val = 8647) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8647 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08648 (tag : Fin 10000) (htag : tag.val = 8648) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8648 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08649 (tag : Fin 10000) (htag : tag.val = 8649) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8649 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08650 (tag : Fin 10000) (htag : tag.val = 8650) (k : Ring12) : tag.val = 8650 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08651 (tag : Fin 10000) (htag : tag.val = 8651) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8651 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08652 (tag : Fin 10000) (htag : tag.val = 8652) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8652 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08653 (tag : Fin 10000) (htag : tag.val = 8653) (x : State) (e : Event) (dr : Ring12) : tag.val = 8653 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08654 (tag : Fin 10000) (htag : tag.val = 8654) (x : State) (e : Event) (dr : Ring12) : tag.val = 8654 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08655 (tag : Fin 10000) (htag : tag.val = 8655) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8655 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08656 (tag : Fin 10000) (htag : tag.val = 8656) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8656 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08657 (tag : Fin 10000) (htag : tag.val = 8657) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8657 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08658 (tag : Fin 10000) (htag : tag.val = 8658) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8658 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08659 (tag : Fin 10000) (htag : tag.val = 8659) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8659 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08660 (tag : Fin 10000) (htag : tag.val = 8660) (k : Ring12) : tag.val = 8660 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08661 (tag : Fin 10000) (htag : tag.val = 8661) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8661 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08662 (tag : Fin 10000) (htag : tag.val = 8662) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8662 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08663 (tag : Fin 10000) (htag : tag.val = 8663) (x : State) (e : Event) (dr : Ring12) : tag.val = 8663 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08664 (tag : Fin 10000) (htag : tag.val = 8664) (x : State) (e : Event) (dr : Ring12) : tag.val = 8664 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08665 (tag : Fin 10000) (htag : tag.val = 8665) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8665 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08666 (tag : Fin 10000) (htag : tag.val = 8666) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8666 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08667 (tag : Fin 10000) (htag : tag.val = 8667) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8667 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08668 (tag : Fin 10000) (htag : tag.val = 8668) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8668 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08669 (tag : Fin 10000) (htag : tag.val = 8669) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8669 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08670 (tag : Fin 10000) (htag : tag.val = 8670) (k : Ring12) : tag.val = 8670 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08671 (tag : Fin 10000) (htag : tag.val = 8671) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8671 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08672 (tag : Fin 10000) (htag : tag.val = 8672) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8672 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08673 (tag : Fin 10000) (htag : tag.val = 8673) (x : State) (e : Event) (dr : Ring12) : tag.val = 8673 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08674 (tag : Fin 10000) (htag : tag.val = 8674) (x : State) (e : Event) (dr : Ring12) : tag.val = 8674 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08675 (tag : Fin 10000) (htag : tag.val = 8675) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8675 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08676 (tag : Fin 10000) (htag : tag.val = 8676) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8676 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08677 (tag : Fin 10000) (htag : tag.val = 8677) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8677 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08678 (tag : Fin 10000) (htag : tag.val = 8678) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8678 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08679 (tag : Fin 10000) (htag : tag.val = 8679) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8679 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08680 (tag : Fin 10000) (htag : tag.val = 8680) (k : Ring12) : tag.val = 8680 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08681 (tag : Fin 10000) (htag : tag.val = 8681) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8681 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08682 (tag : Fin 10000) (htag : tag.val = 8682) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8682 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08683 (tag : Fin 10000) (htag : tag.val = 8683) (x : State) (e : Event) (dr : Ring12) : tag.val = 8683 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08684 (tag : Fin 10000) (htag : tag.val = 8684) (x : State) (e : Event) (dr : Ring12) : tag.val = 8684 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08685 (tag : Fin 10000) (htag : tag.val = 8685) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8685 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08686 (tag : Fin 10000) (htag : tag.val = 8686) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8686 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08687 (tag : Fin 10000) (htag : tag.val = 8687) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8687 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08688 (tag : Fin 10000) (htag : tag.val = 8688) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8688 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08689 (tag : Fin 10000) (htag : tag.val = 8689) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8689 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08690 (tag : Fin 10000) (htag : tag.val = 8690) (k : Ring12) : tag.val = 8690 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08691 (tag : Fin 10000) (htag : tag.val = 8691) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8691 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08692 (tag : Fin 10000) (htag : tag.val = 8692) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8692 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08693 (tag : Fin 10000) (htag : tag.val = 8693) (x : State) (e : Event) (dr : Ring12) : tag.val = 8693 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08694 (tag : Fin 10000) (htag : tag.val = 8694) (x : State) (e : Event) (dr : Ring12) : tag.val = 8694 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08695 (tag : Fin 10000) (htag : tag.val = 8695) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8695 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08696 (tag : Fin 10000) (htag : tag.val = 8696) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8696 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08697 (tag : Fin 10000) (htag : tag.val = 8697) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8697 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08698 (tag : Fin 10000) (htag : tag.val = 8698) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8698 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08699 (tag : Fin 10000) (htag : tag.val = 8699) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8699 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
