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
theorem generated_09600 (tag : Fin 10000) (htag : tag.val = 9600) (k : Ring12) : tag.val = 9600 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09601 (tag : Fin 10000) (htag : tag.val = 9601) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9601 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09602 (tag : Fin 10000) (htag : tag.val = 9602) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9602 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09603 (tag : Fin 10000) (htag : tag.val = 9603) (x : State) (e : Event) (dr : Ring12) : tag.val = 9603 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09604 (tag : Fin 10000) (htag : tag.val = 9604) (x : State) (e : Event) (dr : Ring12) : tag.val = 9604 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09605 (tag : Fin 10000) (htag : tag.val = 9605) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9605 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09606 (tag : Fin 10000) (htag : tag.val = 9606) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9606 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09607 (tag : Fin 10000) (htag : tag.val = 9607) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9607 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09608 (tag : Fin 10000) (htag : tag.val = 9608) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9608 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09609 (tag : Fin 10000) (htag : tag.val = 9609) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9609 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09610 (tag : Fin 10000) (htag : tag.val = 9610) (k : Ring12) : tag.val = 9610 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09611 (tag : Fin 10000) (htag : tag.val = 9611) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9611 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09612 (tag : Fin 10000) (htag : tag.val = 9612) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9612 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09613 (tag : Fin 10000) (htag : tag.val = 9613) (x : State) (e : Event) (dr : Ring12) : tag.val = 9613 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09614 (tag : Fin 10000) (htag : tag.val = 9614) (x : State) (e : Event) (dr : Ring12) : tag.val = 9614 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09615 (tag : Fin 10000) (htag : tag.val = 9615) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9615 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09616 (tag : Fin 10000) (htag : tag.val = 9616) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9616 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09617 (tag : Fin 10000) (htag : tag.val = 9617) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9617 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09618 (tag : Fin 10000) (htag : tag.val = 9618) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9618 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09619 (tag : Fin 10000) (htag : tag.val = 9619) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9619 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09620 (tag : Fin 10000) (htag : tag.val = 9620) (k : Ring12) : tag.val = 9620 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09621 (tag : Fin 10000) (htag : tag.val = 9621) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9621 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09622 (tag : Fin 10000) (htag : tag.val = 9622) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9622 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09623 (tag : Fin 10000) (htag : tag.val = 9623) (x : State) (e : Event) (dr : Ring12) : tag.val = 9623 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09624 (tag : Fin 10000) (htag : tag.val = 9624) (x : State) (e : Event) (dr : Ring12) : tag.val = 9624 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09625 (tag : Fin 10000) (htag : tag.val = 9625) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9625 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09626 (tag : Fin 10000) (htag : tag.val = 9626) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9626 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09627 (tag : Fin 10000) (htag : tag.val = 9627) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9627 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09628 (tag : Fin 10000) (htag : tag.val = 9628) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9628 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09629 (tag : Fin 10000) (htag : tag.val = 9629) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9629 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09630 (tag : Fin 10000) (htag : tag.val = 9630) (k : Ring12) : tag.val = 9630 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09631 (tag : Fin 10000) (htag : tag.val = 9631) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9631 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09632 (tag : Fin 10000) (htag : tag.val = 9632) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9632 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09633 (tag : Fin 10000) (htag : tag.val = 9633) (x : State) (e : Event) (dr : Ring12) : tag.val = 9633 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09634 (tag : Fin 10000) (htag : tag.val = 9634) (x : State) (e : Event) (dr : Ring12) : tag.val = 9634 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09635 (tag : Fin 10000) (htag : tag.val = 9635) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9635 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09636 (tag : Fin 10000) (htag : tag.val = 9636) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9636 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09637 (tag : Fin 10000) (htag : tag.val = 9637) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9637 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09638 (tag : Fin 10000) (htag : tag.val = 9638) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9638 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09639 (tag : Fin 10000) (htag : tag.val = 9639) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9639 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09640 (tag : Fin 10000) (htag : tag.val = 9640) (k : Ring12) : tag.val = 9640 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09641 (tag : Fin 10000) (htag : tag.val = 9641) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9641 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09642 (tag : Fin 10000) (htag : tag.val = 9642) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9642 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09643 (tag : Fin 10000) (htag : tag.val = 9643) (x : State) (e : Event) (dr : Ring12) : tag.val = 9643 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09644 (tag : Fin 10000) (htag : tag.val = 9644) (x : State) (e : Event) (dr : Ring12) : tag.val = 9644 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09645 (tag : Fin 10000) (htag : tag.val = 9645) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9645 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09646 (tag : Fin 10000) (htag : tag.val = 9646) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9646 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09647 (tag : Fin 10000) (htag : tag.val = 9647) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9647 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09648 (tag : Fin 10000) (htag : tag.val = 9648) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9648 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09649 (tag : Fin 10000) (htag : tag.val = 9649) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9649 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09650 (tag : Fin 10000) (htag : tag.val = 9650) (k : Ring12) : tag.val = 9650 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09651 (tag : Fin 10000) (htag : tag.val = 9651) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9651 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09652 (tag : Fin 10000) (htag : tag.val = 9652) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9652 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09653 (tag : Fin 10000) (htag : tag.val = 9653) (x : State) (e : Event) (dr : Ring12) : tag.val = 9653 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09654 (tag : Fin 10000) (htag : tag.val = 9654) (x : State) (e : Event) (dr : Ring12) : tag.val = 9654 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09655 (tag : Fin 10000) (htag : tag.val = 9655) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9655 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09656 (tag : Fin 10000) (htag : tag.val = 9656) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9656 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09657 (tag : Fin 10000) (htag : tag.val = 9657) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9657 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09658 (tag : Fin 10000) (htag : tag.val = 9658) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9658 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09659 (tag : Fin 10000) (htag : tag.val = 9659) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9659 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09660 (tag : Fin 10000) (htag : tag.val = 9660) (k : Ring12) : tag.val = 9660 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09661 (tag : Fin 10000) (htag : tag.val = 9661) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9661 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09662 (tag : Fin 10000) (htag : tag.val = 9662) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9662 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09663 (tag : Fin 10000) (htag : tag.val = 9663) (x : State) (e : Event) (dr : Ring12) : tag.val = 9663 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09664 (tag : Fin 10000) (htag : tag.val = 9664) (x : State) (e : Event) (dr : Ring12) : tag.val = 9664 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09665 (tag : Fin 10000) (htag : tag.val = 9665) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9665 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09666 (tag : Fin 10000) (htag : tag.val = 9666) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9666 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09667 (tag : Fin 10000) (htag : tag.val = 9667) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9667 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09668 (tag : Fin 10000) (htag : tag.val = 9668) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9668 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09669 (tag : Fin 10000) (htag : tag.val = 9669) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9669 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09670 (tag : Fin 10000) (htag : tag.val = 9670) (k : Ring12) : tag.val = 9670 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09671 (tag : Fin 10000) (htag : tag.val = 9671) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9671 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09672 (tag : Fin 10000) (htag : tag.val = 9672) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9672 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09673 (tag : Fin 10000) (htag : tag.val = 9673) (x : State) (e : Event) (dr : Ring12) : tag.val = 9673 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09674 (tag : Fin 10000) (htag : tag.val = 9674) (x : State) (e : Event) (dr : Ring12) : tag.val = 9674 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09675 (tag : Fin 10000) (htag : tag.val = 9675) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9675 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09676 (tag : Fin 10000) (htag : tag.val = 9676) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9676 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09677 (tag : Fin 10000) (htag : tag.val = 9677) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9677 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09678 (tag : Fin 10000) (htag : tag.val = 9678) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9678 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09679 (tag : Fin 10000) (htag : tag.val = 9679) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9679 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09680 (tag : Fin 10000) (htag : tag.val = 9680) (k : Ring12) : tag.val = 9680 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09681 (tag : Fin 10000) (htag : tag.val = 9681) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9681 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09682 (tag : Fin 10000) (htag : tag.val = 9682) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9682 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09683 (tag : Fin 10000) (htag : tag.val = 9683) (x : State) (e : Event) (dr : Ring12) : tag.val = 9683 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09684 (tag : Fin 10000) (htag : tag.val = 9684) (x : State) (e : Event) (dr : Ring12) : tag.val = 9684 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09685 (tag : Fin 10000) (htag : tag.val = 9685) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9685 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09686 (tag : Fin 10000) (htag : tag.val = 9686) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9686 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09687 (tag : Fin 10000) (htag : tag.val = 9687) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9687 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09688 (tag : Fin 10000) (htag : tag.val = 9688) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9688 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09689 (tag : Fin 10000) (htag : tag.val = 9689) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9689 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09690 (tag : Fin 10000) (htag : tag.val = 9690) (k : Ring12) : tag.val = 9690 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09691 (tag : Fin 10000) (htag : tag.val = 9691) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9691 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09692 (tag : Fin 10000) (htag : tag.val = 9692) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9692 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09693 (tag : Fin 10000) (htag : tag.val = 9693) (x : State) (e : Event) (dr : Ring12) : tag.val = 9693 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09694 (tag : Fin 10000) (htag : tag.val = 9694) (x : State) (e : Event) (dr : Ring12) : tag.val = 9694 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09695 (tag : Fin 10000) (htag : tag.val = 9695) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9695 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09696 (tag : Fin 10000) (htag : tag.val = 9696) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9696 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09697 (tag : Fin 10000) (htag : tag.val = 9697) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9697 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09698 (tag : Fin 10000) (htag : tag.val = 9698) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9698 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09699 (tag : Fin 10000) (htag : tag.val = 9699) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9699 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
