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
theorem generated_05600 (tag : Fin 10000) (htag : tag.val = 5600) (k : Ring12) : tag.val = 5600 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05601 (tag : Fin 10000) (htag : tag.val = 5601) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5601 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05602 (tag : Fin 10000) (htag : tag.val = 5602) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5602 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05603 (tag : Fin 10000) (htag : tag.val = 5603) (x : State) (e : Event) (dr : Ring12) : tag.val = 5603 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05604 (tag : Fin 10000) (htag : tag.val = 5604) (x : State) (e : Event) (dr : Ring12) : tag.val = 5604 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05605 (tag : Fin 10000) (htag : tag.val = 5605) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5605 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05606 (tag : Fin 10000) (htag : tag.val = 5606) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5606 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05607 (tag : Fin 10000) (htag : tag.val = 5607) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5607 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05608 (tag : Fin 10000) (htag : tag.val = 5608) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5608 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05609 (tag : Fin 10000) (htag : tag.val = 5609) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5609 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05610 (tag : Fin 10000) (htag : tag.val = 5610) (k : Ring12) : tag.val = 5610 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05611 (tag : Fin 10000) (htag : tag.val = 5611) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5611 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05612 (tag : Fin 10000) (htag : tag.val = 5612) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5612 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05613 (tag : Fin 10000) (htag : tag.val = 5613) (x : State) (e : Event) (dr : Ring12) : tag.val = 5613 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05614 (tag : Fin 10000) (htag : tag.val = 5614) (x : State) (e : Event) (dr : Ring12) : tag.val = 5614 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05615 (tag : Fin 10000) (htag : tag.val = 5615) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5615 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05616 (tag : Fin 10000) (htag : tag.val = 5616) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5616 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05617 (tag : Fin 10000) (htag : tag.val = 5617) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5617 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05618 (tag : Fin 10000) (htag : tag.val = 5618) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5618 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05619 (tag : Fin 10000) (htag : tag.val = 5619) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5619 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05620 (tag : Fin 10000) (htag : tag.val = 5620) (k : Ring12) : tag.val = 5620 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05621 (tag : Fin 10000) (htag : tag.val = 5621) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5621 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05622 (tag : Fin 10000) (htag : tag.val = 5622) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5622 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05623 (tag : Fin 10000) (htag : tag.val = 5623) (x : State) (e : Event) (dr : Ring12) : tag.val = 5623 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05624 (tag : Fin 10000) (htag : tag.val = 5624) (x : State) (e : Event) (dr : Ring12) : tag.val = 5624 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05625 (tag : Fin 10000) (htag : tag.val = 5625) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5625 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05626 (tag : Fin 10000) (htag : tag.val = 5626) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5626 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05627 (tag : Fin 10000) (htag : tag.val = 5627) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5627 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05628 (tag : Fin 10000) (htag : tag.val = 5628) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5628 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05629 (tag : Fin 10000) (htag : tag.val = 5629) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5629 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05630 (tag : Fin 10000) (htag : tag.val = 5630) (k : Ring12) : tag.val = 5630 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05631 (tag : Fin 10000) (htag : tag.val = 5631) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5631 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05632 (tag : Fin 10000) (htag : tag.val = 5632) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5632 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05633 (tag : Fin 10000) (htag : tag.val = 5633) (x : State) (e : Event) (dr : Ring12) : tag.val = 5633 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05634 (tag : Fin 10000) (htag : tag.val = 5634) (x : State) (e : Event) (dr : Ring12) : tag.val = 5634 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05635 (tag : Fin 10000) (htag : tag.val = 5635) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5635 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05636 (tag : Fin 10000) (htag : tag.val = 5636) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5636 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05637 (tag : Fin 10000) (htag : tag.val = 5637) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5637 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05638 (tag : Fin 10000) (htag : tag.val = 5638) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5638 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05639 (tag : Fin 10000) (htag : tag.val = 5639) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5639 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05640 (tag : Fin 10000) (htag : tag.val = 5640) (k : Ring12) : tag.val = 5640 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05641 (tag : Fin 10000) (htag : tag.val = 5641) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5641 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05642 (tag : Fin 10000) (htag : tag.val = 5642) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5642 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05643 (tag : Fin 10000) (htag : tag.val = 5643) (x : State) (e : Event) (dr : Ring12) : tag.val = 5643 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05644 (tag : Fin 10000) (htag : tag.val = 5644) (x : State) (e : Event) (dr : Ring12) : tag.val = 5644 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05645 (tag : Fin 10000) (htag : tag.val = 5645) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5645 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05646 (tag : Fin 10000) (htag : tag.val = 5646) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5646 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05647 (tag : Fin 10000) (htag : tag.val = 5647) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5647 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05648 (tag : Fin 10000) (htag : tag.val = 5648) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5648 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05649 (tag : Fin 10000) (htag : tag.val = 5649) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5649 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05650 (tag : Fin 10000) (htag : tag.val = 5650) (k : Ring12) : tag.val = 5650 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05651 (tag : Fin 10000) (htag : tag.val = 5651) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5651 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05652 (tag : Fin 10000) (htag : tag.val = 5652) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5652 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05653 (tag : Fin 10000) (htag : tag.val = 5653) (x : State) (e : Event) (dr : Ring12) : tag.val = 5653 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05654 (tag : Fin 10000) (htag : tag.val = 5654) (x : State) (e : Event) (dr : Ring12) : tag.val = 5654 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05655 (tag : Fin 10000) (htag : tag.val = 5655) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5655 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05656 (tag : Fin 10000) (htag : tag.val = 5656) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5656 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05657 (tag : Fin 10000) (htag : tag.val = 5657) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5657 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05658 (tag : Fin 10000) (htag : tag.val = 5658) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5658 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05659 (tag : Fin 10000) (htag : tag.val = 5659) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5659 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05660 (tag : Fin 10000) (htag : tag.val = 5660) (k : Ring12) : tag.val = 5660 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05661 (tag : Fin 10000) (htag : tag.val = 5661) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5661 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05662 (tag : Fin 10000) (htag : tag.val = 5662) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5662 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05663 (tag : Fin 10000) (htag : tag.val = 5663) (x : State) (e : Event) (dr : Ring12) : tag.val = 5663 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05664 (tag : Fin 10000) (htag : tag.val = 5664) (x : State) (e : Event) (dr : Ring12) : tag.val = 5664 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05665 (tag : Fin 10000) (htag : tag.val = 5665) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5665 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05666 (tag : Fin 10000) (htag : tag.val = 5666) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5666 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05667 (tag : Fin 10000) (htag : tag.val = 5667) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5667 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05668 (tag : Fin 10000) (htag : tag.val = 5668) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5668 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05669 (tag : Fin 10000) (htag : tag.val = 5669) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5669 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05670 (tag : Fin 10000) (htag : tag.val = 5670) (k : Ring12) : tag.val = 5670 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05671 (tag : Fin 10000) (htag : tag.val = 5671) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5671 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05672 (tag : Fin 10000) (htag : tag.val = 5672) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5672 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05673 (tag : Fin 10000) (htag : tag.val = 5673) (x : State) (e : Event) (dr : Ring12) : tag.val = 5673 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05674 (tag : Fin 10000) (htag : tag.val = 5674) (x : State) (e : Event) (dr : Ring12) : tag.val = 5674 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05675 (tag : Fin 10000) (htag : tag.val = 5675) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5675 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05676 (tag : Fin 10000) (htag : tag.val = 5676) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5676 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05677 (tag : Fin 10000) (htag : tag.val = 5677) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5677 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05678 (tag : Fin 10000) (htag : tag.val = 5678) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5678 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05679 (tag : Fin 10000) (htag : tag.val = 5679) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5679 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05680 (tag : Fin 10000) (htag : tag.val = 5680) (k : Ring12) : tag.val = 5680 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05681 (tag : Fin 10000) (htag : tag.val = 5681) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5681 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05682 (tag : Fin 10000) (htag : tag.val = 5682) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5682 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05683 (tag : Fin 10000) (htag : tag.val = 5683) (x : State) (e : Event) (dr : Ring12) : tag.val = 5683 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05684 (tag : Fin 10000) (htag : tag.val = 5684) (x : State) (e : Event) (dr : Ring12) : tag.val = 5684 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05685 (tag : Fin 10000) (htag : tag.val = 5685) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5685 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05686 (tag : Fin 10000) (htag : tag.val = 5686) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5686 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05687 (tag : Fin 10000) (htag : tag.val = 5687) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5687 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05688 (tag : Fin 10000) (htag : tag.val = 5688) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5688 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05689 (tag : Fin 10000) (htag : tag.val = 5689) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5689 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05690 (tag : Fin 10000) (htag : tag.val = 5690) (k : Ring12) : tag.val = 5690 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05691 (tag : Fin 10000) (htag : tag.val = 5691) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5691 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05692 (tag : Fin 10000) (htag : tag.val = 5692) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5692 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05693 (tag : Fin 10000) (htag : tag.val = 5693) (x : State) (e : Event) (dr : Ring12) : tag.val = 5693 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05694 (tag : Fin 10000) (htag : tag.val = 5694) (x : State) (e : Event) (dr : Ring12) : tag.val = 5694 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05695 (tag : Fin 10000) (htag : tag.val = 5695) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5695 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05696 (tag : Fin 10000) (htag : tag.val = 5696) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5696 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05697 (tag : Fin 10000) (htag : tag.val = 5697) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5697 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05698 (tag : Fin 10000) (htag : tag.val = 5698) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5698 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05699 (tag : Fin 10000) (htag : tag.val = 5699) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5699 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
