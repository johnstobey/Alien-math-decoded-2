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
theorem generated_04600 (tag : Fin 10000) (htag : tag.val = 4600) (k : Ring12) : tag.val = 4600 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04601 (tag : Fin 10000) (htag : tag.val = 4601) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4601 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04602 (tag : Fin 10000) (htag : tag.val = 4602) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4602 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04603 (tag : Fin 10000) (htag : tag.val = 4603) (x : State) (e : Event) (dr : Ring12) : tag.val = 4603 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04604 (tag : Fin 10000) (htag : tag.val = 4604) (x : State) (e : Event) (dr : Ring12) : tag.val = 4604 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04605 (tag : Fin 10000) (htag : tag.val = 4605) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4605 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04606 (tag : Fin 10000) (htag : tag.val = 4606) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4606 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04607 (tag : Fin 10000) (htag : tag.val = 4607) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4607 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04608 (tag : Fin 10000) (htag : tag.val = 4608) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4608 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04609 (tag : Fin 10000) (htag : tag.val = 4609) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4609 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04610 (tag : Fin 10000) (htag : tag.val = 4610) (k : Ring12) : tag.val = 4610 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04611 (tag : Fin 10000) (htag : tag.val = 4611) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4611 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04612 (tag : Fin 10000) (htag : tag.val = 4612) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4612 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04613 (tag : Fin 10000) (htag : tag.val = 4613) (x : State) (e : Event) (dr : Ring12) : tag.val = 4613 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04614 (tag : Fin 10000) (htag : tag.val = 4614) (x : State) (e : Event) (dr : Ring12) : tag.val = 4614 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04615 (tag : Fin 10000) (htag : tag.val = 4615) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4615 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04616 (tag : Fin 10000) (htag : tag.val = 4616) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4616 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04617 (tag : Fin 10000) (htag : tag.val = 4617) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4617 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04618 (tag : Fin 10000) (htag : tag.val = 4618) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4618 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04619 (tag : Fin 10000) (htag : tag.val = 4619) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4619 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04620 (tag : Fin 10000) (htag : tag.val = 4620) (k : Ring12) : tag.val = 4620 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04621 (tag : Fin 10000) (htag : tag.val = 4621) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4621 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04622 (tag : Fin 10000) (htag : tag.val = 4622) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4622 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04623 (tag : Fin 10000) (htag : tag.val = 4623) (x : State) (e : Event) (dr : Ring12) : tag.val = 4623 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04624 (tag : Fin 10000) (htag : tag.val = 4624) (x : State) (e : Event) (dr : Ring12) : tag.val = 4624 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04625 (tag : Fin 10000) (htag : tag.val = 4625) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4625 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04626 (tag : Fin 10000) (htag : tag.val = 4626) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4626 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04627 (tag : Fin 10000) (htag : tag.val = 4627) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4627 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04628 (tag : Fin 10000) (htag : tag.val = 4628) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4628 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04629 (tag : Fin 10000) (htag : tag.val = 4629) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4629 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04630 (tag : Fin 10000) (htag : tag.val = 4630) (k : Ring12) : tag.val = 4630 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04631 (tag : Fin 10000) (htag : tag.val = 4631) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4631 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04632 (tag : Fin 10000) (htag : tag.val = 4632) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4632 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04633 (tag : Fin 10000) (htag : tag.val = 4633) (x : State) (e : Event) (dr : Ring12) : tag.val = 4633 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04634 (tag : Fin 10000) (htag : tag.val = 4634) (x : State) (e : Event) (dr : Ring12) : tag.val = 4634 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04635 (tag : Fin 10000) (htag : tag.val = 4635) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4635 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04636 (tag : Fin 10000) (htag : tag.val = 4636) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4636 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04637 (tag : Fin 10000) (htag : tag.val = 4637) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4637 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04638 (tag : Fin 10000) (htag : tag.val = 4638) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4638 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04639 (tag : Fin 10000) (htag : tag.val = 4639) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4639 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04640 (tag : Fin 10000) (htag : tag.val = 4640) (k : Ring12) : tag.val = 4640 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04641 (tag : Fin 10000) (htag : tag.val = 4641) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4641 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04642 (tag : Fin 10000) (htag : tag.val = 4642) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4642 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04643 (tag : Fin 10000) (htag : tag.val = 4643) (x : State) (e : Event) (dr : Ring12) : tag.val = 4643 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04644 (tag : Fin 10000) (htag : tag.val = 4644) (x : State) (e : Event) (dr : Ring12) : tag.val = 4644 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04645 (tag : Fin 10000) (htag : tag.val = 4645) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4645 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04646 (tag : Fin 10000) (htag : tag.val = 4646) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4646 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04647 (tag : Fin 10000) (htag : tag.val = 4647) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4647 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04648 (tag : Fin 10000) (htag : tag.val = 4648) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4648 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04649 (tag : Fin 10000) (htag : tag.val = 4649) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4649 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04650 (tag : Fin 10000) (htag : tag.val = 4650) (k : Ring12) : tag.val = 4650 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04651 (tag : Fin 10000) (htag : tag.val = 4651) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4651 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04652 (tag : Fin 10000) (htag : tag.val = 4652) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4652 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04653 (tag : Fin 10000) (htag : tag.val = 4653) (x : State) (e : Event) (dr : Ring12) : tag.val = 4653 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04654 (tag : Fin 10000) (htag : tag.val = 4654) (x : State) (e : Event) (dr : Ring12) : tag.val = 4654 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04655 (tag : Fin 10000) (htag : tag.val = 4655) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4655 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04656 (tag : Fin 10000) (htag : tag.val = 4656) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4656 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04657 (tag : Fin 10000) (htag : tag.val = 4657) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4657 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04658 (tag : Fin 10000) (htag : tag.val = 4658) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4658 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04659 (tag : Fin 10000) (htag : tag.val = 4659) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4659 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04660 (tag : Fin 10000) (htag : tag.val = 4660) (k : Ring12) : tag.val = 4660 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04661 (tag : Fin 10000) (htag : tag.val = 4661) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4661 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04662 (tag : Fin 10000) (htag : tag.val = 4662) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4662 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04663 (tag : Fin 10000) (htag : tag.val = 4663) (x : State) (e : Event) (dr : Ring12) : tag.val = 4663 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04664 (tag : Fin 10000) (htag : tag.val = 4664) (x : State) (e : Event) (dr : Ring12) : tag.val = 4664 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04665 (tag : Fin 10000) (htag : tag.val = 4665) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4665 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04666 (tag : Fin 10000) (htag : tag.val = 4666) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4666 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04667 (tag : Fin 10000) (htag : tag.val = 4667) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4667 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04668 (tag : Fin 10000) (htag : tag.val = 4668) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4668 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04669 (tag : Fin 10000) (htag : tag.val = 4669) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4669 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04670 (tag : Fin 10000) (htag : tag.val = 4670) (k : Ring12) : tag.val = 4670 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04671 (tag : Fin 10000) (htag : tag.val = 4671) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4671 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04672 (tag : Fin 10000) (htag : tag.val = 4672) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4672 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04673 (tag : Fin 10000) (htag : tag.val = 4673) (x : State) (e : Event) (dr : Ring12) : tag.val = 4673 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04674 (tag : Fin 10000) (htag : tag.val = 4674) (x : State) (e : Event) (dr : Ring12) : tag.val = 4674 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04675 (tag : Fin 10000) (htag : tag.val = 4675) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4675 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04676 (tag : Fin 10000) (htag : tag.val = 4676) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4676 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04677 (tag : Fin 10000) (htag : tag.val = 4677) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4677 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04678 (tag : Fin 10000) (htag : tag.val = 4678) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4678 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04679 (tag : Fin 10000) (htag : tag.val = 4679) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4679 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04680 (tag : Fin 10000) (htag : tag.val = 4680) (k : Ring12) : tag.val = 4680 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04681 (tag : Fin 10000) (htag : tag.val = 4681) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4681 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04682 (tag : Fin 10000) (htag : tag.val = 4682) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4682 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04683 (tag : Fin 10000) (htag : tag.val = 4683) (x : State) (e : Event) (dr : Ring12) : tag.val = 4683 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04684 (tag : Fin 10000) (htag : tag.val = 4684) (x : State) (e : Event) (dr : Ring12) : tag.val = 4684 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04685 (tag : Fin 10000) (htag : tag.val = 4685) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4685 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04686 (tag : Fin 10000) (htag : tag.val = 4686) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4686 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04687 (tag : Fin 10000) (htag : tag.val = 4687) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4687 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04688 (tag : Fin 10000) (htag : tag.val = 4688) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4688 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04689 (tag : Fin 10000) (htag : tag.val = 4689) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4689 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04690 (tag : Fin 10000) (htag : tag.val = 4690) (k : Ring12) : tag.val = 4690 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04691 (tag : Fin 10000) (htag : tag.val = 4691) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4691 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04692 (tag : Fin 10000) (htag : tag.val = 4692) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4692 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04693 (tag : Fin 10000) (htag : tag.val = 4693) (x : State) (e : Event) (dr : Ring12) : tag.val = 4693 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04694 (tag : Fin 10000) (htag : tag.val = 4694) (x : State) (e : Event) (dr : Ring12) : tag.val = 4694 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04695 (tag : Fin 10000) (htag : tag.val = 4695) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4695 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04696 (tag : Fin 10000) (htag : tag.val = 4696) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4696 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04697 (tag : Fin 10000) (htag : tag.val = 4697) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4697 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04698 (tag : Fin 10000) (htag : tag.val = 4698) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4698 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04699 (tag : Fin 10000) (htag : tag.val = 4699) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4699 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
