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
theorem generated_03600 (tag : Fin 10000) (htag : tag.val = 3600) (k : Ring12) : tag.val = 3600 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03601 (tag : Fin 10000) (htag : tag.val = 3601) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3601 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03602 (tag : Fin 10000) (htag : tag.val = 3602) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3602 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03603 (tag : Fin 10000) (htag : tag.val = 3603) (x : State) (e : Event) (dr : Ring12) : tag.val = 3603 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03604 (tag : Fin 10000) (htag : tag.val = 3604) (x : State) (e : Event) (dr : Ring12) : tag.val = 3604 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03605 (tag : Fin 10000) (htag : tag.val = 3605) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3605 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03606 (tag : Fin 10000) (htag : tag.val = 3606) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3606 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03607 (tag : Fin 10000) (htag : tag.val = 3607) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3607 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03608 (tag : Fin 10000) (htag : tag.val = 3608) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3608 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03609 (tag : Fin 10000) (htag : tag.val = 3609) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3609 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03610 (tag : Fin 10000) (htag : tag.val = 3610) (k : Ring12) : tag.val = 3610 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03611 (tag : Fin 10000) (htag : tag.val = 3611) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3611 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03612 (tag : Fin 10000) (htag : tag.val = 3612) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3612 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03613 (tag : Fin 10000) (htag : tag.val = 3613) (x : State) (e : Event) (dr : Ring12) : tag.val = 3613 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03614 (tag : Fin 10000) (htag : tag.val = 3614) (x : State) (e : Event) (dr : Ring12) : tag.val = 3614 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03615 (tag : Fin 10000) (htag : tag.val = 3615) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3615 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03616 (tag : Fin 10000) (htag : tag.val = 3616) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3616 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03617 (tag : Fin 10000) (htag : tag.val = 3617) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3617 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03618 (tag : Fin 10000) (htag : tag.val = 3618) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3618 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03619 (tag : Fin 10000) (htag : tag.val = 3619) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3619 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03620 (tag : Fin 10000) (htag : tag.val = 3620) (k : Ring12) : tag.val = 3620 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03621 (tag : Fin 10000) (htag : tag.val = 3621) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3621 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03622 (tag : Fin 10000) (htag : tag.val = 3622) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3622 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03623 (tag : Fin 10000) (htag : tag.val = 3623) (x : State) (e : Event) (dr : Ring12) : tag.val = 3623 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03624 (tag : Fin 10000) (htag : tag.val = 3624) (x : State) (e : Event) (dr : Ring12) : tag.val = 3624 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03625 (tag : Fin 10000) (htag : tag.val = 3625) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3625 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03626 (tag : Fin 10000) (htag : tag.val = 3626) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3626 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03627 (tag : Fin 10000) (htag : tag.val = 3627) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3627 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03628 (tag : Fin 10000) (htag : tag.val = 3628) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3628 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03629 (tag : Fin 10000) (htag : tag.val = 3629) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3629 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03630 (tag : Fin 10000) (htag : tag.val = 3630) (k : Ring12) : tag.val = 3630 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03631 (tag : Fin 10000) (htag : tag.val = 3631) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3631 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03632 (tag : Fin 10000) (htag : tag.val = 3632) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3632 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03633 (tag : Fin 10000) (htag : tag.val = 3633) (x : State) (e : Event) (dr : Ring12) : tag.val = 3633 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03634 (tag : Fin 10000) (htag : tag.val = 3634) (x : State) (e : Event) (dr : Ring12) : tag.val = 3634 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03635 (tag : Fin 10000) (htag : tag.val = 3635) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3635 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03636 (tag : Fin 10000) (htag : tag.val = 3636) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3636 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03637 (tag : Fin 10000) (htag : tag.val = 3637) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3637 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03638 (tag : Fin 10000) (htag : tag.val = 3638) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3638 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03639 (tag : Fin 10000) (htag : tag.val = 3639) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3639 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03640 (tag : Fin 10000) (htag : tag.val = 3640) (k : Ring12) : tag.val = 3640 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03641 (tag : Fin 10000) (htag : tag.val = 3641) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3641 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03642 (tag : Fin 10000) (htag : tag.val = 3642) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3642 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03643 (tag : Fin 10000) (htag : tag.val = 3643) (x : State) (e : Event) (dr : Ring12) : tag.val = 3643 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03644 (tag : Fin 10000) (htag : tag.val = 3644) (x : State) (e : Event) (dr : Ring12) : tag.val = 3644 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03645 (tag : Fin 10000) (htag : tag.val = 3645) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3645 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03646 (tag : Fin 10000) (htag : tag.val = 3646) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3646 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03647 (tag : Fin 10000) (htag : tag.val = 3647) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3647 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03648 (tag : Fin 10000) (htag : tag.val = 3648) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3648 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03649 (tag : Fin 10000) (htag : tag.val = 3649) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3649 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03650 (tag : Fin 10000) (htag : tag.val = 3650) (k : Ring12) : tag.val = 3650 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03651 (tag : Fin 10000) (htag : tag.val = 3651) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3651 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03652 (tag : Fin 10000) (htag : tag.val = 3652) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3652 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03653 (tag : Fin 10000) (htag : tag.val = 3653) (x : State) (e : Event) (dr : Ring12) : tag.val = 3653 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03654 (tag : Fin 10000) (htag : tag.val = 3654) (x : State) (e : Event) (dr : Ring12) : tag.val = 3654 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03655 (tag : Fin 10000) (htag : tag.val = 3655) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3655 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03656 (tag : Fin 10000) (htag : tag.val = 3656) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3656 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03657 (tag : Fin 10000) (htag : tag.val = 3657) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3657 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03658 (tag : Fin 10000) (htag : tag.val = 3658) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3658 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03659 (tag : Fin 10000) (htag : tag.val = 3659) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3659 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03660 (tag : Fin 10000) (htag : tag.val = 3660) (k : Ring12) : tag.val = 3660 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03661 (tag : Fin 10000) (htag : tag.val = 3661) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3661 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03662 (tag : Fin 10000) (htag : tag.val = 3662) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3662 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03663 (tag : Fin 10000) (htag : tag.val = 3663) (x : State) (e : Event) (dr : Ring12) : tag.val = 3663 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03664 (tag : Fin 10000) (htag : tag.val = 3664) (x : State) (e : Event) (dr : Ring12) : tag.val = 3664 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03665 (tag : Fin 10000) (htag : tag.val = 3665) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3665 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03666 (tag : Fin 10000) (htag : tag.val = 3666) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3666 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03667 (tag : Fin 10000) (htag : tag.val = 3667) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3667 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03668 (tag : Fin 10000) (htag : tag.val = 3668) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3668 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03669 (tag : Fin 10000) (htag : tag.val = 3669) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3669 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03670 (tag : Fin 10000) (htag : tag.val = 3670) (k : Ring12) : tag.val = 3670 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03671 (tag : Fin 10000) (htag : tag.val = 3671) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3671 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03672 (tag : Fin 10000) (htag : tag.val = 3672) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3672 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03673 (tag : Fin 10000) (htag : tag.val = 3673) (x : State) (e : Event) (dr : Ring12) : tag.val = 3673 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03674 (tag : Fin 10000) (htag : tag.val = 3674) (x : State) (e : Event) (dr : Ring12) : tag.val = 3674 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03675 (tag : Fin 10000) (htag : tag.val = 3675) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3675 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03676 (tag : Fin 10000) (htag : tag.val = 3676) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3676 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03677 (tag : Fin 10000) (htag : tag.val = 3677) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3677 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03678 (tag : Fin 10000) (htag : tag.val = 3678) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3678 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03679 (tag : Fin 10000) (htag : tag.val = 3679) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3679 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03680 (tag : Fin 10000) (htag : tag.val = 3680) (k : Ring12) : tag.val = 3680 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03681 (tag : Fin 10000) (htag : tag.val = 3681) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3681 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03682 (tag : Fin 10000) (htag : tag.val = 3682) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3682 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03683 (tag : Fin 10000) (htag : tag.val = 3683) (x : State) (e : Event) (dr : Ring12) : tag.val = 3683 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03684 (tag : Fin 10000) (htag : tag.val = 3684) (x : State) (e : Event) (dr : Ring12) : tag.val = 3684 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03685 (tag : Fin 10000) (htag : tag.val = 3685) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3685 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03686 (tag : Fin 10000) (htag : tag.val = 3686) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3686 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03687 (tag : Fin 10000) (htag : tag.val = 3687) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3687 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03688 (tag : Fin 10000) (htag : tag.val = 3688) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3688 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03689 (tag : Fin 10000) (htag : tag.val = 3689) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3689 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03690 (tag : Fin 10000) (htag : tag.val = 3690) (k : Ring12) : tag.val = 3690 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03691 (tag : Fin 10000) (htag : tag.val = 3691) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3691 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03692 (tag : Fin 10000) (htag : tag.val = 3692) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3692 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03693 (tag : Fin 10000) (htag : tag.val = 3693) (x : State) (e : Event) (dr : Ring12) : tag.val = 3693 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03694 (tag : Fin 10000) (htag : tag.val = 3694) (x : State) (e : Event) (dr : Ring12) : tag.val = 3694 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03695 (tag : Fin 10000) (htag : tag.val = 3695) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3695 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03696 (tag : Fin 10000) (htag : tag.val = 3696) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3696 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03697 (tag : Fin 10000) (htag : tag.val = 3697) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3697 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03698 (tag : Fin 10000) (htag : tag.val = 3698) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3698 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03699 (tag : Fin 10000) (htag : tag.val = 3699) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3699 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
