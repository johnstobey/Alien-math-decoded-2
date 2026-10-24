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
theorem generated_07600 (tag : Fin 10000) (htag : tag.val = 7600) (k : Ring12) : tag.val = 7600 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07601 (tag : Fin 10000) (htag : tag.val = 7601) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7601 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07602 (tag : Fin 10000) (htag : tag.val = 7602) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7602 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07603 (tag : Fin 10000) (htag : tag.val = 7603) (x : State) (e : Event) (dr : Ring12) : tag.val = 7603 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07604 (tag : Fin 10000) (htag : tag.val = 7604) (x : State) (e : Event) (dr : Ring12) : tag.val = 7604 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07605 (tag : Fin 10000) (htag : tag.val = 7605) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7605 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07606 (tag : Fin 10000) (htag : tag.val = 7606) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7606 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07607 (tag : Fin 10000) (htag : tag.val = 7607) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7607 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07608 (tag : Fin 10000) (htag : tag.val = 7608) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7608 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07609 (tag : Fin 10000) (htag : tag.val = 7609) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7609 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07610 (tag : Fin 10000) (htag : tag.val = 7610) (k : Ring12) : tag.val = 7610 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07611 (tag : Fin 10000) (htag : tag.val = 7611) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7611 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07612 (tag : Fin 10000) (htag : tag.val = 7612) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7612 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07613 (tag : Fin 10000) (htag : tag.val = 7613) (x : State) (e : Event) (dr : Ring12) : tag.val = 7613 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07614 (tag : Fin 10000) (htag : tag.val = 7614) (x : State) (e : Event) (dr : Ring12) : tag.val = 7614 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07615 (tag : Fin 10000) (htag : tag.val = 7615) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7615 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07616 (tag : Fin 10000) (htag : tag.val = 7616) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7616 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07617 (tag : Fin 10000) (htag : tag.val = 7617) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7617 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07618 (tag : Fin 10000) (htag : tag.val = 7618) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7618 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07619 (tag : Fin 10000) (htag : tag.val = 7619) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7619 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07620 (tag : Fin 10000) (htag : tag.val = 7620) (k : Ring12) : tag.val = 7620 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07621 (tag : Fin 10000) (htag : tag.val = 7621) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7621 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07622 (tag : Fin 10000) (htag : tag.val = 7622) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7622 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07623 (tag : Fin 10000) (htag : tag.val = 7623) (x : State) (e : Event) (dr : Ring12) : tag.val = 7623 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07624 (tag : Fin 10000) (htag : tag.val = 7624) (x : State) (e : Event) (dr : Ring12) : tag.val = 7624 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07625 (tag : Fin 10000) (htag : tag.val = 7625) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7625 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07626 (tag : Fin 10000) (htag : tag.val = 7626) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7626 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07627 (tag : Fin 10000) (htag : tag.val = 7627) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7627 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07628 (tag : Fin 10000) (htag : tag.val = 7628) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7628 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07629 (tag : Fin 10000) (htag : tag.val = 7629) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7629 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07630 (tag : Fin 10000) (htag : tag.val = 7630) (k : Ring12) : tag.val = 7630 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07631 (tag : Fin 10000) (htag : tag.val = 7631) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7631 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07632 (tag : Fin 10000) (htag : tag.val = 7632) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7632 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07633 (tag : Fin 10000) (htag : tag.val = 7633) (x : State) (e : Event) (dr : Ring12) : tag.val = 7633 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07634 (tag : Fin 10000) (htag : tag.val = 7634) (x : State) (e : Event) (dr : Ring12) : tag.val = 7634 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07635 (tag : Fin 10000) (htag : tag.val = 7635) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7635 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07636 (tag : Fin 10000) (htag : tag.val = 7636) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7636 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07637 (tag : Fin 10000) (htag : tag.val = 7637) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7637 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07638 (tag : Fin 10000) (htag : tag.val = 7638) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7638 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07639 (tag : Fin 10000) (htag : tag.val = 7639) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7639 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07640 (tag : Fin 10000) (htag : tag.val = 7640) (k : Ring12) : tag.val = 7640 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07641 (tag : Fin 10000) (htag : tag.val = 7641) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7641 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07642 (tag : Fin 10000) (htag : tag.val = 7642) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7642 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07643 (tag : Fin 10000) (htag : tag.val = 7643) (x : State) (e : Event) (dr : Ring12) : tag.val = 7643 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07644 (tag : Fin 10000) (htag : tag.val = 7644) (x : State) (e : Event) (dr : Ring12) : tag.val = 7644 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07645 (tag : Fin 10000) (htag : tag.val = 7645) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7645 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07646 (tag : Fin 10000) (htag : tag.val = 7646) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7646 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07647 (tag : Fin 10000) (htag : tag.val = 7647) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7647 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07648 (tag : Fin 10000) (htag : tag.val = 7648) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7648 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07649 (tag : Fin 10000) (htag : tag.val = 7649) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7649 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07650 (tag : Fin 10000) (htag : tag.val = 7650) (k : Ring12) : tag.val = 7650 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07651 (tag : Fin 10000) (htag : tag.val = 7651) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7651 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07652 (tag : Fin 10000) (htag : tag.val = 7652) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7652 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07653 (tag : Fin 10000) (htag : tag.val = 7653) (x : State) (e : Event) (dr : Ring12) : tag.val = 7653 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07654 (tag : Fin 10000) (htag : tag.val = 7654) (x : State) (e : Event) (dr : Ring12) : tag.val = 7654 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07655 (tag : Fin 10000) (htag : tag.val = 7655) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7655 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07656 (tag : Fin 10000) (htag : tag.val = 7656) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7656 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07657 (tag : Fin 10000) (htag : tag.val = 7657) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7657 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07658 (tag : Fin 10000) (htag : tag.val = 7658) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7658 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07659 (tag : Fin 10000) (htag : tag.val = 7659) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7659 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07660 (tag : Fin 10000) (htag : tag.val = 7660) (k : Ring12) : tag.val = 7660 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07661 (tag : Fin 10000) (htag : tag.val = 7661) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7661 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07662 (tag : Fin 10000) (htag : tag.val = 7662) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7662 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07663 (tag : Fin 10000) (htag : tag.val = 7663) (x : State) (e : Event) (dr : Ring12) : tag.val = 7663 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07664 (tag : Fin 10000) (htag : tag.val = 7664) (x : State) (e : Event) (dr : Ring12) : tag.val = 7664 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07665 (tag : Fin 10000) (htag : tag.val = 7665) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7665 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07666 (tag : Fin 10000) (htag : tag.val = 7666) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7666 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07667 (tag : Fin 10000) (htag : tag.val = 7667) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7667 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07668 (tag : Fin 10000) (htag : tag.val = 7668) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7668 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07669 (tag : Fin 10000) (htag : tag.val = 7669) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7669 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07670 (tag : Fin 10000) (htag : tag.val = 7670) (k : Ring12) : tag.val = 7670 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07671 (tag : Fin 10000) (htag : tag.val = 7671) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7671 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07672 (tag : Fin 10000) (htag : tag.val = 7672) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7672 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07673 (tag : Fin 10000) (htag : tag.val = 7673) (x : State) (e : Event) (dr : Ring12) : tag.val = 7673 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07674 (tag : Fin 10000) (htag : tag.val = 7674) (x : State) (e : Event) (dr : Ring12) : tag.val = 7674 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07675 (tag : Fin 10000) (htag : tag.val = 7675) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7675 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07676 (tag : Fin 10000) (htag : tag.val = 7676) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7676 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07677 (tag : Fin 10000) (htag : tag.val = 7677) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7677 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07678 (tag : Fin 10000) (htag : tag.val = 7678) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7678 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07679 (tag : Fin 10000) (htag : tag.val = 7679) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7679 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07680 (tag : Fin 10000) (htag : tag.val = 7680) (k : Ring12) : tag.val = 7680 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07681 (tag : Fin 10000) (htag : tag.val = 7681) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7681 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07682 (tag : Fin 10000) (htag : tag.val = 7682) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7682 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07683 (tag : Fin 10000) (htag : tag.val = 7683) (x : State) (e : Event) (dr : Ring12) : tag.val = 7683 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07684 (tag : Fin 10000) (htag : tag.val = 7684) (x : State) (e : Event) (dr : Ring12) : tag.val = 7684 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07685 (tag : Fin 10000) (htag : tag.val = 7685) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7685 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07686 (tag : Fin 10000) (htag : tag.val = 7686) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7686 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07687 (tag : Fin 10000) (htag : tag.val = 7687) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7687 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07688 (tag : Fin 10000) (htag : tag.val = 7688) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7688 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07689 (tag : Fin 10000) (htag : tag.val = 7689) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7689 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07690 (tag : Fin 10000) (htag : tag.val = 7690) (k : Ring12) : tag.val = 7690 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07691 (tag : Fin 10000) (htag : tag.val = 7691) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7691 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07692 (tag : Fin 10000) (htag : tag.val = 7692) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7692 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07693 (tag : Fin 10000) (htag : tag.val = 7693) (x : State) (e : Event) (dr : Ring12) : tag.val = 7693 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07694 (tag : Fin 10000) (htag : tag.val = 7694) (x : State) (e : Event) (dr : Ring12) : tag.val = 7694 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07695 (tag : Fin 10000) (htag : tag.val = 7695) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7695 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07696 (tag : Fin 10000) (htag : tag.val = 7696) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7696 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07697 (tag : Fin 10000) (htag : tag.val = 7697) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7697 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07698 (tag : Fin 10000) (htag : tag.val = 7698) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7698 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07699 (tag : Fin 10000) (htag : tag.val = 7699) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7699 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
