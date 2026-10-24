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
theorem generated_02600 (tag : Fin 10000) (htag : tag.val = 2600) (k : Ring12) : tag.val = 2600 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02601 (tag : Fin 10000) (htag : tag.val = 2601) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2601 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02602 (tag : Fin 10000) (htag : tag.val = 2602) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2602 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02603 (tag : Fin 10000) (htag : tag.val = 2603) (x : State) (e : Event) (dr : Ring12) : tag.val = 2603 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02604 (tag : Fin 10000) (htag : tag.val = 2604) (x : State) (e : Event) (dr : Ring12) : tag.val = 2604 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02605 (tag : Fin 10000) (htag : tag.val = 2605) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2605 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02606 (tag : Fin 10000) (htag : tag.val = 2606) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2606 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02607 (tag : Fin 10000) (htag : tag.val = 2607) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2607 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02608 (tag : Fin 10000) (htag : tag.val = 2608) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2608 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02609 (tag : Fin 10000) (htag : tag.val = 2609) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2609 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02610 (tag : Fin 10000) (htag : tag.val = 2610) (k : Ring12) : tag.val = 2610 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02611 (tag : Fin 10000) (htag : tag.val = 2611) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2611 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02612 (tag : Fin 10000) (htag : tag.val = 2612) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2612 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02613 (tag : Fin 10000) (htag : tag.val = 2613) (x : State) (e : Event) (dr : Ring12) : tag.val = 2613 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02614 (tag : Fin 10000) (htag : tag.val = 2614) (x : State) (e : Event) (dr : Ring12) : tag.val = 2614 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02615 (tag : Fin 10000) (htag : tag.val = 2615) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2615 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02616 (tag : Fin 10000) (htag : tag.val = 2616) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2616 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02617 (tag : Fin 10000) (htag : tag.val = 2617) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2617 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02618 (tag : Fin 10000) (htag : tag.val = 2618) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2618 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02619 (tag : Fin 10000) (htag : tag.val = 2619) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2619 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02620 (tag : Fin 10000) (htag : tag.val = 2620) (k : Ring12) : tag.val = 2620 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02621 (tag : Fin 10000) (htag : tag.val = 2621) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2621 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02622 (tag : Fin 10000) (htag : tag.val = 2622) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2622 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02623 (tag : Fin 10000) (htag : tag.val = 2623) (x : State) (e : Event) (dr : Ring12) : tag.val = 2623 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02624 (tag : Fin 10000) (htag : tag.val = 2624) (x : State) (e : Event) (dr : Ring12) : tag.val = 2624 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02625 (tag : Fin 10000) (htag : tag.val = 2625) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2625 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02626 (tag : Fin 10000) (htag : tag.val = 2626) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2626 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02627 (tag : Fin 10000) (htag : tag.val = 2627) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2627 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02628 (tag : Fin 10000) (htag : tag.val = 2628) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2628 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02629 (tag : Fin 10000) (htag : tag.val = 2629) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2629 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02630 (tag : Fin 10000) (htag : tag.val = 2630) (k : Ring12) : tag.val = 2630 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02631 (tag : Fin 10000) (htag : tag.val = 2631) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2631 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02632 (tag : Fin 10000) (htag : tag.val = 2632) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2632 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02633 (tag : Fin 10000) (htag : tag.val = 2633) (x : State) (e : Event) (dr : Ring12) : tag.val = 2633 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02634 (tag : Fin 10000) (htag : tag.val = 2634) (x : State) (e : Event) (dr : Ring12) : tag.val = 2634 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02635 (tag : Fin 10000) (htag : tag.val = 2635) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2635 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02636 (tag : Fin 10000) (htag : tag.val = 2636) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2636 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02637 (tag : Fin 10000) (htag : tag.val = 2637) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2637 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02638 (tag : Fin 10000) (htag : tag.val = 2638) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2638 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02639 (tag : Fin 10000) (htag : tag.val = 2639) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2639 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02640 (tag : Fin 10000) (htag : tag.val = 2640) (k : Ring12) : tag.val = 2640 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02641 (tag : Fin 10000) (htag : tag.val = 2641) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2641 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02642 (tag : Fin 10000) (htag : tag.val = 2642) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2642 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02643 (tag : Fin 10000) (htag : tag.val = 2643) (x : State) (e : Event) (dr : Ring12) : tag.val = 2643 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02644 (tag : Fin 10000) (htag : tag.val = 2644) (x : State) (e : Event) (dr : Ring12) : tag.val = 2644 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02645 (tag : Fin 10000) (htag : tag.val = 2645) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2645 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02646 (tag : Fin 10000) (htag : tag.val = 2646) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2646 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02647 (tag : Fin 10000) (htag : tag.val = 2647) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2647 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02648 (tag : Fin 10000) (htag : tag.val = 2648) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2648 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02649 (tag : Fin 10000) (htag : tag.val = 2649) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2649 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02650 (tag : Fin 10000) (htag : tag.val = 2650) (k : Ring12) : tag.val = 2650 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02651 (tag : Fin 10000) (htag : tag.val = 2651) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2651 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02652 (tag : Fin 10000) (htag : tag.val = 2652) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2652 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02653 (tag : Fin 10000) (htag : tag.val = 2653) (x : State) (e : Event) (dr : Ring12) : tag.val = 2653 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02654 (tag : Fin 10000) (htag : tag.val = 2654) (x : State) (e : Event) (dr : Ring12) : tag.val = 2654 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02655 (tag : Fin 10000) (htag : tag.val = 2655) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2655 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02656 (tag : Fin 10000) (htag : tag.val = 2656) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2656 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02657 (tag : Fin 10000) (htag : tag.val = 2657) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2657 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02658 (tag : Fin 10000) (htag : tag.val = 2658) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2658 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02659 (tag : Fin 10000) (htag : tag.val = 2659) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2659 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02660 (tag : Fin 10000) (htag : tag.val = 2660) (k : Ring12) : tag.val = 2660 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02661 (tag : Fin 10000) (htag : tag.val = 2661) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2661 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02662 (tag : Fin 10000) (htag : tag.val = 2662) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2662 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02663 (tag : Fin 10000) (htag : tag.val = 2663) (x : State) (e : Event) (dr : Ring12) : tag.val = 2663 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02664 (tag : Fin 10000) (htag : tag.val = 2664) (x : State) (e : Event) (dr : Ring12) : tag.val = 2664 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02665 (tag : Fin 10000) (htag : tag.val = 2665) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2665 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02666 (tag : Fin 10000) (htag : tag.val = 2666) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2666 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02667 (tag : Fin 10000) (htag : tag.val = 2667) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2667 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02668 (tag : Fin 10000) (htag : tag.val = 2668) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2668 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02669 (tag : Fin 10000) (htag : tag.val = 2669) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2669 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02670 (tag : Fin 10000) (htag : tag.val = 2670) (k : Ring12) : tag.val = 2670 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02671 (tag : Fin 10000) (htag : tag.val = 2671) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2671 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02672 (tag : Fin 10000) (htag : tag.val = 2672) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2672 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02673 (tag : Fin 10000) (htag : tag.val = 2673) (x : State) (e : Event) (dr : Ring12) : tag.val = 2673 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02674 (tag : Fin 10000) (htag : tag.val = 2674) (x : State) (e : Event) (dr : Ring12) : tag.val = 2674 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02675 (tag : Fin 10000) (htag : tag.val = 2675) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2675 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02676 (tag : Fin 10000) (htag : tag.val = 2676) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2676 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02677 (tag : Fin 10000) (htag : tag.val = 2677) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2677 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02678 (tag : Fin 10000) (htag : tag.val = 2678) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2678 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02679 (tag : Fin 10000) (htag : tag.val = 2679) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2679 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02680 (tag : Fin 10000) (htag : tag.val = 2680) (k : Ring12) : tag.val = 2680 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02681 (tag : Fin 10000) (htag : tag.val = 2681) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2681 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02682 (tag : Fin 10000) (htag : tag.val = 2682) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2682 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02683 (tag : Fin 10000) (htag : tag.val = 2683) (x : State) (e : Event) (dr : Ring12) : tag.val = 2683 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02684 (tag : Fin 10000) (htag : tag.val = 2684) (x : State) (e : Event) (dr : Ring12) : tag.val = 2684 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02685 (tag : Fin 10000) (htag : tag.val = 2685) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2685 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02686 (tag : Fin 10000) (htag : tag.val = 2686) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2686 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02687 (tag : Fin 10000) (htag : tag.val = 2687) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2687 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02688 (tag : Fin 10000) (htag : tag.val = 2688) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2688 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02689 (tag : Fin 10000) (htag : tag.val = 2689) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2689 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02690 (tag : Fin 10000) (htag : tag.val = 2690) (k : Ring12) : tag.val = 2690 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02691 (tag : Fin 10000) (htag : tag.val = 2691) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2691 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02692 (tag : Fin 10000) (htag : tag.val = 2692) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2692 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02693 (tag : Fin 10000) (htag : tag.val = 2693) (x : State) (e : Event) (dr : Ring12) : tag.val = 2693 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02694 (tag : Fin 10000) (htag : tag.val = 2694) (x : State) (e : Event) (dr : Ring12) : tag.val = 2694 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02695 (tag : Fin 10000) (htag : tag.val = 2695) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2695 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02696 (tag : Fin 10000) (htag : tag.val = 2696) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2696 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02697 (tag : Fin 10000) (htag : tag.val = 2697) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2697 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02698 (tag : Fin 10000) (htag : tag.val = 2698) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2698 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02699 (tag : Fin 10000) (htag : tag.val = 2699) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2699 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
