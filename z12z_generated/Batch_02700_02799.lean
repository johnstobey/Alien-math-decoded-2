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
theorem generated_02700 (tag : Fin 10000) (htag : tag.val = 2700) (k : Ring12) : tag.val = 2700 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02701 (tag : Fin 10000) (htag : tag.val = 2701) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2701 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02702 (tag : Fin 10000) (htag : tag.val = 2702) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2702 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02703 (tag : Fin 10000) (htag : tag.val = 2703) (x : State) (e : Event) (dr : Ring12) : tag.val = 2703 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02704 (tag : Fin 10000) (htag : tag.val = 2704) (x : State) (e : Event) (dr : Ring12) : tag.val = 2704 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02705 (tag : Fin 10000) (htag : tag.val = 2705) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2705 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02706 (tag : Fin 10000) (htag : tag.val = 2706) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2706 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02707 (tag : Fin 10000) (htag : tag.val = 2707) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2707 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02708 (tag : Fin 10000) (htag : tag.val = 2708) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2708 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02709 (tag : Fin 10000) (htag : tag.val = 2709) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2709 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02710 (tag : Fin 10000) (htag : tag.val = 2710) (k : Ring12) : tag.val = 2710 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02711 (tag : Fin 10000) (htag : tag.val = 2711) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2711 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02712 (tag : Fin 10000) (htag : tag.val = 2712) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2712 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02713 (tag : Fin 10000) (htag : tag.val = 2713) (x : State) (e : Event) (dr : Ring12) : tag.val = 2713 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02714 (tag : Fin 10000) (htag : tag.val = 2714) (x : State) (e : Event) (dr : Ring12) : tag.val = 2714 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02715 (tag : Fin 10000) (htag : tag.val = 2715) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2715 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02716 (tag : Fin 10000) (htag : tag.val = 2716) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2716 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02717 (tag : Fin 10000) (htag : tag.val = 2717) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2717 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02718 (tag : Fin 10000) (htag : tag.val = 2718) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2718 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02719 (tag : Fin 10000) (htag : tag.val = 2719) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2719 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02720 (tag : Fin 10000) (htag : tag.val = 2720) (k : Ring12) : tag.val = 2720 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02721 (tag : Fin 10000) (htag : tag.val = 2721) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2721 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02722 (tag : Fin 10000) (htag : tag.val = 2722) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2722 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02723 (tag : Fin 10000) (htag : tag.val = 2723) (x : State) (e : Event) (dr : Ring12) : tag.val = 2723 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02724 (tag : Fin 10000) (htag : tag.val = 2724) (x : State) (e : Event) (dr : Ring12) : tag.val = 2724 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02725 (tag : Fin 10000) (htag : tag.val = 2725) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2725 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02726 (tag : Fin 10000) (htag : tag.val = 2726) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2726 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02727 (tag : Fin 10000) (htag : tag.val = 2727) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2727 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02728 (tag : Fin 10000) (htag : tag.val = 2728) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2728 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02729 (tag : Fin 10000) (htag : tag.val = 2729) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2729 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02730 (tag : Fin 10000) (htag : tag.val = 2730) (k : Ring12) : tag.val = 2730 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02731 (tag : Fin 10000) (htag : tag.val = 2731) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2731 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02732 (tag : Fin 10000) (htag : tag.val = 2732) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2732 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02733 (tag : Fin 10000) (htag : tag.val = 2733) (x : State) (e : Event) (dr : Ring12) : tag.val = 2733 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02734 (tag : Fin 10000) (htag : tag.val = 2734) (x : State) (e : Event) (dr : Ring12) : tag.val = 2734 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02735 (tag : Fin 10000) (htag : tag.val = 2735) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2735 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02736 (tag : Fin 10000) (htag : tag.val = 2736) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2736 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02737 (tag : Fin 10000) (htag : tag.val = 2737) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2737 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02738 (tag : Fin 10000) (htag : tag.val = 2738) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2738 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02739 (tag : Fin 10000) (htag : tag.val = 2739) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2739 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02740 (tag : Fin 10000) (htag : tag.val = 2740) (k : Ring12) : tag.val = 2740 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02741 (tag : Fin 10000) (htag : tag.val = 2741) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2741 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02742 (tag : Fin 10000) (htag : tag.val = 2742) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2742 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02743 (tag : Fin 10000) (htag : tag.val = 2743) (x : State) (e : Event) (dr : Ring12) : tag.val = 2743 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02744 (tag : Fin 10000) (htag : tag.val = 2744) (x : State) (e : Event) (dr : Ring12) : tag.val = 2744 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02745 (tag : Fin 10000) (htag : tag.val = 2745) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2745 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02746 (tag : Fin 10000) (htag : tag.val = 2746) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2746 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02747 (tag : Fin 10000) (htag : tag.val = 2747) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2747 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02748 (tag : Fin 10000) (htag : tag.val = 2748) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2748 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02749 (tag : Fin 10000) (htag : tag.val = 2749) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2749 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02750 (tag : Fin 10000) (htag : tag.val = 2750) (k : Ring12) : tag.val = 2750 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02751 (tag : Fin 10000) (htag : tag.val = 2751) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2751 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02752 (tag : Fin 10000) (htag : tag.val = 2752) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2752 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02753 (tag : Fin 10000) (htag : tag.val = 2753) (x : State) (e : Event) (dr : Ring12) : tag.val = 2753 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02754 (tag : Fin 10000) (htag : tag.val = 2754) (x : State) (e : Event) (dr : Ring12) : tag.val = 2754 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02755 (tag : Fin 10000) (htag : tag.val = 2755) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2755 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02756 (tag : Fin 10000) (htag : tag.val = 2756) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2756 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02757 (tag : Fin 10000) (htag : tag.val = 2757) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2757 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02758 (tag : Fin 10000) (htag : tag.val = 2758) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2758 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02759 (tag : Fin 10000) (htag : tag.val = 2759) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2759 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02760 (tag : Fin 10000) (htag : tag.val = 2760) (k : Ring12) : tag.val = 2760 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02761 (tag : Fin 10000) (htag : tag.val = 2761) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2761 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02762 (tag : Fin 10000) (htag : tag.val = 2762) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2762 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02763 (tag : Fin 10000) (htag : tag.val = 2763) (x : State) (e : Event) (dr : Ring12) : tag.val = 2763 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02764 (tag : Fin 10000) (htag : tag.val = 2764) (x : State) (e : Event) (dr : Ring12) : tag.val = 2764 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02765 (tag : Fin 10000) (htag : tag.val = 2765) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2765 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02766 (tag : Fin 10000) (htag : tag.val = 2766) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2766 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02767 (tag : Fin 10000) (htag : tag.val = 2767) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2767 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02768 (tag : Fin 10000) (htag : tag.val = 2768) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2768 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02769 (tag : Fin 10000) (htag : tag.val = 2769) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2769 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02770 (tag : Fin 10000) (htag : tag.val = 2770) (k : Ring12) : tag.val = 2770 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02771 (tag : Fin 10000) (htag : tag.val = 2771) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2771 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02772 (tag : Fin 10000) (htag : tag.val = 2772) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2772 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02773 (tag : Fin 10000) (htag : tag.val = 2773) (x : State) (e : Event) (dr : Ring12) : tag.val = 2773 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02774 (tag : Fin 10000) (htag : tag.val = 2774) (x : State) (e : Event) (dr : Ring12) : tag.val = 2774 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02775 (tag : Fin 10000) (htag : tag.val = 2775) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2775 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02776 (tag : Fin 10000) (htag : tag.val = 2776) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2776 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02777 (tag : Fin 10000) (htag : tag.val = 2777) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2777 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02778 (tag : Fin 10000) (htag : tag.val = 2778) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2778 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02779 (tag : Fin 10000) (htag : tag.val = 2779) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2779 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02780 (tag : Fin 10000) (htag : tag.val = 2780) (k : Ring12) : tag.val = 2780 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02781 (tag : Fin 10000) (htag : tag.val = 2781) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2781 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02782 (tag : Fin 10000) (htag : tag.val = 2782) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2782 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02783 (tag : Fin 10000) (htag : tag.val = 2783) (x : State) (e : Event) (dr : Ring12) : tag.val = 2783 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02784 (tag : Fin 10000) (htag : tag.val = 2784) (x : State) (e : Event) (dr : Ring12) : tag.val = 2784 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02785 (tag : Fin 10000) (htag : tag.val = 2785) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2785 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02786 (tag : Fin 10000) (htag : tag.val = 2786) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2786 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02787 (tag : Fin 10000) (htag : tag.val = 2787) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2787 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02788 (tag : Fin 10000) (htag : tag.val = 2788) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2788 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02789 (tag : Fin 10000) (htag : tag.val = 2789) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2789 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02790 (tag : Fin 10000) (htag : tag.val = 2790) (k : Ring12) : tag.val = 2790 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02791 (tag : Fin 10000) (htag : tag.val = 2791) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2791 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02792 (tag : Fin 10000) (htag : tag.val = 2792) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2792 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02793 (tag : Fin 10000) (htag : tag.val = 2793) (x : State) (e : Event) (dr : Ring12) : tag.val = 2793 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02794 (tag : Fin 10000) (htag : tag.val = 2794) (x : State) (e : Event) (dr : Ring12) : tag.val = 2794 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02795 (tag : Fin 10000) (htag : tag.val = 2795) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2795 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02796 (tag : Fin 10000) (htag : tag.val = 2796) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2796 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02797 (tag : Fin 10000) (htag : tag.val = 2797) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2797 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02798 (tag : Fin 10000) (htag : tag.val = 2798) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2798 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02799 (tag : Fin 10000) (htag : tag.val = 2799) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2799 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
