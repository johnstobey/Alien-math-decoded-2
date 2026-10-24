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
theorem generated_03700 (tag : Fin 10000) (htag : tag.val = 3700) (k : Ring12) : tag.val = 3700 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03701 (tag : Fin 10000) (htag : tag.val = 3701) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3701 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03702 (tag : Fin 10000) (htag : tag.val = 3702) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3702 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03703 (tag : Fin 10000) (htag : tag.val = 3703) (x : State) (e : Event) (dr : Ring12) : tag.val = 3703 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03704 (tag : Fin 10000) (htag : tag.val = 3704) (x : State) (e : Event) (dr : Ring12) : tag.val = 3704 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03705 (tag : Fin 10000) (htag : tag.val = 3705) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3705 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03706 (tag : Fin 10000) (htag : tag.val = 3706) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3706 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03707 (tag : Fin 10000) (htag : tag.val = 3707) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3707 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03708 (tag : Fin 10000) (htag : tag.val = 3708) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3708 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03709 (tag : Fin 10000) (htag : tag.val = 3709) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3709 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03710 (tag : Fin 10000) (htag : tag.val = 3710) (k : Ring12) : tag.val = 3710 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03711 (tag : Fin 10000) (htag : tag.val = 3711) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3711 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03712 (tag : Fin 10000) (htag : tag.val = 3712) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3712 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03713 (tag : Fin 10000) (htag : tag.val = 3713) (x : State) (e : Event) (dr : Ring12) : tag.val = 3713 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03714 (tag : Fin 10000) (htag : tag.val = 3714) (x : State) (e : Event) (dr : Ring12) : tag.val = 3714 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03715 (tag : Fin 10000) (htag : tag.val = 3715) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3715 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03716 (tag : Fin 10000) (htag : tag.val = 3716) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3716 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03717 (tag : Fin 10000) (htag : tag.val = 3717) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3717 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03718 (tag : Fin 10000) (htag : tag.val = 3718) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3718 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03719 (tag : Fin 10000) (htag : tag.val = 3719) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3719 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03720 (tag : Fin 10000) (htag : tag.val = 3720) (k : Ring12) : tag.val = 3720 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03721 (tag : Fin 10000) (htag : tag.val = 3721) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3721 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03722 (tag : Fin 10000) (htag : tag.val = 3722) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3722 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03723 (tag : Fin 10000) (htag : tag.val = 3723) (x : State) (e : Event) (dr : Ring12) : tag.val = 3723 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03724 (tag : Fin 10000) (htag : tag.val = 3724) (x : State) (e : Event) (dr : Ring12) : tag.val = 3724 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03725 (tag : Fin 10000) (htag : tag.val = 3725) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3725 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03726 (tag : Fin 10000) (htag : tag.val = 3726) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3726 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03727 (tag : Fin 10000) (htag : tag.val = 3727) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3727 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03728 (tag : Fin 10000) (htag : tag.val = 3728) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3728 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03729 (tag : Fin 10000) (htag : tag.val = 3729) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3729 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03730 (tag : Fin 10000) (htag : tag.val = 3730) (k : Ring12) : tag.val = 3730 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03731 (tag : Fin 10000) (htag : tag.val = 3731) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3731 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03732 (tag : Fin 10000) (htag : tag.val = 3732) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3732 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03733 (tag : Fin 10000) (htag : tag.val = 3733) (x : State) (e : Event) (dr : Ring12) : tag.val = 3733 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03734 (tag : Fin 10000) (htag : tag.val = 3734) (x : State) (e : Event) (dr : Ring12) : tag.val = 3734 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03735 (tag : Fin 10000) (htag : tag.val = 3735) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3735 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03736 (tag : Fin 10000) (htag : tag.val = 3736) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3736 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03737 (tag : Fin 10000) (htag : tag.val = 3737) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3737 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03738 (tag : Fin 10000) (htag : tag.val = 3738) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3738 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03739 (tag : Fin 10000) (htag : tag.val = 3739) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3739 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03740 (tag : Fin 10000) (htag : tag.val = 3740) (k : Ring12) : tag.val = 3740 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03741 (tag : Fin 10000) (htag : tag.val = 3741) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3741 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03742 (tag : Fin 10000) (htag : tag.val = 3742) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3742 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03743 (tag : Fin 10000) (htag : tag.val = 3743) (x : State) (e : Event) (dr : Ring12) : tag.val = 3743 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03744 (tag : Fin 10000) (htag : tag.val = 3744) (x : State) (e : Event) (dr : Ring12) : tag.val = 3744 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03745 (tag : Fin 10000) (htag : tag.val = 3745) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3745 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03746 (tag : Fin 10000) (htag : tag.val = 3746) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3746 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03747 (tag : Fin 10000) (htag : tag.val = 3747) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3747 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03748 (tag : Fin 10000) (htag : tag.val = 3748) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3748 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03749 (tag : Fin 10000) (htag : tag.val = 3749) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3749 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03750 (tag : Fin 10000) (htag : tag.val = 3750) (k : Ring12) : tag.val = 3750 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03751 (tag : Fin 10000) (htag : tag.val = 3751) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3751 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03752 (tag : Fin 10000) (htag : tag.val = 3752) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3752 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03753 (tag : Fin 10000) (htag : tag.val = 3753) (x : State) (e : Event) (dr : Ring12) : tag.val = 3753 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03754 (tag : Fin 10000) (htag : tag.val = 3754) (x : State) (e : Event) (dr : Ring12) : tag.val = 3754 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03755 (tag : Fin 10000) (htag : tag.val = 3755) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3755 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03756 (tag : Fin 10000) (htag : tag.val = 3756) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3756 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03757 (tag : Fin 10000) (htag : tag.val = 3757) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3757 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03758 (tag : Fin 10000) (htag : tag.val = 3758) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3758 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03759 (tag : Fin 10000) (htag : tag.val = 3759) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3759 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03760 (tag : Fin 10000) (htag : tag.val = 3760) (k : Ring12) : tag.val = 3760 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03761 (tag : Fin 10000) (htag : tag.val = 3761) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3761 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03762 (tag : Fin 10000) (htag : tag.val = 3762) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3762 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03763 (tag : Fin 10000) (htag : tag.val = 3763) (x : State) (e : Event) (dr : Ring12) : tag.val = 3763 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03764 (tag : Fin 10000) (htag : tag.val = 3764) (x : State) (e : Event) (dr : Ring12) : tag.val = 3764 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03765 (tag : Fin 10000) (htag : tag.val = 3765) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3765 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03766 (tag : Fin 10000) (htag : tag.val = 3766) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3766 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03767 (tag : Fin 10000) (htag : tag.val = 3767) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3767 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03768 (tag : Fin 10000) (htag : tag.val = 3768) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3768 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03769 (tag : Fin 10000) (htag : tag.val = 3769) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3769 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03770 (tag : Fin 10000) (htag : tag.val = 3770) (k : Ring12) : tag.val = 3770 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03771 (tag : Fin 10000) (htag : tag.val = 3771) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3771 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03772 (tag : Fin 10000) (htag : tag.val = 3772) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3772 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03773 (tag : Fin 10000) (htag : tag.val = 3773) (x : State) (e : Event) (dr : Ring12) : tag.val = 3773 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03774 (tag : Fin 10000) (htag : tag.val = 3774) (x : State) (e : Event) (dr : Ring12) : tag.val = 3774 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03775 (tag : Fin 10000) (htag : tag.val = 3775) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3775 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03776 (tag : Fin 10000) (htag : tag.val = 3776) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3776 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03777 (tag : Fin 10000) (htag : tag.val = 3777) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3777 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03778 (tag : Fin 10000) (htag : tag.val = 3778) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3778 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03779 (tag : Fin 10000) (htag : tag.val = 3779) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3779 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03780 (tag : Fin 10000) (htag : tag.val = 3780) (k : Ring12) : tag.val = 3780 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03781 (tag : Fin 10000) (htag : tag.val = 3781) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3781 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03782 (tag : Fin 10000) (htag : tag.val = 3782) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3782 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03783 (tag : Fin 10000) (htag : tag.val = 3783) (x : State) (e : Event) (dr : Ring12) : tag.val = 3783 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03784 (tag : Fin 10000) (htag : tag.val = 3784) (x : State) (e : Event) (dr : Ring12) : tag.val = 3784 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03785 (tag : Fin 10000) (htag : tag.val = 3785) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3785 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03786 (tag : Fin 10000) (htag : tag.val = 3786) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3786 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03787 (tag : Fin 10000) (htag : tag.val = 3787) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3787 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03788 (tag : Fin 10000) (htag : tag.val = 3788) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3788 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03789 (tag : Fin 10000) (htag : tag.val = 3789) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3789 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03790 (tag : Fin 10000) (htag : tag.val = 3790) (k : Ring12) : tag.val = 3790 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03791 (tag : Fin 10000) (htag : tag.val = 3791) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3791 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03792 (tag : Fin 10000) (htag : tag.val = 3792) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3792 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03793 (tag : Fin 10000) (htag : tag.val = 3793) (x : State) (e : Event) (dr : Ring12) : tag.val = 3793 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03794 (tag : Fin 10000) (htag : tag.val = 3794) (x : State) (e : Event) (dr : Ring12) : tag.val = 3794 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03795 (tag : Fin 10000) (htag : tag.val = 3795) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3795 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03796 (tag : Fin 10000) (htag : tag.val = 3796) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3796 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03797 (tag : Fin 10000) (htag : tag.val = 3797) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3797 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03798 (tag : Fin 10000) (htag : tag.val = 3798) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3798 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03799 (tag : Fin 10000) (htag : tag.val = 3799) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3799 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
