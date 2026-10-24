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
theorem generated_03800 (tag : Fin 10000) (htag : tag.val = 3800) (k : Ring12) : tag.val = 3800 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03801 (tag : Fin 10000) (htag : tag.val = 3801) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3801 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03802 (tag : Fin 10000) (htag : tag.val = 3802) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3802 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03803 (tag : Fin 10000) (htag : tag.val = 3803) (x : State) (e : Event) (dr : Ring12) : tag.val = 3803 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03804 (tag : Fin 10000) (htag : tag.val = 3804) (x : State) (e : Event) (dr : Ring12) : tag.val = 3804 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03805 (tag : Fin 10000) (htag : tag.val = 3805) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3805 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03806 (tag : Fin 10000) (htag : tag.val = 3806) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3806 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03807 (tag : Fin 10000) (htag : tag.val = 3807) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3807 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03808 (tag : Fin 10000) (htag : tag.val = 3808) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3808 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03809 (tag : Fin 10000) (htag : tag.val = 3809) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3809 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03810 (tag : Fin 10000) (htag : tag.val = 3810) (k : Ring12) : tag.val = 3810 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03811 (tag : Fin 10000) (htag : tag.val = 3811) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3811 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03812 (tag : Fin 10000) (htag : tag.val = 3812) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3812 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03813 (tag : Fin 10000) (htag : tag.val = 3813) (x : State) (e : Event) (dr : Ring12) : tag.val = 3813 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03814 (tag : Fin 10000) (htag : tag.val = 3814) (x : State) (e : Event) (dr : Ring12) : tag.val = 3814 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03815 (tag : Fin 10000) (htag : tag.val = 3815) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3815 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03816 (tag : Fin 10000) (htag : tag.val = 3816) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3816 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03817 (tag : Fin 10000) (htag : tag.val = 3817) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3817 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03818 (tag : Fin 10000) (htag : tag.val = 3818) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3818 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03819 (tag : Fin 10000) (htag : tag.val = 3819) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3819 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03820 (tag : Fin 10000) (htag : tag.val = 3820) (k : Ring12) : tag.val = 3820 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03821 (tag : Fin 10000) (htag : tag.val = 3821) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3821 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03822 (tag : Fin 10000) (htag : tag.val = 3822) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3822 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03823 (tag : Fin 10000) (htag : tag.val = 3823) (x : State) (e : Event) (dr : Ring12) : tag.val = 3823 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03824 (tag : Fin 10000) (htag : tag.val = 3824) (x : State) (e : Event) (dr : Ring12) : tag.val = 3824 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03825 (tag : Fin 10000) (htag : tag.val = 3825) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3825 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03826 (tag : Fin 10000) (htag : tag.val = 3826) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3826 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03827 (tag : Fin 10000) (htag : tag.val = 3827) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3827 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03828 (tag : Fin 10000) (htag : tag.val = 3828) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3828 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03829 (tag : Fin 10000) (htag : tag.val = 3829) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3829 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03830 (tag : Fin 10000) (htag : tag.val = 3830) (k : Ring12) : tag.val = 3830 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03831 (tag : Fin 10000) (htag : tag.val = 3831) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3831 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03832 (tag : Fin 10000) (htag : tag.val = 3832) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3832 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03833 (tag : Fin 10000) (htag : tag.val = 3833) (x : State) (e : Event) (dr : Ring12) : tag.val = 3833 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03834 (tag : Fin 10000) (htag : tag.val = 3834) (x : State) (e : Event) (dr : Ring12) : tag.val = 3834 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03835 (tag : Fin 10000) (htag : tag.val = 3835) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3835 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03836 (tag : Fin 10000) (htag : tag.val = 3836) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3836 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03837 (tag : Fin 10000) (htag : tag.val = 3837) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3837 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03838 (tag : Fin 10000) (htag : tag.val = 3838) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3838 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03839 (tag : Fin 10000) (htag : tag.val = 3839) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3839 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03840 (tag : Fin 10000) (htag : tag.val = 3840) (k : Ring12) : tag.val = 3840 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03841 (tag : Fin 10000) (htag : tag.val = 3841) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3841 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03842 (tag : Fin 10000) (htag : tag.val = 3842) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3842 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03843 (tag : Fin 10000) (htag : tag.val = 3843) (x : State) (e : Event) (dr : Ring12) : tag.val = 3843 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03844 (tag : Fin 10000) (htag : tag.val = 3844) (x : State) (e : Event) (dr : Ring12) : tag.val = 3844 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03845 (tag : Fin 10000) (htag : tag.val = 3845) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3845 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03846 (tag : Fin 10000) (htag : tag.val = 3846) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3846 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03847 (tag : Fin 10000) (htag : tag.val = 3847) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3847 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03848 (tag : Fin 10000) (htag : tag.val = 3848) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3848 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03849 (tag : Fin 10000) (htag : tag.val = 3849) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3849 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03850 (tag : Fin 10000) (htag : tag.val = 3850) (k : Ring12) : tag.val = 3850 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03851 (tag : Fin 10000) (htag : tag.val = 3851) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3851 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03852 (tag : Fin 10000) (htag : tag.val = 3852) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3852 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03853 (tag : Fin 10000) (htag : tag.val = 3853) (x : State) (e : Event) (dr : Ring12) : tag.val = 3853 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03854 (tag : Fin 10000) (htag : tag.val = 3854) (x : State) (e : Event) (dr : Ring12) : tag.val = 3854 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03855 (tag : Fin 10000) (htag : tag.val = 3855) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3855 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03856 (tag : Fin 10000) (htag : tag.val = 3856) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3856 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03857 (tag : Fin 10000) (htag : tag.val = 3857) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3857 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03858 (tag : Fin 10000) (htag : tag.val = 3858) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3858 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03859 (tag : Fin 10000) (htag : tag.val = 3859) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3859 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03860 (tag : Fin 10000) (htag : tag.val = 3860) (k : Ring12) : tag.val = 3860 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03861 (tag : Fin 10000) (htag : tag.val = 3861) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3861 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03862 (tag : Fin 10000) (htag : tag.val = 3862) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3862 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03863 (tag : Fin 10000) (htag : tag.val = 3863) (x : State) (e : Event) (dr : Ring12) : tag.val = 3863 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03864 (tag : Fin 10000) (htag : tag.val = 3864) (x : State) (e : Event) (dr : Ring12) : tag.val = 3864 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03865 (tag : Fin 10000) (htag : tag.val = 3865) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3865 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03866 (tag : Fin 10000) (htag : tag.val = 3866) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3866 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03867 (tag : Fin 10000) (htag : tag.val = 3867) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3867 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03868 (tag : Fin 10000) (htag : tag.val = 3868) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3868 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03869 (tag : Fin 10000) (htag : tag.val = 3869) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3869 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03870 (tag : Fin 10000) (htag : tag.val = 3870) (k : Ring12) : tag.val = 3870 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03871 (tag : Fin 10000) (htag : tag.val = 3871) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3871 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03872 (tag : Fin 10000) (htag : tag.val = 3872) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3872 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03873 (tag : Fin 10000) (htag : tag.val = 3873) (x : State) (e : Event) (dr : Ring12) : tag.val = 3873 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03874 (tag : Fin 10000) (htag : tag.val = 3874) (x : State) (e : Event) (dr : Ring12) : tag.val = 3874 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03875 (tag : Fin 10000) (htag : tag.val = 3875) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3875 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03876 (tag : Fin 10000) (htag : tag.val = 3876) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3876 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03877 (tag : Fin 10000) (htag : tag.val = 3877) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3877 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03878 (tag : Fin 10000) (htag : tag.val = 3878) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3878 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03879 (tag : Fin 10000) (htag : tag.val = 3879) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3879 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03880 (tag : Fin 10000) (htag : tag.val = 3880) (k : Ring12) : tag.val = 3880 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03881 (tag : Fin 10000) (htag : tag.val = 3881) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3881 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03882 (tag : Fin 10000) (htag : tag.val = 3882) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3882 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03883 (tag : Fin 10000) (htag : tag.val = 3883) (x : State) (e : Event) (dr : Ring12) : tag.val = 3883 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03884 (tag : Fin 10000) (htag : tag.val = 3884) (x : State) (e : Event) (dr : Ring12) : tag.val = 3884 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03885 (tag : Fin 10000) (htag : tag.val = 3885) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3885 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03886 (tag : Fin 10000) (htag : tag.val = 3886) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3886 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03887 (tag : Fin 10000) (htag : tag.val = 3887) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3887 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03888 (tag : Fin 10000) (htag : tag.val = 3888) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3888 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03889 (tag : Fin 10000) (htag : tag.val = 3889) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3889 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03890 (tag : Fin 10000) (htag : tag.val = 3890) (k : Ring12) : tag.val = 3890 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03891 (tag : Fin 10000) (htag : tag.val = 3891) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3891 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03892 (tag : Fin 10000) (htag : tag.val = 3892) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3892 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03893 (tag : Fin 10000) (htag : tag.val = 3893) (x : State) (e : Event) (dr : Ring12) : tag.val = 3893 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03894 (tag : Fin 10000) (htag : tag.val = 3894) (x : State) (e : Event) (dr : Ring12) : tag.val = 3894 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03895 (tag : Fin 10000) (htag : tag.val = 3895) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3895 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03896 (tag : Fin 10000) (htag : tag.val = 3896) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3896 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03897 (tag : Fin 10000) (htag : tag.val = 3897) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3897 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03898 (tag : Fin 10000) (htag : tag.val = 3898) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3898 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03899 (tag : Fin 10000) (htag : tag.val = 3899) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3899 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
