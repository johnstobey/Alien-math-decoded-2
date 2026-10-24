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
theorem generated_00800 (tag : Fin 10000) (htag : tag.val = 800) (k : Ring12) : tag.val = 800 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00801 (tag : Fin 10000) (htag : tag.val = 801) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 801 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00802 (tag : Fin 10000) (htag : tag.val = 802) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 802 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00803 (tag : Fin 10000) (htag : tag.val = 803) (x : State) (e : Event) (dr : Ring12) : tag.val = 803 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00804 (tag : Fin 10000) (htag : tag.val = 804) (x : State) (e : Event) (dr : Ring12) : tag.val = 804 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00805 (tag : Fin 10000) (htag : tag.val = 805) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 805 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00806 (tag : Fin 10000) (htag : tag.val = 806) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 806 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00807 (tag : Fin 10000) (htag : tag.val = 807) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 807 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00808 (tag : Fin 10000) (htag : tag.val = 808) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 808 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00809 (tag : Fin 10000) (htag : tag.val = 809) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 809 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00810 (tag : Fin 10000) (htag : tag.val = 810) (k : Ring12) : tag.val = 810 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00811 (tag : Fin 10000) (htag : tag.val = 811) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 811 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00812 (tag : Fin 10000) (htag : tag.val = 812) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 812 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00813 (tag : Fin 10000) (htag : tag.val = 813) (x : State) (e : Event) (dr : Ring12) : tag.val = 813 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00814 (tag : Fin 10000) (htag : tag.val = 814) (x : State) (e : Event) (dr : Ring12) : tag.val = 814 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00815 (tag : Fin 10000) (htag : tag.val = 815) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 815 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00816 (tag : Fin 10000) (htag : tag.val = 816) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 816 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00817 (tag : Fin 10000) (htag : tag.val = 817) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 817 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00818 (tag : Fin 10000) (htag : tag.val = 818) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 818 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00819 (tag : Fin 10000) (htag : tag.val = 819) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 819 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00820 (tag : Fin 10000) (htag : tag.val = 820) (k : Ring12) : tag.val = 820 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00821 (tag : Fin 10000) (htag : tag.val = 821) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 821 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00822 (tag : Fin 10000) (htag : tag.val = 822) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 822 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00823 (tag : Fin 10000) (htag : tag.val = 823) (x : State) (e : Event) (dr : Ring12) : tag.val = 823 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00824 (tag : Fin 10000) (htag : tag.val = 824) (x : State) (e : Event) (dr : Ring12) : tag.val = 824 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00825 (tag : Fin 10000) (htag : tag.val = 825) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 825 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00826 (tag : Fin 10000) (htag : tag.val = 826) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 826 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00827 (tag : Fin 10000) (htag : tag.val = 827) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 827 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00828 (tag : Fin 10000) (htag : tag.val = 828) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 828 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00829 (tag : Fin 10000) (htag : tag.val = 829) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 829 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00830 (tag : Fin 10000) (htag : tag.val = 830) (k : Ring12) : tag.val = 830 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00831 (tag : Fin 10000) (htag : tag.val = 831) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 831 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00832 (tag : Fin 10000) (htag : tag.val = 832) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 832 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00833 (tag : Fin 10000) (htag : tag.val = 833) (x : State) (e : Event) (dr : Ring12) : tag.val = 833 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00834 (tag : Fin 10000) (htag : tag.val = 834) (x : State) (e : Event) (dr : Ring12) : tag.val = 834 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00835 (tag : Fin 10000) (htag : tag.val = 835) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 835 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00836 (tag : Fin 10000) (htag : tag.val = 836) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 836 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00837 (tag : Fin 10000) (htag : tag.val = 837) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 837 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00838 (tag : Fin 10000) (htag : tag.val = 838) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 838 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00839 (tag : Fin 10000) (htag : tag.val = 839) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 839 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00840 (tag : Fin 10000) (htag : tag.val = 840) (k : Ring12) : tag.val = 840 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00841 (tag : Fin 10000) (htag : tag.val = 841) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 841 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00842 (tag : Fin 10000) (htag : tag.val = 842) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 842 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00843 (tag : Fin 10000) (htag : tag.val = 843) (x : State) (e : Event) (dr : Ring12) : tag.val = 843 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00844 (tag : Fin 10000) (htag : tag.val = 844) (x : State) (e : Event) (dr : Ring12) : tag.val = 844 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00845 (tag : Fin 10000) (htag : tag.val = 845) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 845 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00846 (tag : Fin 10000) (htag : tag.val = 846) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 846 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00847 (tag : Fin 10000) (htag : tag.val = 847) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 847 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00848 (tag : Fin 10000) (htag : tag.val = 848) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 848 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00849 (tag : Fin 10000) (htag : tag.val = 849) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 849 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00850 (tag : Fin 10000) (htag : tag.val = 850) (k : Ring12) : tag.val = 850 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00851 (tag : Fin 10000) (htag : tag.val = 851) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 851 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00852 (tag : Fin 10000) (htag : tag.val = 852) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 852 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00853 (tag : Fin 10000) (htag : tag.val = 853) (x : State) (e : Event) (dr : Ring12) : tag.val = 853 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00854 (tag : Fin 10000) (htag : tag.val = 854) (x : State) (e : Event) (dr : Ring12) : tag.val = 854 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00855 (tag : Fin 10000) (htag : tag.val = 855) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 855 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00856 (tag : Fin 10000) (htag : tag.val = 856) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 856 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00857 (tag : Fin 10000) (htag : tag.val = 857) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 857 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00858 (tag : Fin 10000) (htag : tag.val = 858) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 858 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00859 (tag : Fin 10000) (htag : tag.val = 859) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 859 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00860 (tag : Fin 10000) (htag : tag.val = 860) (k : Ring12) : tag.val = 860 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00861 (tag : Fin 10000) (htag : tag.val = 861) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 861 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00862 (tag : Fin 10000) (htag : tag.val = 862) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 862 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00863 (tag : Fin 10000) (htag : tag.val = 863) (x : State) (e : Event) (dr : Ring12) : tag.val = 863 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00864 (tag : Fin 10000) (htag : tag.val = 864) (x : State) (e : Event) (dr : Ring12) : tag.val = 864 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00865 (tag : Fin 10000) (htag : tag.val = 865) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 865 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00866 (tag : Fin 10000) (htag : tag.val = 866) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 866 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00867 (tag : Fin 10000) (htag : tag.val = 867) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 867 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00868 (tag : Fin 10000) (htag : tag.val = 868) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 868 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00869 (tag : Fin 10000) (htag : tag.val = 869) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 869 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00870 (tag : Fin 10000) (htag : tag.val = 870) (k : Ring12) : tag.val = 870 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00871 (tag : Fin 10000) (htag : tag.val = 871) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 871 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00872 (tag : Fin 10000) (htag : tag.val = 872) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 872 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00873 (tag : Fin 10000) (htag : tag.val = 873) (x : State) (e : Event) (dr : Ring12) : tag.val = 873 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00874 (tag : Fin 10000) (htag : tag.val = 874) (x : State) (e : Event) (dr : Ring12) : tag.val = 874 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00875 (tag : Fin 10000) (htag : tag.val = 875) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 875 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00876 (tag : Fin 10000) (htag : tag.val = 876) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 876 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00877 (tag : Fin 10000) (htag : tag.val = 877) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 877 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00878 (tag : Fin 10000) (htag : tag.val = 878) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 878 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00879 (tag : Fin 10000) (htag : tag.val = 879) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 879 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00880 (tag : Fin 10000) (htag : tag.val = 880) (k : Ring12) : tag.val = 880 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00881 (tag : Fin 10000) (htag : tag.val = 881) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 881 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00882 (tag : Fin 10000) (htag : tag.val = 882) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 882 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00883 (tag : Fin 10000) (htag : tag.val = 883) (x : State) (e : Event) (dr : Ring12) : tag.val = 883 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00884 (tag : Fin 10000) (htag : tag.val = 884) (x : State) (e : Event) (dr : Ring12) : tag.val = 884 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00885 (tag : Fin 10000) (htag : tag.val = 885) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 885 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00886 (tag : Fin 10000) (htag : tag.val = 886) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 886 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00887 (tag : Fin 10000) (htag : tag.val = 887) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 887 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00888 (tag : Fin 10000) (htag : tag.val = 888) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 888 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00889 (tag : Fin 10000) (htag : tag.val = 889) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 889 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_00890 (tag : Fin 10000) (htag : tag.val = 890) (k : Ring12) : tag.val = 890 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_00891 (tag : Fin 10000) (htag : tag.val = 891) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 891 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_00892 (tag : Fin 10000) (htag : tag.val = 892) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 892 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_00893 (tag : Fin 10000) (htag : tag.val = 893) (x : State) (e : Event) (dr : Ring12) : tag.val = 893 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_00894 (tag : Fin 10000) (htag : tag.val = 894) (x : State) (e : Event) (dr : Ring12) : tag.val = 894 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_00895 (tag : Fin 10000) (htag : tag.val = 895) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 895 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_00896 (tag : Fin 10000) (htag : tag.val = 896) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 896 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_00897 (tag : Fin 10000) (htag : tag.val = 897) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 897 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_00898 (tag : Fin 10000) (htag : tag.val = 898) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 898 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_00899 (tag : Fin 10000) (htag : tag.val = 899) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 899 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
