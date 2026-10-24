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
theorem generated_02800 (tag : Fin 10000) (htag : tag.val = 2800) (k : Ring12) : tag.val = 2800 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02801 (tag : Fin 10000) (htag : tag.val = 2801) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2801 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02802 (tag : Fin 10000) (htag : tag.val = 2802) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2802 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02803 (tag : Fin 10000) (htag : tag.val = 2803) (x : State) (e : Event) (dr : Ring12) : tag.val = 2803 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02804 (tag : Fin 10000) (htag : tag.val = 2804) (x : State) (e : Event) (dr : Ring12) : tag.val = 2804 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02805 (tag : Fin 10000) (htag : tag.val = 2805) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2805 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02806 (tag : Fin 10000) (htag : tag.val = 2806) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2806 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02807 (tag : Fin 10000) (htag : tag.val = 2807) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2807 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02808 (tag : Fin 10000) (htag : tag.val = 2808) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2808 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02809 (tag : Fin 10000) (htag : tag.val = 2809) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2809 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02810 (tag : Fin 10000) (htag : tag.val = 2810) (k : Ring12) : tag.val = 2810 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02811 (tag : Fin 10000) (htag : tag.val = 2811) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2811 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02812 (tag : Fin 10000) (htag : tag.val = 2812) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2812 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02813 (tag : Fin 10000) (htag : tag.val = 2813) (x : State) (e : Event) (dr : Ring12) : tag.val = 2813 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02814 (tag : Fin 10000) (htag : tag.val = 2814) (x : State) (e : Event) (dr : Ring12) : tag.val = 2814 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02815 (tag : Fin 10000) (htag : tag.val = 2815) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2815 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02816 (tag : Fin 10000) (htag : tag.val = 2816) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2816 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02817 (tag : Fin 10000) (htag : tag.val = 2817) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2817 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02818 (tag : Fin 10000) (htag : tag.val = 2818) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2818 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02819 (tag : Fin 10000) (htag : tag.val = 2819) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2819 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02820 (tag : Fin 10000) (htag : tag.val = 2820) (k : Ring12) : tag.val = 2820 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02821 (tag : Fin 10000) (htag : tag.val = 2821) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2821 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02822 (tag : Fin 10000) (htag : tag.val = 2822) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2822 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02823 (tag : Fin 10000) (htag : tag.val = 2823) (x : State) (e : Event) (dr : Ring12) : tag.val = 2823 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02824 (tag : Fin 10000) (htag : tag.val = 2824) (x : State) (e : Event) (dr : Ring12) : tag.val = 2824 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02825 (tag : Fin 10000) (htag : tag.val = 2825) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2825 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02826 (tag : Fin 10000) (htag : tag.val = 2826) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2826 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02827 (tag : Fin 10000) (htag : tag.val = 2827) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2827 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02828 (tag : Fin 10000) (htag : tag.val = 2828) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2828 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02829 (tag : Fin 10000) (htag : tag.val = 2829) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2829 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02830 (tag : Fin 10000) (htag : tag.val = 2830) (k : Ring12) : tag.val = 2830 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02831 (tag : Fin 10000) (htag : tag.val = 2831) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2831 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02832 (tag : Fin 10000) (htag : tag.val = 2832) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2832 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02833 (tag : Fin 10000) (htag : tag.val = 2833) (x : State) (e : Event) (dr : Ring12) : tag.val = 2833 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02834 (tag : Fin 10000) (htag : tag.val = 2834) (x : State) (e : Event) (dr : Ring12) : tag.val = 2834 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02835 (tag : Fin 10000) (htag : tag.val = 2835) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2835 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02836 (tag : Fin 10000) (htag : tag.val = 2836) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2836 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02837 (tag : Fin 10000) (htag : tag.val = 2837) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2837 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02838 (tag : Fin 10000) (htag : tag.val = 2838) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2838 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02839 (tag : Fin 10000) (htag : tag.val = 2839) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2839 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02840 (tag : Fin 10000) (htag : tag.val = 2840) (k : Ring12) : tag.val = 2840 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02841 (tag : Fin 10000) (htag : tag.val = 2841) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2841 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02842 (tag : Fin 10000) (htag : tag.val = 2842) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2842 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02843 (tag : Fin 10000) (htag : tag.val = 2843) (x : State) (e : Event) (dr : Ring12) : tag.val = 2843 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02844 (tag : Fin 10000) (htag : tag.val = 2844) (x : State) (e : Event) (dr : Ring12) : tag.val = 2844 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02845 (tag : Fin 10000) (htag : tag.val = 2845) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2845 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02846 (tag : Fin 10000) (htag : tag.val = 2846) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2846 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02847 (tag : Fin 10000) (htag : tag.val = 2847) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2847 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02848 (tag : Fin 10000) (htag : tag.val = 2848) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2848 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02849 (tag : Fin 10000) (htag : tag.val = 2849) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2849 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02850 (tag : Fin 10000) (htag : tag.val = 2850) (k : Ring12) : tag.val = 2850 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02851 (tag : Fin 10000) (htag : tag.val = 2851) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2851 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02852 (tag : Fin 10000) (htag : tag.val = 2852) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2852 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02853 (tag : Fin 10000) (htag : tag.val = 2853) (x : State) (e : Event) (dr : Ring12) : tag.val = 2853 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02854 (tag : Fin 10000) (htag : tag.val = 2854) (x : State) (e : Event) (dr : Ring12) : tag.val = 2854 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02855 (tag : Fin 10000) (htag : tag.val = 2855) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2855 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02856 (tag : Fin 10000) (htag : tag.val = 2856) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2856 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02857 (tag : Fin 10000) (htag : tag.val = 2857) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2857 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02858 (tag : Fin 10000) (htag : tag.val = 2858) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2858 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02859 (tag : Fin 10000) (htag : tag.val = 2859) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2859 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02860 (tag : Fin 10000) (htag : tag.val = 2860) (k : Ring12) : tag.val = 2860 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02861 (tag : Fin 10000) (htag : tag.val = 2861) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2861 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02862 (tag : Fin 10000) (htag : tag.val = 2862) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2862 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02863 (tag : Fin 10000) (htag : tag.val = 2863) (x : State) (e : Event) (dr : Ring12) : tag.val = 2863 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02864 (tag : Fin 10000) (htag : tag.val = 2864) (x : State) (e : Event) (dr : Ring12) : tag.val = 2864 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02865 (tag : Fin 10000) (htag : tag.val = 2865) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2865 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02866 (tag : Fin 10000) (htag : tag.val = 2866) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2866 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02867 (tag : Fin 10000) (htag : tag.val = 2867) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2867 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02868 (tag : Fin 10000) (htag : tag.val = 2868) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2868 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02869 (tag : Fin 10000) (htag : tag.val = 2869) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2869 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02870 (tag : Fin 10000) (htag : tag.val = 2870) (k : Ring12) : tag.val = 2870 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02871 (tag : Fin 10000) (htag : tag.val = 2871) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2871 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02872 (tag : Fin 10000) (htag : tag.val = 2872) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2872 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02873 (tag : Fin 10000) (htag : tag.val = 2873) (x : State) (e : Event) (dr : Ring12) : tag.val = 2873 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02874 (tag : Fin 10000) (htag : tag.val = 2874) (x : State) (e : Event) (dr : Ring12) : tag.val = 2874 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02875 (tag : Fin 10000) (htag : tag.val = 2875) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2875 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02876 (tag : Fin 10000) (htag : tag.val = 2876) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2876 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02877 (tag : Fin 10000) (htag : tag.val = 2877) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2877 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02878 (tag : Fin 10000) (htag : tag.val = 2878) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2878 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02879 (tag : Fin 10000) (htag : tag.val = 2879) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2879 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02880 (tag : Fin 10000) (htag : tag.val = 2880) (k : Ring12) : tag.val = 2880 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02881 (tag : Fin 10000) (htag : tag.val = 2881) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2881 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02882 (tag : Fin 10000) (htag : tag.val = 2882) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2882 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02883 (tag : Fin 10000) (htag : tag.val = 2883) (x : State) (e : Event) (dr : Ring12) : tag.val = 2883 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02884 (tag : Fin 10000) (htag : tag.val = 2884) (x : State) (e : Event) (dr : Ring12) : tag.val = 2884 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02885 (tag : Fin 10000) (htag : tag.val = 2885) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2885 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02886 (tag : Fin 10000) (htag : tag.val = 2886) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2886 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02887 (tag : Fin 10000) (htag : tag.val = 2887) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2887 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02888 (tag : Fin 10000) (htag : tag.val = 2888) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2888 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02889 (tag : Fin 10000) (htag : tag.val = 2889) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2889 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02890 (tag : Fin 10000) (htag : tag.val = 2890) (k : Ring12) : tag.val = 2890 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02891 (tag : Fin 10000) (htag : tag.val = 2891) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2891 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02892 (tag : Fin 10000) (htag : tag.val = 2892) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2892 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02893 (tag : Fin 10000) (htag : tag.val = 2893) (x : State) (e : Event) (dr : Ring12) : tag.val = 2893 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02894 (tag : Fin 10000) (htag : tag.val = 2894) (x : State) (e : Event) (dr : Ring12) : tag.val = 2894 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02895 (tag : Fin 10000) (htag : tag.val = 2895) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2895 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02896 (tag : Fin 10000) (htag : tag.val = 2896) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2896 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02897 (tag : Fin 10000) (htag : tag.val = 2897) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2897 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02898 (tag : Fin 10000) (htag : tag.val = 2898) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2898 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02899 (tag : Fin 10000) (htag : tag.val = 2899) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2899 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
