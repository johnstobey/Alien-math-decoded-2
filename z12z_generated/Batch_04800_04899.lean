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
theorem generated_04800 (tag : Fin 10000) (htag : tag.val = 4800) (k : Ring12) : tag.val = 4800 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04801 (tag : Fin 10000) (htag : tag.val = 4801) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4801 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04802 (tag : Fin 10000) (htag : tag.val = 4802) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4802 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04803 (tag : Fin 10000) (htag : tag.val = 4803) (x : State) (e : Event) (dr : Ring12) : tag.val = 4803 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04804 (tag : Fin 10000) (htag : tag.val = 4804) (x : State) (e : Event) (dr : Ring12) : tag.val = 4804 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04805 (tag : Fin 10000) (htag : tag.val = 4805) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4805 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04806 (tag : Fin 10000) (htag : tag.val = 4806) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4806 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04807 (tag : Fin 10000) (htag : tag.val = 4807) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4807 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04808 (tag : Fin 10000) (htag : tag.val = 4808) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4808 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04809 (tag : Fin 10000) (htag : tag.val = 4809) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4809 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04810 (tag : Fin 10000) (htag : tag.val = 4810) (k : Ring12) : tag.val = 4810 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04811 (tag : Fin 10000) (htag : tag.val = 4811) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4811 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04812 (tag : Fin 10000) (htag : tag.val = 4812) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4812 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04813 (tag : Fin 10000) (htag : tag.val = 4813) (x : State) (e : Event) (dr : Ring12) : tag.val = 4813 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04814 (tag : Fin 10000) (htag : tag.val = 4814) (x : State) (e : Event) (dr : Ring12) : tag.val = 4814 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04815 (tag : Fin 10000) (htag : tag.val = 4815) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4815 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04816 (tag : Fin 10000) (htag : tag.val = 4816) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4816 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04817 (tag : Fin 10000) (htag : tag.val = 4817) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4817 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04818 (tag : Fin 10000) (htag : tag.val = 4818) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4818 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04819 (tag : Fin 10000) (htag : tag.val = 4819) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4819 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04820 (tag : Fin 10000) (htag : tag.val = 4820) (k : Ring12) : tag.val = 4820 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04821 (tag : Fin 10000) (htag : tag.val = 4821) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4821 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04822 (tag : Fin 10000) (htag : tag.val = 4822) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4822 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04823 (tag : Fin 10000) (htag : tag.val = 4823) (x : State) (e : Event) (dr : Ring12) : tag.val = 4823 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04824 (tag : Fin 10000) (htag : tag.val = 4824) (x : State) (e : Event) (dr : Ring12) : tag.val = 4824 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04825 (tag : Fin 10000) (htag : tag.val = 4825) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4825 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04826 (tag : Fin 10000) (htag : tag.val = 4826) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4826 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04827 (tag : Fin 10000) (htag : tag.val = 4827) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4827 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04828 (tag : Fin 10000) (htag : tag.val = 4828) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4828 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04829 (tag : Fin 10000) (htag : tag.val = 4829) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4829 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04830 (tag : Fin 10000) (htag : tag.val = 4830) (k : Ring12) : tag.val = 4830 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04831 (tag : Fin 10000) (htag : tag.val = 4831) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4831 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04832 (tag : Fin 10000) (htag : tag.val = 4832) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4832 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04833 (tag : Fin 10000) (htag : tag.val = 4833) (x : State) (e : Event) (dr : Ring12) : tag.val = 4833 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04834 (tag : Fin 10000) (htag : tag.val = 4834) (x : State) (e : Event) (dr : Ring12) : tag.val = 4834 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04835 (tag : Fin 10000) (htag : tag.val = 4835) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4835 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04836 (tag : Fin 10000) (htag : tag.val = 4836) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4836 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04837 (tag : Fin 10000) (htag : tag.val = 4837) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4837 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04838 (tag : Fin 10000) (htag : tag.val = 4838) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4838 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04839 (tag : Fin 10000) (htag : tag.val = 4839) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4839 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04840 (tag : Fin 10000) (htag : tag.val = 4840) (k : Ring12) : tag.val = 4840 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04841 (tag : Fin 10000) (htag : tag.val = 4841) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4841 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04842 (tag : Fin 10000) (htag : tag.val = 4842) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4842 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04843 (tag : Fin 10000) (htag : tag.val = 4843) (x : State) (e : Event) (dr : Ring12) : tag.val = 4843 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04844 (tag : Fin 10000) (htag : tag.val = 4844) (x : State) (e : Event) (dr : Ring12) : tag.val = 4844 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04845 (tag : Fin 10000) (htag : tag.val = 4845) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4845 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04846 (tag : Fin 10000) (htag : tag.val = 4846) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4846 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04847 (tag : Fin 10000) (htag : tag.val = 4847) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4847 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04848 (tag : Fin 10000) (htag : tag.val = 4848) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4848 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04849 (tag : Fin 10000) (htag : tag.val = 4849) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4849 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04850 (tag : Fin 10000) (htag : tag.val = 4850) (k : Ring12) : tag.val = 4850 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04851 (tag : Fin 10000) (htag : tag.val = 4851) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4851 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04852 (tag : Fin 10000) (htag : tag.val = 4852) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4852 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04853 (tag : Fin 10000) (htag : tag.val = 4853) (x : State) (e : Event) (dr : Ring12) : tag.val = 4853 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04854 (tag : Fin 10000) (htag : tag.val = 4854) (x : State) (e : Event) (dr : Ring12) : tag.val = 4854 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04855 (tag : Fin 10000) (htag : tag.val = 4855) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4855 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04856 (tag : Fin 10000) (htag : tag.val = 4856) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4856 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04857 (tag : Fin 10000) (htag : tag.val = 4857) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4857 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04858 (tag : Fin 10000) (htag : tag.val = 4858) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4858 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04859 (tag : Fin 10000) (htag : tag.val = 4859) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4859 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04860 (tag : Fin 10000) (htag : tag.val = 4860) (k : Ring12) : tag.val = 4860 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04861 (tag : Fin 10000) (htag : tag.val = 4861) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4861 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04862 (tag : Fin 10000) (htag : tag.val = 4862) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4862 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04863 (tag : Fin 10000) (htag : tag.val = 4863) (x : State) (e : Event) (dr : Ring12) : tag.val = 4863 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04864 (tag : Fin 10000) (htag : tag.val = 4864) (x : State) (e : Event) (dr : Ring12) : tag.val = 4864 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04865 (tag : Fin 10000) (htag : tag.val = 4865) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4865 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04866 (tag : Fin 10000) (htag : tag.val = 4866) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4866 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04867 (tag : Fin 10000) (htag : tag.val = 4867) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4867 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04868 (tag : Fin 10000) (htag : tag.val = 4868) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4868 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04869 (tag : Fin 10000) (htag : tag.val = 4869) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4869 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04870 (tag : Fin 10000) (htag : tag.val = 4870) (k : Ring12) : tag.val = 4870 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04871 (tag : Fin 10000) (htag : tag.val = 4871) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4871 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04872 (tag : Fin 10000) (htag : tag.val = 4872) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4872 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04873 (tag : Fin 10000) (htag : tag.val = 4873) (x : State) (e : Event) (dr : Ring12) : tag.val = 4873 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04874 (tag : Fin 10000) (htag : tag.val = 4874) (x : State) (e : Event) (dr : Ring12) : tag.val = 4874 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04875 (tag : Fin 10000) (htag : tag.val = 4875) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4875 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04876 (tag : Fin 10000) (htag : tag.val = 4876) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4876 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04877 (tag : Fin 10000) (htag : tag.val = 4877) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4877 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04878 (tag : Fin 10000) (htag : tag.val = 4878) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4878 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04879 (tag : Fin 10000) (htag : tag.val = 4879) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4879 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04880 (tag : Fin 10000) (htag : tag.val = 4880) (k : Ring12) : tag.val = 4880 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04881 (tag : Fin 10000) (htag : tag.val = 4881) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4881 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04882 (tag : Fin 10000) (htag : tag.val = 4882) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4882 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04883 (tag : Fin 10000) (htag : tag.val = 4883) (x : State) (e : Event) (dr : Ring12) : tag.val = 4883 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04884 (tag : Fin 10000) (htag : tag.val = 4884) (x : State) (e : Event) (dr : Ring12) : tag.val = 4884 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04885 (tag : Fin 10000) (htag : tag.val = 4885) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4885 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04886 (tag : Fin 10000) (htag : tag.val = 4886) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4886 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04887 (tag : Fin 10000) (htag : tag.val = 4887) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4887 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04888 (tag : Fin 10000) (htag : tag.val = 4888) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4888 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04889 (tag : Fin 10000) (htag : tag.val = 4889) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4889 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04890 (tag : Fin 10000) (htag : tag.val = 4890) (k : Ring12) : tag.val = 4890 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04891 (tag : Fin 10000) (htag : tag.val = 4891) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4891 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04892 (tag : Fin 10000) (htag : tag.val = 4892) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4892 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04893 (tag : Fin 10000) (htag : tag.val = 4893) (x : State) (e : Event) (dr : Ring12) : tag.val = 4893 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04894 (tag : Fin 10000) (htag : tag.val = 4894) (x : State) (e : Event) (dr : Ring12) : tag.val = 4894 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04895 (tag : Fin 10000) (htag : tag.val = 4895) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4895 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04896 (tag : Fin 10000) (htag : tag.val = 4896) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4896 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04897 (tag : Fin 10000) (htag : tag.val = 4897) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4897 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04898 (tag : Fin 10000) (htag : tag.val = 4898) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4898 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04899 (tag : Fin 10000) (htag : tag.val = 4899) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4899 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
