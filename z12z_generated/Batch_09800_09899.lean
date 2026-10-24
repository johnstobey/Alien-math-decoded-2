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
theorem generated_09800 (tag : Fin 10000) (htag : tag.val = 9800) (k : Ring12) : tag.val = 9800 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09801 (tag : Fin 10000) (htag : tag.val = 9801) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9801 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09802 (tag : Fin 10000) (htag : tag.val = 9802) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9802 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09803 (tag : Fin 10000) (htag : tag.val = 9803) (x : State) (e : Event) (dr : Ring12) : tag.val = 9803 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09804 (tag : Fin 10000) (htag : tag.val = 9804) (x : State) (e : Event) (dr : Ring12) : tag.val = 9804 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09805 (tag : Fin 10000) (htag : tag.val = 9805) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9805 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09806 (tag : Fin 10000) (htag : tag.val = 9806) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9806 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09807 (tag : Fin 10000) (htag : tag.val = 9807) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9807 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09808 (tag : Fin 10000) (htag : tag.val = 9808) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9808 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09809 (tag : Fin 10000) (htag : tag.val = 9809) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9809 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09810 (tag : Fin 10000) (htag : tag.val = 9810) (k : Ring12) : tag.val = 9810 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09811 (tag : Fin 10000) (htag : tag.val = 9811) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9811 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09812 (tag : Fin 10000) (htag : tag.val = 9812) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9812 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09813 (tag : Fin 10000) (htag : tag.val = 9813) (x : State) (e : Event) (dr : Ring12) : tag.val = 9813 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09814 (tag : Fin 10000) (htag : tag.val = 9814) (x : State) (e : Event) (dr : Ring12) : tag.val = 9814 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09815 (tag : Fin 10000) (htag : tag.val = 9815) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9815 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09816 (tag : Fin 10000) (htag : tag.val = 9816) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9816 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09817 (tag : Fin 10000) (htag : tag.val = 9817) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9817 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09818 (tag : Fin 10000) (htag : tag.val = 9818) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9818 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09819 (tag : Fin 10000) (htag : tag.val = 9819) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9819 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09820 (tag : Fin 10000) (htag : tag.val = 9820) (k : Ring12) : tag.val = 9820 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09821 (tag : Fin 10000) (htag : tag.val = 9821) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9821 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09822 (tag : Fin 10000) (htag : tag.val = 9822) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9822 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09823 (tag : Fin 10000) (htag : tag.val = 9823) (x : State) (e : Event) (dr : Ring12) : tag.val = 9823 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09824 (tag : Fin 10000) (htag : tag.val = 9824) (x : State) (e : Event) (dr : Ring12) : tag.val = 9824 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09825 (tag : Fin 10000) (htag : tag.val = 9825) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9825 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09826 (tag : Fin 10000) (htag : tag.val = 9826) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9826 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09827 (tag : Fin 10000) (htag : tag.val = 9827) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9827 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09828 (tag : Fin 10000) (htag : tag.val = 9828) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9828 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09829 (tag : Fin 10000) (htag : tag.val = 9829) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9829 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09830 (tag : Fin 10000) (htag : tag.val = 9830) (k : Ring12) : tag.val = 9830 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09831 (tag : Fin 10000) (htag : tag.val = 9831) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9831 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09832 (tag : Fin 10000) (htag : tag.val = 9832) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9832 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09833 (tag : Fin 10000) (htag : tag.val = 9833) (x : State) (e : Event) (dr : Ring12) : tag.val = 9833 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09834 (tag : Fin 10000) (htag : tag.val = 9834) (x : State) (e : Event) (dr : Ring12) : tag.val = 9834 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09835 (tag : Fin 10000) (htag : tag.val = 9835) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9835 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09836 (tag : Fin 10000) (htag : tag.val = 9836) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9836 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09837 (tag : Fin 10000) (htag : tag.val = 9837) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9837 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09838 (tag : Fin 10000) (htag : tag.val = 9838) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9838 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09839 (tag : Fin 10000) (htag : tag.val = 9839) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9839 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09840 (tag : Fin 10000) (htag : tag.val = 9840) (k : Ring12) : tag.val = 9840 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09841 (tag : Fin 10000) (htag : tag.val = 9841) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9841 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09842 (tag : Fin 10000) (htag : tag.val = 9842) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9842 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09843 (tag : Fin 10000) (htag : tag.val = 9843) (x : State) (e : Event) (dr : Ring12) : tag.val = 9843 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09844 (tag : Fin 10000) (htag : tag.val = 9844) (x : State) (e : Event) (dr : Ring12) : tag.val = 9844 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09845 (tag : Fin 10000) (htag : tag.val = 9845) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9845 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09846 (tag : Fin 10000) (htag : tag.val = 9846) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9846 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09847 (tag : Fin 10000) (htag : tag.val = 9847) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9847 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09848 (tag : Fin 10000) (htag : tag.val = 9848) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9848 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09849 (tag : Fin 10000) (htag : tag.val = 9849) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9849 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09850 (tag : Fin 10000) (htag : tag.val = 9850) (k : Ring12) : tag.val = 9850 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09851 (tag : Fin 10000) (htag : tag.val = 9851) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9851 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09852 (tag : Fin 10000) (htag : tag.val = 9852) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9852 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09853 (tag : Fin 10000) (htag : tag.val = 9853) (x : State) (e : Event) (dr : Ring12) : tag.val = 9853 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09854 (tag : Fin 10000) (htag : tag.val = 9854) (x : State) (e : Event) (dr : Ring12) : tag.val = 9854 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09855 (tag : Fin 10000) (htag : tag.val = 9855) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9855 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09856 (tag : Fin 10000) (htag : tag.val = 9856) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9856 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09857 (tag : Fin 10000) (htag : tag.val = 9857) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9857 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09858 (tag : Fin 10000) (htag : tag.val = 9858) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9858 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09859 (tag : Fin 10000) (htag : tag.val = 9859) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9859 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09860 (tag : Fin 10000) (htag : tag.val = 9860) (k : Ring12) : tag.val = 9860 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09861 (tag : Fin 10000) (htag : tag.val = 9861) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9861 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09862 (tag : Fin 10000) (htag : tag.val = 9862) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9862 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09863 (tag : Fin 10000) (htag : tag.val = 9863) (x : State) (e : Event) (dr : Ring12) : tag.val = 9863 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09864 (tag : Fin 10000) (htag : tag.val = 9864) (x : State) (e : Event) (dr : Ring12) : tag.val = 9864 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09865 (tag : Fin 10000) (htag : tag.val = 9865) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9865 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09866 (tag : Fin 10000) (htag : tag.val = 9866) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9866 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09867 (tag : Fin 10000) (htag : tag.val = 9867) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9867 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09868 (tag : Fin 10000) (htag : tag.val = 9868) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9868 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09869 (tag : Fin 10000) (htag : tag.val = 9869) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9869 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09870 (tag : Fin 10000) (htag : tag.val = 9870) (k : Ring12) : tag.val = 9870 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09871 (tag : Fin 10000) (htag : tag.val = 9871) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9871 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09872 (tag : Fin 10000) (htag : tag.val = 9872) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9872 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09873 (tag : Fin 10000) (htag : tag.val = 9873) (x : State) (e : Event) (dr : Ring12) : tag.val = 9873 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09874 (tag : Fin 10000) (htag : tag.val = 9874) (x : State) (e : Event) (dr : Ring12) : tag.val = 9874 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09875 (tag : Fin 10000) (htag : tag.val = 9875) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9875 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09876 (tag : Fin 10000) (htag : tag.val = 9876) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9876 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09877 (tag : Fin 10000) (htag : tag.val = 9877) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9877 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09878 (tag : Fin 10000) (htag : tag.val = 9878) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9878 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09879 (tag : Fin 10000) (htag : tag.val = 9879) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9879 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09880 (tag : Fin 10000) (htag : tag.val = 9880) (k : Ring12) : tag.val = 9880 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09881 (tag : Fin 10000) (htag : tag.val = 9881) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9881 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09882 (tag : Fin 10000) (htag : tag.val = 9882) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9882 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09883 (tag : Fin 10000) (htag : tag.val = 9883) (x : State) (e : Event) (dr : Ring12) : tag.val = 9883 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09884 (tag : Fin 10000) (htag : tag.val = 9884) (x : State) (e : Event) (dr : Ring12) : tag.val = 9884 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09885 (tag : Fin 10000) (htag : tag.val = 9885) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9885 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09886 (tag : Fin 10000) (htag : tag.val = 9886) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9886 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09887 (tag : Fin 10000) (htag : tag.val = 9887) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9887 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09888 (tag : Fin 10000) (htag : tag.val = 9888) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9888 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09889 (tag : Fin 10000) (htag : tag.val = 9889) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9889 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09890 (tag : Fin 10000) (htag : tag.val = 9890) (k : Ring12) : tag.val = 9890 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09891 (tag : Fin 10000) (htag : tag.val = 9891) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9891 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09892 (tag : Fin 10000) (htag : tag.val = 9892) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9892 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09893 (tag : Fin 10000) (htag : tag.val = 9893) (x : State) (e : Event) (dr : Ring12) : tag.val = 9893 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09894 (tag : Fin 10000) (htag : tag.val = 9894) (x : State) (e : Event) (dr : Ring12) : tag.val = 9894 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09895 (tag : Fin 10000) (htag : tag.val = 9895) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9895 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09896 (tag : Fin 10000) (htag : tag.val = 9896) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9896 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09897 (tag : Fin 10000) (htag : tag.val = 9897) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9897 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09898 (tag : Fin 10000) (htag : tag.val = 9898) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9898 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09899 (tag : Fin 10000) (htag : tag.val = 9899) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9899 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
