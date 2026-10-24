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
theorem generated_08800 (tag : Fin 10000) (htag : tag.val = 8800) (k : Ring12) : tag.val = 8800 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08801 (tag : Fin 10000) (htag : tag.val = 8801) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8801 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08802 (tag : Fin 10000) (htag : tag.val = 8802) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8802 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08803 (tag : Fin 10000) (htag : tag.val = 8803) (x : State) (e : Event) (dr : Ring12) : tag.val = 8803 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08804 (tag : Fin 10000) (htag : tag.val = 8804) (x : State) (e : Event) (dr : Ring12) : tag.val = 8804 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08805 (tag : Fin 10000) (htag : tag.val = 8805) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8805 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08806 (tag : Fin 10000) (htag : tag.val = 8806) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8806 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08807 (tag : Fin 10000) (htag : tag.val = 8807) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8807 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08808 (tag : Fin 10000) (htag : tag.val = 8808) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8808 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08809 (tag : Fin 10000) (htag : tag.val = 8809) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8809 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08810 (tag : Fin 10000) (htag : tag.val = 8810) (k : Ring12) : tag.val = 8810 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08811 (tag : Fin 10000) (htag : tag.val = 8811) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8811 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08812 (tag : Fin 10000) (htag : tag.val = 8812) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8812 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08813 (tag : Fin 10000) (htag : tag.val = 8813) (x : State) (e : Event) (dr : Ring12) : tag.val = 8813 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08814 (tag : Fin 10000) (htag : tag.val = 8814) (x : State) (e : Event) (dr : Ring12) : tag.val = 8814 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08815 (tag : Fin 10000) (htag : tag.val = 8815) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8815 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08816 (tag : Fin 10000) (htag : tag.val = 8816) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8816 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08817 (tag : Fin 10000) (htag : tag.val = 8817) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8817 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08818 (tag : Fin 10000) (htag : tag.val = 8818) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8818 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08819 (tag : Fin 10000) (htag : tag.val = 8819) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8819 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08820 (tag : Fin 10000) (htag : tag.val = 8820) (k : Ring12) : tag.val = 8820 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08821 (tag : Fin 10000) (htag : tag.val = 8821) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8821 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08822 (tag : Fin 10000) (htag : tag.val = 8822) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8822 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08823 (tag : Fin 10000) (htag : tag.val = 8823) (x : State) (e : Event) (dr : Ring12) : tag.val = 8823 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08824 (tag : Fin 10000) (htag : tag.val = 8824) (x : State) (e : Event) (dr : Ring12) : tag.val = 8824 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08825 (tag : Fin 10000) (htag : tag.val = 8825) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8825 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08826 (tag : Fin 10000) (htag : tag.val = 8826) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8826 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08827 (tag : Fin 10000) (htag : tag.val = 8827) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8827 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08828 (tag : Fin 10000) (htag : tag.val = 8828) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8828 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08829 (tag : Fin 10000) (htag : tag.val = 8829) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8829 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08830 (tag : Fin 10000) (htag : tag.val = 8830) (k : Ring12) : tag.val = 8830 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08831 (tag : Fin 10000) (htag : tag.val = 8831) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8831 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08832 (tag : Fin 10000) (htag : tag.val = 8832) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8832 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08833 (tag : Fin 10000) (htag : tag.val = 8833) (x : State) (e : Event) (dr : Ring12) : tag.val = 8833 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08834 (tag : Fin 10000) (htag : tag.val = 8834) (x : State) (e : Event) (dr : Ring12) : tag.val = 8834 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08835 (tag : Fin 10000) (htag : tag.val = 8835) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8835 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08836 (tag : Fin 10000) (htag : tag.val = 8836) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8836 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08837 (tag : Fin 10000) (htag : tag.val = 8837) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8837 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08838 (tag : Fin 10000) (htag : tag.val = 8838) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8838 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08839 (tag : Fin 10000) (htag : tag.val = 8839) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8839 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08840 (tag : Fin 10000) (htag : tag.val = 8840) (k : Ring12) : tag.val = 8840 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08841 (tag : Fin 10000) (htag : tag.val = 8841) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8841 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08842 (tag : Fin 10000) (htag : tag.val = 8842) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8842 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08843 (tag : Fin 10000) (htag : tag.val = 8843) (x : State) (e : Event) (dr : Ring12) : tag.val = 8843 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08844 (tag : Fin 10000) (htag : tag.val = 8844) (x : State) (e : Event) (dr : Ring12) : tag.val = 8844 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08845 (tag : Fin 10000) (htag : tag.val = 8845) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8845 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08846 (tag : Fin 10000) (htag : tag.val = 8846) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8846 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08847 (tag : Fin 10000) (htag : tag.val = 8847) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8847 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08848 (tag : Fin 10000) (htag : tag.val = 8848) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8848 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08849 (tag : Fin 10000) (htag : tag.val = 8849) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8849 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08850 (tag : Fin 10000) (htag : tag.val = 8850) (k : Ring12) : tag.val = 8850 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08851 (tag : Fin 10000) (htag : tag.val = 8851) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8851 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08852 (tag : Fin 10000) (htag : tag.val = 8852) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8852 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08853 (tag : Fin 10000) (htag : tag.val = 8853) (x : State) (e : Event) (dr : Ring12) : tag.val = 8853 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08854 (tag : Fin 10000) (htag : tag.val = 8854) (x : State) (e : Event) (dr : Ring12) : tag.val = 8854 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08855 (tag : Fin 10000) (htag : tag.val = 8855) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8855 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08856 (tag : Fin 10000) (htag : tag.val = 8856) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8856 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08857 (tag : Fin 10000) (htag : tag.val = 8857) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8857 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08858 (tag : Fin 10000) (htag : tag.val = 8858) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8858 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08859 (tag : Fin 10000) (htag : tag.val = 8859) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8859 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08860 (tag : Fin 10000) (htag : tag.val = 8860) (k : Ring12) : tag.val = 8860 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08861 (tag : Fin 10000) (htag : tag.val = 8861) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8861 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08862 (tag : Fin 10000) (htag : tag.val = 8862) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8862 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08863 (tag : Fin 10000) (htag : tag.val = 8863) (x : State) (e : Event) (dr : Ring12) : tag.val = 8863 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08864 (tag : Fin 10000) (htag : tag.val = 8864) (x : State) (e : Event) (dr : Ring12) : tag.val = 8864 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08865 (tag : Fin 10000) (htag : tag.val = 8865) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8865 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08866 (tag : Fin 10000) (htag : tag.val = 8866) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8866 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08867 (tag : Fin 10000) (htag : tag.val = 8867) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8867 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08868 (tag : Fin 10000) (htag : tag.val = 8868) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8868 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08869 (tag : Fin 10000) (htag : tag.val = 8869) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8869 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08870 (tag : Fin 10000) (htag : tag.val = 8870) (k : Ring12) : tag.val = 8870 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08871 (tag : Fin 10000) (htag : tag.val = 8871) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8871 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08872 (tag : Fin 10000) (htag : tag.val = 8872) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8872 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08873 (tag : Fin 10000) (htag : tag.val = 8873) (x : State) (e : Event) (dr : Ring12) : tag.val = 8873 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08874 (tag : Fin 10000) (htag : tag.val = 8874) (x : State) (e : Event) (dr : Ring12) : tag.val = 8874 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08875 (tag : Fin 10000) (htag : tag.val = 8875) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8875 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08876 (tag : Fin 10000) (htag : tag.val = 8876) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8876 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08877 (tag : Fin 10000) (htag : tag.val = 8877) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8877 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08878 (tag : Fin 10000) (htag : tag.val = 8878) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8878 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08879 (tag : Fin 10000) (htag : tag.val = 8879) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8879 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08880 (tag : Fin 10000) (htag : tag.val = 8880) (k : Ring12) : tag.val = 8880 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08881 (tag : Fin 10000) (htag : tag.val = 8881) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8881 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08882 (tag : Fin 10000) (htag : tag.val = 8882) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8882 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08883 (tag : Fin 10000) (htag : tag.val = 8883) (x : State) (e : Event) (dr : Ring12) : tag.val = 8883 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08884 (tag : Fin 10000) (htag : tag.val = 8884) (x : State) (e : Event) (dr : Ring12) : tag.val = 8884 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08885 (tag : Fin 10000) (htag : tag.val = 8885) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8885 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08886 (tag : Fin 10000) (htag : tag.val = 8886) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8886 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08887 (tag : Fin 10000) (htag : tag.val = 8887) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8887 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08888 (tag : Fin 10000) (htag : tag.val = 8888) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8888 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08889 (tag : Fin 10000) (htag : tag.val = 8889) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8889 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08890 (tag : Fin 10000) (htag : tag.val = 8890) (k : Ring12) : tag.val = 8890 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08891 (tag : Fin 10000) (htag : tag.val = 8891) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8891 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08892 (tag : Fin 10000) (htag : tag.val = 8892) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8892 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08893 (tag : Fin 10000) (htag : tag.val = 8893) (x : State) (e : Event) (dr : Ring12) : tag.val = 8893 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08894 (tag : Fin 10000) (htag : tag.val = 8894) (x : State) (e : Event) (dr : Ring12) : tag.val = 8894 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08895 (tag : Fin 10000) (htag : tag.val = 8895) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8895 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08896 (tag : Fin 10000) (htag : tag.val = 8896) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8896 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08897 (tag : Fin 10000) (htag : tag.val = 8897) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8897 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08898 (tag : Fin 10000) (htag : tag.val = 8898) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8898 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08899 (tag : Fin 10000) (htag : tag.val = 8899) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8899 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
