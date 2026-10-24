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
theorem generated_06800 (tag : Fin 10000) (htag : tag.val = 6800) (k : Ring12) : tag.val = 6800 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06801 (tag : Fin 10000) (htag : tag.val = 6801) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6801 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06802 (tag : Fin 10000) (htag : tag.val = 6802) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6802 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06803 (tag : Fin 10000) (htag : tag.val = 6803) (x : State) (e : Event) (dr : Ring12) : tag.val = 6803 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06804 (tag : Fin 10000) (htag : tag.val = 6804) (x : State) (e : Event) (dr : Ring12) : tag.val = 6804 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06805 (tag : Fin 10000) (htag : tag.val = 6805) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6805 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06806 (tag : Fin 10000) (htag : tag.val = 6806) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6806 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06807 (tag : Fin 10000) (htag : tag.val = 6807) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6807 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06808 (tag : Fin 10000) (htag : tag.val = 6808) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6808 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06809 (tag : Fin 10000) (htag : tag.val = 6809) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6809 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06810 (tag : Fin 10000) (htag : tag.val = 6810) (k : Ring12) : tag.val = 6810 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06811 (tag : Fin 10000) (htag : tag.val = 6811) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6811 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06812 (tag : Fin 10000) (htag : tag.val = 6812) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6812 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06813 (tag : Fin 10000) (htag : tag.val = 6813) (x : State) (e : Event) (dr : Ring12) : tag.val = 6813 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06814 (tag : Fin 10000) (htag : tag.val = 6814) (x : State) (e : Event) (dr : Ring12) : tag.val = 6814 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06815 (tag : Fin 10000) (htag : tag.val = 6815) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6815 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06816 (tag : Fin 10000) (htag : tag.val = 6816) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6816 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06817 (tag : Fin 10000) (htag : tag.val = 6817) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6817 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06818 (tag : Fin 10000) (htag : tag.val = 6818) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6818 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06819 (tag : Fin 10000) (htag : tag.val = 6819) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6819 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06820 (tag : Fin 10000) (htag : tag.val = 6820) (k : Ring12) : tag.val = 6820 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06821 (tag : Fin 10000) (htag : tag.val = 6821) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6821 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06822 (tag : Fin 10000) (htag : tag.val = 6822) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6822 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06823 (tag : Fin 10000) (htag : tag.val = 6823) (x : State) (e : Event) (dr : Ring12) : tag.val = 6823 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06824 (tag : Fin 10000) (htag : tag.val = 6824) (x : State) (e : Event) (dr : Ring12) : tag.val = 6824 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06825 (tag : Fin 10000) (htag : tag.val = 6825) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6825 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06826 (tag : Fin 10000) (htag : tag.val = 6826) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6826 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06827 (tag : Fin 10000) (htag : tag.val = 6827) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6827 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06828 (tag : Fin 10000) (htag : tag.val = 6828) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6828 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06829 (tag : Fin 10000) (htag : tag.val = 6829) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6829 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06830 (tag : Fin 10000) (htag : tag.val = 6830) (k : Ring12) : tag.val = 6830 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06831 (tag : Fin 10000) (htag : tag.val = 6831) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6831 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06832 (tag : Fin 10000) (htag : tag.val = 6832) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6832 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06833 (tag : Fin 10000) (htag : tag.val = 6833) (x : State) (e : Event) (dr : Ring12) : tag.val = 6833 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06834 (tag : Fin 10000) (htag : tag.val = 6834) (x : State) (e : Event) (dr : Ring12) : tag.val = 6834 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06835 (tag : Fin 10000) (htag : tag.val = 6835) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6835 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06836 (tag : Fin 10000) (htag : tag.val = 6836) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6836 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06837 (tag : Fin 10000) (htag : tag.val = 6837) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6837 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06838 (tag : Fin 10000) (htag : tag.val = 6838) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6838 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06839 (tag : Fin 10000) (htag : tag.val = 6839) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6839 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06840 (tag : Fin 10000) (htag : tag.val = 6840) (k : Ring12) : tag.val = 6840 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06841 (tag : Fin 10000) (htag : tag.val = 6841) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6841 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06842 (tag : Fin 10000) (htag : tag.val = 6842) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6842 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06843 (tag : Fin 10000) (htag : tag.val = 6843) (x : State) (e : Event) (dr : Ring12) : tag.val = 6843 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06844 (tag : Fin 10000) (htag : tag.val = 6844) (x : State) (e : Event) (dr : Ring12) : tag.val = 6844 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06845 (tag : Fin 10000) (htag : tag.val = 6845) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6845 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06846 (tag : Fin 10000) (htag : tag.val = 6846) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6846 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06847 (tag : Fin 10000) (htag : tag.val = 6847) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6847 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06848 (tag : Fin 10000) (htag : tag.val = 6848) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6848 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06849 (tag : Fin 10000) (htag : tag.val = 6849) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6849 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06850 (tag : Fin 10000) (htag : tag.val = 6850) (k : Ring12) : tag.val = 6850 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06851 (tag : Fin 10000) (htag : tag.val = 6851) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6851 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06852 (tag : Fin 10000) (htag : tag.val = 6852) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6852 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06853 (tag : Fin 10000) (htag : tag.val = 6853) (x : State) (e : Event) (dr : Ring12) : tag.val = 6853 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06854 (tag : Fin 10000) (htag : tag.val = 6854) (x : State) (e : Event) (dr : Ring12) : tag.val = 6854 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06855 (tag : Fin 10000) (htag : tag.val = 6855) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6855 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06856 (tag : Fin 10000) (htag : tag.val = 6856) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6856 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06857 (tag : Fin 10000) (htag : tag.val = 6857) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6857 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06858 (tag : Fin 10000) (htag : tag.val = 6858) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6858 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06859 (tag : Fin 10000) (htag : tag.val = 6859) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6859 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06860 (tag : Fin 10000) (htag : tag.val = 6860) (k : Ring12) : tag.val = 6860 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06861 (tag : Fin 10000) (htag : tag.val = 6861) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6861 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06862 (tag : Fin 10000) (htag : tag.val = 6862) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6862 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06863 (tag : Fin 10000) (htag : tag.val = 6863) (x : State) (e : Event) (dr : Ring12) : tag.val = 6863 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06864 (tag : Fin 10000) (htag : tag.val = 6864) (x : State) (e : Event) (dr : Ring12) : tag.val = 6864 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06865 (tag : Fin 10000) (htag : tag.val = 6865) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6865 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06866 (tag : Fin 10000) (htag : tag.val = 6866) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6866 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06867 (tag : Fin 10000) (htag : tag.val = 6867) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6867 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06868 (tag : Fin 10000) (htag : tag.val = 6868) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6868 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06869 (tag : Fin 10000) (htag : tag.val = 6869) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6869 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06870 (tag : Fin 10000) (htag : tag.val = 6870) (k : Ring12) : tag.val = 6870 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06871 (tag : Fin 10000) (htag : tag.val = 6871) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6871 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06872 (tag : Fin 10000) (htag : tag.val = 6872) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6872 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06873 (tag : Fin 10000) (htag : tag.val = 6873) (x : State) (e : Event) (dr : Ring12) : tag.val = 6873 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06874 (tag : Fin 10000) (htag : tag.val = 6874) (x : State) (e : Event) (dr : Ring12) : tag.val = 6874 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06875 (tag : Fin 10000) (htag : tag.val = 6875) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6875 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06876 (tag : Fin 10000) (htag : tag.val = 6876) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6876 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06877 (tag : Fin 10000) (htag : tag.val = 6877) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6877 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06878 (tag : Fin 10000) (htag : tag.val = 6878) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6878 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06879 (tag : Fin 10000) (htag : tag.val = 6879) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6879 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06880 (tag : Fin 10000) (htag : tag.val = 6880) (k : Ring12) : tag.val = 6880 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06881 (tag : Fin 10000) (htag : tag.val = 6881) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6881 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06882 (tag : Fin 10000) (htag : tag.val = 6882) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6882 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06883 (tag : Fin 10000) (htag : tag.val = 6883) (x : State) (e : Event) (dr : Ring12) : tag.val = 6883 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06884 (tag : Fin 10000) (htag : tag.val = 6884) (x : State) (e : Event) (dr : Ring12) : tag.val = 6884 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06885 (tag : Fin 10000) (htag : tag.val = 6885) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6885 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06886 (tag : Fin 10000) (htag : tag.val = 6886) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6886 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06887 (tag : Fin 10000) (htag : tag.val = 6887) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6887 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06888 (tag : Fin 10000) (htag : tag.val = 6888) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6888 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06889 (tag : Fin 10000) (htag : tag.val = 6889) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6889 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06890 (tag : Fin 10000) (htag : tag.val = 6890) (k : Ring12) : tag.val = 6890 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06891 (tag : Fin 10000) (htag : tag.val = 6891) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6891 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06892 (tag : Fin 10000) (htag : tag.val = 6892) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6892 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06893 (tag : Fin 10000) (htag : tag.val = 6893) (x : State) (e : Event) (dr : Ring12) : tag.val = 6893 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06894 (tag : Fin 10000) (htag : tag.val = 6894) (x : State) (e : Event) (dr : Ring12) : tag.val = 6894 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06895 (tag : Fin 10000) (htag : tag.val = 6895) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6895 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06896 (tag : Fin 10000) (htag : tag.val = 6896) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6896 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06897 (tag : Fin 10000) (htag : tag.val = 6897) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6897 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06898 (tag : Fin 10000) (htag : tag.val = 6898) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6898 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06899 (tag : Fin 10000) (htag : tag.val = 6899) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6899 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
