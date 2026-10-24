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
theorem generated_05800 (tag : Fin 10000) (htag : tag.val = 5800) (k : Ring12) : tag.val = 5800 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05801 (tag : Fin 10000) (htag : tag.val = 5801) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5801 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05802 (tag : Fin 10000) (htag : tag.val = 5802) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5802 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05803 (tag : Fin 10000) (htag : tag.val = 5803) (x : State) (e : Event) (dr : Ring12) : tag.val = 5803 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05804 (tag : Fin 10000) (htag : tag.val = 5804) (x : State) (e : Event) (dr : Ring12) : tag.val = 5804 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05805 (tag : Fin 10000) (htag : tag.val = 5805) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5805 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05806 (tag : Fin 10000) (htag : tag.val = 5806) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5806 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05807 (tag : Fin 10000) (htag : tag.val = 5807) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5807 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05808 (tag : Fin 10000) (htag : tag.val = 5808) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5808 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05809 (tag : Fin 10000) (htag : tag.val = 5809) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5809 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05810 (tag : Fin 10000) (htag : tag.val = 5810) (k : Ring12) : tag.val = 5810 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05811 (tag : Fin 10000) (htag : tag.val = 5811) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5811 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05812 (tag : Fin 10000) (htag : tag.val = 5812) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5812 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05813 (tag : Fin 10000) (htag : tag.val = 5813) (x : State) (e : Event) (dr : Ring12) : tag.val = 5813 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05814 (tag : Fin 10000) (htag : tag.val = 5814) (x : State) (e : Event) (dr : Ring12) : tag.val = 5814 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05815 (tag : Fin 10000) (htag : tag.val = 5815) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5815 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05816 (tag : Fin 10000) (htag : tag.val = 5816) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5816 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05817 (tag : Fin 10000) (htag : tag.val = 5817) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5817 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05818 (tag : Fin 10000) (htag : tag.val = 5818) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5818 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05819 (tag : Fin 10000) (htag : tag.val = 5819) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5819 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05820 (tag : Fin 10000) (htag : tag.val = 5820) (k : Ring12) : tag.val = 5820 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05821 (tag : Fin 10000) (htag : tag.val = 5821) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5821 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05822 (tag : Fin 10000) (htag : tag.val = 5822) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5822 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05823 (tag : Fin 10000) (htag : tag.val = 5823) (x : State) (e : Event) (dr : Ring12) : tag.val = 5823 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05824 (tag : Fin 10000) (htag : tag.val = 5824) (x : State) (e : Event) (dr : Ring12) : tag.val = 5824 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05825 (tag : Fin 10000) (htag : tag.val = 5825) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5825 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05826 (tag : Fin 10000) (htag : tag.val = 5826) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5826 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05827 (tag : Fin 10000) (htag : tag.val = 5827) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5827 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05828 (tag : Fin 10000) (htag : tag.val = 5828) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5828 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05829 (tag : Fin 10000) (htag : tag.val = 5829) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5829 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05830 (tag : Fin 10000) (htag : tag.val = 5830) (k : Ring12) : tag.val = 5830 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05831 (tag : Fin 10000) (htag : tag.val = 5831) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5831 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05832 (tag : Fin 10000) (htag : tag.val = 5832) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5832 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05833 (tag : Fin 10000) (htag : tag.val = 5833) (x : State) (e : Event) (dr : Ring12) : tag.val = 5833 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05834 (tag : Fin 10000) (htag : tag.val = 5834) (x : State) (e : Event) (dr : Ring12) : tag.val = 5834 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05835 (tag : Fin 10000) (htag : tag.val = 5835) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5835 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05836 (tag : Fin 10000) (htag : tag.val = 5836) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5836 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05837 (tag : Fin 10000) (htag : tag.val = 5837) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5837 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05838 (tag : Fin 10000) (htag : tag.val = 5838) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5838 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05839 (tag : Fin 10000) (htag : tag.val = 5839) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5839 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05840 (tag : Fin 10000) (htag : tag.val = 5840) (k : Ring12) : tag.val = 5840 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05841 (tag : Fin 10000) (htag : tag.val = 5841) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5841 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05842 (tag : Fin 10000) (htag : tag.val = 5842) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5842 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05843 (tag : Fin 10000) (htag : tag.val = 5843) (x : State) (e : Event) (dr : Ring12) : tag.val = 5843 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05844 (tag : Fin 10000) (htag : tag.val = 5844) (x : State) (e : Event) (dr : Ring12) : tag.val = 5844 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05845 (tag : Fin 10000) (htag : tag.val = 5845) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5845 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05846 (tag : Fin 10000) (htag : tag.val = 5846) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5846 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05847 (tag : Fin 10000) (htag : tag.val = 5847) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5847 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05848 (tag : Fin 10000) (htag : tag.val = 5848) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5848 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05849 (tag : Fin 10000) (htag : tag.val = 5849) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5849 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05850 (tag : Fin 10000) (htag : tag.val = 5850) (k : Ring12) : tag.val = 5850 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05851 (tag : Fin 10000) (htag : tag.val = 5851) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5851 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05852 (tag : Fin 10000) (htag : tag.val = 5852) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5852 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05853 (tag : Fin 10000) (htag : tag.val = 5853) (x : State) (e : Event) (dr : Ring12) : tag.val = 5853 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05854 (tag : Fin 10000) (htag : tag.val = 5854) (x : State) (e : Event) (dr : Ring12) : tag.val = 5854 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05855 (tag : Fin 10000) (htag : tag.val = 5855) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5855 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05856 (tag : Fin 10000) (htag : tag.val = 5856) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5856 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05857 (tag : Fin 10000) (htag : tag.val = 5857) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5857 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05858 (tag : Fin 10000) (htag : tag.val = 5858) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5858 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05859 (tag : Fin 10000) (htag : tag.val = 5859) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5859 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05860 (tag : Fin 10000) (htag : tag.val = 5860) (k : Ring12) : tag.val = 5860 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05861 (tag : Fin 10000) (htag : tag.val = 5861) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5861 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05862 (tag : Fin 10000) (htag : tag.val = 5862) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5862 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05863 (tag : Fin 10000) (htag : tag.val = 5863) (x : State) (e : Event) (dr : Ring12) : tag.val = 5863 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05864 (tag : Fin 10000) (htag : tag.val = 5864) (x : State) (e : Event) (dr : Ring12) : tag.val = 5864 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05865 (tag : Fin 10000) (htag : tag.val = 5865) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5865 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05866 (tag : Fin 10000) (htag : tag.val = 5866) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5866 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05867 (tag : Fin 10000) (htag : tag.val = 5867) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5867 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05868 (tag : Fin 10000) (htag : tag.val = 5868) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5868 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05869 (tag : Fin 10000) (htag : tag.val = 5869) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5869 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05870 (tag : Fin 10000) (htag : tag.val = 5870) (k : Ring12) : tag.val = 5870 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05871 (tag : Fin 10000) (htag : tag.val = 5871) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5871 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05872 (tag : Fin 10000) (htag : tag.val = 5872) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5872 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05873 (tag : Fin 10000) (htag : tag.val = 5873) (x : State) (e : Event) (dr : Ring12) : tag.val = 5873 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05874 (tag : Fin 10000) (htag : tag.val = 5874) (x : State) (e : Event) (dr : Ring12) : tag.val = 5874 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05875 (tag : Fin 10000) (htag : tag.val = 5875) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5875 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05876 (tag : Fin 10000) (htag : tag.val = 5876) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5876 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05877 (tag : Fin 10000) (htag : tag.val = 5877) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5877 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05878 (tag : Fin 10000) (htag : tag.val = 5878) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5878 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05879 (tag : Fin 10000) (htag : tag.val = 5879) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5879 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05880 (tag : Fin 10000) (htag : tag.val = 5880) (k : Ring12) : tag.val = 5880 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05881 (tag : Fin 10000) (htag : tag.val = 5881) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5881 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05882 (tag : Fin 10000) (htag : tag.val = 5882) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5882 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05883 (tag : Fin 10000) (htag : tag.val = 5883) (x : State) (e : Event) (dr : Ring12) : tag.val = 5883 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05884 (tag : Fin 10000) (htag : tag.val = 5884) (x : State) (e : Event) (dr : Ring12) : tag.val = 5884 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05885 (tag : Fin 10000) (htag : tag.val = 5885) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5885 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05886 (tag : Fin 10000) (htag : tag.val = 5886) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5886 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05887 (tag : Fin 10000) (htag : tag.val = 5887) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5887 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05888 (tag : Fin 10000) (htag : tag.val = 5888) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5888 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05889 (tag : Fin 10000) (htag : tag.val = 5889) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5889 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05890 (tag : Fin 10000) (htag : tag.val = 5890) (k : Ring12) : tag.val = 5890 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05891 (tag : Fin 10000) (htag : tag.val = 5891) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5891 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05892 (tag : Fin 10000) (htag : tag.val = 5892) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5892 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05893 (tag : Fin 10000) (htag : tag.val = 5893) (x : State) (e : Event) (dr : Ring12) : tag.val = 5893 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05894 (tag : Fin 10000) (htag : tag.val = 5894) (x : State) (e : Event) (dr : Ring12) : tag.val = 5894 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05895 (tag : Fin 10000) (htag : tag.val = 5895) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5895 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05896 (tag : Fin 10000) (htag : tag.val = 5896) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5896 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05897 (tag : Fin 10000) (htag : tag.val = 5897) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5897 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05898 (tag : Fin 10000) (htag : tag.val = 5898) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5898 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05899 (tag : Fin 10000) (htag : tag.val = 5899) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5899 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
