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
theorem generated_07800 (tag : Fin 10000) (htag : tag.val = 7800) (k : Ring12) : tag.val = 7800 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07801 (tag : Fin 10000) (htag : tag.val = 7801) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7801 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07802 (tag : Fin 10000) (htag : tag.val = 7802) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7802 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07803 (tag : Fin 10000) (htag : tag.val = 7803) (x : State) (e : Event) (dr : Ring12) : tag.val = 7803 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07804 (tag : Fin 10000) (htag : tag.val = 7804) (x : State) (e : Event) (dr : Ring12) : tag.val = 7804 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07805 (tag : Fin 10000) (htag : tag.val = 7805) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7805 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07806 (tag : Fin 10000) (htag : tag.val = 7806) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7806 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07807 (tag : Fin 10000) (htag : tag.val = 7807) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7807 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07808 (tag : Fin 10000) (htag : tag.val = 7808) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7808 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07809 (tag : Fin 10000) (htag : tag.val = 7809) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7809 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07810 (tag : Fin 10000) (htag : tag.val = 7810) (k : Ring12) : tag.val = 7810 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07811 (tag : Fin 10000) (htag : tag.val = 7811) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7811 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07812 (tag : Fin 10000) (htag : tag.val = 7812) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7812 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07813 (tag : Fin 10000) (htag : tag.val = 7813) (x : State) (e : Event) (dr : Ring12) : tag.val = 7813 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07814 (tag : Fin 10000) (htag : tag.val = 7814) (x : State) (e : Event) (dr : Ring12) : tag.val = 7814 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07815 (tag : Fin 10000) (htag : tag.val = 7815) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7815 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07816 (tag : Fin 10000) (htag : tag.val = 7816) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7816 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07817 (tag : Fin 10000) (htag : tag.val = 7817) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7817 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07818 (tag : Fin 10000) (htag : tag.val = 7818) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7818 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07819 (tag : Fin 10000) (htag : tag.val = 7819) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7819 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07820 (tag : Fin 10000) (htag : tag.val = 7820) (k : Ring12) : tag.val = 7820 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07821 (tag : Fin 10000) (htag : tag.val = 7821) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7821 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07822 (tag : Fin 10000) (htag : tag.val = 7822) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7822 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07823 (tag : Fin 10000) (htag : tag.val = 7823) (x : State) (e : Event) (dr : Ring12) : tag.val = 7823 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07824 (tag : Fin 10000) (htag : tag.val = 7824) (x : State) (e : Event) (dr : Ring12) : tag.val = 7824 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07825 (tag : Fin 10000) (htag : tag.val = 7825) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7825 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07826 (tag : Fin 10000) (htag : tag.val = 7826) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7826 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07827 (tag : Fin 10000) (htag : tag.val = 7827) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7827 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07828 (tag : Fin 10000) (htag : tag.val = 7828) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7828 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07829 (tag : Fin 10000) (htag : tag.val = 7829) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7829 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07830 (tag : Fin 10000) (htag : tag.val = 7830) (k : Ring12) : tag.val = 7830 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07831 (tag : Fin 10000) (htag : tag.val = 7831) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7831 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07832 (tag : Fin 10000) (htag : tag.val = 7832) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7832 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07833 (tag : Fin 10000) (htag : tag.val = 7833) (x : State) (e : Event) (dr : Ring12) : tag.val = 7833 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07834 (tag : Fin 10000) (htag : tag.val = 7834) (x : State) (e : Event) (dr : Ring12) : tag.val = 7834 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07835 (tag : Fin 10000) (htag : tag.val = 7835) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7835 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07836 (tag : Fin 10000) (htag : tag.val = 7836) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7836 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07837 (tag : Fin 10000) (htag : tag.val = 7837) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7837 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07838 (tag : Fin 10000) (htag : tag.val = 7838) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7838 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07839 (tag : Fin 10000) (htag : tag.val = 7839) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7839 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07840 (tag : Fin 10000) (htag : tag.val = 7840) (k : Ring12) : tag.val = 7840 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07841 (tag : Fin 10000) (htag : tag.val = 7841) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7841 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07842 (tag : Fin 10000) (htag : tag.val = 7842) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7842 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07843 (tag : Fin 10000) (htag : tag.val = 7843) (x : State) (e : Event) (dr : Ring12) : tag.val = 7843 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07844 (tag : Fin 10000) (htag : tag.val = 7844) (x : State) (e : Event) (dr : Ring12) : tag.val = 7844 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07845 (tag : Fin 10000) (htag : tag.val = 7845) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7845 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07846 (tag : Fin 10000) (htag : tag.val = 7846) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7846 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07847 (tag : Fin 10000) (htag : tag.val = 7847) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7847 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07848 (tag : Fin 10000) (htag : tag.val = 7848) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7848 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07849 (tag : Fin 10000) (htag : tag.val = 7849) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7849 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07850 (tag : Fin 10000) (htag : tag.val = 7850) (k : Ring12) : tag.val = 7850 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07851 (tag : Fin 10000) (htag : tag.val = 7851) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7851 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07852 (tag : Fin 10000) (htag : tag.val = 7852) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7852 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07853 (tag : Fin 10000) (htag : tag.val = 7853) (x : State) (e : Event) (dr : Ring12) : tag.val = 7853 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07854 (tag : Fin 10000) (htag : tag.val = 7854) (x : State) (e : Event) (dr : Ring12) : tag.val = 7854 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07855 (tag : Fin 10000) (htag : tag.val = 7855) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7855 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07856 (tag : Fin 10000) (htag : tag.val = 7856) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7856 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07857 (tag : Fin 10000) (htag : tag.val = 7857) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7857 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07858 (tag : Fin 10000) (htag : tag.val = 7858) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7858 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07859 (tag : Fin 10000) (htag : tag.val = 7859) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7859 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07860 (tag : Fin 10000) (htag : tag.val = 7860) (k : Ring12) : tag.val = 7860 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07861 (tag : Fin 10000) (htag : tag.val = 7861) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7861 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07862 (tag : Fin 10000) (htag : tag.val = 7862) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7862 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07863 (tag : Fin 10000) (htag : tag.val = 7863) (x : State) (e : Event) (dr : Ring12) : tag.val = 7863 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07864 (tag : Fin 10000) (htag : tag.val = 7864) (x : State) (e : Event) (dr : Ring12) : tag.val = 7864 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07865 (tag : Fin 10000) (htag : tag.val = 7865) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7865 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07866 (tag : Fin 10000) (htag : tag.val = 7866) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7866 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07867 (tag : Fin 10000) (htag : tag.val = 7867) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7867 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07868 (tag : Fin 10000) (htag : tag.val = 7868) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7868 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07869 (tag : Fin 10000) (htag : tag.val = 7869) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7869 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07870 (tag : Fin 10000) (htag : tag.val = 7870) (k : Ring12) : tag.val = 7870 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07871 (tag : Fin 10000) (htag : tag.val = 7871) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7871 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07872 (tag : Fin 10000) (htag : tag.val = 7872) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7872 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07873 (tag : Fin 10000) (htag : tag.val = 7873) (x : State) (e : Event) (dr : Ring12) : tag.val = 7873 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07874 (tag : Fin 10000) (htag : tag.val = 7874) (x : State) (e : Event) (dr : Ring12) : tag.val = 7874 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07875 (tag : Fin 10000) (htag : tag.val = 7875) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7875 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07876 (tag : Fin 10000) (htag : tag.val = 7876) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7876 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07877 (tag : Fin 10000) (htag : tag.val = 7877) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7877 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07878 (tag : Fin 10000) (htag : tag.val = 7878) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7878 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07879 (tag : Fin 10000) (htag : tag.val = 7879) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7879 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07880 (tag : Fin 10000) (htag : tag.val = 7880) (k : Ring12) : tag.val = 7880 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07881 (tag : Fin 10000) (htag : tag.val = 7881) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7881 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07882 (tag : Fin 10000) (htag : tag.val = 7882) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7882 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07883 (tag : Fin 10000) (htag : tag.val = 7883) (x : State) (e : Event) (dr : Ring12) : tag.val = 7883 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07884 (tag : Fin 10000) (htag : tag.val = 7884) (x : State) (e : Event) (dr : Ring12) : tag.val = 7884 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07885 (tag : Fin 10000) (htag : tag.val = 7885) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7885 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07886 (tag : Fin 10000) (htag : tag.val = 7886) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7886 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07887 (tag : Fin 10000) (htag : tag.val = 7887) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7887 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07888 (tag : Fin 10000) (htag : tag.val = 7888) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7888 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07889 (tag : Fin 10000) (htag : tag.val = 7889) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7889 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07890 (tag : Fin 10000) (htag : tag.val = 7890) (k : Ring12) : tag.val = 7890 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07891 (tag : Fin 10000) (htag : tag.val = 7891) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7891 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07892 (tag : Fin 10000) (htag : tag.val = 7892) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7892 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07893 (tag : Fin 10000) (htag : tag.val = 7893) (x : State) (e : Event) (dr : Ring12) : tag.val = 7893 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07894 (tag : Fin 10000) (htag : tag.val = 7894) (x : State) (e : Event) (dr : Ring12) : tag.val = 7894 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07895 (tag : Fin 10000) (htag : tag.val = 7895) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7895 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07896 (tag : Fin 10000) (htag : tag.val = 7896) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7896 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07897 (tag : Fin 10000) (htag : tag.val = 7897) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7897 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07898 (tag : Fin 10000) (htag : tag.val = 7898) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7898 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07899 (tag : Fin 10000) (htag : tag.val = 7899) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7899 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
