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
theorem generated_01800 (tag : Fin 10000) (htag : tag.val = 1800) (k : Ring12) : tag.val = 1800 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01801 (tag : Fin 10000) (htag : tag.val = 1801) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1801 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01802 (tag : Fin 10000) (htag : tag.val = 1802) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1802 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01803 (tag : Fin 10000) (htag : tag.val = 1803) (x : State) (e : Event) (dr : Ring12) : tag.val = 1803 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01804 (tag : Fin 10000) (htag : tag.val = 1804) (x : State) (e : Event) (dr : Ring12) : tag.val = 1804 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01805 (tag : Fin 10000) (htag : tag.val = 1805) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1805 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01806 (tag : Fin 10000) (htag : tag.val = 1806) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1806 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01807 (tag : Fin 10000) (htag : tag.val = 1807) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1807 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01808 (tag : Fin 10000) (htag : tag.val = 1808) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1808 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01809 (tag : Fin 10000) (htag : tag.val = 1809) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1809 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01810 (tag : Fin 10000) (htag : tag.val = 1810) (k : Ring12) : tag.val = 1810 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01811 (tag : Fin 10000) (htag : tag.val = 1811) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1811 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01812 (tag : Fin 10000) (htag : tag.val = 1812) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1812 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01813 (tag : Fin 10000) (htag : tag.val = 1813) (x : State) (e : Event) (dr : Ring12) : tag.val = 1813 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01814 (tag : Fin 10000) (htag : tag.val = 1814) (x : State) (e : Event) (dr : Ring12) : tag.val = 1814 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01815 (tag : Fin 10000) (htag : tag.val = 1815) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1815 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01816 (tag : Fin 10000) (htag : tag.val = 1816) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1816 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01817 (tag : Fin 10000) (htag : tag.val = 1817) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1817 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01818 (tag : Fin 10000) (htag : tag.val = 1818) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1818 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01819 (tag : Fin 10000) (htag : tag.val = 1819) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1819 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01820 (tag : Fin 10000) (htag : tag.val = 1820) (k : Ring12) : tag.val = 1820 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01821 (tag : Fin 10000) (htag : tag.val = 1821) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1821 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01822 (tag : Fin 10000) (htag : tag.val = 1822) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1822 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01823 (tag : Fin 10000) (htag : tag.val = 1823) (x : State) (e : Event) (dr : Ring12) : tag.val = 1823 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01824 (tag : Fin 10000) (htag : tag.val = 1824) (x : State) (e : Event) (dr : Ring12) : tag.val = 1824 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01825 (tag : Fin 10000) (htag : tag.val = 1825) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1825 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01826 (tag : Fin 10000) (htag : tag.val = 1826) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1826 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01827 (tag : Fin 10000) (htag : tag.val = 1827) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1827 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01828 (tag : Fin 10000) (htag : tag.val = 1828) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1828 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01829 (tag : Fin 10000) (htag : tag.val = 1829) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1829 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01830 (tag : Fin 10000) (htag : tag.val = 1830) (k : Ring12) : tag.val = 1830 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01831 (tag : Fin 10000) (htag : tag.val = 1831) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1831 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01832 (tag : Fin 10000) (htag : tag.val = 1832) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1832 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01833 (tag : Fin 10000) (htag : tag.val = 1833) (x : State) (e : Event) (dr : Ring12) : tag.val = 1833 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01834 (tag : Fin 10000) (htag : tag.val = 1834) (x : State) (e : Event) (dr : Ring12) : tag.val = 1834 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01835 (tag : Fin 10000) (htag : tag.val = 1835) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1835 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01836 (tag : Fin 10000) (htag : tag.val = 1836) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1836 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01837 (tag : Fin 10000) (htag : tag.val = 1837) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1837 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01838 (tag : Fin 10000) (htag : tag.val = 1838) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1838 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01839 (tag : Fin 10000) (htag : tag.val = 1839) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1839 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01840 (tag : Fin 10000) (htag : tag.val = 1840) (k : Ring12) : tag.val = 1840 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01841 (tag : Fin 10000) (htag : tag.val = 1841) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1841 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01842 (tag : Fin 10000) (htag : tag.val = 1842) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1842 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01843 (tag : Fin 10000) (htag : tag.val = 1843) (x : State) (e : Event) (dr : Ring12) : tag.val = 1843 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01844 (tag : Fin 10000) (htag : tag.val = 1844) (x : State) (e : Event) (dr : Ring12) : tag.val = 1844 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01845 (tag : Fin 10000) (htag : tag.val = 1845) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1845 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01846 (tag : Fin 10000) (htag : tag.val = 1846) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1846 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01847 (tag : Fin 10000) (htag : tag.val = 1847) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1847 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01848 (tag : Fin 10000) (htag : tag.val = 1848) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1848 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01849 (tag : Fin 10000) (htag : tag.val = 1849) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1849 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01850 (tag : Fin 10000) (htag : tag.val = 1850) (k : Ring12) : tag.val = 1850 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01851 (tag : Fin 10000) (htag : tag.val = 1851) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1851 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01852 (tag : Fin 10000) (htag : tag.val = 1852) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1852 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01853 (tag : Fin 10000) (htag : tag.val = 1853) (x : State) (e : Event) (dr : Ring12) : tag.val = 1853 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01854 (tag : Fin 10000) (htag : tag.val = 1854) (x : State) (e : Event) (dr : Ring12) : tag.val = 1854 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01855 (tag : Fin 10000) (htag : tag.val = 1855) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1855 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01856 (tag : Fin 10000) (htag : tag.val = 1856) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1856 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01857 (tag : Fin 10000) (htag : tag.val = 1857) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1857 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01858 (tag : Fin 10000) (htag : tag.val = 1858) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1858 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01859 (tag : Fin 10000) (htag : tag.val = 1859) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1859 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01860 (tag : Fin 10000) (htag : tag.val = 1860) (k : Ring12) : tag.val = 1860 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01861 (tag : Fin 10000) (htag : tag.val = 1861) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1861 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01862 (tag : Fin 10000) (htag : tag.val = 1862) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1862 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01863 (tag : Fin 10000) (htag : tag.val = 1863) (x : State) (e : Event) (dr : Ring12) : tag.val = 1863 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01864 (tag : Fin 10000) (htag : tag.val = 1864) (x : State) (e : Event) (dr : Ring12) : tag.val = 1864 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01865 (tag : Fin 10000) (htag : tag.val = 1865) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1865 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01866 (tag : Fin 10000) (htag : tag.val = 1866) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1866 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01867 (tag : Fin 10000) (htag : tag.val = 1867) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1867 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01868 (tag : Fin 10000) (htag : tag.val = 1868) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1868 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01869 (tag : Fin 10000) (htag : tag.val = 1869) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1869 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01870 (tag : Fin 10000) (htag : tag.val = 1870) (k : Ring12) : tag.val = 1870 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01871 (tag : Fin 10000) (htag : tag.val = 1871) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1871 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01872 (tag : Fin 10000) (htag : tag.val = 1872) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1872 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01873 (tag : Fin 10000) (htag : tag.val = 1873) (x : State) (e : Event) (dr : Ring12) : tag.val = 1873 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01874 (tag : Fin 10000) (htag : tag.val = 1874) (x : State) (e : Event) (dr : Ring12) : tag.val = 1874 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01875 (tag : Fin 10000) (htag : tag.val = 1875) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1875 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01876 (tag : Fin 10000) (htag : tag.val = 1876) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1876 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01877 (tag : Fin 10000) (htag : tag.val = 1877) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1877 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01878 (tag : Fin 10000) (htag : tag.val = 1878) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1878 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01879 (tag : Fin 10000) (htag : tag.val = 1879) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1879 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01880 (tag : Fin 10000) (htag : tag.val = 1880) (k : Ring12) : tag.val = 1880 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01881 (tag : Fin 10000) (htag : tag.val = 1881) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1881 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01882 (tag : Fin 10000) (htag : tag.val = 1882) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1882 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01883 (tag : Fin 10000) (htag : tag.val = 1883) (x : State) (e : Event) (dr : Ring12) : tag.val = 1883 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01884 (tag : Fin 10000) (htag : tag.val = 1884) (x : State) (e : Event) (dr : Ring12) : tag.val = 1884 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01885 (tag : Fin 10000) (htag : tag.val = 1885) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1885 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01886 (tag : Fin 10000) (htag : tag.val = 1886) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1886 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01887 (tag : Fin 10000) (htag : tag.val = 1887) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1887 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01888 (tag : Fin 10000) (htag : tag.val = 1888) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1888 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01889 (tag : Fin 10000) (htag : tag.val = 1889) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1889 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01890 (tag : Fin 10000) (htag : tag.val = 1890) (k : Ring12) : tag.val = 1890 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01891 (tag : Fin 10000) (htag : tag.val = 1891) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1891 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01892 (tag : Fin 10000) (htag : tag.val = 1892) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1892 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01893 (tag : Fin 10000) (htag : tag.val = 1893) (x : State) (e : Event) (dr : Ring12) : tag.val = 1893 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01894 (tag : Fin 10000) (htag : tag.val = 1894) (x : State) (e : Event) (dr : Ring12) : tag.val = 1894 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01895 (tag : Fin 10000) (htag : tag.val = 1895) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1895 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01896 (tag : Fin 10000) (htag : tag.val = 1896) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1896 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01897 (tag : Fin 10000) (htag : tag.val = 1897) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1897 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01898 (tag : Fin 10000) (htag : tag.val = 1898) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1898 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01899 (tag : Fin 10000) (htag : tag.val = 1899) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1899 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
