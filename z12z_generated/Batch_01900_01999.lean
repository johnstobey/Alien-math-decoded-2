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
theorem generated_01900 (tag : Fin 10000) (htag : tag.val = 1900) (k : Ring12) : tag.val = 1900 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01901 (tag : Fin 10000) (htag : tag.val = 1901) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1901 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01902 (tag : Fin 10000) (htag : tag.val = 1902) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1902 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01903 (tag : Fin 10000) (htag : tag.val = 1903) (x : State) (e : Event) (dr : Ring12) : tag.val = 1903 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01904 (tag : Fin 10000) (htag : tag.val = 1904) (x : State) (e : Event) (dr : Ring12) : tag.val = 1904 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01905 (tag : Fin 10000) (htag : tag.val = 1905) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1905 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01906 (tag : Fin 10000) (htag : tag.val = 1906) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1906 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01907 (tag : Fin 10000) (htag : tag.val = 1907) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1907 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01908 (tag : Fin 10000) (htag : tag.val = 1908) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1908 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01909 (tag : Fin 10000) (htag : tag.val = 1909) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1909 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01910 (tag : Fin 10000) (htag : tag.val = 1910) (k : Ring12) : tag.val = 1910 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01911 (tag : Fin 10000) (htag : tag.val = 1911) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1911 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01912 (tag : Fin 10000) (htag : tag.val = 1912) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1912 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01913 (tag : Fin 10000) (htag : tag.val = 1913) (x : State) (e : Event) (dr : Ring12) : tag.val = 1913 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01914 (tag : Fin 10000) (htag : tag.val = 1914) (x : State) (e : Event) (dr : Ring12) : tag.val = 1914 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01915 (tag : Fin 10000) (htag : tag.val = 1915) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1915 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01916 (tag : Fin 10000) (htag : tag.val = 1916) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1916 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01917 (tag : Fin 10000) (htag : tag.val = 1917) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1917 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01918 (tag : Fin 10000) (htag : tag.val = 1918) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1918 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01919 (tag : Fin 10000) (htag : tag.val = 1919) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1919 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01920 (tag : Fin 10000) (htag : tag.val = 1920) (k : Ring12) : tag.val = 1920 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01921 (tag : Fin 10000) (htag : tag.val = 1921) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1921 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01922 (tag : Fin 10000) (htag : tag.val = 1922) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1922 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01923 (tag : Fin 10000) (htag : tag.val = 1923) (x : State) (e : Event) (dr : Ring12) : tag.val = 1923 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01924 (tag : Fin 10000) (htag : tag.val = 1924) (x : State) (e : Event) (dr : Ring12) : tag.val = 1924 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01925 (tag : Fin 10000) (htag : tag.val = 1925) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1925 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01926 (tag : Fin 10000) (htag : tag.val = 1926) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1926 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01927 (tag : Fin 10000) (htag : tag.val = 1927) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1927 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01928 (tag : Fin 10000) (htag : tag.val = 1928) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1928 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01929 (tag : Fin 10000) (htag : tag.val = 1929) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1929 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01930 (tag : Fin 10000) (htag : tag.val = 1930) (k : Ring12) : tag.val = 1930 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01931 (tag : Fin 10000) (htag : tag.val = 1931) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1931 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01932 (tag : Fin 10000) (htag : tag.val = 1932) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1932 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01933 (tag : Fin 10000) (htag : tag.val = 1933) (x : State) (e : Event) (dr : Ring12) : tag.val = 1933 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01934 (tag : Fin 10000) (htag : tag.val = 1934) (x : State) (e : Event) (dr : Ring12) : tag.val = 1934 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01935 (tag : Fin 10000) (htag : tag.val = 1935) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1935 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01936 (tag : Fin 10000) (htag : tag.val = 1936) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1936 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01937 (tag : Fin 10000) (htag : tag.val = 1937) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1937 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01938 (tag : Fin 10000) (htag : tag.val = 1938) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1938 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01939 (tag : Fin 10000) (htag : tag.val = 1939) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1939 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01940 (tag : Fin 10000) (htag : tag.val = 1940) (k : Ring12) : tag.val = 1940 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01941 (tag : Fin 10000) (htag : tag.val = 1941) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1941 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01942 (tag : Fin 10000) (htag : tag.val = 1942) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1942 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01943 (tag : Fin 10000) (htag : tag.val = 1943) (x : State) (e : Event) (dr : Ring12) : tag.val = 1943 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01944 (tag : Fin 10000) (htag : tag.val = 1944) (x : State) (e : Event) (dr : Ring12) : tag.val = 1944 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01945 (tag : Fin 10000) (htag : tag.val = 1945) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1945 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01946 (tag : Fin 10000) (htag : tag.val = 1946) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1946 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01947 (tag : Fin 10000) (htag : tag.val = 1947) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1947 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01948 (tag : Fin 10000) (htag : tag.val = 1948) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1948 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01949 (tag : Fin 10000) (htag : tag.val = 1949) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1949 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01950 (tag : Fin 10000) (htag : tag.val = 1950) (k : Ring12) : tag.val = 1950 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01951 (tag : Fin 10000) (htag : tag.val = 1951) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1951 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01952 (tag : Fin 10000) (htag : tag.val = 1952) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1952 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01953 (tag : Fin 10000) (htag : tag.val = 1953) (x : State) (e : Event) (dr : Ring12) : tag.val = 1953 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01954 (tag : Fin 10000) (htag : tag.val = 1954) (x : State) (e : Event) (dr : Ring12) : tag.val = 1954 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01955 (tag : Fin 10000) (htag : tag.val = 1955) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1955 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01956 (tag : Fin 10000) (htag : tag.val = 1956) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1956 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01957 (tag : Fin 10000) (htag : tag.val = 1957) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1957 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01958 (tag : Fin 10000) (htag : tag.val = 1958) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1958 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01959 (tag : Fin 10000) (htag : tag.val = 1959) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1959 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01960 (tag : Fin 10000) (htag : tag.val = 1960) (k : Ring12) : tag.val = 1960 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01961 (tag : Fin 10000) (htag : tag.val = 1961) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1961 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01962 (tag : Fin 10000) (htag : tag.val = 1962) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1962 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01963 (tag : Fin 10000) (htag : tag.val = 1963) (x : State) (e : Event) (dr : Ring12) : tag.val = 1963 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01964 (tag : Fin 10000) (htag : tag.val = 1964) (x : State) (e : Event) (dr : Ring12) : tag.val = 1964 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01965 (tag : Fin 10000) (htag : tag.val = 1965) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1965 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01966 (tag : Fin 10000) (htag : tag.val = 1966) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1966 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01967 (tag : Fin 10000) (htag : tag.val = 1967) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1967 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01968 (tag : Fin 10000) (htag : tag.val = 1968) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1968 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01969 (tag : Fin 10000) (htag : tag.val = 1969) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1969 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01970 (tag : Fin 10000) (htag : tag.val = 1970) (k : Ring12) : tag.val = 1970 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01971 (tag : Fin 10000) (htag : tag.val = 1971) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1971 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01972 (tag : Fin 10000) (htag : tag.val = 1972) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1972 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01973 (tag : Fin 10000) (htag : tag.val = 1973) (x : State) (e : Event) (dr : Ring12) : tag.val = 1973 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01974 (tag : Fin 10000) (htag : tag.val = 1974) (x : State) (e : Event) (dr : Ring12) : tag.val = 1974 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01975 (tag : Fin 10000) (htag : tag.val = 1975) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1975 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01976 (tag : Fin 10000) (htag : tag.val = 1976) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1976 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01977 (tag : Fin 10000) (htag : tag.val = 1977) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1977 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01978 (tag : Fin 10000) (htag : tag.val = 1978) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1978 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01979 (tag : Fin 10000) (htag : tag.val = 1979) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1979 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01980 (tag : Fin 10000) (htag : tag.val = 1980) (k : Ring12) : tag.val = 1980 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01981 (tag : Fin 10000) (htag : tag.val = 1981) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1981 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01982 (tag : Fin 10000) (htag : tag.val = 1982) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1982 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01983 (tag : Fin 10000) (htag : tag.val = 1983) (x : State) (e : Event) (dr : Ring12) : tag.val = 1983 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01984 (tag : Fin 10000) (htag : tag.val = 1984) (x : State) (e : Event) (dr : Ring12) : tag.val = 1984 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01985 (tag : Fin 10000) (htag : tag.val = 1985) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1985 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01986 (tag : Fin 10000) (htag : tag.val = 1986) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1986 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01987 (tag : Fin 10000) (htag : tag.val = 1987) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1987 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01988 (tag : Fin 10000) (htag : tag.val = 1988) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1988 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01989 (tag : Fin 10000) (htag : tag.val = 1989) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1989 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01990 (tag : Fin 10000) (htag : tag.val = 1990) (k : Ring12) : tag.val = 1990 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01991 (tag : Fin 10000) (htag : tag.val = 1991) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1991 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01992 (tag : Fin 10000) (htag : tag.val = 1992) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1992 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01993 (tag : Fin 10000) (htag : tag.val = 1993) (x : State) (e : Event) (dr : Ring12) : tag.val = 1993 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01994 (tag : Fin 10000) (htag : tag.val = 1994) (x : State) (e : Event) (dr : Ring12) : tag.val = 1994 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01995 (tag : Fin 10000) (htag : tag.val = 1995) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1995 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01996 (tag : Fin 10000) (htag : tag.val = 1996) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1996 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01997 (tag : Fin 10000) (htag : tag.val = 1997) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1997 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01998 (tag : Fin 10000) (htag : tag.val = 1998) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1998 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01999 (tag : Fin 10000) (htag : tag.val = 1999) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1999 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
