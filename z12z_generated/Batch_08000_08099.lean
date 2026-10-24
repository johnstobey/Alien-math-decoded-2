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
theorem generated_08000 (tag : Fin 10000) (htag : tag.val = 8000) (k : Ring12) : tag.val = 8000 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08001 (tag : Fin 10000) (htag : tag.val = 8001) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8001 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08002 (tag : Fin 10000) (htag : tag.val = 8002) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8002 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08003 (tag : Fin 10000) (htag : tag.val = 8003) (x : State) (e : Event) (dr : Ring12) : tag.val = 8003 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08004 (tag : Fin 10000) (htag : tag.val = 8004) (x : State) (e : Event) (dr : Ring12) : tag.val = 8004 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08005 (tag : Fin 10000) (htag : tag.val = 8005) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8005 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08006 (tag : Fin 10000) (htag : tag.val = 8006) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8006 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08007 (tag : Fin 10000) (htag : tag.val = 8007) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8007 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08008 (tag : Fin 10000) (htag : tag.val = 8008) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8008 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08009 (tag : Fin 10000) (htag : tag.val = 8009) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8009 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08010 (tag : Fin 10000) (htag : tag.val = 8010) (k : Ring12) : tag.val = 8010 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08011 (tag : Fin 10000) (htag : tag.val = 8011) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8011 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08012 (tag : Fin 10000) (htag : tag.val = 8012) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8012 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08013 (tag : Fin 10000) (htag : tag.val = 8013) (x : State) (e : Event) (dr : Ring12) : tag.val = 8013 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08014 (tag : Fin 10000) (htag : tag.val = 8014) (x : State) (e : Event) (dr : Ring12) : tag.val = 8014 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08015 (tag : Fin 10000) (htag : tag.val = 8015) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8015 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08016 (tag : Fin 10000) (htag : tag.val = 8016) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8016 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08017 (tag : Fin 10000) (htag : tag.val = 8017) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8017 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08018 (tag : Fin 10000) (htag : tag.val = 8018) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8018 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08019 (tag : Fin 10000) (htag : tag.val = 8019) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8019 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08020 (tag : Fin 10000) (htag : tag.val = 8020) (k : Ring12) : tag.val = 8020 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08021 (tag : Fin 10000) (htag : tag.val = 8021) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8021 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08022 (tag : Fin 10000) (htag : tag.val = 8022) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8022 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08023 (tag : Fin 10000) (htag : tag.val = 8023) (x : State) (e : Event) (dr : Ring12) : tag.val = 8023 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08024 (tag : Fin 10000) (htag : tag.val = 8024) (x : State) (e : Event) (dr : Ring12) : tag.val = 8024 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08025 (tag : Fin 10000) (htag : tag.val = 8025) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8025 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08026 (tag : Fin 10000) (htag : tag.val = 8026) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8026 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08027 (tag : Fin 10000) (htag : tag.val = 8027) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8027 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08028 (tag : Fin 10000) (htag : tag.val = 8028) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8028 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08029 (tag : Fin 10000) (htag : tag.val = 8029) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8029 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08030 (tag : Fin 10000) (htag : tag.val = 8030) (k : Ring12) : tag.val = 8030 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08031 (tag : Fin 10000) (htag : tag.val = 8031) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8031 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08032 (tag : Fin 10000) (htag : tag.val = 8032) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8032 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08033 (tag : Fin 10000) (htag : tag.val = 8033) (x : State) (e : Event) (dr : Ring12) : tag.val = 8033 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08034 (tag : Fin 10000) (htag : tag.val = 8034) (x : State) (e : Event) (dr : Ring12) : tag.val = 8034 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08035 (tag : Fin 10000) (htag : tag.val = 8035) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8035 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08036 (tag : Fin 10000) (htag : tag.val = 8036) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8036 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08037 (tag : Fin 10000) (htag : tag.val = 8037) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8037 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08038 (tag : Fin 10000) (htag : tag.val = 8038) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8038 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08039 (tag : Fin 10000) (htag : tag.val = 8039) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8039 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08040 (tag : Fin 10000) (htag : tag.val = 8040) (k : Ring12) : tag.val = 8040 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08041 (tag : Fin 10000) (htag : tag.val = 8041) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8041 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08042 (tag : Fin 10000) (htag : tag.val = 8042) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8042 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08043 (tag : Fin 10000) (htag : tag.val = 8043) (x : State) (e : Event) (dr : Ring12) : tag.val = 8043 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08044 (tag : Fin 10000) (htag : tag.val = 8044) (x : State) (e : Event) (dr : Ring12) : tag.val = 8044 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08045 (tag : Fin 10000) (htag : tag.val = 8045) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8045 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08046 (tag : Fin 10000) (htag : tag.val = 8046) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8046 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08047 (tag : Fin 10000) (htag : tag.val = 8047) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8047 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08048 (tag : Fin 10000) (htag : tag.val = 8048) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8048 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08049 (tag : Fin 10000) (htag : tag.val = 8049) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8049 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08050 (tag : Fin 10000) (htag : tag.val = 8050) (k : Ring12) : tag.val = 8050 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08051 (tag : Fin 10000) (htag : tag.val = 8051) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8051 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08052 (tag : Fin 10000) (htag : tag.val = 8052) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8052 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08053 (tag : Fin 10000) (htag : tag.val = 8053) (x : State) (e : Event) (dr : Ring12) : tag.val = 8053 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08054 (tag : Fin 10000) (htag : tag.val = 8054) (x : State) (e : Event) (dr : Ring12) : tag.val = 8054 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08055 (tag : Fin 10000) (htag : tag.val = 8055) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8055 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08056 (tag : Fin 10000) (htag : tag.val = 8056) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8056 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08057 (tag : Fin 10000) (htag : tag.val = 8057) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8057 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08058 (tag : Fin 10000) (htag : tag.val = 8058) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8058 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08059 (tag : Fin 10000) (htag : tag.val = 8059) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8059 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08060 (tag : Fin 10000) (htag : tag.val = 8060) (k : Ring12) : tag.val = 8060 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08061 (tag : Fin 10000) (htag : tag.val = 8061) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8061 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08062 (tag : Fin 10000) (htag : tag.val = 8062) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8062 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08063 (tag : Fin 10000) (htag : tag.val = 8063) (x : State) (e : Event) (dr : Ring12) : tag.val = 8063 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08064 (tag : Fin 10000) (htag : tag.val = 8064) (x : State) (e : Event) (dr : Ring12) : tag.val = 8064 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08065 (tag : Fin 10000) (htag : tag.val = 8065) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8065 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08066 (tag : Fin 10000) (htag : tag.val = 8066) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8066 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08067 (tag : Fin 10000) (htag : tag.val = 8067) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8067 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08068 (tag : Fin 10000) (htag : tag.val = 8068) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8068 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08069 (tag : Fin 10000) (htag : tag.val = 8069) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8069 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08070 (tag : Fin 10000) (htag : tag.val = 8070) (k : Ring12) : tag.val = 8070 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08071 (tag : Fin 10000) (htag : tag.val = 8071) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8071 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08072 (tag : Fin 10000) (htag : tag.val = 8072) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8072 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08073 (tag : Fin 10000) (htag : tag.val = 8073) (x : State) (e : Event) (dr : Ring12) : tag.val = 8073 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08074 (tag : Fin 10000) (htag : tag.val = 8074) (x : State) (e : Event) (dr : Ring12) : tag.val = 8074 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08075 (tag : Fin 10000) (htag : tag.val = 8075) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8075 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08076 (tag : Fin 10000) (htag : tag.val = 8076) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8076 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08077 (tag : Fin 10000) (htag : tag.val = 8077) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8077 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08078 (tag : Fin 10000) (htag : tag.val = 8078) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8078 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08079 (tag : Fin 10000) (htag : tag.val = 8079) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8079 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08080 (tag : Fin 10000) (htag : tag.val = 8080) (k : Ring12) : tag.val = 8080 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08081 (tag : Fin 10000) (htag : tag.val = 8081) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8081 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08082 (tag : Fin 10000) (htag : tag.val = 8082) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8082 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08083 (tag : Fin 10000) (htag : tag.val = 8083) (x : State) (e : Event) (dr : Ring12) : tag.val = 8083 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08084 (tag : Fin 10000) (htag : tag.val = 8084) (x : State) (e : Event) (dr : Ring12) : tag.val = 8084 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08085 (tag : Fin 10000) (htag : tag.val = 8085) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8085 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08086 (tag : Fin 10000) (htag : tag.val = 8086) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8086 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08087 (tag : Fin 10000) (htag : tag.val = 8087) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8087 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08088 (tag : Fin 10000) (htag : tag.val = 8088) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8088 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08089 (tag : Fin 10000) (htag : tag.val = 8089) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8089 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08090 (tag : Fin 10000) (htag : tag.val = 8090) (k : Ring12) : tag.val = 8090 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08091 (tag : Fin 10000) (htag : tag.val = 8091) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8091 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08092 (tag : Fin 10000) (htag : tag.val = 8092) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8092 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08093 (tag : Fin 10000) (htag : tag.val = 8093) (x : State) (e : Event) (dr : Ring12) : tag.val = 8093 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08094 (tag : Fin 10000) (htag : tag.val = 8094) (x : State) (e : Event) (dr : Ring12) : tag.val = 8094 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08095 (tag : Fin 10000) (htag : tag.val = 8095) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8095 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08096 (tag : Fin 10000) (htag : tag.val = 8096) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8096 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08097 (tag : Fin 10000) (htag : tag.val = 8097) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8097 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08098 (tag : Fin 10000) (htag : tag.val = 8098) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8098 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08099 (tag : Fin 10000) (htag : tag.val = 8099) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8099 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
