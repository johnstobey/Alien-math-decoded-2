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
theorem generated_09000 (tag : Fin 10000) (htag : tag.val = 9000) (k : Ring12) : tag.val = 9000 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09001 (tag : Fin 10000) (htag : tag.val = 9001) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9001 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09002 (tag : Fin 10000) (htag : tag.val = 9002) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9002 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09003 (tag : Fin 10000) (htag : tag.val = 9003) (x : State) (e : Event) (dr : Ring12) : tag.val = 9003 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09004 (tag : Fin 10000) (htag : tag.val = 9004) (x : State) (e : Event) (dr : Ring12) : tag.val = 9004 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09005 (tag : Fin 10000) (htag : tag.val = 9005) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9005 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09006 (tag : Fin 10000) (htag : tag.val = 9006) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9006 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09007 (tag : Fin 10000) (htag : tag.val = 9007) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9007 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09008 (tag : Fin 10000) (htag : tag.val = 9008) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9008 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09009 (tag : Fin 10000) (htag : tag.val = 9009) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9009 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09010 (tag : Fin 10000) (htag : tag.val = 9010) (k : Ring12) : tag.val = 9010 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09011 (tag : Fin 10000) (htag : tag.val = 9011) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9011 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09012 (tag : Fin 10000) (htag : tag.val = 9012) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9012 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09013 (tag : Fin 10000) (htag : tag.val = 9013) (x : State) (e : Event) (dr : Ring12) : tag.val = 9013 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09014 (tag : Fin 10000) (htag : tag.val = 9014) (x : State) (e : Event) (dr : Ring12) : tag.val = 9014 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09015 (tag : Fin 10000) (htag : tag.val = 9015) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9015 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09016 (tag : Fin 10000) (htag : tag.val = 9016) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9016 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09017 (tag : Fin 10000) (htag : tag.val = 9017) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9017 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09018 (tag : Fin 10000) (htag : tag.val = 9018) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9018 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09019 (tag : Fin 10000) (htag : tag.val = 9019) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9019 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09020 (tag : Fin 10000) (htag : tag.val = 9020) (k : Ring12) : tag.val = 9020 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09021 (tag : Fin 10000) (htag : tag.val = 9021) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9021 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09022 (tag : Fin 10000) (htag : tag.val = 9022) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9022 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09023 (tag : Fin 10000) (htag : tag.val = 9023) (x : State) (e : Event) (dr : Ring12) : tag.val = 9023 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09024 (tag : Fin 10000) (htag : tag.val = 9024) (x : State) (e : Event) (dr : Ring12) : tag.val = 9024 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09025 (tag : Fin 10000) (htag : tag.val = 9025) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9025 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09026 (tag : Fin 10000) (htag : tag.val = 9026) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9026 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09027 (tag : Fin 10000) (htag : tag.val = 9027) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9027 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09028 (tag : Fin 10000) (htag : tag.val = 9028) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9028 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09029 (tag : Fin 10000) (htag : tag.val = 9029) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9029 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09030 (tag : Fin 10000) (htag : tag.val = 9030) (k : Ring12) : tag.val = 9030 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09031 (tag : Fin 10000) (htag : tag.val = 9031) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9031 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09032 (tag : Fin 10000) (htag : tag.val = 9032) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9032 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09033 (tag : Fin 10000) (htag : tag.val = 9033) (x : State) (e : Event) (dr : Ring12) : tag.val = 9033 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09034 (tag : Fin 10000) (htag : tag.val = 9034) (x : State) (e : Event) (dr : Ring12) : tag.val = 9034 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09035 (tag : Fin 10000) (htag : tag.val = 9035) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9035 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09036 (tag : Fin 10000) (htag : tag.val = 9036) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9036 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09037 (tag : Fin 10000) (htag : tag.val = 9037) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9037 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09038 (tag : Fin 10000) (htag : tag.val = 9038) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9038 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09039 (tag : Fin 10000) (htag : tag.val = 9039) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9039 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09040 (tag : Fin 10000) (htag : tag.val = 9040) (k : Ring12) : tag.val = 9040 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09041 (tag : Fin 10000) (htag : tag.val = 9041) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9041 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09042 (tag : Fin 10000) (htag : tag.val = 9042) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9042 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09043 (tag : Fin 10000) (htag : tag.val = 9043) (x : State) (e : Event) (dr : Ring12) : tag.val = 9043 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09044 (tag : Fin 10000) (htag : tag.val = 9044) (x : State) (e : Event) (dr : Ring12) : tag.val = 9044 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09045 (tag : Fin 10000) (htag : tag.val = 9045) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9045 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09046 (tag : Fin 10000) (htag : tag.val = 9046) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9046 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09047 (tag : Fin 10000) (htag : tag.val = 9047) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9047 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09048 (tag : Fin 10000) (htag : tag.val = 9048) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9048 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09049 (tag : Fin 10000) (htag : tag.val = 9049) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9049 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09050 (tag : Fin 10000) (htag : tag.val = 9050) (k : Ring12) : tag.val = 9050 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09051 (tag : Fin 10000) (htag : tag.val = 9051) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9051 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09052 (tag : Fin 10000) (htag : tag.val = 9052) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9052 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09053 (tag : Fin 10000) (htag : tag.val = 9053) (x : State) (e : Event) (dr : Ring12) : tag.val = 9053 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09054 (tag : Fin 10000) (htag : tag.val = 9054) (x : State) (e : Event) (dr : Ring12) : tag.val = 9054 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09055 (tag : Fin 10000) (htag : tag.val = 9055) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9055 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09056 (tag : Fin 10000) (htag : tag.val = 9056) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9056 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09057 (tag : Fin 10000) (htag : tag.val = 9057) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9057 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09058 (tag : Fin 10000) (htag : tag.val = 9058) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9058 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09059 (tag : Fin 10000) (htag : tag.val = 9059) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9059 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09060 (tag : Fin 10000) (htag : tag.val = 9060) (k : Ring12) : tag.val = 9060 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09061 (tag : Fin 10000) (htag : tag.val = 9061) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9061 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09062 (tag : Fin 10000) (htag : tag.val = 9062) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9062 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09063 (tag : Fin 10000) (htag : tag.val = 9063) (x : State) (e : Event) (dr : Ring12) : tag.val = 9063 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09064 (tag : Fin 10000) (htag : tag.val = 9064) (x : State) (e : Event) (dr : Ring12) : tag.val = 9064 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09065 (tag : Fin 10000) (htag : tag.val = 9065) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9065 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09066 (tag : Fin 10000) (htag : tag.val = 9066) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9066 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09067 (tag : Fin 10000) (htag : tag.val = 9067) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9067 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09068 (tag : Fin 10000) (htag : tag.val = 9068) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9068 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09069 (tag : Fin 10000) (htag : tag.val = 9069) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9069 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09070 (tag : Fin 10000) (htag : tag.val = 9070) (k : Ring12) : tag.val = 9070 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09071 (tag : Fin 10000) (htag : tag.val = 9071) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9071 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09072 (tag : Fin 10000) (htag : tag.val = 9072) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9072 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09073 (tag : Fin 10000) (htag : tag.val = 9073) (x : State) (e : Event) (dr : Ring12) : tag.val = 9073 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09074 (tag : Fin 10000) (htag : tag.val = 9074) (x : State) (e : Event) (dr : Ring12) : tag.val = 9074 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09075 (tag : Fin 10000) (htag : tag.val = 9075) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9075 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09076 (tag : Fin 10000) (htag : tag.val = 9076) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9076 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09077 (tag : Fin 10000) (htag : tag.val = 9077) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9077 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09078 (tag : Fin 10000) (htag : tag.val = 9078) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9078 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09079 (tag : Fin 10000) (htag : tag.val = 9079) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9079 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09080 (tag : Fin 10000) (htag : tag.val = 9080) (k : Ring12) : tag.val = 9080 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09081 (tag : Fin 10000) (htag : tag.val = 9081) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9081 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09082 (tag : Fin 10000) (htag : tag.val = 9082) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9082 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09083 (tag : Fin 10000) (htag : tag.val = 9083) (x : State) (e : Event) (dr : Ring12) : tag.val = 9083 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09084 (tag : Fin 10000) (htag : tag.val = 9084) (x : State) (e : Event) (dr : Ring12) : tag.val = 9084 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09085 (tag : Fin 10000) (htag : tag.val = 9085) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9085 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09086 (tag : Fin 10000) (htag : tag.val = 9086) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9086 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09087 (tag : Fin 10000) (htag : tag.val = 9087) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9087 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09088 (tag : Fin 10000) (htag : tag.val = 9088) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9088 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09089 (tag : Fin 10000) (htag : tag.val = 9089) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9089 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09090 (tag : Fin 10000) (htag : tag.val = 9090) (k : Ring12) : tag.val = 9090 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09091 (tag : Fin 10000) (htag : tag.val = 9091) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9091 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09092 (tag : Fin 10000) (htag : tag.val = 9092) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9092 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09093 (tag : Fin 10000) (htag : tag.val = 9093) (x : State) (e : Event) (dr : Ring12) : tag.val = 9093 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09094 (tag : Fin 10000) (htag : tag.val = 9094) (x : State) (e : Event) (dr : Ring12) : tag.val = 9094 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09095 (tag : Fin 10000) (htag : tag.val = 9095) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9095 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09096 (tag : Fin 10000) (htag : tag.val = 9096) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9096 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09097 (tag : Fin 10000) (htag : tag.val = 9097) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9097 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09098 (tag : Fin 10000) (htag : tag.val = 9098) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9098 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09099 (tag : Fin 10000) (htag : tag.val = 9099) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9099 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
