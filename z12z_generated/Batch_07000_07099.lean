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
theorem generated_07000 (tag : Fin 10000) (htag : tag.val = 7000) (k : Ring12) : tag.val = 7000 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07001 (tag : Fin 10000) (htag : tag.val = 7001) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7001 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07002 (tag : Fin 10000) (htag : tag.val = 7002) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7002 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07003 (tag : Fin 10000) (htag : tag.val = 7003) (x : State) (e : Event) (dr : Ring12) : tag.val = 7003 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07004 (tag : Fin 10000) (htag : tag.val = 7004) (x : State) (e : Event) (dr : Ring12) : tag.val = 7004 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07005 (tag : Fin 10000) (htag : tag.val = 7005) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7005 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07006 (tag : Fin 10000) (htag : tag.val = 7006) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7006 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07007 (tag : Fin 10000) (htag : tag.val = 7007) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7007 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07008 (tag : Fin 10000) (htag : tag.val = 7008) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7008 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07009 (tag : Fin 10000) (htag : tag.val = 7009) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7009 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07010 (tag : Fin 10000) (htag : tag.val = 7010) (k : Ring12) : tag.val = 7010 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07011 (tag : Fin 10000) (htag : tag.val = 7011) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7011 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07012 (tag : Fin 10000) (htag : tag.val = 7012) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7012 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07013 (tag : Fin 10000) (htag : tag.val = 7013) (x : State) (e : Event) (dr : Ring12) : tag.val = 7013 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07014 (tag : Fin 10000) (htag : tag.val = 7014) (x : State) (e : Event) (dr : Ring12) : tag.val = 7014 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07015 (tag : Fin 10000) (htag : tag.val = 7015) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7015 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07016 (tag : Fin 10000) (htag : tag.val = 7016) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7016 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07017 (tag : Fin 10000) (htag : tag.val = 7017) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7017 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07018 (tag : Fin 10000) (htag : tag.val = 7018) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7018 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07019 (tag : Fin 10000) (htag : tag.val = 7019) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7019 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07020 (tag : Fin 10000) (htag : tag.val = 7020) (k : Ring12) : tag.val = 7020 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07021 (tag : Fin 10000) (htag : tag.val = 7021) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7021 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07022 (tag : Fin 10000) (htag : tag.val = 7022) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7022 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07023 (tag : Fin 10000) (htag : tag.val = 7023) (x : State) (e : Event) (dr : Ring12) : tag.val = 7023 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07024 (tag : Fin 10000) (htag : tag.val = 7024) (x : State) (e : Event) (dr : Ring12) : tag.val = 7024 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07025 (tag : Fin 10000) (htag : tag.val = 7025) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7025 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07026 (tag : Fin 10000) (htag : tag.val = 7026) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7026 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07027 (tag : Fin 10000) (htag : tag.val = 7027) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7027 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07028 (tag : Fin 10000) (htag : tag.val = 7028) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7028 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07029 (tag : Fin 10000) (htag : tag.val = 7029) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7029 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07030 (tag : Fin 10000) (htag : tag.val = 7030) (k : Ring12) : tag.val = 7030 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07031 (tag : Fin 10000) (htag : tag.val = 7031) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7031 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07032 (tag : Fin 10000) (htag : tag.val = 7032) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7032 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07033 (tag : Fin 10000) (htag : tag.val = 7033) (x : State) (e : Event) (dr : Ring12) : tag.val = 7033 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07034 (tag : Fin 10000) (htag : tag.val = 7034) (x : State) (e : Event) (dr : Ring12) : tag.val = 7034 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07035 (tag : Fin 10000) (htag : tag.val = 7035) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7035 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07036 (tag : Fin 10000) (htag : tag.val = 7036) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7036 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07037 (tag : Fin 10000) (htag : tag.val = 7037) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7037 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07038 (tag : Fin 10000) (htag : tag.val = 7038) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7038 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07039 (tag : Fin 10000) (htag : tag.val = 7039) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7039 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07040 (tag : Fin 10000) (htag : tag.val = 7040) (k : Ring12) : tag.val = 7040 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07041 (tag : Fin 10000) (htag : tag.val = 7041) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7041 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07042 (tag : Fin 10000) (htag : tag.val = 7042) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7042 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07043 (tag : Fin 10000) (htag : tag.val = 7043) (x : State) (e : Event) (dr : Ring12) : tag.val = 7043 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07044 (tag : Fin 10000) (htag : tag.val = 7044) (x : State) (e : Event) (dr : Ring12) : tag.val = 7044 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07045 (tag : Fin 10000) (htag : tag.val = 7045) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7045 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07046 (tag : Fin 10000) (htag : tag.val = 7046) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7046 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07047 (tag : Fin 10000) (htag : tag.val = 7047) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7047 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07048 (tag : Fin 10000) (htag : tag.val = 7048) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7048 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07049 (tag : Fin 10000) (htag : tag.val = 7049) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7049 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07050 (tag : Fin 10000) (htag : tag.val = 7050) (k : Ring12) : tag.val = 7050 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07051 (tag : Fin 10000) (htag : tag.val = 7051) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7051 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07052 (tag : Fin 10000) (htag : tag.val = 7052) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7052 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07053 (tag : Fin 10000) (htag : tag.val = 7053) (x : State) (e : Event) (dr : Ring12) : tag.val = 7053 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07054 (tag : Fin 10000) (htag : tag.val = 7054) (x : State) (e : Event) (dr : Ring12) : tag.val = 7054 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07055 (tag : Fin 10000) (htag : tag.val = 7055) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7055 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07056 (tag : Fin 10000) (htag : tag.val = 7056) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7056 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07057 (tag : Fin 10000) (htag : tag.val = 7057) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7057 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07058 (tag : Fin 10000) (htag : tag.val = 7058) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7058 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07059 (tag : Fin 10000) (htag : tag.val = 7059) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7059 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07060 (tag : Fin 10000) (htag : tag.val = 7060) (k : Ring12) : tag.val = 7060 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07061 (tag : Fin 10000) (htag : tag.val = 7061) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7061 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07062 (tag : Fin 10000) (htag : tag.val = 7062) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7062 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07063 (tag : Fin 10000) (htag : tag.val = 7063) (x : State) (e : Event) (dr : Ring12) : tag.val = 7063 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07064 (tag : Fin 10000) (htag : tag.val = 7064) (x : State) (e : Event) (dr : Ring12) : tag.val = 7064 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07065 (tag : Fin 10000) (htag : tag.val = 7065) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7065 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07066 (tag : Fin 10000) (htag : tag.val = 7066) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7066 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07067 (tag : Fin 10000) (htag : tag.val = 7067) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7067 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07068 (tag : Fin 10000) (htag : tag.val = 7068) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7068 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07069 (tag : Fin 10000) (htag : tag.val = 7069) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7069 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07070 (tag : Fin 10000) (htag : tag.val = 7070) (k : Ring12) : tag.val = 7070 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07071 (tag : Fin 10000) (htag : tag.val = 7071) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7071 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07072 (tag : Fin 10000) (htag : tag.val = 7072) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7072 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07073 (tag : Fin 10000) (htag : tag.val = 7073) (x : State) (e : Event) (dr : Ring12) : tag.val = 7073 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07074 (tag : Fin 10000) (htag : tag.val = 7074) (x : State) (e : Event) (dr : Ring12) : tag.val = 7074 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07075 (tag : Fin 10000) (htag : tag.val = 7075) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7075 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07076 (tag : Fin 10000) (htag : tag.val = 7076) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7076 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07077 (tag : Fin 10000) (htag : tag.val = 7077) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7077 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07078 (tag : Fin 10000) (htag : tag.val = 7078) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7078 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07079 (tag : Fin 10000) (htag : tag.val = 7079) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7079 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07080 (tag : Fin 10000) (htag : tag.val = 7080) (k : Ring12) : tag.val = 7080 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07081 (tag : Fin 10000) (htag : tag.val = 7081) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7081 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07082 (tag : Fin 10000) (htag : tag.val = 7082) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7082 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07083 (tag : Fin 10000) (htag : tag.val = 7083) (x : State) (e : Event) (dr : Ring12) : tag.val = 7083 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07084 (tag : Fin 10000) (htag : tag.val = 7084) (x : State) (e : Event) (dr : Ring12) : tag.val = 7084 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07085 (tag : Fin 10000) (htag : tag.val = 7085) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7085 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07086 (tag : Fin 10000) (htag : tag.val = 7086) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7086 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07087 (tag : Fin 10000) (htag : tag.val = 7087) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7087 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07088 (tag : Fin 10000) (htag : tag.val = 7088) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7088 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07089 (tag : Fin 10000) (htag : tag.val = 7089) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7089 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07090 (tag : Fin 10000) (htag : tag.val = 7090) (k : Ring12) : tag.val = 7090 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07091 (tag : Fin 10000) (htag : tag.val = 7091) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7091 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07092 (tag : Fin 10000) (htag : tag.val = 7092) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7092 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07093 (tag : Fin 10000) (htag : tag.val = 7093) (x : State) (e : Event) (dr : Ring12) : tag.val = 7093 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07094 (tag : Fin 10000) (htag : tag.val = 7094) (x : State) (e : Event) (dr : Ring12) : tag.val = 7094 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07095 (tag : Fin 10000) (htag : tag.val = 7095) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7095 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07096 (tag : Fin 10000) (htag : tag.val = 7096) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7096 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07097 (tag : Fin 10000) (htag : tag.val = 7097) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7097 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07098 (tag : Fin 10000) (htag : tag.val = 7098) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7098 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07099 (tag : Fin 10000) (htag : tag.val = 7099) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7099 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
