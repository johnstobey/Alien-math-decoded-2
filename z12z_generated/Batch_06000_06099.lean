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
theorem generated_06000 (tag : Fin 10000) (htag : tag.val = 6000) (k : Ring12) : tag.val = 6000 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06001 (tag : Fin 10000) (htag : tag.val = 6001) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6001 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06002 (tag : Fin 10000) (htag : tag.val = 6002) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6002 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06003 (tag : Fin 10000) (htag : tag.val = 6003) (x : State) (e : Event) (dr : Ring12) : tag.val = 6003 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06004 (tag : Fin 10000) (htag : tag.val = 6004) (x : State) (e : Event) (dr : Ring12) : tag.val = 6004 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06005 (tag : Fin 10000) (htag : tag.val = 6005) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6005 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06006 (tag : Fin 10000) (htag : tag.val = 6006) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6006 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06007 (tag : Fin 10000) (htag : tag.val = 6007) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6007 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06008 (tag : Fin 10000) (htag : tag.val = 6008) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6008 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06009 (tag : Fin 10000) (htag : tag.val = 6009) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6009 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06010 (tag : Fin 10000) (htag : tag.val = 6010) (k : Ring12) : tag.val = 6010 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06011 (tag : Fin 10000) (htag : tag.val = 6011) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6011 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06012 (tag : Fin 10000) (htag : tag.val = 6012) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6012 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06013 (tag : Fin 10000) (htag : tag.val = 6013) (x : State) (e : Event) (dr : Ring12) : tag.val = 6013 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06014 (tag : Fin 10000) (htag : tag.val = 6014) (x : State) (e : Event) (dr : Ring12) : tag.val = 6014 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06015 (tag : Fin 10000) (htag : tag.val = 6015) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6015 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06016 (tag : Fin 10000) (htag : tag.val = 6016) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6016 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06017 (tag : Fin 10000) (htag : tag.val = 6017) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6017 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06018 (tag : Fin 10000) (htag : tag.val = 6018) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6018 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06019 (tag : Fin 10000) (htag : tag.val = 6019) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6019 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06020 (tag : Fin 10000) (htag : tag.val = 6020) (k : Ring12) : tag.val = 6020 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06021 (tag : Fin 10000) (htag : tag.val = 6021) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6021 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06022 (tag : Fin 10000) (htag : tag.val = 6022) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6022 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06023 (tag : Fin 10000) (htag : tag.val = 6023) (x : State) (e : Event) (dr : Ring12) : tag.val = 6023 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06024 (tag : Fin 10000) (htag : tag.val = 6024) (x : State) (e : Event) (dr : Ring12) : tag.val = 6024 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06025 (tag : Fin 10000) (htag : tag.val = 6025) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6025 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06026 (tag : Fin 10000) (htag : tag.val = 6026) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6026 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06027 (tag : Fin 10000) (htag : tag.val = 6027) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6027 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06028 (tag : Fin 10000) (htag : tag.val = 6028) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6028 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06029 (tag : Fin 10000) (htag : tag.val = 6029) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6029 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06030 (tag : Fin 10000) (htag : tag.val = 6030) (k : Ring12) : tag.val = 6030 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06031 (tag : Fin 10000) (htag : tag.val = 6031) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6031 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06032 (tag : Fin 10000) (htag : tag.val = 6032) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6032 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06033 (tag : Fin 10000) (htag : tag.val = 6033) (x : State) (e : Event) (dr : Ring12) : tag.val = 6033 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06034 (tag : Fin 10000) (htag : tag.val = 6034) (x : State) (e : Event) (dr : Ring12) : tag.val = 6034 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06035 (tag : Fin 10000) (htag : tag.val = 6035) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6035 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06036 (tag : Fin 10000) (htag : tag.val = 6036) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6036 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06037 (tag : Fin 10000) (htag : tag.val = 6037) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6037 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06038 (tag : Fin 10000) (htag : tag.val = 6038) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6038 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06039 (tag : Fin 10000) (htag : tag.val = 6039) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6039 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06040 (tag : Fin 10000) (htag : tag.val = 6040) (k : Ring12) : tag.val = 6040 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06041 (tag : Fin 10000) (htag : tag.val = 6041) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6041 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06042 (tag : Fin 10000) (htag : tag.val = 6042) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6042 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06043 (tag : Fin 10000) (htag : tag.val = 6043) (x : State) (e : Event) (dr : Ring12) : tag.val = 6043 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06044 (tag : Fin 10000) (htag : tag.val = 6044) (x : State) (e : Event) (dr : Ring12) : tag.val = 6044 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06045 (tag : Fin 10000) (htag : tag.val = 6045) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6045 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06046 (tag : Fin 10000) (htag : tag.val = 6046) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6046 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06047 (tag : Fin 10000) (htag : tag.val = 6047) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6047 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06048 (tag : Fin 10000) (htag : tag.val = 6048) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6048 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06049 (tag : Fin 10000) (htag : tag.val = 6049) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6049 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06050 (tag : Fin 10000) (htag : tag.val = 6050) (k : Ring12) : tag.val = 6050 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06051 (tag : Fin 10000) (htag : tag.val = 6051) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6051 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06052 (tag : Fin 10000) (htag : tag.val = 6052) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6052 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06053 (tag : Fin 10000) (htag : tag.val = 6053) (x : State) (e : Event) (dr : Ring12) : tag.val = 6053 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06054 (tag : Fin 10000) (htag : tag.val = 6054) (x : State) (e : Event) (dr : Ring12) : tag.val = 6054 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06055 (tag : Fin 10000) (htag : tag.val = 6055) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6055 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06056 (tag : Fin 10000) (htag : tag.val = 6056) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6056 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06057 (tag : Fin 10000) (htag : tag.val = 6057) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6057 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06058 (tag : Fin 10000) (htag : tag.val = 6058) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6058 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06059 (tag : Fin 10000) (htag : tag.val = 6059) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6059 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06060 (tag : Fin 10000) (htag : tag.val = 6060) (k : Ring12) : tag.val = 6060 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06061 (tag : Fin 10000) (htag : tag.val = 6061) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6061 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06062 (tag : Fin 10000) (htag : tag.val = 6062) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6062 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06063 (tag : Fin 10000) (htag : tag.val = 6063) (x : State) (e : Event) (dr : Ring12) : tag.val = 6063 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06064 (tag : Fin 10000) (htag : tag.val = 6064) (x : State) (e : Event) (dr : Ring12) : tag.val = 6064 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06065 (tag : Fin 10000) (htag : tag.val = 6065) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6065 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06066 (tag : Fin 10000) (htag : tag.val = 6066) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6066 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06067 (tag : Fin 10000) (htag : tag.val = 6067) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6067 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06068 (tag : Fin 10000) (htag : tag.val = 6068) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6068 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06069 (tag : Fin 10000) (htag : tag.val = 6069) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6069 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06070 (tag : Fin 10000) (htag : tag.val = 6070) (k : Ring12) : tag.val = 6070 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06071 (tag : Fin 10000) (htag : tag.val = 6071) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6071 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06072 (tag : Fin 10000) (htag : tag.val = 6072) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6072 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06073 (tag : Fin 10000) (htag : tag.val = 6073) (x : State) (e : Event) (dr : Ring12) : tag.val = 6073 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06074 (tag : Fin 10000) (htag : tag.val = 6074) (x : State) (e : Event) (dr : Ring12) : tag.val = 6074 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06075 (tag : Fin 10000) (htag : tag.val = 6075) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6075 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06076 (tag : Fin 10000) (htag : tag.val = 6076) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6076 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06077 (tag : Fin 10000) (htag : tag.val = 6077) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6077 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06078 (tag : Fin 10000) (htag : tag.val = 6078) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6078 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06079 (tag : Fin 10000) (htag : tag.val = 6079) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6079 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06080 (tag : Fin 10000) (htag : tag.val = 6080) (k : Ring12) : tag.val = 6080 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06081 (tag : Fin 10000) (htag : tag.val = 6081) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6081 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06082 (tag : Fin 10000) (htag : tag.val = 6082) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6082 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06083 (tag : Fin 10000) (htag : tag.val = 6083) (x : State) (e : Event) (dr : Ring12) : tag.val = 6083 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06084 (tag : Fin 10000) (htag : tag.val = 6084) (x : State) (e : Event) (dr : Ring12) : tag.val = 6084 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06085 (tag : Fin 10000) (htag : tag.val = 6085) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6085 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06086 (tag : Fin 10000) (htag : tag.val = 6086) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6086 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06087 (tag : Fin 10000) (htag : tag.val = 6087) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6087 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06088 (tag : Fin 10000) (htag : tag.val = 6088) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6088 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06089 (tag : Fin 10000) (htag : tag.val = 6089) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6089 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06090 (tag : Fin 10000) (htag : tag.val = 6090) (k : Ring12) : tag.val = 6090 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06091 (tag : Fin 10000) (htag : tag.val = 6091) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6091 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06092 (tag : Fin 10000) (htag : tag.val = 6092) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6092 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06093 (tag : Fin 10000) (htag : tag.val = 6093) (x : State) (e : Event) (dr : Ring12) : tag.val = 6093 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06094 (tag : Fin 10000) (htag : tag.val = 6094) (x : State) (e : Event) (dr : Ring12) : tag.val = 6094 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06095 (tag : Fin 10000) (htag : tag.val = 6095) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6095 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06096 (tag : Fin 10000) (htag : tag.val = 6096) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6096 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06097 (tag : Fin 10000) (htag : tag.val = 6097) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6097 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06098 (tag : Fin 10000) (htag : tag.val = 6098) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6098 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06099 (tag : Fin 10000) (htag : tag.val = 6099) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6099 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
