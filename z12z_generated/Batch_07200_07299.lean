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
theorem generated_07200 (tag : Fin 10000) (htag : tag.val = 7200) (k : Ring12) : tag.val = 7200 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07201 (tag : Fin 10000) (htag : tag.val = 7201) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7201 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07202 (tag : Fin 10000) (htag : tag.val = 7202) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7202 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07203 (tag : Fin 10000) (htag : tag.val = 7203) (x : State) (e : Event) (dr : Ring12) : tag.val = 7203 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07204 (tag : Fin 10000) (htag : tag.val = 7204) (x : State) (e : Event) (dr : Ring12) : tag.val = 7204 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07205 (tag : Fin 10000) (htag : tag.val = 7205) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7205 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07206 (tag : Fin 10000) (htag : tag.val = 7206) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7206 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07207 (tag : Fin 10000) (htag : tag.val = 7207) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7207 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07208 (tag : Fin 10000) (htag : tag.val = 7208) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7208 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07209 (tag : Fin 10000) (htag : tag.val = 7209) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7209 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07210 (tag : Fin 10000) (htag : tag.val = 7210) (k : Ring12) : tag.val = 7210 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07211 (tag : Fin 10000) (htag : tag.val = 7211) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7211 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07212 (tag : Fin 10000) (htag : tag.val = 7212) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7212 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07213 (tag : Fin 10000) (htag : tag.val = 7213) (x : State) (e : Event) (dr : Ring12) : tag.val = 7213 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07214 (tag : Fin 10000) (htag : tag.val = 7214) (x : State) (e : Event) (dr : Ring12) : tag.val = 7214 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07215 (tag : Fin 10000) (htag : tag.val = 7215) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7215 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07216 (tag : Fin 10000) (htag : tag.val = 7216) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7216 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07217 (tag : Fin 10000) (htag : tag.val = 7217) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7217 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07218 (tag : Fin 10000) (htag : tag.val = 7218) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7218 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07219 (tag : Fin 10000) (htag : tag.val = 7219) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7219 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07220 (tag : Fin 10000) (htag : tag.val = 7220) (k : Ring12) : tag.val = 7220 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07221 (tag : Fin 10000) (htag : tag.val = 7221) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7221 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07222 (tag : Fin 10000) (htag : tag.val = 7222) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7222 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07223 (tag : Fin 10000) (htag : tag.val = 7223) (x : State) (e : Event) (dr : Ring12) : tag.val = 7223 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07224 (tag : Fin 10000) (htag : tag.val = 7224) (x : State) (e : Event) (dr : Ring12) : tag.val = 7224 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07225 (tag : Fin 10000) (htag : tag.val = 7225) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7225 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07226 (tag : Fin 10000) (htag : tag.val = 7226) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7226 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07227 (tag : Fin 10000) (htag : tag.val = 7227) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7227 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07228 (tag : Fin 10000) (htag : tag.val = 7228) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7228 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07229 (tag : Fin 10000) (htag : tag.val = 7229) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7229 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07230 (tag : Fin 10000) (htag : tag.val = 7230) (k : Ring12) : tag.val = 7230 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07231 (tag : Fin 10000) (htag : tag.val = 7231) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7231 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07232 (tag : Fin 10000) (htag : tag.val = 7232) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7232 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07233 (tag : Fin 10000) (htag : tag.val = 7233) (x : State) (e : Event) (dr : Ring12) : tag.val = 7233 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07234 (tag : Fin 10000) (htag : tag.val = 7234) (x : State) (e : Event) (dr : Ring12) : tag.val = 7234 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07235 (tag : Fin 10000) (htag : tag.val = 7235) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7235 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07236 (tag : Fin 10000) (htag : tag.val = 7236) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7236 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07237 (tag : Fin 10000) (htag : tag.val = 7237) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7237 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07238 (tag : Fin 10000) (htag : tag.val = 7238) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7238 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07239 (tag : Fin 10000) (htag : tag.val = 7239) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7239 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07240 (tag : Fin 10000) (htag : tag.val = 7240) (k : Ring12) : tag.val = 7240 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07241 (tag : Fin 10000) (htag : tag.val = 7241) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7241 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07242 (tag : Fin 10000) (htag : tag.val = 7242) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7242 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07243 (tag : Fin 10000) (htag : tag.val = 7243) (x : State) (e : Event) (dr : Ring12) : tag.val = 7243 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07244 (tag : Fin 10000) (htag : tag.val = 7244) (x : State) (e : Event) (dr : Ring12) : tag.val = 7244 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07245 (tag : Fin 10000) (htag : tag.val = 7245) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7245 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07246 (tag : Fin 10000) (htag : tag.val = 7246) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7246 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07247 (tag : Fin 10000) (htag : tag.val = 7247) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7247 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07248 (tag : Fin 10000) (htag : tag.val = 7248) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7248 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07249 (tag : Fin 10000) (htag : tag.val = 7249) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7249 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07250 (tag : Fin 10000) (htag : tag.val = 7250) (k : Ring12) : tag.val = 7250 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07251 (tag : Fin 10000) (htag : tag.val = 7251) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7251 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07252 (tag : Fin 10000) (htag : tag.val = 7252) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7252 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07253 (tag : Fin 10000) (htag : tag.val = 7253) (x : State) (e : Event) (dr : Ring12) : tag.val = 7253 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07254 (tag : Fin 10000) (htag : tag.val = 7254) (x : State) (e : Event) (dr : Ring12) : tag.val = 7254 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07255 (tag : Fin 10000) (htag : tag.val = 7255) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7255 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07256 (tag : Fin 10000) (htag : tag.val = 7256) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7256 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07257 (tag : Fin 10000) (htag : tag.val = 7257) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7257 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07258 (tag : Fin 10000) (htag : tag.val = 7258) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7258 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07259 (tag : Fin 10000) (htag : tag.val = 7259) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7259 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07260 (tag : Fin 10000) (htag : tag.val = 7260) (k : Ring12) : tag.val = 7260 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07261 (tag : Fin 10000) (htag : tag.val = 7261) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7261 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07262 (tag : Fin 10000) (htag : tag.val = 7262) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7262 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07263 (tag : Fin 10000) (htag : tag.val = 7263) (x : State) (e : Event) (dr : Ring12) : tag.val = 7263 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07264 (tag : Fin 10000) (htag : tag.val = 7264) (x : State) (e : Event) (dr : Ring12) : tag.val = 7264 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07265 (tag : Fin 10000) (htag : tag.val = 7265) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7265 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07266 (tag : Fin 10000) (htag : tag.val = 7266) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7266 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07267 (tag : Fin 10000) (htag : tag.val = 7267) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7267 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07268 (tag : Fin 10000) (htag : tag.val = 7268) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7268 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07269 (tag : Fin 10000) (htag : tag.val = 7269) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7269 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07270 (tag : Fin 10000) (htag : tag.val = 7270) (k : Ring12) : tag.val = 7270 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07271 (tag : Fin 10000) (htag : tag.val = 7271) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7271 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07272 (tag : Fin 10000) (htag : tag.val = 7272) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7272 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07273 (tag : Fin 10000) (htag : tag.val = 7273) (x : State) (e : Event) (dr : Ring12) : tag.val = 7273 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07274 (tag : Fin 10000) (htag : tag.val = 7274) (x : State) (e : Event) (dr : Ring12) : tag.val = 7274 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07275 (tag : Fin 10000) (htag : tag.val = 7275) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7275 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07276 (tag : Fin 10000) (htag : tag.val = 7276) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7276 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07277 (tag : Fin 10000) (htag : tag.val = 7277) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7277 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07278 (tag : Fin 10000) (htag : tag.val = 7278) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7278 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07279 (tag : Fin 10000) (htag : tag.val = 7279) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7279 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07280 (tag : Fin 10000) (htag : tag.val = 7280) (k : Ring12) : tag.val = 7280 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07281 (tag : Fin 10000) (htag : tag.val = 7281) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7281 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07282 (tag : Fin 10000) (htag : tag.val = 7282) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7282 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07283 (tag : Fin 10000) (htag : tag.val = 7283) (x : State) (e : Event) (dr : Ring12) : tag.val = 7283 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07284 (tag : Fin 10000) (htag : tag.val = 7284) (x : State) (e : Event) (dr : Ring12) : tag.val = 7284 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07285 (tag : Fin 10000) (htag : tag.val = 7285) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7285 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07286 (tag : Fin 10000) (htag : tag.val = 7286) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7286 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07287 (tag : Fin 10000) (htag : tag.val = 7287) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7287 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07288 (tag : Fin 10000) (htag : tag.val = 7288) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7288 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07289 (tag : Fin 10000) (htag : tag.val = 7289) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7289 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07290 (tag : Fin 10000) (htag : tag.val = 7290) (k : Ring12) : tag.val = 7290 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07291 (tag : Fin 10000) (htag : tag.val = 7291) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7291 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07292 (tag : Fin 10000) (htag : tag.val = 7292) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7292 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07293 (tag : Fin 10000) (htag : tag.val = 7293) (x : State) (e : Event) (dr : Ring12) : tag.val = 7293 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07294 (tag : Fin 10000) (htag : tag.val = 7294) (x : State) (e : Event) (dr : Ring12) : tag.val = 7294 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07295 (tag : Fin 10000) (htag : tag.val = 7295) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7295 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07296 (tag : Fin 10000) (htag : tag.val = 7296) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7296 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07297 (tag : Fin 10000) (htag : tag.val = 7297) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7297 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07298 (tag : Fin 10000) (htag : tag.val = 7298) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7298 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07299 (tag : Fin 10000) (htag : tag.val = 7299) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7299 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
