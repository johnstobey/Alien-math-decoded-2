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
theorem generated_09200 (tag : Fin 10000) (htag : tag.val = 9200) (k : Ring12) : tag.val = 9200 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09201 (tag : Fin 10000) (htag : tag.val = 9201) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9201 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09202 (tag : Fin 10000) (htag : tag.val = 9202) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9202 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09203 (tag : Fin 10000) (htag : tag.val = 9203) (x : State) (e : Event) (dr : Ring12) : tag.val = 9203 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09204 (tag : Fin 10000) (htag : tag.val = 9204) (x : State) (e : Event) (dr : Ring12) : tag.val = 9204 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09205 (tag : Fin 10000) (htag : tag.val = 9205) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9205 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09206 (tag : Fin 10000) (htag : tag.val = 9206) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9206 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09207 (tag : Fin 10000) (htag : tag.val = 9207) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9207 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09208 (tag : Fin 10000) (htag : tag.val = 9208) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9208 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09209 (tag : Fin 10000) (htag : tag.val = 9209) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9209 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09210 (tag : Fin 10000) (htag : tag.val = 9210) (k : Ring12) : tag.val = 9210 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09211 (tag : Fin 10000) (htag : tag.val = 9211) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9211 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09212 (tag : Fin 10000) (htag : tag.val = 9212) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9212 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09213 (tag : Fin 10000) (htag : tag.val = 9213) (x : State) (e : Event) (dr : Ring12) : tag.val = 9213 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09214 (tag : Fin 10000) (htag : tag.val = 9214) (x : State) (e : Event) (dr : Ring12) : tag.val = 9214 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09215 (tag : Fin 10000) (htag : tag.val = 9215) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9215 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09216 (tag : Fin 10000) (htag : tag.val = 9216) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9216 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09217 (tag : Fin 10000) (htag : tag.val = 9217) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9217 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09218 (tag : Fin 10000) (htag : tag.val = 9218) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9218 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09219 (tag : Fin 10000) (htag : tag.val = 9219) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9219 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09220 (tag : Fin 10000) (htag : tag.val = 9220) (k : Ring12) : tag.val = 9220 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09221 (tag : Fin 10000) (htag : tag.val = 9221) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9221 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09222 (tag : Fin 10000) (htag : tag.val = 9222) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9222 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09223 (tag : Fin 10000) (htag : tag.val = 9223) (x : State) (e : Event) (dr : Ring12) : tag.val = 9223 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09224 (tag : Fin 10000) (htag : tag.val = 9224) (x : State) (e : Event) (dr : Ring12) : tag.val = 9224 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09225 (tag : Fin 10000) (htag : tag.val = 9225) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9225 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09226 (tag : Fin 10000) (htag : tag.val = 9226) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9226 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09227 (tag : Fin 10000) (htag : tag.val = 9227) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9227 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09228 (tag : Fin 10000) (htag : tag.val = 9228) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9228 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09229 (tag : Fin 10000) (htag : tag.val = 9229) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9229 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09230 (tag : Fin 10000) (htag : tag.val = 9230) (k : Ring12) : tag.val = 9230 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09231 (tag : Fin 10000) (htag : tag.val = 9231) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9231 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09232 (tag : Fin 10000) (htag : tag.val = 9232) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9232 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09233 (tag : Fin 10000) (htag : tag.val = 9233) (x : State) (e : Event) (dr : Ring12) : tag.val = 9233 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09234 (tag : Fin 10000) (htag : tag.val = 9234) (x : State) (e : Event) (dr : Ring12) : tag.val = 9234 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09235 (tag : Fin 10000) (htag : tag.val = 9235) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9235 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09236 (tag : Fin 10000) (htag : tag.val = 9236) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9236 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09237 (tag : Fin 10000) (htag : tag.val = 9237) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9237 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09238 (tag : Fin 10000) (htag : tag.val = 9238) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9238 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09239 (tag : Fin 10000) (htag : tag.val = 9239) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9239 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09240 (tag : Fin 10000) (htag : tag.val = 9240) (k : Ring12) : tag.val = 9240 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09241 (tag : Fin 10000) (htag : tag.val = 9241) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9241 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09242 (tag : Fin 10000) (htag : tag.val = 9242) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9242 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09243 (tag : Fin 10000) (htag : tag.val = 9243) (x : State) (e : Event) (dr : Ring12) : tag.val = 9243 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09244 (tag : Fin 10000) (htag : tag.val = 9244) (x : State) (e : Event) (dr : Ring12) : tag.val = 9244 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09245 (tag : Fin 10000) (htag : tag.val = 9245) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9245 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09246 (tag : Fin 10000) (htag : tag.val = 9246) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9246 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09247 (tag : Fin 10000) (htag : tag.val = 9247) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9247 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09248 (tag : Fin 10000) (htag : tag.val = 9248) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9248 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09249 (tag : Fin 10000) (htag : tag.val = 9249) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9249 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09250 (tag : Fin 10000) (htag : tag.val = 9250) (k : Ring12) : tag.val = 9250 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09251 (tag : Fin 10000) (htag : tag.val = 9251) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9251 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09252 (tag : Fin 10000) (htag : tag.val = 9252) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9252 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09253 (tag : Fin 10000) (htag : tag.val = 9253) (x : State) (e : Event) (dr : Ring12) : tag.val = 9253 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09254 (tag : Fin 10000) (htag : tag.val = 9254) (x : State) (e : Event) (dr : Ring12) : tag.val = 9254 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09255 (tag : Fin 10000) (htag : tag.val = 9255) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9255 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09256 (tag : Fin 10000) (htag : tag.val = 9256) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9256 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09257 (tag : Fin 10000) (htag : tag.val = 9257) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9257 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09258 (tag : Fin 10000) (htag : tag.val = 9258) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9258 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09259 (tag : Fin 10000) (htag : tag.val = 9259) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9259 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09260 (tag : Fin 10000) (htag : tag.val = 9260) (k : Ring12) : tag.val = 9260 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09261 (tag : Fin 10000) (htag : tag.val = 9261) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9261 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09262 (tag : Fin 10000) (htag : tag.val = 9262) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9262 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09263 (tag : Fin 10000) (htag : tag.val = 9263) (x : State) (e : Event) (dr : Ring12) : tag.val = 9263 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09264 (tag : Fin 10000) (htag : tag.val = 9264) (x : State) (e : Event) (dr : Ring12) : tag.val = 9264 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09265 (tag : Fin 10000) (htag : tag.val = 9265) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9265 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09266 (tag : Fin 10000) (htag : tag.val = 9266) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9266 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09267 (tag : Fin 10000) (htag : tag.val = 9267) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9267 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09268 (tag : Fin 10000) (htag : tag.val = 9268) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9268 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09269 (tag : Fin 10000) (htag : tag.val = 9269) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9269 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09270 (tag : Fin 10000) (htag : tag.val = 9270) (k : Ring12) : tag.val = 9270 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09271 (tag : Fin 10000) (htag : tag.val = 9271) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9271 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09272 (tag : Fin 10000) (htag : tag.val = 9272) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9272 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09273 (tag : Fin 10000) (htag : tag.val = 9273) (x : State) (e : Event) (dr : Ring12) : tag.val = 9273 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09274 (tag : Fin 10000) (htag : tag.val = 9274) (x : State) (e : Event) (dr : Ring12) : tag.val = 9274 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09275 (tag : Fin 10000) (htag : tag.val = 9275) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9275 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09276 (tag : Fin 10000) (htag : tag.val = 9276) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9276 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09277 (tag : Fin 10000) (htag : tag.val = 9277) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9277 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09278 (tag : Fin 10000) (htag : tag.val = 9278) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9278 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09279 (tag : Fin 10000) (htag : tag.val = 9279) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9279 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09280 (tag : Fin 10000) (htag : tag.val = 9280) (k : Ring12) : tag.val = 9280 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09281 (tag : Fin 10000) (htag : tag.val = 9281) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9281 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09282 (tag : Fin 10000) (htag : tag.val = 9282) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9282 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09283 (tag : Fin 10000) (htag : tag.val = 9283) (x : State) (e : Event) (dr : Ring12) : tag.val = 9283 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09284 (tag : Fin 10000) (htag : tag.val = 9284) (x : State) (e : Event) (dr : Ring12) : tag.val = 9284 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09285 (tag : Fin 10000) (htag : tag.val = 9285) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9285 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09286 (tag : Fin 10000) (htag : tag.val = 9286) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9286 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09287 (tag : Fin 10000) (htag : tag.val = 9287) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9287 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09288 (tag : Fin 10000) (htag : tag.val = 9288) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9288 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09289 (tag : Fin 10000) (htag : tag.val = 9289) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9289 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09290 (tag : Fin 10000) (htag : tag.val = 9290) (k : Ring12) : tag.val = 9290 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09291 (tag : Fin 10000) (htag : tag.val = 9291) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9291 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09292 (tag : Fin 10000) (htag : tag.val = 9292) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9292 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09293 (tag : Fin 10000) (htag : tag.val = 9293) (x : State) (e : Event) (dr : Ring12) : tag.val = 9293 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09294 (tag : Fin 10000) (htag : tag.val = 9294) (x : State) (e : Event) (dr : Ring12) : tag.val = 9294 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09295 (tag : Fin 10000) (htag : tag.val = 9295) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9295 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09296 (tag : Fin 10000) (htag : tag.val = 9296) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9296 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09297 (tag : Fin 10000) (htag : tag.val = 9297) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9297 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09298 (tag : Fin 10000) (htag : tag.val = 9298) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9298 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09299 (tag : Fin 10000) (htag : tag.val = 9299) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9299 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
