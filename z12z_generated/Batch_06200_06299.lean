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
theorem generated_06200 (tag : Fin 10000) (htag : tag.val = 6200) (k : Ring12) : tag.val = 6200 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06201 (tag : Fin 10000) (htag : tag.val = 6201) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6201 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06202 (tag : Fin 10000) (htag : tag.val = 6202) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6202 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06203 (tag : Fin 10000) (htag : tag.val = 6203) (x : State) (e : Event) (dr : Ring12) : tag.val = 6203 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06204 (tag : Fin 10000) (htag : tag.val = 6204) (x : State) (e : Event) (dr : Ring12) : tag.val = 6204 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06205 (tag : Fin 10000) (htag : tag.val = 6205) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6205 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06206 (tag : Fin 10000) (htag : tag.val = 6206) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6206 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06207 (tag : Fin 10000) (htag : tag.val = 6207) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6207 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06208 (tag : Fin 10000) (htag : tag.val = 6208) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6208 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06209 (tag : Fin 10000) (htag : tag.val = 6209) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6209 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06210 (tag : Fin 10000) (htag : tag.val = 6210) (k : Ring12) : tag.val = 6210 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06211 (tag : Fin 10000) (htag : tag.val = 6211) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6211 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06212 (tag : Fin 10000) (htag : tag.val = 6212) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6212 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06213 (tag : Fin 10000) (htag : tag.val = 6213) (x : State) (e : Event) (dr : Ring12) : tag.val = 6213 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06214 (tag : Fin 10000) (htag : tag.val = 6214) (x : State) (e : Event) (dr : Ring12) : tag.val = 6214 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06215 (tag : Fin 10000) (htag : tag.val = 6215) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6215 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06216 (tag : Fin 10000) (htag : tag.val = 6216) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6216 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06217 (tag : Fin 10000) (htag : tag.val = 6217) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6217 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06218 (tag : Fin 10000) (htag : tag.val = 6218) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6218 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06219 (tag : Fin 10000) (htag : tag.val = 6219) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6219 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06220 (tag : Fin 10000) (htag : tag.val = 6220) (k : Ring12) : tag.val = 6220 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06221 (tag : Fin 10000) (htag : tag.val = 6221) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6221 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06222 (tag : Fin 10000) (htag : tag.val = 6222) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6222 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06223 (tag : Fin 10000) (htag : tag.val = 6223) (x : State) (e : Event) (dr : Ring12) : tag.val = 6223 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06224 (tag : Fin 10000) (htag : tag.val = 6224) (x : State) (e : Event) (dr : Ring12) : tag.val = 6224 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06225 (tag : Fin 10000) (htag : tag.val = 6225) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6225 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06226 (tag : Fin 10000) (htag : tag.val = 6226) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6226 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06227 (tag : Fin 10000) (htag : tag.val = 6227) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6227 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06228 (tag : Fin 10000) (htag : tag.val = 6228) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6228 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06229 (tag : Fin 10000) (htag : tag.val = 6229) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6229 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06230 (tag : Fin 10000) (htag : tag.val = 6230) (k : Ring12) : tag.val = 6230 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06231 (tag : Fin 10000) (htag : tag.val = 6231) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6231 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06232 (tag : Fin 10000) (htag : tag.val = 6232) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6232 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06233 (tag : Fin 10000) (htag : tag.val = 6233) (x : State) (e : Event) (dr : Ring12) : tag.val = 6233 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06234 (tag : Fin 10000) (htag : tag.val = 6234) (x : State) (e : Event) (dr : Ring12) : tag.val = 6234 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06235 (tag : Fin 10000) (htag : tag.val = 6235) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6235 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06236 (tag : Fin 10000) (htag : tag.val = 6236) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6236 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06237 (tag : Fin 10000) (htag : tag.val = 6237) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6237 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06238 (tag : Fin 10000) (htag : tag.val = 6238) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6238 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06239 (tag : Fin 10000) (htag : tag.val = 6239) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6239 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06240 (tag : Fin 10000) (htag : tag.val = 6240) (k : Ring12) : tag.val = 6240 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06241 (tag : Fin 10000) (htag : tag.val = 6241) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6241 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06242 (tag : Fin 10000) (htag : tag.val = 6242) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6242 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06243 (tag : Fin 10000) (htag : tag.val = 6243) (x : State) (e : Event) (dr : Ring12) : tag.val = 6243 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06244 (tag : Fin 10000) (htag : tag.val = 6244) (x : State) (e : Event) (dr : Ring12) : tag.val = 6244 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06245 (tag : Fin 10000) (htag : tag.val = 6245) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6245 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06246 (tag : Fin 10000) (htag : tag.val = 6246) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6246 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06247 (tag : Fin 10000) (htag : tag.val = 6247) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6247 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06248 (tag : Fin 10000) (htag : tag.val = 6248) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6248 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06249 (tag : Fin 10000) (htag : tag.val = 6249) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6249 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06250 (tag : Fin 10000) (htag : tag.val = 6250) (k : Ring12) : tag.val = 6250 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06251 (tag : Fin 10000) (htag : tag.val = 6251) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6251 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06252 (tag : Fin 10000) (htag : tag.val = 6252) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6252 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06253 (tag : Fin 10000) (htag : tag.val = 6253) (x : State) (e : Event) (dr : Ring12) : tag.val = 6253 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06254 (tag : Fin 10000) (htag : tag.val = 6254) (x : State) (e : Event) (dr : Ring12) : tag.val = 6254 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06255 (tag : Fin 10000) (htag : tag.val = 6255) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6255 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06256 (tag : Fin 10000) (htag : tag.val = 6256) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6256 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06257 (tag : Fin 10000) (htag : tag.val = 6257) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6257 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06258 (tag : Fin 10000) (htag : tag.val = 6258) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6258 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06259 (tag : Fin 10000) (htag : tag.val = 6259) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6259 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06260 (tag : Fin 10000) (htag : tag.val = 6260) (k : Ring12) : tag.val = 6260 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06261 (tag : Fin 10000) (htag : tag.val = 6261) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6261 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06262 (tag : Fin 10000) (htag : tag.val = 6262) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6262 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06263 (tag : Fin 10000) (htag : tag.val = 6263) (x : State) (e : Event) (dr : Ring12) : tag.val = 6263 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06264 (tag : Fin 10000) (htag : tag.val = 6264) (x : State) (e : Event) (dr : Ring12) : tag.val = 6264 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06265 (tag : Fin 10000) (htag : tag.val = 6265) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6265 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06266 (tag : Fin 10000) (htag : tag.val = 6266) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6266 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06267 (tag : Fin 10000) (htag : tag.val = 6267) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6267 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06268 (tag : Fin 10000) (htag : tag.val = 6268) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6268 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06269 (tag : Fin 10000) (htag : tag.val = 6269) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6269 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06270 (tag : Fin 10000) (htag : tag.val = 6270) (k : Ring12) : tag.val = 6270 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06271 (tag : Fin 10000) (htag : tag.val = 6271) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6271 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06272 (tag : Fin 10000) (htag : tag.val = 6272) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6272 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06273 (tag : Fin 10000) (htag : tag.val = 6273) (x : State) (e : Event) (dr : Ring12) : tag.val = 6273 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06274 (tag : Fin 10000) (htag : tag.val = 6274) (x : State) (e : Event) (dr : Ring12) : tag.val = 6274 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06275 (tag : Fin 10000) (htag : tag.val = 6275) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6275 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06276 (tag : Fin 10000) (htag : tag.val = 6276) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6276 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06277 (tag : Fin 10000) (htag : tag.val = 6277) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6277 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06278 (tag : Fin 10000) (htag : tag.val = 6278) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6278 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06279 (tag : Fin 10000) (htag : tag.val = 6279) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6279 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06280 (tag : Fin 10000) (htag : tag.val = 6280) (k : Ring12) : tag.val = 6280 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06281 (tag : Fin 10000) (htag : tag.val = 6281) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6281 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06282 (tag : Fin 10000) (htag : tag.val = 6282) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6282 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06283 (tag : Fin 10000) (htag : tag.val = 6283) (x : State) (e : Event) (dr : Ring12) : tag.val = 6283 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06284 (tag : Fin 10000) (htag : tag.val = 6284) (x : State) (e : Event) (dr : Ring12) : tag.val = 6284 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06285 (tag : Fin 10000) (htag : tag.val = 6285) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6285 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06286 (tag : Fin 10000) (htag : tag.val = 6286) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6286 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06287 (tag : Fin 10000) (htag : tag.val = 6287) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6287 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06288 (tag : Fin 10000) (htag : tag.val = 6288) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6288 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06289 (tag : Fin 10000) (htag : tag.val = 6289) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6289 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06290 (tag : Fin 10000) (htag : tag.val = 6290) (k : Ring12) : tag.val = 6290 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06291 (tag : Fin 10000) (htag : tag.val = 6291) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6291 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06292 (tag : Fin 10000) (htag : tag.val = 6292) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6292 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06293 (tag : Fin 10000) (htag : tag.val = 6293) (x : State) (e : Event) (dr : Ring12) : tag.val = 6293 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06294 (tag : Fin 10000) (htag : tag.val = 6294) (x : State) (e : Event) (dr : Ring12) : tag.val = 6294 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06295 (tag : Fin 10000) (htag : tag.val = 6295) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6295 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06296 (tag : Fin 10000) (htag : tag.val = 6296) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6296 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06297 (tag : Fin 10000) (htag : tag.val = 6297) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6297 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06298 (tag : Fin 10000) (htag : tag.val = 6298) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6298 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06299 (tag : Fin 10000) (htag : tag.val = 6299) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6299 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
