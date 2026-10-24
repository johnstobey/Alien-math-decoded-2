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
theorem generated_08300 (tag : Fin 10000) (htag : tag.val = 8300) (k : Ring12) : tag.val = 8300 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08301 (tag : Fin 10000) (htag : tag.val = 8301) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8301 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08302 (tag : Fin 10000) (htag : tag.val = 8302) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8302 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08303 (tag : Fin 10000) (htag : tag.val = 8303) (x : State) (e : Event) (dr : Ring12) : tag.val = 8303 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08304 (tag : Fin 10000) (htag : tag.val = 8304) (x : State) (e : Event) (dr : Ring12) : tag.val = 8304 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08305 (tag : Fin 10000) (htag : tag.val = 8305) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8305 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08306 (tag : Fin 10000) (htag : tag.val = 8306) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8306 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08307 (tag : Fin 10000) (htag : tag.val = 8307) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8307 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08308 (tag : Fin 10000) (htag : tag.val = 8308) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8308 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08309 (tag : Fin 10000) (htag : tag.val = 8309) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8309 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08310 (tag : Fin 10000) (htag : tag.val = 8310) (k : Ring12) : tag.val = 8310 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08311 (tag : Fin 10000) (htag : tag.val = 8311) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8311 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08312 (tag : Fin 10000) (htag : tag.val = 8312) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8312 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08313 (tag : Fin 10000) (htag : tag.val = 8313) (x : State) (e : Event) (dr : Ring12) : tag.val = 8313 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08314 (tag : Fin 10000) (htag : tag.val = 8314) (x : State) (e : Event) (dr : Ring12) : tag.val = 8314 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08315 (tag : Fin 10000) (htag : tag.val = 8315) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8315 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08316 (tag : Fin 10000) (htag : tag.val = 8316) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8316 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08317 (tag : Fin 10000) (htag : tag.val = 8317) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8317 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08318 (tag : Fin 10000) (htag : tag.val = 8318) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8318 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08319 (tag : Fin 10000) (htag : tag.val = 8319) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8319 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08320 (tag : Fin 10000) (htag : tag.val = 8320) (k : Ring12) : tag.val = 8320 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08321 (tag : Fin 10000) (htag : tag.val = 8321) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8321 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08322 (tag : Fin 10000) (htag : tag.val = 8322) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8322 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08323 (tag : Fin 10000) (htag : tag.val = 8323) (x : State) (e : Event) (dr : Ring12) : tag.val = 8323 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08324 (tag : Fin 10000) (htag : tag.val = 8324) (x : State) (e : Event) (dr : Ring12) : tag.val = 8324 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08325 (tag : Fin 10000) (htag : tag.val = 8325) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8325 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08326 (tag : Fin 10000) (htag : tag.val = 8326) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8326 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08327 (tag : Fin 10000) (htag : tag.val = 8327) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8327 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08328 (tag : Fin 10000) (htag : tag.val = 8328) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8328 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08329 (tag : Fin 10000) (htag : tag.val = 8329) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8329 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08330 (tag : Fin 10000) (htag : tag.val = 8330) (k : Ring12) : tag.val = 8330 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08331 (tag : Fin 10000) (htag : tag.val = 8331) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8331 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08332 (tag : Fin 10000) (htag : tag.val = 8332) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8332 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08333 (tag : Fin 10000) (htag : tag.val = 8333) (x : State) (e : Event) (dr : Ring12) : tag.val = 8333 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08334 (tag : Fin 10000) (htag : tag.val = 8334) (x : State) (e : Event) (dr : Ring12) : tag.val = 8334 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08335 (tag : Fin 10000) (htag : tag.val = 8335) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8335 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08336 (tag : Fin 10000) (htag : tag.val = 8336) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8336 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08337 (tag : Fin 10000) (htag : tag.val = 8337) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8337 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08338 (tag : Fin 10000) (htag : tag.val = 8338) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8338 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08339 (tag : Fin 10000) (htag : tag.val = 8339) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8339 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08340 (tag : Fin 10000) (htag : tag.val = 8340) (k : Ring12) : tag.val = 8340 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08341 (tag : Fin 10000) (htag : tag.val = 8341) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8341 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08342 (tag : Fin 10000) (htag : tag.val = 8342) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8342 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08343 (tag : Fin 10000) (htag : tag.val = 8343) (x : State) (e : Event) (dr : Ring12) : tag.val = 8343 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08344 (tag : Fin 10000) (htag : tag.val = 8344) (x : State) (e : Event) (dr : Ring12) : tag.val = 8344 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08345 (tag : Fin 10000) (htag : tag.val = 8345) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8345 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08346 (tag : Fin 10000) (htag : tag.val = 8346) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8346 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08347 (tag : Fin 10000) (htag : tag.val = 8347) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8347 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08348 (tag : Fin 10000) (htag : tag.val = 8348) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8348 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08349 (tag : Fin 10000) (htag : tag.val = 8349) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8349 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08350 (tag : Fin 10000) (htag : tag.val = 8350) (k : Ring12) : tag.val = 8350 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08351 (tag : Fin 10000) (htag : tag.val = 8351) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8351 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08352 (tag : Fin 10000) (htag : tag.val = 8352) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8352 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08353 (tag : Fin 10000) (htag : tag.val = 8353) (x : State) (e : Event) (dr : Ring12) : tag.val = 8353 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08354 (tag : Fin 10000) (htag : tag.val = 8354) (x : State) (e : Event) (dr : Ring12) : tag.val = 8354 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08355 (tag : Fin 10000) (htag : tag.val = 8355) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8355 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08356 (tag : Fin 10000) (htag : tag.val = 8356) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8356 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08357 (tag : Fin 10000) (htag : tag.val = 8357) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8357 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08358 (tag : Fin 10000) (htag : tag.val = 8358) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8358 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08359 (tag : Fin 10000) (htag : tag.val = 8359) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8359 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08360 (tag : Fin 10000) (htag : tag.val = 8360) (k : Ring12) : tag.val = 8360 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08361 (tag : Fin 10000) (htag : tag.val = 8361) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8361 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08362 (tag : Fin 10000) (htag : tag.val = 8362) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8362 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08363 (tag : Fin 10000) (htag : tag.val = 8363) (x : State) (e : Event) (dr : Ring12) : tag.val = 8363 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08364 (tag : Fin 10000) (htag : tag.val = 8364) (x : State) (e : Event) (dr : Ring12) : tag.val = 8364 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08365 (tag : Fin 10000) (htag : tag.val = 8365) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8365 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08366 (tag : Fin 10000) (htag : tag.val = 8366) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8366 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08367 (tag : Fin 10000) (htag : tag.val = 8367) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8367 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08368 (tag : Fin 10000) (htag : tag.val = 8368) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8368 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08369 (tag : Fin 10000) (htag : tag.val = 8369) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8369 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08370 (tag : Fin 10000) (htag : tag.val = 8370) (k : Ring12) : tag.val = 8370 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08371 (tag : Fin 10000) (htag : tag.val = 8371) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8371 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08372 (tag : Fin 10000) (htag : tag.val = 8372) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8372 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08373 (tag : Fin 10000) (htag : tag.val = 8373) (x : State) (e : Event) (dr : Ring12) : tag.val = 8373 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08374 (tag : Fin 10000) (htag : tag.val = 8374) (x : State) (e : Event) (dr : Ring12) : tag.val = 8374 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08375 (tag : Fin 10000) (htag : tag.val = 8375) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8375 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08376 (tag : Fin 10000) (htag : tag.val = 8376) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8376 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08377 (tag : Fin 10000) (htag : tag.val = 8377) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8377 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08378 (tag : Fin 10000) (htag : tag.val = 8378) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8378 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08379 (tag : Fin 10000) (htag : tag.val = 8379) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8379 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08380 (tag : Fin 10000) (htag : tag.val = 8380) (k : Ring12) : tag.val = 8380 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08381 (tag : Fin 10000) (htag : tag.val = 8381) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8381 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08382 (tag : Fin 10000) (htag : tag.val = 8382) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8382 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08383 (tag : Fin 10000) (htag : tag.val = 8383) (x : State) (e : Event) (dr : Ring12) : tag.val = 8383 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08384 (tag : Fin 10000) (htag : tag.val = 8384) (x : State) (e : Event) (dr : Ring12) : tag.val = 8384 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08385 (tag : Fin 10000) (htag : tag.val = 8385) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8385 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08386 (tag : Fin 10000) (htag : tag.val = 8386) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8386 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08387 (tag : Fin 10000) (htag : tag.val = 8387) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8387 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08388 (tag : Fin 10000) (htag : tag.val = 8388) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8388 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08389 (tag : Fin 10000) (htag : tag.val = 8389) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8389 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08390 (tag : Fin 10000) (htag : tag.val = 8390) (k : Ring12) : tag.val = 8390 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08391 (tag : Fin 10000) (htag : tag.val = 8391) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8391 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08392 (tag : Fin 10000) (htag : tag.val = 8392) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8392 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08393 (tag : Fin 10000) (htag : tag.val = 8393) (x : State) (e : Event) (dr : Ring12) : tag.val = 8393 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08394 (tag : Fin 10000) (htag : tag.val = 8394) (x : State) (e : Event) (dr : Ring12) : tag.val = 8394 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08395 (tag : Fin 10000) (htag : tag.val = 8395) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8395 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08396 (tag : Fin 10000) (htag : tag.val = 8396) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8396 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08397 (tag : Fin 10000) (htag : tag.val = 8397) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8397 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08398 (tag : Fin 10000) (htag : tag.val = 8398) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8398 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08399 (tag : Fin 10000) (htag : tag.val = 8399) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8399 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
