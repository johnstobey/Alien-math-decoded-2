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
theorem generated_09300 (tag : Fin 10000) (htag : tag.val = 9300) (k : Ring12) : tag.val = 9300 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09301 (tag : Fin 10000) (htag : tag.val = 9301) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9301 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09302 (tag : Fin 10000) (htag : tag.val = 9302) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9302 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09303 (tag : Fin 10000) (htag : tag.val = 9303) (x : State) (e : Event) (dr : Ring12) : tag.val = 9303 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09304 (tag : Fin 10000) (htag : tag.val = 9304) (x : State) (e : Event) (dr : Ring12) : tag.val = 9304 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09305 (tag : Fin 10000) (htag : tag.val = 9305) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9305 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09306 (tag : Fin 10000) (htag : tag.val = 9306) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9306 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09307 (tag : Fin 10000) (htag : tag.val = 9307) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9307 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09308 (tag : Fin 10000) (htag : tag.val = 9308) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9308 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09309 (tag : Fin 10000) (htag : tag.val = 9309) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9309 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09310 (tag : Fin 10000) (htag : tag.val = 9310) (k : Ring12) : tag.val = 9310 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09311 (tag : Fin 10000) (htag : tag.val = 9311) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9311 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09312 (tag : Fin 10000) (htag : tag.val = 9312) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9312 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09313 (tag : Fin 10000) (htag : tag.val = 9313) (x : State) (e : Event) (dr : Ring12) : tag.val = 9313 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09314 (tag : Fin 10000) (htag : tag.val = 9314) (x : State) (e : Event) (dr : Ring12) : tag.val = 9314 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09315 (tag : Fin 10000) (htag : tag.val = 9315) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9315 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09316 (tag : Fin 10000) (htag : tag.val = 9316) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9316 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09317 (tag : Fin 10000) (htag : tag.val = 9317) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9317 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09318 (tag : Fin 10000) (htag : tag.val = 9318) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9318 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09319 (tag : Fin 10000) (htag : tag.val = 9319) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9319 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09320 (tag : Fin 10000) (htag : tag.val = 9320) (k : Ring12) : tag.val = 9320 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09321 (tag : Fin 10000) (htag : tag.val = 9321) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9321 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09322 (tag : Fin 10000) (htag : tag.val = 9322) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9322 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09323 (tag : Fin 10000) (htag : tag.val = 9323) (x : State) (e : Event) (dr : Ring12) : tag.val = 9323 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09324 (tag : Fin 10000) (htag : tag.val = 9324) (x : State) (e : Event) (dr : Ring12) : tag.val = 9324 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09325 (tag : Fin 10000) (htag : tag.val = 9325) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9325 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09326 (tag : Fin 10000) (htag : tag.val = 9326) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9326 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09327 (tag : Fin 10000) (htag : tag.val = 9327) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9327 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09328 (tag : Fin 10000) (htag : tag.val = 9328) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9328 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09329 (tag : Fin 10000) (htag : tag.val = 9329) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9329 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09330 (tag : Fin 10000) (htag : tag.val = 9330) (k : Ring12) : tag.val = 9330 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09331 (tag : Fin 10000) (htag : tag.val = 9331) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9331 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09332 (tag : Fin 10000) (htag : tag.val = 9332) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9332 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09333 (tag : Fin 10000) (htag : tag.val = 9333) (x : State) (e : Event) (dr : Ring12) : tag.val = 9333 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09334 (tag : Fin 10000) (htag : tag.val = 9334) (x : State) (e : Event) (dr : Ring12) : tag.val = 9334 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09335 (tag : Fin 10000) (htag : tag.val = 9335) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9335 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09336 (tag : Fin 10000) (htag : tag.val = 9336) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9336 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09337 (tag : Fin 10000) (htag : tag.val = 9337) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9337 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09338 (tag : Fin 10000) (htag : tag.val = 9338) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9338 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09339 (tag : Fin 10000) (htag : tag.val = 9339) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9339 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09340 (tag : Fin 10000) (htag : tag.val = 9340) (k : Ring12) : tag.val = 9340 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09341 (tag : Fin 10000) (htag : tag.val = 9341) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9341 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09342 (tag : Fin 10000) (htag : tag.val = 9342) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9342 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09343 (tag : Fin 10000) (htag : tag.val = 9343) (x : State) (e : Event) (dr : Ring12) : tag.val = 9343 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09344 (tag : Fin 10000) (htag : tag.val = 9344) (x : State) (e : Event) (dr : Ring12) : tag.val = 9344 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09345 (tag : Fin 10000) (htag : tag.val = 9345) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9345 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09346 (tag : Fin 10000) (htag : tag.val = 9346) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9346 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09347 (tag : Fin 10000) (htag : tag.val = 9347) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9347 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09348 (tag : Fin 10000) (htag : tag.val = 9348) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9348 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09349 (tag : Fin 10000) (htag : tag.val = 9349) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9349 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09350 (tag : Fin 10000) (htag : tag.val = 9350) (k : Ring12) : tag.val = 9350 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09351 (tag : Fin 10000) (htag : tag.val = 9351) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9351 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09352 (tag : Fin 10000) (htag : tag.val = 9352) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9352 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09353 (tag : Fin 10000) (htag : tag.val = 9353) (x : State) (e : Event) (dr : Ring12) : tag.val = 9353 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09354 (tag : Fin 10000) (htag : tag.val = 9354) (x : State) (e : Event) (dr : Ring12) : tag.val = 9354 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09355 (tag : Fin 10000) (htag : tag.val = 9355) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9355 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09356 (tag : Fin 10000) (htag : tag.val = 9356) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9356 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09357 (tag : Fin 10000) (htag : tag.val = 9357) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9357 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09358 (tag : Fin 10000) (htag : tag.val = 9358) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9358 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09359 (tag : Fin 10000) (htag : tag.val = 9359) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9359 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09360 (tag : Fin 10000) (htag : tag.val = 9360) (k : Ring12) : tag.val = 9360 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09361 (tag : Fin 10000) (htag : tag.val = 9361) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9361 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09362 (tag : Fin 10000) (htag : tag.val = 9362) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9362 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09363 (tag : Fin 10000) (htag : tag.val = 9363) (x : State) (e : Event) (dr : Ring12) : tag.val = 9363 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09364 (tag : Fin 10000) (htag : tag.val = 9364) (x : State) (e : Event) (dr : Ring12) : tag.val = 9364 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09365 (tag : Fin 10000) (htag : tag.val = 9365) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9365 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09366 (tag : Fin 10000) (htag : tag.val = 9366) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9366 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09367 (tag : Fin 10000) (htag : tag.val = 9367) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9367 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09368 (tag : Fin 10000) (htag : tag.val = 9368) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9368 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09369 (tag : Fin 10000) (htag : tag.val = 9369) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9369 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09370 (tag : Fin 10000) (htag : tag.val = 9370) (k : Ring12) : tag.val = 9370 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09371 (tag : Fin 10000) (htag : tag.val = 9371) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9371 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09372 (tag : Fin 10000) (htag : tag.val = 9372) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9372 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09373 (tag : Fin 10000) (htag : tag.val = 9373) (x : State) (e : Event) (dr : Ring12) : tag.val = 9373 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09374 (tag : Fin 10000) (htag : tag.val = 9374) (x : State) (e : Event) (dr : Ring12) : tag.val = 9374 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09375 (tag : Fin 10000) (htag : tag.val = 9375) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9375 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09376 (tag : Fin 10000) (htag : tag.val = 9376) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9376 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09377 (tag : Fin 10000) (htag : tag.val = 9377) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9377 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09378 (tag : Fin 10000) (htag : tag.val = 9378) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9378 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09379 (tag : Fin 10000) (htag : tag.val = 9379) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9379 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09380 (tag : Fin 10000) (htag : tag.val = 9380) (k : Ring12) : tag.val = 9380 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09381 (tag : Fin 10000) (htag : tag.val = 9381) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9381 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09382 (tag : Fin 10000) (htag : tag.val = 9382) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9382 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09383 (tag : Fin 10000) (htag : tag.val = 9383) (x : State) (e : Event) (dr : Ring12) : tag.val = 9383 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09384 (tag : Fin 10000) (htag : tag.val = 9384) (x : State) (e : Event) (dr : Ring12) : tag.val = 9384 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09385 (tag : Fin 10000) (htag : tag.val = 9385) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9385 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09386 (tag : Fin 10000) (htag : tag.val = 9386) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9386 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09387 (tag : Fin 10000) (htag : tag.val = 9387) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9387 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09388 (tag : Fin 10000) (htag : tag.val = 9388) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9388 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09389 (tag : Fin 10000) (htag : tag.val = 9389) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9389 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09390 (tag : Fin 10000) (htag : tag.val = 9390) (k : Ring12) : tag.val = 9390 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09391 (tag : Fin 10000) (htag : tag.val = 9391) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9391 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09392 (tag : Fin 10000) (htag : tag.val = 9392) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9392 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09393 (tag : Fin 10000) (htag : tag.val = 9393) (x : State) (e : Event) (dr : Ring12) : tag.val = 9393 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09394 (tag : Fin 10000) (htag : tag.val = 9394) (x : State) (e : Event) (dr : Ring12) : tag.val = 9394 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09395 (tag : Fin 10000) (htag : tag.val = 9395) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9395 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09396 (tag : Fin 10000) (htag : tag.val = 9396) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9396 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09397 (tag : Fin 10000) (htag : tag.val = 9397) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9397 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09398 (tag : Fin 10000) (htag : tag.val = 9398) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9398 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09399 (tag : Fin 10000) (htag : tag.val = 9399) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9399 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
