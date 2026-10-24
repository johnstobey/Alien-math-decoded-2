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
theorem generated_03300 (tag : Fin 10000) (htag : tag.val = 3300) (k : Ring12) : tag.val = 3300 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03301 (tag : Fin 10000) (htag : tag.val = 3301) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3301 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03302 (tag : Fin 10000) (htag : tag.val = 3302) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3302 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03303 (tag : Fin 10000) (htag : tag.val = 3303) (x : State) (e : Event) (dr : Ring12) : tag.val = 3303 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03304 (tag : Fin 10000) (htag : tag.val = 3304) (x : State) (e : Event) (dr : Ring12) : tag.val = 3304 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03305 (tag : Fin 10000) (htag : tag.val = 3305) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3305 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03306 (tag : Fin 10000) (htag : tag.val = 3306) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3306 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03307 (tag : Fin 10000) (htag : tag.val = 3307) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3307 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03308 (tag : Fin 10000) (htag : tag.val = 3308) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3308 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03309 (tag : Fin 10000) (htag : tag.val = 3309) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3309 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03310 (tag : Fin 10000) (htag : tag.val = 3310) (k : Ring12) : tag.val = 3310 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03311 (tag : Fin 10000) (htag : tag.val = 3311) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3311 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03312 (tag : Fin 10000) (htag : tag.val = 3312) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3312 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03313 (tag : Fin 10000) (htag : tag.val = 3313) (x : State) (e : Event) (dr : Ring12) : tag.val = 3313 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03314 (tag : Fin 10000) (htag : tag.val = 3314) (x : State) (e : Event) (dr : Ring12) : tag.val = 3314 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03315 (tag : Fin 10000) (htag : tag.val = 3315) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3315 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03316 (tag : Fin 10000) (htag : tag.val = 3316) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3316 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03317 (tag : Fin 10000) (htag : tag.val = 3317) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3317 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03318 (tag : Fin 10000) (htag : tag.val = 3318) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3318 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03319 (tag : Fin 10000) (htag : tag.val = 3319) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3319 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03320 (tag : Fin 10000) (htag : tag.val = 3320) (k : Ring12) : tag.val = 3320 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03321 (tag : Fin 10000) (htag : tag.val = 3321) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3321 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03322 (tag : Fin 10000) (htag : tag.val = 3322) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3322 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03323 (tag : Fin 10000) (htag : tag.val = 3323) (x : State) (e : Event) (dr : Ring12) : tag.val = 3323 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03324 (tag : Fin 10000) (htag : tag.val = 3324) (x : State) (e : Event) (dr : Ring12) : tag.val = 3324 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03325 (tag : Fin 10000) (htag : tag.val = 3325) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3325 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03326 (tag : Fin 10000) (htag : tag.val = 3326) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3326 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03327 (tag : Fin 10000) (htag : tag.val = 3327) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3327 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03328 (tag : Fin 10000) (htag : tag.val = 3328) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3328 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03329 (tag : Fin 10000) (htag : tag.val = 3329) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3329 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03330 (tag : Fin 10000) (htag : tag.val = 3330) (k : Ring12) : tag.val = 3330 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03331 (tag : Fin 10000) (htag : tag.val = 3331) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3331 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03332 (tag : Fin 10000) (htag : tag.val = 3332) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3332 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03333 (tag : Fin 10000) (htag : tag.val = 3333) (x : State) (e : Event) (dr : Ring12) : tag.val = 3333 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03334 (tag : Fin 10000) (htag : tag.val = 3334) (x : State) (e : Event) (dr : Ring12) : tag.val = 3334 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03335 (tag : Fin 10000) (htag : tag.val = 3335) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3335 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03336 (tag : Fin 10000) (htag : tag.val = 3336) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3336 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03337 (tag : Fin 10000) (htag : tag.val = 3337) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3337 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03338 (tag : Fin 10000) (htag : tag.val = 3338) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3338 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03339 (tag : Fin 10000) (htag : tag.val = 3339) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3339 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03340 (tag : Fin 10000) (htag : tag.val = 3340) (k : Ring12) : tag.val = 3340 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03341 (tag : Fin 10000) (htag : tag.val = 3341) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3341 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03342 (tag : Fin 10000) (htag : tag.val = 3342) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3342 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03343 (tag : Fin 10000) (htag : tag.val = 3343) (x : State) (e : Event) (dr : Ring12) : tag.val = 3343 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03344 (tag : Fin 10000) (htag : tag.val = 3344) (x : State) (e : Event) (dr : Ring12) : tag.val = 3344 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03345 (tag : Fin 10000) (htag : tag.val = 3345) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3345 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03346 (tag : Fin 10000) (htag : tag.val = 3346) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3346 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03347 (tag : Fin 10000) (htag : tag.val = 3347) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3347 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03348 (tag : Fin 10000) (htag : tag.val = 3348) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3348 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03349 (tag : Fin 10000) (htag : tag.val = 3349) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3349 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03350 (tag : Fin 10000) (htag : tag.val = 3350) (k : Ring12) : tag.val = 3350 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03351 (tag : Fin 10000) (htag : tag.val = 3351) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3351 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03352 (tag : Fin 10000) (htag : tag.val = 3352) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3352 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03353 (tag : Fin 10000) (htag : tag.val = 3353) (x : State) (e : Event) (dr : Ring12) : tag.val = 3353 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03354 (tag : Fin 10000) (htag : tag.val = 3354) (x : State) (e : Event) (dr : Ring12) : tag.val = 3354 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03355 (tag : Fin 10000) (htag : tag.val = 3355) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3355 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03356 (tag : Fin 10000) (htag : tag.val = 3356) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3356 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03357 (tag : Fin 10000) (htag : tag.val = 3357) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3357 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03358 (tag : Fin 10000) (htag : tag.val = 3358) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3358 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03359 (tag : Fin 10000) (htag : tag.val = 3359) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3359 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03360 (tag : Fin 10000) (htag : tag.val = 3360) (k : Ring12) : tag.val = 3360 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03361 (tag : Fin 10000) (htag : tag.val = 3361) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3361 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03362 (tag : Fin 10000) (htag : tag.val = 3362) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3362 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03363 (tag : Fin 10000) (htag : tag.val = 3363) (x : State) (e : Event) (dr : Ring12) : tag.val = 3363 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03364 (tag : Fin 10000) (htag : tag.val = 3364) (x : State) (e : Event) (dr : Ring12) : tag.val = 3364 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03365 (tag : Fin 10000) (htag : tag.val = 3365) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3365 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03366 (tag : Fin 10000) (htag : tag.val = 3366) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3366 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03367 (tag : Fin 10000) (htag : tag.val = 3367) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3367 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03368 (tag : Fin 10000) (htag : tag.val = 3368) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3368 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03369 (tag : Fin 10000) (htag : tag.val = 3369) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3369 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03370 (tag : Fin 10000) (htag : tag.val = 3370) (k : Ring12) : tag.val = 3370 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03371 (tag : Fin 10000) (htag : tag.val = 3371) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3371 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03372 (tag : Fin 10000) (htag : tag.val = 3372) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3372 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03373 (tag : Fin 10000) (htag : tag.val = 3373) (x : State) (e : Event) (dr : Ring12) : tag.val = 3373 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03374 (tag : Fin 10000) (htag : tag.val = 3374) (x : State) (e : Event) (dr : Ring12) : tag.val = 3374 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03375 (tag : Fin 10000) (htag : tag.val = 3375) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3375 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03376 (tag : Fin 10000) (htag : tag.val = 3376) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3376 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03377 (tag : Fin 10000) (htag : tag.val = 3377) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3377 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03378 (tag : Fin 10000) (htag : tag.val = 3378) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3378 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03379 (tag : Fin 10000) (htag : tag.val = 3379) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3379 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03380 (tag : Fin 10000) (htag : tag.val = 3380) (k : Ring12) : tag.val = 3380 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03381 (tag : Fin 10000) (htag : tag.val = 3381) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3381 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03382 (tag : Fin 10000) (htag : tag.val = 3382) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3382 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03383 (tag : Fin 10000) (htag : tag.val = 3383) (x : State) (e : Event) (dr : Ring12) : tag.val = 3383 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03384 (tag : Fin 10000) (htag : tag.val = 3384) (x : State) (e : Event) (dr : Ring12) : tag.val = 3384 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03385 (tag : Fin 10000) (htag : tag.val = 3385) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3385 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03386 (tag : Fin 10000) (htag : tag.val = 3386) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3386 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03387 (tag : Fin 10000) (htag : tag.val = 3387) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3387 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03388 (tag : Fin 10000) (htag : tag.val = 3388) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3388 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03389 (tag : Fin 10000) (htag : tag.val = 3389) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3389 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03390 (tag : Fin 10000) (htag : tag.val = 3390) (k : Ring12) : tag.val = 3390 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03391 (tag : Fin 10000) (htag : tag.val = 3391) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3391 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03392 (tag : Fin 10000) (htag : tag.val = 3392) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3392 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03393 (tag : Fin 10000) (htag : tag.val = 3393) (x : State) (e : Event) (dr : Ring12) : tag.val = 3393 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03394 (tag : Fin 10000) (htag : tag.val = 3394) (x : State) (e : Event) (dr : Ring12) : tag.val = 3394 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03395 (tag : Fin 10000) (htag : tag.val = 3395) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3395 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03396 (tag : Fin 10000) (htag : tag.val = 3396) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3396 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03397 (tag : Fin 10000) (htag : tag.val = 3397) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3397 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03398 (tag : Fin 10000) (htag : tag.val = 3398) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3398 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03399 (tag : Fin 10000) (htag : tag.val = 3399) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3399 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
