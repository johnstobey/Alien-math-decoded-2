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
theorem generated_03400 (tag : Fin 10000) (htag : tag.val = 3400) (k : Ring12) : tag.val = 3400 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03401 (tag : Fin 10000) (htag : tag.val = 3401) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3401 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03402 (tag : Fin 10000) (htag : tag.val = 3402) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3402 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03403 (tag : Fin 10000) (htag : tag.val = 3403) (x : State) (e : Event) (dr : Ring12) : tag.val = 3403 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03404 (tag : Fin 10000) (htag : tag.val = 3404) (x : State) (e : Event) (dr : Ring12) : tag.val = 3404 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03405 (tag : Fin 10000) (htag : tag.val = 3405) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3405 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03406 (tag : Fin 10000) (htag : tag.val = 3406) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3406 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03407 (tag : Fin 10000) (htag : tag.val = 3407) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3407 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03408 (tag : Fin 10000) (htag : tag.val = 3408) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3408 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03409 (tag : Fin 10000) (htag : tag.val = 3409) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3409 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03410 (tag : Fin 10000) (htag : tag.val = 3410) (k : Ring12) : tag.val = 3410 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03411 (tag : Fin 10000) (htag : tag.val = 3411) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3411 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03412 (tag : Fin 10000) (htag : tag.val = 3412) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3412 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03413 (tag : Fin 10000) (htag : tag.val = 3413) (x : State) (e : Event) (dr : Ring12) : tag.val = 3413 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03414 (tag : Fin 10000) (htag : tag.val = 3414) (x : State) (e : Event) (dr : Ring12) : tag.val = 3414 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03415 (tag : Fin 10000) (htag : tag.val = 3415) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3415 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03416 (tag : Fin 10000) (htag : tag.val = 3416) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3416 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03417 (tag : Fin 10000) (htag : tag.val = 3417) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3417 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03418 (tag : Fin 10000) (htag : tag.val = 3418) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3418 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03419 (tag : Fin 10000) (htag : tag.val = 3419) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3419 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03420 (tag : Fin 10000) (htag : tag.val = 3420) (k : Ring12) : tag.val = 3420 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03421 (tag : Fin 10000) (htag : tag.val = 3421) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3421 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03422 (tag : Fin 10000) (htag : tag.val = 3422) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3422 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03423 (tag : Fin 10000) (htag : tag.val = 3423) (x : State) (e : Event) (dr : Ring12) : tag.val = 3423 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03424 (tag : Fin 10000) (htag : tag.val = 3424) (x : State) (e : Event) (dr : Ring12) : tag.val = 3424 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03425 (tag : Fin 10000) (htag : tag.val = 3425) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3425 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03426 (tag : Fin 10000) (htag : tag.val = 3426) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3426 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03427 (tag : Fin 10000) (htag : tag.val = 3427) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3427 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03428 (tag : Fin 10000) (htag : tag.val = 3428) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3428 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03429 (tag : Fin 10000) (htag : tag.val = 3429) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3429 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03430 (tag : Fin 10000) (htag : tag.val = 3430) (k : Ring12) : tag.val = 3430 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03431 (tag : Fin 10000) (htag : tag.val = 3431) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3431 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03432 (tag : Fin 10000) (htag : tag.val = 3432) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3432 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03433 (tag : Fin 10000) (htag : tag.val = 3433) (x : State) (e : Event) (dr : Ring12) : tag.val = 3433 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03434 (tag : Fin 10000) (htag : tag.val = 3434) (x : State) (e : Event) (dr : Ring12) : tag.val = 3434 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03435 (tag : Fin 10000) (htag : tag.val = 3435) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3435 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03436 (tag : Fin 10000) (htag : tag.val = 3436) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3436 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03437 (tag : Fin 10000) (htag : tag.val = 3437) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3437 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03438 (tag : Fin 10000) (htag : tag.val = 3438) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3438 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03439 (tag : Fin 10000) (htag : tag.val = 3439) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3439 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03440 (tag : Fin 10000) (htag : tag.val = 3440) (k : Ring12) : tag.val = 3440 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03441 (tag : Fin 10000) (htag : tag.val = 3441) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3441 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03442 (tag : Fin 10000) (htag : tag.val = 3442) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3442 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03443 (tag : Fin 10000) (htag : tag.val = 3443) (x : State) (e : Event) (dr : Ring12) : tag.val = 3443 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03444 (tag : Fin 10000) (htag : tag.val = 3444) (x : State) (e : Event) (dr : Ring12) : tag.val = 3444 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03445 (tag : Fin 10000) (htag : tag.val = 3445) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3445 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03446 (tag : Fin 10000) (htag : tag.val = 3446) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3446 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03447 (tag : Fin 10000) (htag : tag.val = 3447) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3447 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03448 (tag : Fin 10000) (htag : tag.val = 3448) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3448 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03449 (tag : Fin 10000) (htag : tag.val = 3449) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3449 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03450 (tag : Fin 10000) (htag : tag.val = 3450) (k : Ring12) : tag.val = 3450 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03451 (tag : Fin 10000) (htag : tag.val = 3451) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3451 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03452 (tag : Fin 10000) (htag : tag.val = 3452) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3452 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03453 (tag : Fin 10000) (htag : tag.val = 3453) (x : State) (e : Event) (dr : Ring12) : tag.val = 3453 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03454 (tag : Fin 10000) (htag : tag.val = 3454) (x : State) (e : Event) (dr : Ring12) : tag.val = 3454 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03455 (tag : Fin 10000) (htag : tag.val = 3455) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3455 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03456 (tag : Fin 10000) (htag : tag.val = 3456) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3456 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03457 (tag : Fin 10000) (htag : tag.val = 3457) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3457 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03458 (tag : Fin 10000) (htag : tag.val = 3458) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3458 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03459 (tag : Fin 10000) (htag : tag.val = 3459) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3459 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03460 (tag : Fin 10000) (htag : tag.val = 3460) (k : Ring12) : tag.val = 3460 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03461 (tag : Fin 10000) (htag : tag.val = 3461) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3461 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03462 (tag : Fin 10000) (htag : tag.val = 3462) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3462 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03463 (tag : Fin 10000) (htag : tag.val = 3463) (x : State) (e : Event) (dr : Ring12) : tag.val = 3463 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03464 (tag : Fin 10000) (htag : tag.val = 3464) (x : State) (e : Event) (dr : Ring12) : tag.val = 3464 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03465 (tag : Fin 10000) (htag : tag.val = 3465) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3465 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03466 (tag : Fin 10000) (htag : tag.val = 3466) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3466 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03467 (tag : Fin 10000) (htag : tag.val = 3467) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3467 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03468 (tag : Fin 10000) (htag : tag.val = 3468) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3468 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03469 (tag : Fin 10000) (htag : tag.val = 3469) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3469 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03470 (tag : Fin 10000) (htag : tag.val = 3470) (k : Ring12) : tag.val = 3470 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03471 (tag : Fin 10000) (htag : tag.val = 3471) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3471 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03472 (tag : Fin 10000) (htag : tag.val = 3472) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3472 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03473 (tag : Fin 10000) (htag : tag.val = 3473) (x : State) (e : Event) (dr : Ring12) : tag.val = 3473 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03474 (tag : Fin 10000) (htag : tag.val = 3474) (x : State) (e : Event) (dr : Ring12) : tag.val = 3474 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03475 (tag : Fin 10000) (htag : tag.val = 3475) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3475 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03476 (tag : Fin 10000) (htag : tag.val = 3476) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3476 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03477 (tag : Fin 10000) (htag : tag.val = 3477) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3477 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03478 (tag : Fin 10000) (htag : tag.val = 3478) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3478 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03479 (tag : Fin 10000) (htag : tag.val = 3479) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3479 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03480 (tag : Fin 10000) (htag : tag.val = 3480) (k : Ring12) : tag.val = 3480 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03481 (tag : Fin 10000) (htag : tag.val = 3481) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3481 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03482 (tag : Fin 10000) (htag : tag.val = 3482) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3482 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03483 (tag : Fin 10000) (htag : tag.val = 3483) (x : State) (e : Event) (dr : Ring12) : tag.val = 3483 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03484 (tag : Fin 10000) (htag : tag.val = 3484) (x : State) (e : Event) (dr : Ring12) : tag.val = 3484 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03485 (tag : Fin 10000) (htag : tag.val = 3485) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3485 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03486 (tag : Fin 10000) (htag : tag.val = 3486) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3486 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03487 (tag : Fin 10000) (htag : tag.val = 3487) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3487 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03488 (tag : Fin 10000) (htag : tag.val = 3488) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3488 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03489 (tag : Fin 10000) (htag : tag.val = 3489) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3489 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_03490 (tag : Fin 10000) (htag : tag.val = 3490) (k : Ring12) : tag.val = 3490 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_03491 (tag : Fin 10000) (htag : tag.val = 3491) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3491 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_03492 (tag : Fin 10000) (htag : tag.val = 3492) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3492 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_03493 (tag : Fin 10000) (htag : tag.val = 3493) (x : State) (e : Event) (dr : Ring12) : tag.val = 3493 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_03494 (tag : Fin 10000) (htag : tag.val = 3494) (x : State) (e : Event) (dr : Ring12) : tag.val = 3494 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_03495 (tag : Fin 10000) (htag : tag.val = 3495) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3495 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_03496 (tag : Fin 10000) (htag : tag.val = 3496) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 3496 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_03497 (tag : Fin 10000) (htag : tag.val = 3497) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 3497 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_03498 (tag : Fin 10000) (htag : tag.val = 3498) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 3498 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_03499 (tag : Fin 10000) (htag : tag.val = 3499) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 3499 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
