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
theorem generated_02500 (tag : Fin 10000) (htag : tag.val = 2500) (k : Ring12) : tag.val = 2500 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02501 (tag : Fin 10000) (htag : tag.val = 2501) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2501 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02502 (tag : Fin 10000) (htag : tag.val = 2502) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2502 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02503 (tag : Fin 10000) (htag : tag.val = 2503) (x : State) (e : Event) (dr : Ring12) : tag.val = 2503 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02504 (tag : Fin 10000) (htag : tag.val = 2504) (x : State) (e : Event) (dr : Ring12) : tag.val = 2504 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02505 (tag : Fin 10000) (htag : tag.val = 2505) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2505 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02506 (tag : Fin 10000) (htag : tag.val = 2506) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2506 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02507 (tag : Fin 10000) (htag : tag.val = 2507) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2507 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02508 (tag : Fin 10000) (htag : tag.val = 2508) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2508 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02509 (tag : Fin 10000) (htag : tag.val = 2509) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2509 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02510 (tag : Fin 10000) (htag : tag.val = 2510) (k : Ring12) : tag.val = 2510 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02511 (tag : Fin 10000) (htag : tag.val = 2511) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2511 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02512 (tag : Fin 10000) (htag : tag.val = 2512) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2512 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02513 (tag : Fin 10000) (htag : tag.val = 2513) (x : State) (e : Event) (dr : Ring12) : tag.val = 2513 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02514 (tag : Fin 10000) (htag : tag.val = 2514) (x : State) (e : Event) (dr : Ring12) : tag.val = 2514 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02515 (tag : Fin 10000) (htag : tag.val = 2515) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2515 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02516 (tag : Fin 10000) (htag : tag.val = 2516) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2516 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02517 (tag : Fin 10000) (htag : tag.val = 2517) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2517 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02518 (tag : Fin 10000) (htag : tag.val = 2518) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2518 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02519 (tag : Fin 10000) (htag : tag.val = 2519) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2519 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02520 (tag : Fin 10000) (htag : tag.val = 2520) (k : Ring12) : tag.val = 2520 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02521 (tag : Fin 10000) (htag : tag.val = 2521) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2521 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02522 (tag : Fin 10000) (htag : tag.val = 2522) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2522 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02523 (tag : Fin 10000) (htag : tag.val = 2523) (x : State) (e : Event) (dr : Ring12) : tag.val = 2523 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02524 (tag : Fin 10000) (htag : tag.val = 2524) (x : State) (e : Event) (dr : Ring12) : tag.val = 2524 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02525 (tag : Fin 10000) (htag : tag.val = 2525) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2525 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02526 (tag : Fin 10000) (htag : tag.val = 2526) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2526 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02527 (tag : Fin 10000) (htag : tag.val = 2527) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2527 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02528 (tag : Fin 10000) (htag : tag.val = 2528) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2528 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02529 (tag : Fin 10000) (htag : tag.val = 2529) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2529 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02530 (tag : Fin 10000) (htag : tag.val = 2530) (k : Ring12) : tag.val = 2530 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02531 (tag : Fin 10000) (htag : tag.val = 2531) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2531 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02532 (tag : Fin 10000) (htag : tag.val = 2532) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2532 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02533 (tag : Fin 10000) (htag : tag.val = 2533) (x : State) (e : Event) (dr : Ring12) : tag.val = 2533 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02534 (tag : Fin 10000) (htag : tag.val = 2534) (x : State) (e : Event) (dr : Ring12) : tag.val = 2534 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02535 (tag : Fin 10000) (htag : tag.val = 2535) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2535 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02536 (tag : Fin 10000) (htag : tag.val = 2536) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2536 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02537 (tag : Fin 10000) (htag : tag.val = 2537) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2537 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02538 (tag : Fin 10000) (htag : tag.val = 2538) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2538 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02539 (tag : Fin 10000) (htag : tag.val = 2539) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2539 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02540 (tag : Fin 10000) (htag : tag.val = 2540) (k : Ring12) : tag.val = 2540 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02541 (tag : Fin 10000) (htag : tag.val = 2541) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2541 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02542 (tag : Fin 10000) (htag : tag.val = 2542) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2542 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02543 (tag : Fin 10000) (htag : tag.val = 2543) (x : State) (e : Event) (dr : Ring12) : tag.val = 2543 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02544 (tag : Fin 10000) (htag : tag.val = 2544) (x : State) (e : Event) (dr : Ring12) : tag.val = 2544 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02545 (tag : Fin 10000) (htag : tag.val = 2545) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2545 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02546 (tag : Fin 10000) (htag : tag.val = 2546) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2546 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02547 (tag : Fin 10000) (htag : tag.val = 2547) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2547 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02548 (tag : Fin 10000) (htag : tag.val = 2548) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2548 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02549 (tag : Fin 10000) (htag : tag.val = 2549) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2549 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02550 (tag : Fin 10000) (htag : tag.val = 2550) (k : Ring12) : tag.val = 2550 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02551 (tag : Fin 10000) (htag : tag.val = 2551) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2551 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02552 (tag : Fin 10000) (htag : tag.val = 2552) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2552 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02553 (tag : Fin 10000) (htag : tag.val = 2553) (x : State) (e : Event) (dr : Ring12) : tag.val = 2553 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02554 (tag : Fin 10000) (htag : tag.val = 2554) (x : State) (e : Event) (dr : Ring12) : tag.val = 2554 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02555 (tag : Fin 10000) (htag : tag.val = 2555) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2555 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02556 (tag : Fin 10000) (htag : tag.val = 2556) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2556 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02557 (tag : Fin 10000) (htag : tag.val = 2557) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2557 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02558 (tag : Fin 10000) (htag : tag.val = 2558) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2558 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02559 (tag : Fin 10000) (htag : tag.val = 2559) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2559 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02560 (tag : Fin 10000) (htag : tag.val = 2560) (k : Ring12) : tag.val = 2560 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02561 (tag : Fin 10000) (htag : tag.val = 2561) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2561 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02562 (tag : Fin 10000) (htag : tag.val = 2562) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2562 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02563 (tag : Fin 10000) (htag : tag.val = 2563) (x : State) (e : Event) (dr : Ring12) : tag.val = 2563 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02564 (tag : Fin 10000) (htag : tag.val = 2564) (x : State) (e : Event) (dr : Ring12) : tag.val = 2564 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02565 (tag : Fin 10000) (htag : tag.val = 2565) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2565 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02566 (tag : Fin 10000) (htag : tag.val = 2566) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2566 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02567 (tag : Fin 10000) (htag : tag.val = 2567) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2567 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02568 (tag : Fin 10000) (htag : tag.val = 2568) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2568 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02569 (tag : Fin 10000) (htag : tag.val = 2569) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2569 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02570 (tag : Fin 10000) (htag : tag.val = 2570) (k : Ring12) : tag.val = 2570 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02571 (tag : Fin 10000) (htag : tag.val = 2571) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2571 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02572 (tag : Fin 10000) (htag : tag.val = 2572) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2572 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02573 (tag : Fin 10000) (htag : tag.val = 2573) (x : State) (e : Event) (dr : Ring12) : tag.val = 2573 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02574 (tag : Fin 10000) (htag : tag.val = 2574) (x : State) (e : Event) (dr : Ring12) : tag.val = 2574 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02575 (tag : Fin 10000) (htag : tag.val = 2575) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2575 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02576 (tag : Fin 10000) (htag : tag.val = 2576) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2576 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02577 (tag : Fin 10000) (htag : tag.val = 2577) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2577 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02578 (tag : Fin 10000) (htag : tag.val = 2578) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2578 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02579 (tag : Fin 10000) (htag : tag.val = 2579) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2579 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02580 (tag : Fin 10000) (htag : tag.val = 2580) (k : Ring12) : tag.val = 2580 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02581 (tag : Fin 10000) (htag : tag.val = 2581) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2581 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02582 (tag : Fin 10000) (htag : tag.val = 2582) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2582 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02583 (tag : Fin 10000) (htag : tag.val = 2583) (x : State) (e : Event) (dr : Ring12) : tag.val = 2583 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02584 (tag : Fin 10000) (htag : tag.val = 2584) (x : State) (e : Event) (dr : Ring12) : tag.val = 2584 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02585 (tag : Fin 10000) (htag : tag.val = 2585) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2585 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02586 (tag : Fin 10000) (htag : tag.val = 2586) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2586 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02587 (tag : Fin 10000) (htag : tag.val = 2587) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2587 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02588 (tag : Fin 10000) (htag : tag.val = 2588) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2588 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02589 (tag : Fin 10000) (htag : tag.val = 2589) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2589 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02590 (tag : Fin 10000) (htag : tag.val = 2590) (k : Ring12) : tag.val = 2590 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02591 (tag : Fin 10000) (htag : tag.val = 2591) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2591 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02592 (tag : Fin 10000) (htag : tag.val = 2592) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2592 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02593 (tag : Fin 10000) (htag : tag.val = 2593) (x : State) (e : Event) (dr : Ring12) : tag.val = 2593 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02594 (tag : Fin 10000) (htag : tag.val = 2594) (x : State) (e : Event) (dr : Ring12) : tag.val = 2594 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02595 (tag : Fin 10000) (htag : tag.val = 2595) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2595 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02596 (tag : Fin 10000) (htag : tag.val = 2596) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2596 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02597 (tag : Fin 10000) (htag : tag.val = 2597) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2597 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02598 (tag : Fin 10000) (htag : tag.val = 2598) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2598 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02599 (tag : Fin 10000) (htag : tag.val = 2599) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2599 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
