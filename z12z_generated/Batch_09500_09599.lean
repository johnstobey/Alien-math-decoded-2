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
theorem generated_09500 (tag : Fin 10000) (htag : tag.val = 9500) (k : Ring12) : tag.val = 9500 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09501 (tag : Fin 10000) (htag : tag.val = 9501) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9501 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09502 (tag : Fin 10000) (htag : tag.val = 9502) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9502 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09503 (tag : Fin 10000) (htag : tag.val = 9503) (x : State) (e : Event) (dr : Ring12) : tag.val = 9503 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09504 (tag : Fin 10000) (htag : tag.val = 9504) (x : State) (e : Event) (dr : Ring12) : tag.val = 9504 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09505 (tag : Fin 10000) (htag : tag.val = 9505) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9505 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09506 (tag : Fin 10000) (htag : tag.val = 9506) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9506 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09507 (tag : Fin 10000) (htag : tag.val = 9507) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9507 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09508 (tag : Fin 10000) (htag : tag.val = 9508) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9508 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09509 (tag : Fin 10000) (htag : tag.val = 9509) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9509 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09510 (tag : Fin 10000) (htag : tag.val = 9510) (k : Ring12) : tag.val = 9510 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09511 (tag : Fin 10000) (htag : tag.val = 9511) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9511 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09512 (tag : Fin 10000) (htag : tag.val = 9512) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9512 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09513 (tag : Fin 10000) (htag : tag.val = 9513) (x : State) (e : Event) (dr : Ring12) : tag.val = 9513 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09514 (tag : Fin 10000) (htag : tag.val = 9514) (x : State) (e : Event) (dr : Ring12) : tag.val = 9514 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09515 (tag : Fin 10000) (htag : tag.val = 9515) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9515 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09516 (tag : Fin 10000) (htag : tag.val = 9516) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9516 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09517 (tag : Fin 10000) (htag : tag.val = 9517) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9517 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09518 (tag : Fin 10000) (htag : tag.val = 9518) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9518 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09519 (tag : Fin 10000) (htag : tag.val = 9519) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9519 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09520 (tag : Fin 10000) (htag : tag.val = 9520) (k : Ring12) : tag.val = 9520 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09521 (tag : Fin 10000) (htag : tag.val = 9521) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9521 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09522 (tag : Fin 10000) (htag : tag.val = 9522) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9522 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09523 (tag : Fin 10000) (htag : tag.val = 9523) (x : State) (e : Event) (dr : Ring12) : tag.val = 9523 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09524 (tag : Fin 10000) (htag : tag.val = 9524) (x : State) (e : Event) (dr : Ring12) : tag.val = 9524 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09525 (tag : Fin 10000) (htag : tag.val = 9525) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9525 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09526 (tag : Fin 10000) (htag : tag.val = 9526) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9526 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09527 (tag : Fin 10000) (htag : tag.val = 9527) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9527 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09528 (tag : Fin 10000) (htag : tag.val = 9528) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9528 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09529 (tag : Fin 10000) (htag : tag.val = 9529) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9529 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09530 (tag : Fin 10000) (htag : tag.val = 9530) (k : Ring12) : tag.val = 9530 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09531 (tag : Fin 10000) (htag : tag.val = 9531) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9531 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09532 (tag : Fin 10000) (htag : tag.val = 9532) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9532 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09533 (tag : Fin 10000) (htag : tag.val = 9533) (x : State) (e : Event) (dr : Ring12) : tag.val = 9533 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09534 (tag : Fin 10000) (htag : tag.val = 9534) (x : State) (e : Event) (dr : Ring12) : tag.val = 9534 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09535 (tag : Fin 10000) (htag : tag.val = 9535) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9535 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09536 (tag : Fin 10000) (htag : tag.val = 9536) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9536 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09537 (tag : Fin 10000) (htag : tag.val = 9537) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9537 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09538 (tag : Fin 10000) (htag : tag.val = 9538) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9538 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09539 (tag : Fin 10000) (htag : tag.val = 9539) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9539 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09540 (tag : Fin 10000) (htag : tag.val = 9540) (k : Ring12) : tag.val = 9540 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09541 (tag : Fin 10000) (htag : tag.val = 9541) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9541 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09542 (tag : Fin 10000) (htag : tag.val = 9542) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9542 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09543 (tag : Fin 10000) (htag : tag.val = 9543) (x : State) (e : Event) (dr : Ring12) : tag.val = 9543 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09544 (tag : Fin 10000) (htag : tag.val = 9544) (x : State) (e : Event) (dr : Ring12) : tag.val = 9544 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09545 (tag : Fin 10000) (htag : tag.val = 9545) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9545 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09546 (tag : Fin 10000) (htag : tag.val = 9546) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9546 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09547 (tag : Fin 10000) (htag : tag.val = 9547) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9547 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09548 (tag : Fin 10000) (htag : tag.val = 9548) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9548 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09549 (tag : Fin 10000) (htag : tag.val = 9549) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9549 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09550 (tag : Fin 10000) (htag : tag.val = 9550) (k : Ring12) : tag.val = 9550 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09551 (tag : Fin 10000) (htag : tag.val = 9551) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9551 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09552 (tag : Fin 10000) (htag : tag.val = 9552) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9552 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09553 (tag : Fin 10000) (htag : tag.val = 9553) (x : State) (e : Event) (dr : Ring12) : tag.val = 9553 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09554 (tag : Fin 10000) (htag : tag.val = 9554) (x : State) (e : Event) (dr : Ring12) : tag.val = 9554 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09555 (tag : Fin 10000) (htag : tag.val = 9555) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9555 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09556 (tag : Fin 10000) (htag : tag.val = 9556) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9556 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09557 (tag : Fin 10000) (htag : tag.val = 9557) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9557 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09558 (tag : Fin 10000) (htag : tag.val = 9558) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9558 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09559 (tag : Fin 10000) (htag : tag.val = 9559) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9559 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09560 (tag : Fin 10000) (htag : tag.val = 9560) (k : Ring12) : tag.val = 9560 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09561 (tag : Fin 10000) (htag : tag.val = 9561) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9561 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09562 (tag : Fin 10000) (htag : tag.val = 9562) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9562 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09563 (tag : Fin 10000) (htag : tag.val = 9563) (x : State) (e : Event) (dr : Ring12) : tag.val = 9563 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09564 (tag : Fin 10000) (htag : tag.val = 9564) (x : State) (e : Event) (dr : Ring12) : tag.val = 9564 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09565 (tag : Fin 10000) (htag : tag.val = 9565) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9565 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09566 (tag : Fin 10000) (htag : tag.val = 9566) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9566 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09567 (tag : Fin 10000) (htag : tag.val = 9567) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9567 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09568 (tag : Fin 10000) (htag : tag.val = 9568) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9568 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09569 (tag : Fin 10000) (htag : tag.val = 9569) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9569 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09570 (tag : Fin 10000) (htag : tag.val = 9570) (k : Ring12) : tag.val = 9570 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09571 (tag : Fin 10000) (htag : tag.val = 9571) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9571 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09572 (tag : Fin 10000) (htag : tag.val = 9572) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9572 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09573 (tag : Fin 10000) (htag : tag.val = 9573) (x : State) (e : Event) (dr : Ring12) : tag.val = 9573 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09574 (tag : Fin 10000) (htag : tag.val = 9574) (x : State) (e : Event) (dr : Ring12) : tag.val = 9574 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09575 (tag : Fin 10000) (htag : tag.val = 9575) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9575 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09576 (tag : Fin 10000) (htag : tag.val = 9576) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9576 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09577 (tag : Fin 10000) (htag : tag.val = 9577) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9577 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09578 (tag : Fin 10000) (htag : tag.val = 9578) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9578 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09579 (tag : Fin 10000) (htag : tag.val = 9579) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9579 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09580 (tag : Fin 10000) (htag : tag.val = 9580) (k : Ring12) : tag.val = 9580 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09581 (tag : Fin 10000) (htag : tag.val = 9581) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9581 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09582 (tag : Fin 10000) (htag : tag.val = 9582) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9582 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09583 (tag : Fin 10000) (htag : tag.val = 9583) (x : State) (e : Event) (dr : Ring12) : tag.val = 9583 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09584 (tag : Fin 10000) (htag : tag.val = 9584) (x : State) (e : Event) (dr : Ring12) : tag.val = 9584 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09585 (tag : Fin 10000) (htag : tag.val = 9585) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9585 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09586 (tag : Fin 10000) (htag : tag.val = 9586) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9586 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09587 (tag : Fin 10000) (htag : tag.val = 9587) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9587 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09588 (tag : Fin 10000) (htag : tag.val = 9588) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9588 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09589 (tag : Fin 10000) (htag : tag.val = 9589) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9589 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09590 (tag : Fin 10000) (htag : tag.val = 9590) (k : Ring12) : tag.val = 9590 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09591 (tag : Fin 10000) (htag : tag.val = 9591) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9591 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09592 (tag : Fin 10000) (htag : tag.val = 9592) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9592 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09593 (tag : Fin 10000) (htag : tag.val = 9593) (x : State) (e : Event) (dr : Ring12) : tag.val = 9593 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09594 (tag : Fin 10000) (htag : tag.val = 9594) (x : State) (e : Event) (dr : Ring12) : tag.val = 9594 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09595 (tag : Fin 10000) (htag : tag.val = 9595) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9595 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09596 (tag : Fin 10000) (htag : tag.val = 9596) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9596 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09597 (tag : Fin 10000) (htag : tag.val = 9597) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9597 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09598 (tag : Fin 10000) (htag : tag.val = 9598) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9598 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09599 (tag : Fin 10000) (htag : tag.val = 9599) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9599 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
