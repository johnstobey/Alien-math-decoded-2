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
theorem generated_06500 (tag : Fin 10000) (htag : tag.val = 6500) (k : Ring12) : tag.val = 6500 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06501 (tag : Fin 10000) (htag : tag.val = 6501) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6501 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06502 (tag : Fin 10000) (htag : tag.val = 6502) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6502 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06503 (tag : Fin 10000) (htag : tag.val = 6503) (x : State) (e : Event) (dr : Ring12) : tag.val = 6503 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06504 (tag : Fin 10000) (htag : tag.val = 6504) (x : State) (e : Event) (dr : Ring12) : tag.val = 6504 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06505 (tag : Fin 10000) (htag : tag.val = 6505) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6505 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06506 (tag : Fin 10000) (htag : tag.val = 6506) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6506 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06507 (tag : Fin 10000) (htag : tag.val = 6507) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6507 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06508 (tag : Fin 10000) (htag : tag.val = 6508) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6508 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06509 (tag : Fin 10000) (htag : tag.val = 6509) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6509 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06510 (tag : Fin 10000) (htag : tag.val = 6510) (k : Ring12) : tag.val = 6510 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06511 (tag : Fin 10000) (htag : tag.val = 6511) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6511 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06512 (tag : Fin 10000) (htag : tag.val = 6512) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6512 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06513 (tag : Fin 10000) (htag : tag.val = 6513) (x : State) (e : Event) (dr : Ring12) : tag.val = 6513 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06514 (tag : Fin 10000) (htag : tag.val = 6514) (x : State) (e : Event) (dr : Ring12) : tag.val = 6514 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06515 (tag : Fin 10000) (htag : tag.val = 6515) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6515 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06516 (tag : Fin 10000) (htag : tag.val = 6516) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6516 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06517 (tag : Fin 10000) (htag : tag.val = 6517) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6517 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06518 (tag : Fin 10000) (htag : tag.val = 6518) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6518 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06519 (tag : Fin 10000) (htag : tag.val = 6519) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6519 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06520 (tag : Fin 10000) (htag : tag.val = 6520) (k : Ring12) : tag.val = 6520 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06521 (tag : Fin 10000) (htag : tag.val = 6521) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6521 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06522 (tag : Fin 10000) (htag : tag.val = 6522) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6522 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06523 (tag : Fin 10000) (htag : tag.val = 6523) (x : State) (e : Event) (dr : Ring12) : tag.val = 6523 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06524 (tag : Fin 10000) (htag : tag.val = 6524) (x : State) (e : Event) (dr : Ring12) : tag.val = 6524 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06525 (tag : Fin 10000) (htag : tag.val = 6525) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6525 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06526 (tag : Fin 10000) (htag : tag.val = 6526) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6526 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06527 (tag : Fin 10000) (htag : tag.val = 6527) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6527 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06528 (tag : Fin 10000) (htag : tag.val = 6528) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6528 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06529 (tag : Fin 10000) (htag : tag.val = 6529) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6529 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06530 (tag : Fin 10000) (htag : tag.val = 6530) (k : Ring12) : tag.val = 6530 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06531 (tag : Fin 10000) (htag : tag.val = 6531) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6531 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06532 (tag : Fin 10000) (htag : tag.val = 6532) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6532 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06533 (tag : Fin 10000) (htag : tag.val = 6533) (x : State) (e : Event) (dr : Ring12) : tag.val = 6533 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06534 (tag : Fin 10000) (htag : tag.val = 6534) (x : State) (e : Event) (dr : Ring12) : tag.val = 6534 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06535 (tag : Fin 10000) (htag : tag.val = 6535) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6535 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06536 (tag : Fin 10000) (htag : tag.val = 6536) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6536 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06537 (tag : Fin 10000) (htag : tag.val = 6537) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6537 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06538 (tag : Fin 10000) (htag : tag.val = 6538) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6538 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06539 (tag : Fin 10000) (htag : tag.val = 6539) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6539 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06540 (tag : Fin 10000) (htag : tag.val = 6540) (k : Ring12) : tag.val = 6540 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06541 (tag : Fin 10000) (htag : tag.val = 6541) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6541 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06542 (tag : Fin 10000) (htag : tag.val = 6542) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6542 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06543 (tag : Fin 10000) (htag : tag.val = 6543) (x : State) (e : Event) (dr : Ring12) : tag.val = 6543 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06544 (tag : Fin 10000) (htag : tag.val = 6544) (x : State) (e : Event) (dr : Ring12) : tag.val = 6544 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06545 (tag : Fin 10000) (htag : tag.val = 6545) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6545 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06546 (tag : Fin 10000) (htag : tag.val = 6546) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6546 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06547 (tag : Fin 10000) (htag : tag.val = 6547) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6547 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06548 (tag : Fin 10000) (htag : tag.val = 6548) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6548 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06549 (tag : Fin 10000) (htag : tag.val = 6549) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6549 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06550 (tag : Fin 10000) (htag : tag.val = 6550) (k : Ring12) : tag.val = 6550 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06551 (tag : Fin 10000) (htag : tag.val = 6551) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6551 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06552 (tag : Fin 10000) (htag : tag.val = 6552) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6552 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06553 (tag : Fin 10000) (htag : tag.val = 6553) (x : State) (e : Event) (dr : Ring12) : tag.val = 6553 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06554 (tag : Fin 10000) (htag : tag.val = 6554) (x : State) (e : Event) (dr : Ring12) : tag.val = 6554 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06555 (tag : Fin 10000) (htag : tag.val = 6555) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6555 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06556 (tag : Fin 10000) (htag : tag.val = 6556) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6556 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06557 (tag : Fin 10000) (htag : tag.val = 6557) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6557 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06558 (tag : Fin 10000) (htag : tag.val = 6558) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6558 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06559 (tag : Fin 10000) (htag : tag.val = 6559) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6559 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06560 (tag : Fin 10000) (htag : tag.val = 6560) (k : Ring12) : tag.val = 6560 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06561 (tag : Fin 10000) (htag : tag.val = 6561) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6561 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06562 (tag : Fin 10000) (htag : tag.val = 6562) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6562 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06563 (tag : Fin 10000) (htag : tag.val = 6563) (x : State) (e : Event) (dr : Ring12) : tag.val = 6563 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06564 (tag : Fin 10000) (htag : tag.val = 6564) (x : State) (e : Event) (dr : Ring12) : tag.val = 6564 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06565 (tag : Fin 10000) (htag : tag.val = 6565) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6565 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06566 (tag : Fin 10000) (htag : tag.val = 6566) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6566 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06567 (tag : Fin 10000) (htag : tag.val = 6567) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6567 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06568 (tag : Fin 10000) (htag : tag.val = 6568) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6568 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06569 (tag : Fin 10000) (htag : tag.val = 6569) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6569 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06570 (tag : Fin 10000) (htag : tag.val = 6570) (k : Ring12) : tag.val = 6570 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06571 (tag : Fin 10000) (htag : tag.val = 6571) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6571 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06572 (tag : Fin 10000) (htag : tag.val = 6572) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6572 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06573 (tag : Fin 10000) (htag : tag.val = 6573) (x : State) (e : Event) (dr : Ring12) : tag.val = 6573 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06574 (tag : Fin 10000) (htag : tag.val = 6574) (x : State) (e : Event) (dr : Ring12) : tag.val = 6574 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06575 (tag : Fin 10000) (htag : tag.val = 6575) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6575 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06576 (tag : Fin 10000) (htag : tag.val = 6576) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6576 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06577 (tag : Fin 10000) (htag : tag.val = 6577) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6577 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06578 (tag : Fin 10000) (htag : tag.val = 6578) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6578 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06579 (tag : Fin 10000) (htag : tag.val = 6579) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6579 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06580 (tag : Fin 10000) (htag : tag.val = 6580) (k : Ring12) : tag.val = 6580 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06581 (tag : Fin 10000) (htag : tag.val = 6581) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6581 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06582 (tag : Fin 10000) (htag : tag.val = 6582) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6582 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06583 (tag : Fin 10000) (htag : tag.val = 6583) (x : State) (e : Event) (dr : Ring12) : tag.val = 6583 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06584 (tag : Fin 10000) (htag : tag.val = 6584) (x : State) (e : Event) (dr : Ring12) : tag.val = 6584 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06585 (tag : Fin 10000) (htag : tag.val = 6585) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6585 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06586 (tag : Fin 10000) (htag : tag.val = 6586) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6586 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06587 (tag : Fin 10000) (htag : tag.val = 6587) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6587 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06588 (tag : Fin 10000) (htag : tag.val = 6588) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6588 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06589 (tag : Fin 10000) (htag : tag.val = 6589) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6589 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06590 (tag : Fin 10000) (htag : tag.val = 6590) (k : Ring12) : tag.val = 6590 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06591 (tag : Fin 10000) (htag : tag.val = 6591) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6591 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06592 (tag : Fin 10000) (htag : tag.val = 6592) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6592 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06593 (tag : Fin 10000) (htag : tag.val = 6593) (x : State) (e : Event) (dr : Ring12) : tag.val = 6593 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06594 (tag : Fin 10000) (htag : tag.val = 6594) (x : State) (e : Event) (dr : Ring12) : tag.val = 6594 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06595 (tag : Fin 10000) (htag : tag.val = 6595) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6595 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06596 (tag : Fin 10000) (htag : tag.val = 6596) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6596 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06597 (tag : Fin 10000) (htag : tag.val = 6597) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6597 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06598 (tag : Fin 10000) (htag : tag.val = 6598) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6598 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06599 (tag : Fin 10000) (htag : tag.val = 6599) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6599 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
