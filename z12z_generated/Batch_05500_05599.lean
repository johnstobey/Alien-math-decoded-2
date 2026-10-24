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
theorem generated_05500 (tag : Fin 10000) (htag : tag.val = 5500) (k : Ring12) : tag.val = 5500 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05501 (tag : Fin 10000) (htag : tag.val = 5501) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5501 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05502 (tag : Fin 10000) (htag : tag.val = 5502) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5502 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05503 (tag : Fin 10000) (htag : tag.val = 5503) (x : State) (e : Event) (dr : Ring12) : tag.val = 5503 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05504 (tag : Fin 10000) (htag : tag.val = 5504) (x : State) (e : Event) (dr : Ring12) : tag.val = 5504 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05505 (tag : Fin 10000) (htag : tag.val = 5505) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5505 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05506 (tag : Fin 10000) (htag : tag.val = 5506) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5506 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05507 (tag : Fin 10000) (htag : tag.val = 5507) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5507 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05508 (tag : Fin 10000) (htag : tag.val = 5508) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5508 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05509 (tag : Fin 10000) (htag : tag.val = 5509) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5509 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05510 (tag : Fin 10000) (htag : tag.val = 5510) (k : Ring12) : tag.val = 5510 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05511 (tag : Fin 10000) (htag : tag.val = 5511) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5511 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05512 (tag : Fin 10000) (htag : tag.val = 5512) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5512 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05513 (tag : Fin 10000) (htag : tag.val = 5513) (x : State) (e : Event) (dr : Ring12) : tag.val = 5513 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05514 (tag : Fin 10000) (htag : tag.val = 5514) (x : State) (e : Event) (dr : Ring12) : tag.val = 5514 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05515 (tag : Fin 10000) (htag : tag.val = 5515) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5515 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05516 (tag : Fin 10000) (htag : tag.val = 5516) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5516 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05517 (tag : Fin 10000) (htag : tag.val = 5517) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5517 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05518 (tag : Fin 10000) (htag : tag.val = 5518) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5518 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05519 (tag : Fin 10000) (htag : tag.val = 5519) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5519 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05520 (tag : Fin 10000) (htag : tag.val = 5520) (k : Ring12) : tag.val = 5520 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05521 (tag : Fin 10000) (htag : tag.val = 5521) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5521 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05522 (tag : Fin 10000) (htag : tag.val = 5522) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5522 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05523 (tag : Fin 10000) (htag : tag.val = 5523) (x : State) (e : Event) (dr : Ring12) : tag.val = 5523 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05524 (tag : Fin 10000) (htag : tag.val = 5524) (x : State) (e : Event) (dr : Ring12) : tag.val = 5524 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05525 (tag : Fin 10000) (htag : tag.val = 5525) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5525 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05526 (tag : Fin 10000) (htag : tag.val = 5526) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5526 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05527 (tag : Fin 10000) (htag : tag.val = 5527) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5527 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05528 (tag : Fin 10000) (htag : tag.val = 5528) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5528 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05529 (tag : Fin 10000) (htag : tag.val = 5529) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5529 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05530 (tag : Fin 10000) (htag : tag.val = 5530) (k : Ring12) : tag.val = 5530 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05531 (tag : Fin 10000) (htag : tag.val = 5531) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5531 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05532 (tag : Fin 10000) (htag : tag.val = 5532) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5532 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05533 (tag : Fin 10000) (htag : tag.val = 5533) (x : State) (e : Event) (dr : Ring12) : tag.val = 5533 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05534 (tag : Fin 10000) (htag : tag.val = 5534) (x : State) (e : Event) (dr : Ring12) : tag.val = 5534 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05535 (tag : Fin 10000) (htag : tag.val = 5535) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5535 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05536 (tag : Fin 10000) (htag : tag.val = 5536) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5536 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05537 (tag : Fin 10000) (htag : tag.val = 5537) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5537 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05538 (tag : Fin 10000) (htag : tag.val = 5538) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5538 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05539 (tag : Fin 10000) (htag : tag.val = 5539) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5539 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05540 (tag : Fin 10000) (htag : tag.val = 5540) (k : Ring12) : tag.val = 5540 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05541 (tag : Fin 10000) (htag : tag.val = 5541) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5541 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05542 (tag : Fin 10000) (htag : tag.val = 5542) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5542 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05543 (tag : Fin 10000) (htag : tag.val = 5543) (x : State) (e : Event) (dr : Ring12) : tag.val = 5543 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05544 (tag : Fin 10000) (htag : tag.val = 5544) (x : State) (e : Event) (dr : Ring12) : tag.val = 5544 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05545 (tag : Fin 10000) (htag : tag.val = 5545) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5545 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05546 (tag : Fin 10000) (htag : tag.val = 5546) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5546 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05547 (tag : Fin 10000) (htag : tag.val = 5547) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5547 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05548 (tag : Fin 10000) (htag : tag.val = 5548) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5548 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05549 (tag : Fin 10000) (htag : tag.val = 5549) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5549 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05550 (tag : Fin 10000) (htag : tag.val = 5550) (k : Ring12) : tag.val = 5550 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05551 (tag : Fin 10000) (htag : tag.val = 5551) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5551 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05552 (tag : Fin 10000) (htag : tag.val = 5552) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5552 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05553 (tag : Fin 10000) (htag : tag.val = 5553) (x : State) (e : Event) (dr : Ring12) : tag.val = 5553 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05554 (tag : Fin 10000) (htag : tag.val = 5554) (x : State) (e : Event) (dr : Ring12) : tag.val = 5554 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05555 (tag : Fin 10000) (htag : tag.val = 5555) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5555 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05556 (tag : Fin 10000) (htag : tag.val = 5556) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5556 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05557 (tag : Fin 10000) (htag : tag.val = 5557) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5557 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05558 (tag : Fin 10000) (htag : tag.val = 5558) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5558 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05559 (tag : Fin 10000) (htag : tag.val = 5559) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5559 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05560 (tag : Fin 10000) (htag : tag.val = 5560) (k : Ring12) : tag.val = 5560 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05561 (tag : Fin 10000) (htag : tag.val = 5561) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5561 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05562 (tag : Fin 10000) (htag : tag.val = 5562) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5562 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05563 (tag : Fin 10000) (htag : tag.val = 5563) (x : State) (e : Event) (dr : Ring12) : tag.val = 5563 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05564 (tag : Fin 10000) (htag : tag.val = 5564) (x : State) (e : Event) (dr : Ring12) : tag.val = 5564 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05565 (tag : Fin 10000) (htag : tag.val = 5565) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5565 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05566 (tag : Fin 10000) (htag : tag.val = 5566) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5566 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05567 (tag : Fin 10000) (htag : tag.val = 5567) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5567 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05568 (tag : Fin 10000) (htag : tag.val = 5568) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5568 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05569 (tag : Fin 10000) (htag : tag.val = 5569) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5569 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05570 (tag : Fin 10000) (htag : tag.val = 5570) (k : Ring12) : tag.val = 5570 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05571 (tag : Fin 10000) (htag : tag.val = 5571) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5571 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05572 (tag : Fin 10000) (htag : tag.val = 5572) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5572 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05573 (tag : Fin 10000) (htag : tag.val = 5573) (x : State) (e : Event) (dr : Ring12) : tag.val = 5573 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05574 (tag : Fin 10000) (htag : tag.val = 5574) (x : State) (e : Event) (dr : Ring12) : tag.val = 5574 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05575 (tag : Fin 10000) (htag : tag.val = 5575) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5575 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05576 (tag : Fin 10000) (htag : tag.val = 5576) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5576 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05577 (tag : Fin 10000) (htag : tag.val = 5577) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5577 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05578 (tag : Fin 10000) (htag : tag.val = 5578) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5578 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05579 (tag : Fin 10000) (htag : tag.val = 5579) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5579 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05580 (tag : Fin 10000) (htag : tag.val = 5580) (k : Ring12) : tag.val = 5580 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05581 (tag : Fin 10000) (htag : tag.val = 5581) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5581 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05582 (tag : Fin 10000) (htag : tag.val = 5582) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5582 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05583 (tag : Fin 10000) (htag : tag.val = 5583) (x : State) (e : Event) (dr : Ring12) : tag.val = 5583 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05584 (tag : Fin 10000) (htag : tag.val = 5584) (x : State) (e : Event) (dr : Ring12) : tag.val = 5584 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05585 (tag : Fin 10000) (htag : tag.val = 5585) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5585 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05586 (tag : Fin 10000) (htag : tag.val = 5586) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5586 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05587 (tag : Fin 10000) (htag : tag.val = 5587) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5587 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05588 (tag : Fin 10000) (htag : tag.val = 5588) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5588 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05589 (tag : Fin 10000) (htag : tag.val = 5589) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5589 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05590 (tag : Fin 10000) (htag : tag.val = 5590) (k : Ring12) : tag.val = 5590 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05591 (tag : Fin 10000) (htag : tag.val = 5591) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5591 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05592 (tag : Fin 10000) (htag : tag.val = 5592) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5592 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05593 (tag : Fin 10000) (htag : tag.val = 5593) (x : State) (e : Event) (dr : Ring12) : tag.val = 5593 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05594 (tag : Fin 10000) (htag : tag.val = 5594) (x : State) (e : Event) (dr : Ring12) : tag.val = 5594 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05595 (tag : Fin 10000) (htag : tag.val = 5595) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5595 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05596 (tag : Fin 10000) (htag : tag.val = 5596) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5596 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05597 (tag : Fin 10000) (htag : tag.val = 5597) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5597 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05598 (tag : Fin 10000) (htag : tag.val = 5598) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5598 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05599 (tag : Fin 10000) (htag : tag.val = 5599) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5599 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
