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
theorem generated_08500 (tag : Fin 10000) (htag : tag.val = 8500) (k : Ring12) : tag.val = 8500 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08501 (tag : Fin 10000) (htag : tag.val = 8501) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8501 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08502 (tag : Fin 10000) (htag : tag.val = 8502) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8502 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08503 (tag : Fin 10000) (htag : tag.val = 8503) (x : State) (e : Event) (dr : Ring12) : tag.val = 8503 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08504 (tag : Fin 10000) (htag : tag.val = 8504) (x : State) (e : Event) (dr : Ring12) : tag.val = 8504 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08505 (tag : Fin 10000) (htag : tag.val = 8505) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8505 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08506 (tag : Fin 10000) (htag : tag.val = 8506) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8506 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08507 (tag : Fin 10000) (htag : tag.val = 8507) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8507 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08508 (tag : Fin 10000) (htag : tag.val = 8508) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8508 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08509 (tag : Fin 10000) (htag : tag.val = 8509) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8509 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08510 (tag : Fin 10000) (htag : tag.val = 8510) (k : Ring12) : tag.val = 8510 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08511 (tag : Fin 10000) (htag : tag.val = 8511) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8511 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08512 (tag : Fin 10000) (htag : tag.val = 8512) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8512 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08513 (tag : Fin 10000) (htag : tag.val = 8513) (x : State) (e : Event) (dr : Ring12) : tag.val = 8513 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08514 (tag : Fin 10000) (htag : tag.val = 8514) (x : State) (e : Event) (dr : Ring12) : tag.val = 8514 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08515 (tag : Fin 10000) (htag : tag.val = 8515) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8515 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08516 (tag : Fin 10000) (htag : tag.val = 8516) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8516 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08517 (tag : Fin 10000) (htag : tag.val = 8517) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8517 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08518 (tag : Fin 10000) (htag : tag.val = 8518) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8518 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08519 (tag : Fin 10000) (htag : tag.val = 8519) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8519 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08520 (tag : Fin 10000) (htag : tag.val = 8520) (k : Ring12) : tag.val = 8520 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08521 (tag : Fin 10000) (htag : tag.val = 8521) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8521 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08522 (tag : Fin 10000) (htag : tag.val = 8522) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8522 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08523 (tag : Fin 10000) (htag : tag.val = 8523) (x : State) (e : Event) (dr : Ring12) : tag.val = 8523 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08524 (tag : Fin 10000) (htag : tag.val = 8524) (x : State) (e : Event) (dr : Ring12) : tag.val = 8524 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08525 (tag : Fin 10000) (htag : tag.val = 8525) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8525 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08526 (tag : Fin 10000) (htag : tag.val = 8526) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8526 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08527 (tag : Fin 10000) (htag : tag.val = 8527) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8527 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08528 (tag : Fin 10000) (htag : tag.val = 8528) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8528 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08529 (tag : Fin 10000) (htag : tag.val = 8529) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8529 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08530 (tag : Fin 10000) (htag : tag.val = 8530) (k : Ring12) : tag.val = 8530 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08531 (tag : Fin 10000) (htag : tag.val = 8531) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8531 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08532 (tag : Fin 10000) (htag : tag.val = 8532) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8532 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08533 (tag : Fin 10000) (htag : tag.val = 8533) (x : State) (e : Event) (dr : Ring12) : tag.val = 8533 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08534 (tag : Fin 10000) (htag : tag.val = 8534) (x : State) (e : Event) (dr : Ring12) : tag.val = 8534 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08535 (tag : Fin 10000) (htag : tag.val = 8535) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8535 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08536 (tag : Fin 10000) (htag : tag.val = 8536) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8536 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08537 (tag : Fin 10000) (htag : tag.val = 8537) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8537 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08538 (tag : Fin 10000) (htag : tag.val = 8538) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8538 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08539 (tag : Fin 10000) (htag : tag.val = 8539) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8539 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08540 (tag : Fin 10000) (htag : tag.val = 8540) (k : Ring12) : tag.val = 8540 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08541 (tag : Fin 10000) (htag : tag.val = 8541) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8541 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08542 (tag : Fin 10000) (htag : tag.val = 8542) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8542 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08543 (tag : Fin 10000) (htag : tag.val = 8543) (x : State) (e : Event) (dr : Ring12) : tag.val = 8543 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08544 (tag : Fin 10000) (htag : tag.val = 8544) (x : State) (e : Event) (dr : Ring12) : tag.val = 8544 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08545 (tag : Fin 10000) (htag : tag.val = 8545) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8545 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08546 (tag : Fin 10000) (htag : tag.val = 8546) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8546 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08547 (tag : Fin 10000) (htag : tag.val = 8547) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8547 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08548 (tag : Fin 10000) (htag : tag.val = 8548) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8548 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08549 (tag : Fin 10000) (htag : tag.val = 8549) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8549 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08550 (tag : Fin 10000) (htag : tag.val = 8550) (k : Ring12) : tag.val = 8550 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08551 (tag : Fin 10000) (htag : tag.val = 8551) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8551 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08552 (tag : Fin 10000) (htag : tag.val = 8552) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8552 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08553 (tag : Fin 10000) (htag : tag.val = 8553) (x : State) (e : Event) (dr : Ring12) : tag.val = 8553 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08554 (tag : Fin 10000) (htag : tag.val = 8554) (x : State) (e : Event) (dr : Ring12) : tag.val = 8554 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08555 (tag : Fin 10000) (htag : tag.val = 8555) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8555 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08556 (tag : Fin 10000) (htag : tag.val = 8556) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8556 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08557 (tag : Fin 10000) (htag : tag.val = 8557) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8557 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08558 (tag : Fin 10000) (htag : tag.val = 8558) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8558 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08559 (tag : Fin 10000) (htag : tag.val = 8559) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8559 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08560 (tag : Fin 10000) (htag : tag.val = 8560) (k : Ring12) : tag.val = 8560 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08561 (tag : Fin 10000) (htag : tag.val = 8561) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8561 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08562 (tag : Fin 10000) (htag : tag.val = 8562) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8562 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08563 (tag : Fin 10000) (htag : tag.val = 8563) (x : State) (e : Event) (dr : Ring12) : tag.val = 8563 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08564 (tag : Fin 10000) (htag : tag.val = 8564) (x : State) (e : Event) (dr : Ring12) : tag.val = 8564 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08565 (tag : Fin 10000) (htag : tag.val = 8565) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8565 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08566 (tag : Fin 10000) (htag : tag.val = 8566) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8566 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08567 (tag : Fin 10000) (htag : tag.val = 8567) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8567 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08568 (tag : Fin 10000) (htag : tag.val = 8568) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8568 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08569 (tag : Fin 10000) (htag : tag.val = 8569) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8569 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08570 (tag : Fin 10000) (htag : tag.val = 8570) (k : Ring12) : tag.val = 8570 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08571 (tag : Fin 10000) (htag : tag.val = 8571) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8571 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08572 (tag : Fin 10000) (htag : tag.val = 8572) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8572 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08573 (tag : Fin 10000) (htag : tag.val = 8573) (x : State) (e : Event) (dr : Ring12) : tag.val = 8573 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08574 (tag : Fin 10000) (htag : tag.val = 8574) (x : State) (e : Event) (dr : Ring12) : tag.val = 8574 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08575 (tag : Fin 10000) (htag : tag.val = 8575) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8575 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08576 (tag : Fin 10000) (htag : tag.val = 8576) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8576 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08577 (tag : Fin 10000) (htag : tag.val = 8577) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8577 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08578 (tag : Fin 10000) (htag : tag.val = 8578) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8578 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08579 (tag : Fin 10000) (htag : tag.val = 8579) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8579 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08580 (tag : Fin 10000) (htag : tag.val = 8580) (k : Ring12) : tag.val = 8580 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08581 (tag : Fin 10000) (htag : tag.val = 8581) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8581 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08582 (tag : Fin 10000) (htag : tag.val = 8582) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8582 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08583 (tag : Fin 10000) (htag : tag.val = 8583) (x : State) (e : Event) (dr : Ring12) : tag.val = 8583 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08584 (tag : Fin 10000) (htag : tag.val = 8584) (x : State) (e : Event) (dr : Ring12) : tag.val = 8584 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08585 (tag : Fin 10000) (htag : tag.val = 8585) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8585 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08586 (tag : Fin 10000) (htag : tag.val = 8586) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8586 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08587 (tag : Fin 10000) (htag : tag.val = 8587) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8587 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08588 (tag : Fin 10000) (htag : tag.val = 8588) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8588 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08589 (tag : Fin 10000) (htag : tag.val = 8589) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8589 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08590 (tag : Fin 10000) (htag : tag.val = 8590) (k : Ring12) : tag.val = 8590 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08591 (tag : Fin 10000) (htag : tag.val = 8591) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8591 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08592 (tag : Fin 10000) (htag : tag.val = 8592) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8592 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08593 (tag : Fin 10000) (htag : tag.val = 8593) (x : State) (e : Event) (dr : Ring12) : tag.val = 8593 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08594 (tag : Fin 10000) (htag : tag.val = 8594) (x : State) (e : Event) (dr : Ring12) : tag.val = 8594 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08595 (tag : Fin 10000) (htag : tag.val = 8595) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8595 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08596 (tag : Fin 10000) (htag : tag.val = 8596) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8596 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08597 (tag : Fin 10000) (htag : tag.val = 8597) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8597 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08598 (tag : Fin 10000) (htag : tag.val = 8598) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8598 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08599 (tag : Fin 10000) (htag : tag.val = 8599) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8599 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
