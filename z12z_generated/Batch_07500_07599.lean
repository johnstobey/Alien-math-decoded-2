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
theorem generated_07500 (tag : Fin 10000) (htag : tag.val = 7500) (k : Ring12) : tag.val = 7500 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07501 (tag : Fin 10000) (htag : tag.val = 7501) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7501 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07502 (tag : Fin 10000) (htag : tag.val = 7502) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7502 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07503 (tag : Fin 10000) (htag : tag.val = 7503) (x : State) (e : Event) (dr : Ring12) : tag.val = 7503 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07504 (tag : Fin 10000) (htag : tag.val = 7504) (x : State) (e : Event) (dr : Ring12) : tag.val = 7504 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07505 (tag : Fin 10000) (htag : tag.val = 7505) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7505 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07506 (tag : Fin 10000) (htag : tag.val = 7506) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7506 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07507 (tag : Fin 10000) (htag : tag.val = 7507) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7507 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07508 (tag : Fin 10000) (htag : tag.val = 7508) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7508 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07509 (tag : Fin 10000) (htag : tag.val = 7509) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7509 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07510 (tag : Fin 10000) (htag : tag.val = 7510) (k : Ring12) : tag.val = 7510 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07511 (tag : Fin 10000) (htag : tag.val = 7511) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7511 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07512 (tag : Fin 10000) (htag : tag.val = 7512) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7512 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07513 (tag : Fin 10000) (htag : tag.val = 7513) (x : State) (e : Event) (dr : Ring12) : tag.val = 7513 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07514 (tag : Fin 10000) (htag : tag.val = 7514) (x : State) (e : Event) (dr : Ring12) : tag.val = 7514 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07515 (tag : Fin 10000) (htag : tag.val = 7515) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7515 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07516 (tag : Fin 10000) (htag : tag.val = 7516) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7516 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07517 (tag : Fin 10000) (htag : tag.val = 7517) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7517 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07518 (tag : Fin 10000) (htag : tag.val = 7518) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7518 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07519 (tag : Fin 10000) (htag : tag.val = 7519) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7519 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07520 (tag : Fin 10000) (htag : tag.val = 7520) (k : Ring12) : tag.val = 7520 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07521 (tag : Fin 10000) (htag : tag.val = 7521) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7521 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07522 (tag : Fin 10000) (htag : tag.val = 7522) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7522 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07523 (tag : Fin 10000) (htag : tag.val = 7523) (x : State) (e : Event) (dr : Ring12) : tag.val = 7523 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07524 (tag : Fin 10000) (htag : tag.val = 7524) (x : State) (e : Event) (dr : Ring12) : tag.val = 7524 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07525 (tag : Fin 10000) (htag : tag.val = 7525) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7525 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07526 (tag : Fin 10000) (htag : tag.val = 7526) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7526 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07527 (tag : Fin 10000) (htag : tag.val = 7527) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7527 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07528 (tag : Fin 10000) (htag : tag.val = 7528) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7528 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07529 (tag : Fin 10000) (htag : tag.val = 7529) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7529 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07530 (tag : Fin 10000) (htag : tag.val = 7530) (k : Ring12) : tag.val = 7530 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07531 (tag : Fin 10000) (htag : tag.val = 7531) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7531 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07532 (tag : Fin 10000) (htag : tag.val = 7532) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7532 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07533 (tag : Fin 10000) (htag : tag.val = 7533) (x : State) (e : Event) (dr : Ring12) : tag.val = 7533 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07534 (tag : Fin 10000) (htag : tag.val = 7534) (x : State) (e : Event) (dr : Ring12) : tag.val = 7534 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07535 (tag : Fin 10000) (htag : tag.val = 7535) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7535 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07536 (tag : Fin 10000) (htag : tag.val = 7536) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7536 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07537 (tag : Fin 10000) (htag : tag.val = 7537) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7537 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07538 (tag : Fin 10000) (htag : tag.val = 7538) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7538 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07539 (tag : Fin 10000) (htag : tag.val = 7539) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7539 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07540 (tag : Fin 10000) (htag : tag.val = 7540) (k : Ring12) : tag.val = 7540 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07541 (tag : Fin 10000) (htag : tag.val = 7541) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7541 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07542 (tag : Fin 10000) (htag : tag.val = 7542) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7542 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07543 (tag : Fin 10000) (htag : tag.val = 7543) (x : State) (e : Event) (dr : Ring12) : tag.val = 7543 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07544 (tag : Fin 10000) (htag : tag.val = 7544) (x : State) (e : Event) (dr : Ring12) : tag.val = 7544 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07545 (tag : Fin 10000) (htag : tag.val = 7545) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7545 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07546 (tag : Fin 10000) (htag : tag.val = 7546) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7546 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07547 (tag : Fin 10000) (htag : tag.val = 7547) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7547 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07548 (tag : Fin 10000) (htag : tag.val = 7548) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7548 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07549 (tag : Fin 10000) (htag : tag.val = 7549) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7549 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07550 (tag : Fin 10000) (htag : tag.val = 7550) (k : Ring12) : tag.val = 7550 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07551 (tag : Fin 10000) (htag : tag.val = 7551) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7551 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07552 (tag : Fin 10000) (htag : tag.val = 7552) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7552 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07553 (tag : Fin 10000) (htag : tag.val = 7553) (x : State) (e : Event) (dr : Ring12) : tag.val = 7553 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07554 (tag : Fin 10000) (htag : tag.val = 7554) (x : State) (e : Event) (dr : Ring12) : tag.val = 7554 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07555 (tag : Fin 10000) (htag : tag.val = 7555) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7555 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07556 (tag : Fin 10000) (htag : tag.val = 7556) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7556 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07557 (tag : Fin 10000) (htag : tag.val = 7557) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7557 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07558 (tag : Fin 10000) (htag : tag.val = 7558) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7558 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07559 (tag : Fin 10000) (htag : tag.val = 7559) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7559 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07560 (tag : Fin 10000) (htag : tag.val = 7560) (k : Ring12) : tag.val = 7560 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07561 (tag : Fin 10000) (htag : tag.val = 7561) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7561 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07562 (tag : Fin 10000) (htag : tag.val = 7562) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7562 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07563 (tag : Fin 10000) (htag : tag.val = 7563) (x : State) (e : Event) (dr : Ring12) : tag.val = 7563 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07564 (tag : Fin 10000) (htag : tag.val = 7564) (x : State) (e : Event) (dr : Ring12) : tag.val = 7564 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07565 (tag : Fin 10000) (htag : tag.val = 7565) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7565 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07566 (tag : Fin 10000) (htag : tag.val = 7566) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7566 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07567 (tag : Fin 10000) (htag : tag.val = 7567) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7567 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07568 (tag : Fin 10000) (htag : tag.val = 7568) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7568 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07569 (tag : Fin 10000) (htag : tag.val = 7569) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7569 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07570 (tag : Fin 10000) (htag : tag.val = 7570) (k : Ring12) : tag.val = 7570 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07571 (tag : Fin 10000) (htag : tag.val = 7571) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7571 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07572 (tag : Fin 10000) (htag : tag.val = 7572) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7572 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07573 (tag : Fin 10000) (htag : tag.val = 7573) (x : State) (e : Event) (dr : Ring12) : tag.val = 7573 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07574 (tag : Fin 10000) (htag : tag.val = 7574) (x : State) (e : Event) (dr : Ring12) : tag.val = 7574 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07575 (tag : Fin 10000) (htag : tag.val = 7575) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7575 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07576 (tag : Fin 10000) (htag : tag.val = 7576) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7576 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07577 (tag : Fin 10000) (htag : tag.val = 7577) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7577 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07578 (tag : Fin 10000) (htag : tag.val = 7578) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7578 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07579 (tag : Fin 10000) (htag : tag.val = 7579) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7579 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07580 (tag : Fin 10000) (htag : tag.val = 7580) (k : Ring12) : tag.val = 7580 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07581 (tag : Fin 10000) (htag : tag.val = 7581) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7581 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07582 (tag : Fin 10000) (htag : tag.val = 7582) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7582 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07583 (tag : Fin 10000) (htag : tag.val = 7583) (x : State) (e : Event) (dr : Ring12) : tag.val = 7583 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07584 (tag : Fin 10000) (htag : tag.val = 7584) (x : State) (e : Event) (dr : Ring12) : tag.val = 7584 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07585 (tag : Fin 10000) (htag : tag.val = 7585) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7585 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07586 (tag : Fin 10000) (htag : tag.val = 7586) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7586 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07587 (tag : Fin 10000) (htag : tag.val = 7587) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7587 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07588 (tag : Fin 10000) (htag : tag.val = 7588) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7588 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07589 (tag : Fin 10000) (htag : tag.val = 7589) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7589 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07590 (tag : Fin 10000) (htag : tag.val = 7590) (k : Ring12) : tag.val = 7590 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07591 (tag : Fin 10000) (htag : tag.val = 7591) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7591 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07592 (tag : Fin 10000) (htag : tag.val = 7592) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7592 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07593 (tag : Fin 10000) (htag : tag.val = 7593) (x : State) (e : Event) (dr : Ring12) : tag.val = 7593 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07594 (tag : Fin 10000) (htag : tag.val = 7594) (x : State) (e : Event) (dr : Ring12) : tag.val = 7594 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07595 (tag : Fin 10000) (htag : tag.val = 7595) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7595 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07596 (tag : Fin 10000) (htag : tag.val = 7596) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7596 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07597 (tag : Fin 10000) (htag : tag.val = 7597) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7597 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07598 (tag : Fin 10000) (htag : tag.val = 7598) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7598 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07599 (tag : Fin 10000) (htag : tag.val = 7599) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7599 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
