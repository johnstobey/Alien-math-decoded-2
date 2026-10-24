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
theorem generated_01500 (tag : Fin 10000) (htag : tag.val = 1500) (k : Ring12) : tag.val = 1500 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01501 (tag : Fin 10000) (htag : tag.val = 1501) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1501 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01502 (tag : Fin 10000) (htag : tag.val = 1502) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1502 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01503 (tag : Fin 10000) (htag : tag.val = 1503) (x : State) (e : Event) (dr : Ring12) : tag.val = 1503 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01504 (tag : Fin 10000) (htag : tag.val = 1504) (x : State) (e : Event) (dr : Ring12) : tag.val = 1504 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01505 (tag : Fin 10000) (htag : tag.val = 1505) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1505 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01506 (tag : Fin 10000) (htag : tag.val = 1506) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1506 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01507 (tag : Fin 10000) (htag : tag.val = 1507) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1507 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01508 (tag : Fin 10000) (htag : tag.val = 1508) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1508 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01509 (tag : Fin 10000) (htag : tag.val = 1509) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1509 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01510 (tag : Fin 10000) (htag : tag.val = 1510) (k : Ring12) : tag.val = 1510 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01511 (tag : Fin 10000) (htag : tag.val = 1511) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1511 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01512 (tag : Fin 10000) (htag : tag.val = 1512) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1512 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01513 (tag : Fin 10000) (htag : tag.val = 1513) (x : State) (e : Event) (dr : Ring12) : tag.val = 1513 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01514 (tag : Fin 10000) (htag : tag.val = 1514) (x : State) (e : Event) (dr : Ring12) : tag.val = 1514 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01515 (tag : Fin 10000) (htag : tag.val = 1515) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1515 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01516 (tag : Fin 10000) (htag : tag.val = 1516) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1516 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01517 (tag : Fin 10000) (htag : tag.val = 1517) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1517 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01518 (tag : Fin 10000) (htag : tag.val = 1518) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1518 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01519 (tag : Fin 10000) (htag : tag.val = 1519) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1519 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01520 (tag : Fin 10000) (htag : tag.val = 1520) (k : Ring12) : tag.val = 1520 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01521 (tag : Fin 10000) (htag : tag.val = 1521) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1521 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01522 (tag : Fin 10000) (htag : tag.val = 1522) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1522 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01523 (tag : Fin 10000) (htag : tag.val = 1523) (x : State) (e : Event) (dr : Ring12) : tag.val = 1523 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01524 (tag : Fin 10000) (htag : tag.val = 1524) (x : State) (e : Event) (dr : Ring12) : tag.val = 1524 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01525 (tag : Fin 10000) (htag : tag.val = 1525) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1525 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01526 (tag : Fin 10000) (htag : tag.val = 1526) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1526 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01527 (tag : Fin 10000) (htag : tag.val = 1527) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1527 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01528 (tag : Fin 10000) (htag : tag.val = 1528) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1528 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01529 (tag : Fin 10000) (htag : tag.val = 1529) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1529 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01530 (tag : Fin 10000) (htag : tag.val = 1530) (k : Ring12) : tag.val = 1530 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01531 (tag : Fin 10000) (htag : tag.val = 1531) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1531 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01532 (tag : Fin 10000) (htag : tag.val = 1532) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1532 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01533 (tag : Fin 10000) (htag : tag.val = 1533) (x : State) (e : Event) (dr : Ring12) : tag.val = 1533 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01534 (tag : Fin 10000) (htag : tag.val = 1534) (x : State) (e : Event) (dr : Ring12) : tag.val = 1534 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01535 (tag : Fin 10000) (htag : tag.val = 1535) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1535 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01536 (tag : Fin 10000) (htag : tag.val = 1536) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1536 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01537 (tag : Fin 10000) (htag : tag.val = 1537) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1537 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01538 (tag : Fin 10000) (htag : tag.val = 1538) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1538 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01539 (tag : Fin 10000) (htag : tag.val = 1539) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1539 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01540 (tag : Fin 10000) (htag : tag.val = 1540) (k : Ring12) : tag.val = 1540 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01541 (tag : Fin 10000) (htag : tag.val = 1541) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1541 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01542 (tag : Fin 10000) (htag : tag.val = 1542) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1542 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01543 (tag : Fin 10000) (htag : tag.val = 1543) (x : State) (e : Event) (dr : Ring12) : tag.val = 1543 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01544 (tag : Fin 10000) (htag : tag.val = 1544) (x : State) (e : Event) (dr : Ring12) : tag.val = 1544 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01545 (tag : Fin 10000) (htag : tag.val = 1545) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1545 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01546 (tag : Fin 10000) (htag : tag.val = 1546) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1546 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01547 (tag : Fin 10000) (htag : tag.val = 1547) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1547 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01548 (tag : Fin 10000) (htag : tag.val = 1548) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1548 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01549 (tag : Fin 10000) (htag : tag.val = 1549) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1549 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01550 (tag : Fin 10000) (htag : tag.val = 1550) (k : Ring12) : tag.val = 1550 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01551 (tag : Fin 10000) (htag : tag.val = 1551) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1551 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01552 (tag : Fin 10000) (htag : tag.val = 1552) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1552 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01553 (tag : Fin 10000) (htag : tag.val = 1553) (x : State) (e : Event) (dr : Ring12) : tag.val = 1553 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01554 (tag : Fin 10000) (htag : tag.val = 1554) (x : State) (e : Event) (dr : Ring12) : tag.val = 1554 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01555 (tag : Fin 10000) (htag : tag.val = 1555) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1555 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01556 (tag : Fin 10000) (htag : tag.val = 1556) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1556 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01557 (tag : Fin 10000) (htag : tag.val = 1557) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1557 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01558 (tag : Fin 10000) (htag : tag.val = 1558) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1558 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01559 (tag : Fin 10000) (htag : tag.val = 1559) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1559 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01560 (tag : Fin 10000) (htag : tag.val = 1560) (k : Ring12) : tag.val = 1560 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01561 (tag : Fin 10000) (htag : tag.val = 1561) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1561 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01562 (tag : Fin 10000) (htag : tag.val = 1562) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1562 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01563 (tag : Fin 10000) (htag : tag.val = 1563) (x : State) (e : Event) (dr : Ring12) : tag.val = 1563 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01564 (tag : Fin 10000) (htag : tag.val = 1564) (x : State) (e : Event) (dr : Ring12) : tag.val = 1564 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01565 (tag : Fin 10000) (htag : tag.val = 1565) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1565 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01566 (tag : Fin 10000) (htag : tag.val = 1566) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1566 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01567 (tag : Fin 10000) (htag : tag.val = 1567) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1567 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01568 (tag : Fin 10000) (htag : tag.val = 1568) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1568 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01569 (tag : Fin 10000) (htag : tag.val = 1569) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1569 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01570 (tag : Fin 10000) (htag : tag.val = 1570) (k : Ring12) : tag.val = 1570 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01571 (tag : Fin 10000) (htag : tag.val = 1571) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1571 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01572 (tag : Fin 10000) (htag : tag.val = 1572) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1572 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01573 (tag : Fin 10000) (htag : tag.val = 1573) (x : State) (e : Event) (dr : Ring12) : tag.val = 1573 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01574 (tag : Fin 10000) (htag : tag.val = 1574) (x : State) (e : Event) (dr : Ring12) : tag.val = 1574 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01575 (tag : Fin 10000) (htag : tag.val = 1575) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1575 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01576 (tag : Fin 10000) (htag : tag.val = 1576) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1576 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01577 (tag : Fin 10000) (htag : tag.val = 1577) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1577 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01578 (tag : Fin 10000) (htag : tag.val = 1578) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1578 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01579 (tag : Fin 10000) (htag : tag.val = 1579) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1579 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01580 (tag : Fin 10000) (htag : tag.val = 1580) (k : Ring12) : tag.val = 1580 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01581 (tag : Fin 10000) (htag : tag.val = 1581) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1581 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01582 (tag : Fin 10000) (htag : tag.val = 1582) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1582 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01583 (tag : Fin 10000) (htag : tag.val = 1583) (x : State) (e : Event) (dr : Ring12) : tag.val = 1583 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01584 (tag : Fin 10000) (htag : tag.val = 1584) (x : State) (e : Event) (dr : Ring12) : tag.val = 1584 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01585 (tag : Fin 10000) (htag : tag.val = 1585) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1585 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01586 (tag : Fin 10000) (htag : tag.val = 1586) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1586 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01587 (tag : Fin 10000) (htag : tag.val = 1587) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1587 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01588 (tag : Fin 10000) (htag : tag.val = 1588) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1588 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01589 (tag : Fin 10000) (htag : tag.val = 1589) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1589 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01590 (tag : Fin 10000) (htag : tag.val = 1590) (k : Ring12) : tag.val = 1590 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01591 (tag : Fin 10000) (htag : tag.val = 1591) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1591 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01592 (tag : Fin 10000) (htag : tag.val = 1592) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1592 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01593 (tag : Fin 10000) (htag : tag.val = 1593) (x : State) (e : Event) (dr : Ring12) : tag.val = 1593 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01594 (tag : Fin 10000) (htag : tag.val = 1594) (x : State) (e : Event) (dr : Ring12) : tag.val = 1594 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01595 (tag : Fin 10000) (htag : tag.val = 1595) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1595 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01596 (tag : Fin 10000) (htag : tag.val = 1596) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1596 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01597 (tag : Fin 10000) (htag : tag.val = 1597) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1597 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01598 (tag : Fin 10000) (htag : tag.val = 1598) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1598 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01599 (tag : Fin 10000) (htag : tag.val = 1599) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1599 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
