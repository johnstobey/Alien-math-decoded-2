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
theorem generated_01400 (tag : Fin 10000) (htag : tag.val = 1400) (k : Ring12) : tag.val = 1400 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01401 (tag : Fin 10000) (htag : tag.val = 1401) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1401 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01402 (tag : Fin 10000) (htag : tag.val = 1402) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1402 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01403 (tag : Fin 10000) (htag : tag.val = 1403) (x : State) (e : Event) (dr : Ring12) : tag.val = 1403 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01404 (tag : Fin 10000) (htag : tag.val = 1404) (x : State) (e : Event) (dr : Ring12) : tag.val = 1404 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01405 (tag : Fin 10000) (htag : tag.val = 1405) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1405 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01406 (tag : Fin 10000) (htag : tag.val = 1406) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1406 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01407 (tag : Fin 10000) (htag : tag.val = 1407) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1407 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01408 (tag : Fin 10000) (htag : tag.val = 1408) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1408 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01409 (tag : Fin 10000) (htag : tag.val = 1409) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1409 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01410 (tag : Fin 10000) (htag : tag.val = 1410) (k : Ring12) : tag.val = 1410 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01411 (tag : Fin 10000) (htag : tag.val = 1411) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1411 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01412 (tag : Fin 10000) (htag : tag.val = 1412) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1412 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01413 (tag : Fin 10000) (htag : tag.val = 1413) (x : State) (e : Event) (dr : Ring12) : tag.val = 1413 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01414 (tag : Fin 10000) (htag : tag.val = 1414) (x : State) (e : Event) (dr : Ring12) : tag.val = 1414 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01415 (tag : Fin 10000) (htag : tag.val = 1415) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1415 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01416 (tag : Fin 10000) (htag : tag.val = 1416) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1416 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01417 (tag : Fin 10000) (htag : tag.val = 1417) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1417 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01418 (tag : Fin 10000) (htag : tag.val = 1418) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1418 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01419 (tag : Fin 10000) (htag : tag.val = 1419) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1419 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01420 (tag : Fin 10000) (htag : tag.val = 1420) (k : Ring12) : tag.val = 1420 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01421 (tag : Fin 10000) (htag : tag.val = 1421) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1421 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01422 (tag : Fin 10000) (htag : tag.val = 1422) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1422 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01423 (tag : Fin 10000) (htag : tag.val = 1423) (x : State) (e : Event) (dr : Ring12) : tag.val = 1423 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01424 (tag : Fin 10000) (htag : tag.val = 1424) (x : State) (e : Event) (dr : Ring12) : tag.val = 1424 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01425 (tag : Fin 10000) (htag : tag.val = 1425) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1425 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01426 (tag : Fin 10000) (htag : tag.val = 1426) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1426 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01427 (tag : Fin 10000) (htag : tag.val = 1427) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1427 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01428 (tag : Fin 10000) (htag : tag.val = 1428) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1428 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01429 (tag : Fin 10000) (htag : tag.val = 1429) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1429 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01430 (tag : Fin 10000) (htag : tag.val = 1430) (k : Ring12) : tag.val = 1430 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01431 (tag : Fin 10000) (htag : tag.val = 1431) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1431 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01432 (tag : Fin 10000) (htag : tag.val = 1432) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1432 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01433 (tag : Fin 10000) (htag : tag.val = 1433) (x : State) (e : Event) (dr : Ring12) : tag.val = 1433 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01434 (tag : Fin 10000) (htag : tag.val = 1434) (x : State) (e : Event) (dr : Ring12) : tag.val = 1434 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01435 (tag : Fin 10000) (htag : tag.val = 1435) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1435 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01436 (tag : Fin 10000) (htag : tag.val = 1436) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1436 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01437 (tag : Fin 10000) (htag : tag.val = 1437) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1437 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01438 (tag : Fin 10000) (htag : tag.val = 1438) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1438 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01439 (tag : Fin 10000) (htag : tag.val = 1439) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1439 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01440 (tag : Fin 10000) (htag : tag.val = 1440) (k : Ring12) : tag.val = 1440 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01441 (tag : Fin 10000) (htag : tag.val = 1441) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1441 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01442 (tag : Fin 10000) (htag : tag.val = 1442) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1442 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01443 (tag : Fin 10000) (htag : tag.val = 1443) (x : State) (e : Event) (dr : Ring12) : tag.val = 1443 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01444 (tag : Fin 10000) (htag : tag.val = 1444) (x : State) (e : Event) (dr : Ring12) : tag.val = 1444 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01445 (tag : Fin 10000) (htag : tag.val = 1445) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1445 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01446 (tag : Fin 10000) (htag : tag.val = 1446) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1446 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01447 (tag : Fin 10000) (htag : tag.val = 1447) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1447 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01448 (tag : Fin 10000) (htag : tag.val = 1448) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1448 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01449 (tag : Fin 10000) (htag : tag.val = 1449) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1449 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01450 (tag : Fin 10000) (htag : tag.val = 1450) (k : Ring12) : tag.val = 1450 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01451 (tag : Fin 10000) (htag : tag.val = 1451) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1451 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01452 (tag : Fin 10000) (htag : tag.val = 1452) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1452 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01453 (tag : Fin 10000) (htag : tag.val = 1453) (x : State) (e : Event) (dr : Ring12) : tag.val = 1453 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01454 (tag : Fin 10000) (htag : tag.val = 1454) (x : State) (e : Event) (dr : Ring12) : tag.val = 1454 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01455 (tag : Fin 10000) (htag : tag.val = 1455) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1455 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01456 (tag : Fin 10000) (htag : tag.val = 1456) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1456 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01457 (tag : Fin 10000) (htag : tag.val = 1457) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1457 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01458 (tag : Fin 10000) (htag : tag.val = 1458) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1458 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01459 (tag : Fin 10000) (htag : tag.val = 1459) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1459 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01460 (tag : Fin 10000) (htag : tag.val = 1460) (k : Ring12) : tag.val = 1460 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01461 (tag : Fin 10000) (htag : tag.val = 1461) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1461 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01462 (tag : Fin 10000) (htag : tag.val = 1462) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1462 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01463 (tag : Fin 10000) (htag : tag.val = 1463) (x : State) (e : Event) (dr : Ring12) : tag.val = 1463 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01464 (tag : Fin 10000) (htag : tag.val = 1464) (x : State) (e : Event) (dr : Ring12) : tag.val = 1464 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01465 (tag : Fin 10000) (htag : tag.val = 1465) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1465 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01466 (tag : Fin 10000) (htag : tag.val = 1466) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1466 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01467 (tag : Fin 10000) (htag : tag.val = 1467) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1467 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01468 (tag : Fin 10000) (htag : tag.val = 1468) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1468 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01469 (tag : Fin 10000) (htag : tag.val = 1469) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1469 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01470 (tag : Fin 10000) (htag : tag.val = 1470) (k : Ring12) : tag.val = 1470 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01471 (tag : Fin 10000) (htag : tag.val = 1471) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1471 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01472 (tag : Fin 10000) (htag : tag.val = 1472) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1472 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01473 (tag : Fin 10000) (htag : tag.val = 1473) (x : State) (e : Event) (dr : Ring12) : tag.val = 1473 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01474 (tag : Fin 10000) (htag : tag.val = 1474) (x : State) (e : Event) (dr : Ring12) : tag.val = 1474 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01475 (tag : Fin 10000) (htag : tag.val = 1475) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1475 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01476 (tag : Fin 10000) (htag : tag.val = 1476) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1476 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01477 (tag : Fin 10000) (htag : tag.val = 1477) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1477 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01478 (tag : Fin 10000) (htag : tag.val = 1478) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1478 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01479 (tag : Fin 10000) (htag : tag.val = 1479) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1479 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01480 (tag : Fin 10000) (htag : tag.val = 1480) (k : Ring12) : tag.val = 1480 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01481 (tag : Fin 10000) (htag : tag.val = 1481) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1481 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01482 (tag : Fin 10000) (htag : tag.val = 1482) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1482 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01483 (tag : Fin 10000) (htag : tag.val = 1483) (x : State) (e : Event) (dr : Ring12) : tag.val = 1483 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01484 (tag : Fin 10000) (htag : tag.val = 1484) (x : State) (e : Event) (dr : Ring12) : tag.val = 1484 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01485 (tag : Fin 10000) (htag : tag.val = 1485) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1485 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01486 (tag : Fin 10000) (htag : tag.val = 1486) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1486 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01487 (tag : Fin 10000) (htag : tag.val = 1487) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1487 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01488 (tag : Fin 10000) (htag : tag.val = 1488) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1488 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01489 (tag : Fin 10000) (htag : tag.val = 1489) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1489 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_01490 (tag : Fin 10000) (htag : tag.val = 1490) (k : Ring12) : tag.val = 1490 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_01491 (tag : Fin 10000) (htag : tag.val = 1491) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1491 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_01492 (tag : Fin 10000) (htag : tag.val = 1492) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1492 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_01493 (tag : Fin 10000) (htag : tag.val = 1493) (x : State) (e : Event) (dr : Ring12) : tag.val = 1493 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_01494 (tag : Fin 10000) (htag : tag.val = 1494) (x : State) (e : Event) (dr : Ring12) : tag.val = 1494 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_01495 (tag : Fin 10000) (htag : tag.val = 1495) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1495 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_01496 (tag : Fin 10000) (htag : tag.val = 1496) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 1496 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_01497 (tag : Fin 10000) (htag : tag.val = 1497) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 1497 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_01498 (tag : Fin 10000) (htag : tag.val = 1498) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 1498 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_01499 (tag : Fin 10000) (htag : tag.val = 1499) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 1499 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
