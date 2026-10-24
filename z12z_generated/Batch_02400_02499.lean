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
theorem generated_02400 (tag : Fin 10000) (htag : tag.val = 2400) (k : Ring12) : tag.val = 2400 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02401 (tag : Fin 10000) (htag : tag.val = 2401) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2401 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02402 (tag : Fin 10000) (htag : tag.val = 2402) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2402 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02403 (tag : Fin 10000) (htag : tag.val = 2403) (x : State) (e : Event) (dr : Ring12) : tag.val = 2403 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02404 (tag : Fin 10000) (htag : tag.val = 2404) (x : State) (e : Event) (dr : Ring12) : tag.val = 2404 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02405 (tag : Fin 10000) (htag : tag.val = 2405) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2405 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02406 (tag : Fin 10000) (htag : tag.val = 2406) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2406 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02407 (tag : Fin 10000) (htag : tag.val = 2407) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2407 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02408 (tag : Fin 10000) (htag : tag.val = 2408) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2408 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02409 (tag : Fin 10000) (htag : tag.val = 2409) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2409 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02410 (tag : Fin 10000) (htag : tag.val = 2410) (k : Ring12) : tag.val = 2410 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02411 (tag : Fin 10000) (htag : tag.val = 2411) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2411 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02412 (tag : Fin 10000) (htag : tag.val = 2412) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2412 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02413 (tag : Fin 10000) (htag : tag.val = 2413) (x : State) (e : Event) (dr : Ring12) : tag.val = 2413 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02414 (tag : Fin 10000) (htag : tag.val = 2414) (x : State) (e : Event) (dr : Ring12) : tag.val = 2414 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02415 (tag : Fin 10000) (htag : tag.val = 2415) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2415 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02416 (tag : Fin 10000) (htag : tag.val = 2416) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2416 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02417 (tag : Fin 10000) (htag : tag.val = 2417) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2417 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02418 (tag : Fin 10000) (htag : tag.val = 2418) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2418 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02419 (tag : Fin 10000) (htag : tag.val = 2419) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2419 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02420 (tag : Fin 10000) (htag : tag.val = 2420) (k : Ring12) : tag.val = 2420 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02421 (tag : Fin 10000) (htag : tag.val = 2421) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2421 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02422 (tag : Fin 10000) (htag : tag.val = 2422) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2422 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02423 (tag : Fin 10000) (htag : tag.val = 2423) (x : State) (e : Event) (dr : Ring12) : tag.val = 2423 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02424 (tag : Fin 10000) (htag : tag.val = 2424) (x : State) (e : Event) (dr : Ring12) : tag.val = 2424 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02425 (tag : Fin 10000) (htag : tag.val = 2425) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2425 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02426 (tag : Fin 10000) (htag : tag.val = 2426) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2426 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02427 (tag : Fin 10000) (htag : tag.val = 2427) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2427 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02428 (tag : Fin 10000) (htag : tag.val = 2428) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2428 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02429 (tag : Fin 10000) (htag : tag.val = 2429) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2429 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02430 (tag : Fin 10000) (htag : tag.val = 2430) (k : Ring12) : tag.val = 2430 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02431 (tag : Fin 10000) (htag : tag.val = 2431) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2431 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02432 (tag : Fin 10000) (htag : tag.val = 2432) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2432 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02433 (tag : Fin 10000) (htag : tag.val = 2433) (x : State) (e : Event) (dr : Ring12) : tag.val = 2433 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02434 (tag : Fin 10000) (htag : tag.val = 2434) (x : State) (e : Event) (dr : Ring12) : tag.val = 2434 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02435 (tag : Fin 10000) (htag : tag.val = 2435) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2435 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02436 (tag : Fin 10000) (htag : tag.val = 2436) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2436 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02437 (tag : Fin 10000) (htag : tag.val = 2437) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2437 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02438 (tag : Fin 10000) (htag : tag.val = 2438) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2438 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02439 (tag : Fin 10000) (htag : tag.val = 2439) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2439 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02440 (tag : Fin 10000) (htag : tag.val = 2440) (k : Ring12) : tag.val = 2440 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02441 (tag : Fin 10000) (htag : tag.val = 2441) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2441 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02442 (tag : Fin 10000) (htag : tag.val = 2442) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2442 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02443 (tag : Fin 10000) (htag : tag.val = 2443) (x : State) (e : Event) (dr : Ring12) : tag.val = 2443 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02444 (tag : Fin 10000) (htag : tag.val = 2444) (x : State) (e : Event) (dr : Ring12) : tag.val = 2444 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02445 (tag : Fin 10000) (htag : tag.val = 2445) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2445 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02446 (tag : Fin 10000) (htag : tag.val = 2446) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2446 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02447 (tag : Fin 10000) (htag : tag.val = 2447) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2447 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02448 (tag : Fin 10000) (htag : tag.val = 2448) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2448 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02449 (tag : Fin 10000) (htag : tag.val = 2449) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2449 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02450 (tag : Fin 10000) (htag : tag.val = 2450) (k : Ring12) : tag.val = 2450 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02451 (tag : Fin 10000) (htag : tag.val = 2451) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2451 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02452 (tag : Fin 10000) (htag : tag.val = 2452) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2452 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02453 (tag : Fin 10000) (htag : tag.val = 2453) (x : State) (e : Event) (dr : Ring12) : tag.val = 2453 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02454 (tag : Fin 10000) (htag : tag.val = 2454) (x : State) (e : Event) (dr : Ring12) : tag.val = 2454 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02455 (tag : Fin 10000) (htag : tag.val = 2455) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2455 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02456 (tag : Fin 10000) (htag : tag.val = 2456) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2456 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02457 (tag : Fin 10000) (htag : tag.val = 2457) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2457 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02458 (tag : Fin 10000) (htag : tag.val = 2458) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2458 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02459 (tag : Fin 10000) (htag : tag.val = 2459) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2459 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02460 (tag : Fin 10000) (htag : tag.val = 2460) (k : Ring12) : tag.val = 2460 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02461 (tag : Fin 10000) (htag : tag.val = 2461) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2461 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02462 (tag : Fin 10000) (htag : tag.val = 2462) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2462 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02463 (tag : Fin 10000) (htag : tag.val = 2463) (x : State) (e : Event) (dr : Ring12) : tag.val = 2463 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02464 (tag : Fin 10000) (htag : tag.val = 2464) (x : State) (e : Event) (dr : Ring12) : tag.val = 2464 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02465 (tag : Fin 10000) (htag : tag.val = 2465) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2465 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02466 (tag : Fin 10000) (htag : tag.val = 2466) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2466 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02467 (tag : Fin 10000) (htag : tag.val = 2467) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2467 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02468 (tag : Fin 10000) (htag : tag.val = 2468) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2468 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02469 (tag : Fin 10000) (htag : tag.val = 2469) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2469 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02470 (tag : Fin 10000) (htag : tag.val = 2470) (k : Ring12) : tag.val = 2470 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02471 (tag : Fin 10000) (htag : tag.val = 2471) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2471 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02472 (tag : Fin 10000) (htag : tag.val = 2472) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2472 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02473 (tag : Fin 10000) (htag : tag.val = 2473) (x : State) (e : Event) (dr : Ring12) : tag.val = 2473 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02474 (tag : Fin 10000) (htag : tag.val = 2474) (x : State) (e : Event) (dr : Ring12) : tag.val = 2474 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02475 (tag : Fin 10000) (htag : tag.val = 2475) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2475 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02476 (tag : Fin 10000) (htag : tag.val = 2476) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2476 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02477 (tag : Fin 10000) (htag : tag.val = 2477) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2477 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02478 (tag : Fin 10000) (htag : tag.val = 2478) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2478 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02479 (tag : Fin 10000) (htag : tag.val = 2479) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2479 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02480 (tag : Fin 10000) (htag : tag.val = 2480) (k : Ring12) : tag.val = 2480 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02481 (tag : Fin 10000) (htag : tag.val = 2481) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2481 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02482 (tag : Fin 10000) (htag : tag.val = 2482) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2482 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02483 (tag : Fin 10000) (htag : tag.val = 2483) (x : State) (e : Event) (dr : Ring12) : tag.val = 2483 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02484 (tag : Fin 10000) (htag : tag.val = 2484) (x : State) (e : Event) (dr : Ring12) : tag.val = 2484 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02485 (tag : Fin 10000) (htag : tag.val = 2485) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2485 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02486 (tag : Fin 10000) (htag : tag.val = 2486) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2486 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02487 (tag : Fin 10000) (htag : tag.val = 2487) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2487 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02488 (tag : Fin 10000) (htag : tag.val = 2488) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2488 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02489 (tag : Fin 10000) (htag : tag.val = 2489) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2489 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_02490 (tag : Fin 10000) (htag : tag.val = 2490) (k : Ring12) : tag.val = 2490 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_02491 (tag : Fin 10000) (htag : tag.val = 2491) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2491 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_02492 (tag : Fin 10000) (htag : tag.val = 2492) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2492 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_02493 (tag : Fin 10000) (htag : tag.val = 2493) (x : State) (e : Event) (dr : Ring12) : tag.val = 2493 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_02494 (tag : Fin 10000) (htag : tag.val = 2494) (x : State) (e : Event) (dr : Ring12) : tag.val = 2494 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_02495 (tag : Fin 10000) (htag : tag.val = 2495) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2495 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_02496 (tag : Fin 10000) (htag : tag.val = 2496) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 2496 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_02497 (tag : Fin 10000) (htag : tag.val = 2497) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 2497 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_02498 (tag : Fin 10000) (htag : tag.val = 2498) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 2498 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_02499 (tag : Fin 10000) (htag : tag.val = 2499) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 2499 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
