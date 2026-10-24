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
theorem generated_08400 (tag : Fin 10000) (htag : tag.val = 8400) (k : Ring12) : tag.val = 8400 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08401 (tag : Fin 10000) (htag : tag.val = 8401) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8401 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08402 (tag : Fin 10000) (htag : tag.val = 8402) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8402 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08403 (tag : Fin 10000) (htag : tag.val = 8403) (x : State) (e : Event) (dr : Ring12) : tag.val = 8403 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08404 (tag : Fin 10000) (htag : tag.val = 8404) (x : State) (e : Event) (dr : Ring12) : tag.val = 8404 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08405 (tag : Fin 10000) (htag : tag.val = 8405) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8405 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08406 (tag : Fin 10000) (htag : tag.val = 8406) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8406 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08407 (tag : Fin 10000) (htag : tag.val = 8407) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8407 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08408 (tag : Fin 10000) (htag : tag.val = 8408) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8408 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08409 (tag : Fin 10000) (htag : tag.val = 8409) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8409 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08410 (tag : Fin 10000) (htag : tag.val = 8410) (k : Ring12) : tag.val = 8410 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08411 (tag : Fin 10000) (htag : tag.val = 8411) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8411 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08412 (tag : Fin 10000) (htag : tag.val = 8412) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8412 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08413 (tag : Fin 10000) (htag : tag.val = 8413) (x : State) (e : Event) (dr : Ring12) : tag.val = 8413 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08414 (tag : Fin 10000) (htag : tag.val = 8414) (x : State) (e : Event) (dr : Ring12) : tag.val = 8414 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08415 (tag : Fin 10000) (htag : tag.val = 8415) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8415 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08416 (tag : Fin 10000) (htag : tag.val = 8416) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8416 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08417 (tag : Fin 10000) (htag : tag.val = 8417) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8417 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08418 (tag : Fin 10000) (htag : tag.val = 8418) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8418 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08419 (tag : Fin 10000) (htag : tag.val = 8419) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8419 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08420 (tag : Fin 10000) (htag : tag.val = 8420) (k : Ring12) : tag.val = 8420 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08421 (tag : Fin 10000) (htag : tag.val = 8421) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8421 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08422 (tag : Fin 10000) (htag : tag.val = 8422) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8422 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08423 (tag : Fin 10000) (htag : tag.val = 8423) (x : State) (e : Event) (dr : Ring12) : tag.val = 8423 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08424 (tag : Fin 10000) (htag : tag.val = 8424) (x : State) (e : Event) (dr : Ring12) : tag.val = 8424 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08425 (tag : Fin 10000) (htag : tag.val = 8425) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8425 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08426 (tag : Fin 10000) (htag : tag.val = 8426) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8426 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08427 (tag : Fin 10000) (htag : tag.val = 8427) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8427 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08428 (tag : Fin 10000) (htag : tag.val = 8428) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8428 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08429 (tag : Fin 10000) (htag : tag.val = 8429) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8429 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08430 (tag : Fin 10000) (htag : tag.val = 8430) (k : Ring12) : tag.val = 8430 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08431 (tag : Fin 10000) (htag : tag.val = 8431) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8431 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08432 (tag : Fin 10000) (htag : tag.val = 8432) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8432 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08433 (tag : Fin 10000) (htag : tag.val = 8433) (x : State) (e : Event) (dr : Ring12) : tag.val = 8433 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08434 (tag : Fin 10000) (htag : tag.val = 8434) (x : State) (e : Event) (dr : Ring12) : tag.val = 8434 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08435 (tag : Fin 10000) (htag : tag.val = 8435) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8435 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08436 (tag : Fin 10000) (htag : tag.val = 8436) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8436 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08437 (tag : Fin 10000) (htag : tag.val = 8437) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8437 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08438 (tag : Fin 10000) (htag : tag.val = 8438) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8438 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08439 (tag : Fin 10000) (htag : tag.val = 8439) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8439 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08440 (tag : Fin 10000) (htag : tag.val = 8440) (k : Ring12) : tag.val = 8440 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08441 (tag : Fin 10000) (htag : tag.val = 8441) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8441 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08442 (tag : Fin 10000) (htag : tag.val = 8442) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8442 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08443 (tag : Fin 10000) (htag : tag.val = 8443) (x : State) (e : Event) (dr : Ring12) : tag.val = 8443 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08444 (tag : Fin 10000) (htag : tag.val = 8444) (x : State) (e : Event) (dr : Ring12) : tag.val = 8444 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08445 (tag : Fin 10000) (htag : tag.val = 8445) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8445 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08446 (tag : Fin 10000) (htag : tag.val = 8446) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8446 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08447 (tag : Fin 10000) (htag : tag.val = 8447) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8447 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08448 (tag : Fin 10000) (htag : tag.val = 8448) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8448 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08449 (tag : Fin 10000) (htag : tag.val = 8449) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8449 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08450 (tag : Fin 10000) (htag : tag.val = 8450) (k : Ring12) : tag.val = 8450 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08451 (tag : Fin 10000) (htag : tag.val = 8451) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8451 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08452 (tag : Fin 10000) (htag : tag.val = 8452) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8452 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08453 (tag : Fin 10000) (htag : tag.val = 8453) (x : State) (e : Event) (dr : Ring12) : tag.val = 8453 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08454 (tag : Fin 10000) (htag : tag.val = 8454) (x : State) (e : Event) (dr : Ring12) : tag.val = 8454 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08455 (tag : Fin 10000) (htag : tag.val = 8455) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8455 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08456 (tag : Fin 10000) (htag : tag.val = 8456) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8456 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08457 (tag : Fin 10000) (htag : tag.val = 8457) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8457 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08458 (tag : Fin 10000) (htag : tag.val = 8458) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8458 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08459 (tag : Fin 10000) (htag : tag.val = 8459) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8459 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08460 (tag : Fin 10000) (htag : tag.val = 8460) (k : Ring12) : tag.val = 8460 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08461 (tag : Fin 10000) (htag : tag.val = 8461) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8461 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08462 (tag : Fin 10000) (htag : tag.val = 8462) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8462 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08463 (tag : Fin 10000) (htag : tag.val = 8463) (x : State) (e : Event) (dr : Ring12) : tag.val = 8463 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08464 (tag : Fin 10000) (htag : tag.val = 8464) (x : State) (e : Event) (dr : Ring12) : tag.val = 8464 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08465 (tag : Fin 10000) (htag : tag.val = 8465) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8465 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08466 (tag : Fin 10000) (htag : tag.val = 8466) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8466 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08467 (tag : Fin 10000) (htag : tag.val = 8467) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8467 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08468 (tag : Fin 10000) (htag : tag.val = 8468) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8468 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08469 (tag : Fin 10000) (htag : tag.val = 8469) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8469 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08470 (tag : Fin 10000) (htag : tag.val = 8470) (k : Ring12) : tag.val = 8470 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08471 (tag : Fin 10000) (htag : tag.val = 8471) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8471 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08472 (tag : Fin 10000) (htag : tag.val = 8472) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8472 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08473 (tag : Fin 10000) (htag : tag.val = 8473) (x : State) (e : Event) (dr : Ring12) : tag.val = 8473 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08474 (tag : Fin 10000) (htag : tag.val = 8474) (x : State) (e : Event) (dr : Ring12) : tag.val = 8474 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08475 (tag : Fin 10000) (htag : tag.val = 8475) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8475 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08476 (tag : Fin 10000) (htag : tag.val = 8476) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8476 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08477 (tag : Fin 10000) (htag : tag.val = 8477) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8477 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08478 (tag : Fin 10000) (htag : tag.val = 8478) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8478 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08479 (tag : Fin 10000) (htag : tag.val = 8479) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8479 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08480 (tag : Fin 10000) (htag : tag.val = 8480) (k : Ring12) : tag.val = 8480 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08481 (tag : Fin 10000) (htag : tag.val = 8481) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8481 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08482 (tag : Fin 10000) (htag : tag.val = 8482) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8482 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08483 (tag : Fin 10000) (htag : tag.val = 8483) (x : State) (e : Event) (dr : Ring12) : tag.val = 8483 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08484 (tag : Fin 10000) (htag : tag.val = 8484) (x : State) (e : Event) (dr : Ring12) : tag.val = 8484 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08485 (tag : Fin 10000) (htag : tag.val = 8485) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8485 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08486 (tag : Fin 10000) (htag : tag.val = 8486) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8486 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08487 (tag : Fin 10000) (htag : tag.val = 8487) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8487 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08488 (tag : Fin 10000) (htag : tag.val = 8488) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8488 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08489 (tag : Fin 10000) (htag : tag.val = 8489) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8489 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_08490 (tag : Fin 10000) (htag : tag.val = 8490) (k : Ring12) : tag.val = 8490 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_08491 (tag : Fin 10000) (htag : tag.val = 8491) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8491 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_08492 (tag : Fin 10000) (htag : tag.val = 8492) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8492 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_08493 (tag : Fin 10000) (htag : tag.val = 8493) (x : State) (e : Event) (dr : Ring12) : tag.val = 8493 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_08494 (tag : Fin 10000) (htag : tag.val = 8494) (x : State) (e : Event) (dr : Ring12) : tag.val = 8494 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_08495 (tag : Fin 10000) (htag : tag.val = 8495) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8495 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_08496 (tag : Fin 10000) (htag : tag.val = 8496) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 8496 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_08497 (tag : Fin 10000) (htag : tag.val = 8497) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 8497 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_08498 (tag : Fin 10000) (htag : tag.val = 8498) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 8498 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_08499 (tag : Fin 10000) (htag : tag.val = 8499) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 8499 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
