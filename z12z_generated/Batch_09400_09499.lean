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
theorem generated_09400 (tag : Fin 10000) (htag : tag.val = 9400) (k : Ring12) : tag.val = 9400 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09401 (tag : Fin 10000) (htag : tag.val = 9401) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9401 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09402 (tag : Fin 10000) (htag : tag.val = 9402) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9402 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09403 (tag : Fin 10000) (htag : tag.val = 9403) (x : State) (e : Event) (dr : Ring12) : tag.val = 9403 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09404 (tag : Fin 10000) (htag : tag.val = 9404) (x : State) (e : Event) (dr : Ring12) : tag.val = 9404 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09405 (tag : Fin 10000) (htag : tag.val = 9405) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9405 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09406 (tag : Fin 10000) (htag : tag.val = 9406) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9406 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09407 (tag : Fin 10000) (htag : tag.val = 9407) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9407 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09408 (tag : Fin 10000) (htag : tag.val = 9408) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9408 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09409 (tag : Fin 10000) (htag : tag.val = 9409) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9409 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09410 (tag : Fin 10000) (htag : tag.val = 9410) (k : Ring12) : tag.val = 9410 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09411 (tag : Fin 10000) (htag : tag.val = 9411) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9411 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09412 (tag : Fin 10000) (htag : tag.val = 9412) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9412 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09413 (tag : Fin 10000) (htag : tag.val = 9413) (x : State) (e : Event) (dr : Ring12) : tag.val = 9413 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09414 (tag : Fin 10000) (htag : tag.val = 9414) (x : State) (e : Event) (dr : Ring12) : tag.val = 9414 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09415 (tag : Fin 10000) (htag : tag.val = 9415) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9415 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09416 (tag : Fin 10000) (htag : tag.val = 9416) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9416 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09417 (tag : Fin 10000) (htag : tag.val = 9417) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9417 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09418 (tag : Fin 10000) (htag : tag.val = 9418) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9418 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09419 (tag : Fin 10000) (htag : tag.val = 9419) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9419 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09420 (tag : Fin 10000) (htag : tag.val = 9420) (k : Ring12) : tag.val = 9420 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09421 (tag : Fin 10000) (htag : tag.val = 9421) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9421 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09422 (tag : Fin 10000) (htag : tag.val = 9422) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9422 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09423 (tag : Fin 10000) (htag : tag.val = 9423) (x : State) (e : Event) (dr : Ring12) : tag.val = 9423 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09424 (tag : Fin 10000) (htag : tag.val = 9424) (x : State) (e : Event) (dr : Ring12) : tag.val = 9424 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09425 (tag : Fin 10000) (htag : tag.val = 9425) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9425 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09426 (tag : Fin 10000) (htag : tag.val = 9426) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9426 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09427 (tag : Fin 10000) (htag : tag.val = 9427) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9427 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09428 (tag : Fin 10000) (htag : tag.val = 9428) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9428 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09429 (tag : Fin 10000) (htag : tag.val = 9429) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9429 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09430 (tag : Fin 10000) (htag : tag.val = 9430) (k : Ring12) : tag.val = 9430 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09431 (tag : Fin 10000) (htag : tag.val = 9431) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9431 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09432 (tag : Fin 10000) (htag : tag.val = 9432) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9432 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09433 (tag : Fin 10000) (htag : tag.val = 9433) (x : State) (e : Event) (dr : Ring12) : tag.val = 9433 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09434 (tag : Fin 10000) (htag : tag.val = 9434) (x : State) (e : Event) (dr : Ring12) : tag.val = 9434 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09435 (tag : Fin 10000) (htag : tag.val = 9435) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9435 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09436 (tag : Fin 10000) (htag : tag.val = 9436) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9436 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09437 (tag : Fin 10000) (htag : tag.val = 9437) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9437 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09438 (tag : Fin 10000) (htag : tag.val = 9438) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9438 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09439 (tag : Fin 10000) (htag : tag.val = 9439) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9439 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09440 (tag : Fin 10000) (htag : tag.val = 9440) (k : Ring12) : tag.val = 9440 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09441 (tag : Fin 10000) (htag : tag.val = 9441) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9441 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09442 (tag : Fin 10000) (htag : tag.val = 9442) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9442 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09443 (tag : Fin 10000) (htag : tag.val = 9443) (x : State) (e : Event) (dr : Ring12) : tag.val = 9443 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09444 (tag : Fin 10000) (htag : tag.val = 9444) (x : State) (e : Event) (dr : Ring12) : tag.val = 9444 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09445 (tag : Fin 10000) (htag : tag.val = 9445) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9445 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09446 (tag : Fin 10000) (htag : tag.val = 9446) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9446 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09447 (tag : Fin 10000) (htag : tag.val = 9447) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9447 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09448 (tag : Fin 10000) (htag : tag.val = 9448) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9448 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09449 (tag : Fin 10000) (htag : tag.val = 9449) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9449 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09450 (tag : Fin 10000) (htag : tag.val = 9450) (k : Ring12) : tag.val = 9450 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09451 (tag : Fin 10000) (htag : tag.val = 9451) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9451 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09452 (tag : Fin 10000) (htag : tag.val = 9452) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9452 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09453 (tag : Fin 10000) (htag : tag.val = 9453) (x : State) (e : Event) (dr : Ring12) : tag.val = 9453 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09454 (tag : Fin 10000) (htag : tag.val = 9454) (x : State) (e : Event) (dr : Ring12) : tag.val = 9454 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09455 (tag : Fin 10000) (htag : tag.val = 9455) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9455 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09456 (tag : Fin 10000) (htag : tag.val = 9456) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9456 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09457 (tag : Fin 10000) (htag : tag.val = 9457) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9457 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09458 (tag : Fin 10000) (htag : tag.val = 9458) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9458 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09459 (tag : Fin 10000) (htag : tag.val = 9459) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9459 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09460 (tag : Fin 10000) (htag : tag.val = 9460) (k : Ring12) : tag.val = 9460 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09461 (tag : Fin 10000) (htag : tag.val = 9461) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9461 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09462 (tag : Fin 10000) (htag : tag.val = 9462) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9462 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09463 (tag : Fin 10000) (htag : tag.val = 9463) (x : State) (e : Event) (dr : Ring12) : tag.val = 9463 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09464 (tag : Fin 10000) (htag : tag.val = 9464) (x : State) (e : Event) (dr : Ring12) : tag.val = 9464 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09465 (tag : Fin 10000) (htag : tag.val = 9465) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9465 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09466 (tag : Fin 10000) (htag : tag.val = 9466) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9466 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09467 (tag : Fin 10000) (htag : tag.val = 9467) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9467 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09468 (tag : Fin 10000) (htag : tag.val = 9468) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9468 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09469 (tag : Fin 10000) (htag : tag.val = 9469) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9469 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09470 (tag : Fin 10000) (htag : tag.val = 9470) (k : Ring12) : tag.val = 9470 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09471 (tag : Fin 10000) (htag : tag.val = 9471) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9471 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09472 (tag : Fin 10000) (htag : tag.val = 9472) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9472 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09473 (tag : Fin 10000) (htag : tag.val = 9473) (x : State) (e : Event) (dr : Ring12) : tag.val = 9473 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09474 (tag : Fin 10000) (htag : tag.val = 9474) (x : State) (e : Event) (dr : Ring12) : tag.val = 9474 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09475 (tag : Fin 10000) (htag : tag.val = 9475) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9475 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09476 (tag : Fin 10000) (htag : tag.val = 9476) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9476 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09477 (tag : Fin 10000) (htag : tag.val = 9477) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9477 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09478 (tag : Fin 10000) (htag : tag.val = 9478) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9478 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09479 (tag : Fin 10000) (htag : tag.val = 9479) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9479 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09480 (tag : Fin 10000) (htag : tag.val = 9480) (k : Ring12) : tag.val = 9480 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09481 (tag : Fin 10000) (htag : tag.val = 9481) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9481 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09482 (tag : Fin 10000) (htag : tag.val = 9482) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9482 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09483 (tag : Fin 10000) (htag : tag.val = 9483) (x : State) (e : Event) (dr : Ring12) : tag.val = 9483 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09484 (tag : Fin 10000) (htag : tag.val = 9484) (x : State) (e : Event) (dr : Ring12) : tag.val = 9484 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09485 (tag : Fin 10000) (htag : tag.val = 9485) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9485 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09486 (tag : Fin 10000) (htag : tag.val = 9486) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9486 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09487 (tag : Fin 10000) (htag : tag.val = 9487) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9487 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09488 (tag : Fin 10000) (htag : tag.val = 9488) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9488 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09489 (tag : Fin 10000) (htag : tag.val = 9489) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9489 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_09490 (tag : Fin 10000) (htag : tag.val = 9490) (k : Ring12) : tag.val = 9490 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_09491 (tag : Fin 10000) (htag : tag.val = 9491) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9491 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_09492 (tag : Fin 10000) (htag : tag.val = 9492) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9492 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_09493 (tag : Fin 10000) (htag : tag.val = 9493) (x : State) (e : Event) (dr : Ring12) : tag.val = 9493 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_09494 (tag : Fin 10000) (htag : tag.val = 9494) (x : State) (e : Event) (dr : Ring12) : tag.val = 9494 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_09495 (tag : Fin 10000) (htag : tag.val = 9495) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9495 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_09496 (tag : Fin 10000) (htag : tag.val = 9496) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 9496 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_09497 (tag : Fin 10000) (htag : tag.val = 9497) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 9497 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_09498 (tag : Fin 10000) (htag : tag.val = 9498) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 9498 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_09499 (tag : Fin 10000) (htag : tag.val = 9499) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 9499 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
