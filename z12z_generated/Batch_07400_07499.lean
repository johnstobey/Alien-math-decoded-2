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
theorem generated_07400 (tag : Fin 10000) (htag : tag.val = 7400) (k : Ring12) : tag.val = 7400 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07401 (tag : Fin 10000) (htag : tag.val = 7401) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7401 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07402 (tag : Fin 10000) (htag : tag.val = 7402) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7402 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07403 (tag : Fin 10000) (htag : tag.val = 7403) (x : State) (e : Event) (dr : Ring12) : tag.val = 7403 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07404 (tag : Fin 10000) (htag : tag.val = 7404) (x : State) (e : Event) (dr : Ring12) : tag.val = 7404 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07405 (tag : Fin 10000) (htag : tag.val = 7405) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7405 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07406 (tag : Fin 10000) (htag : tag.val = 7406) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7406 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07407 (tag : Fin 10000) (htag : tag.val = 7407) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7407 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07408 (tag : Fin 10000) (htag : tag.val = 7408) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7408 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07409 (tag : Fin 10000) (htag : tag.val = 7409) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7409 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07410 (tag : Fin 10000) (htag : tag.val = 7410) (k : Ring12) : tag.val = 7410 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07411 (tag : Fin 10000) (htag : tag.val = 7411) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7411 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07412 (tag : Fin 10000) (htag : tag.val = 7412) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7412 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07413 (tag : Fin 10000) (htag : tag.val = 7413) (x : State) (e : Event) (dr : Ring12) : tag.val = 7413 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07414 (tag : Fin 10000) (htag : tag.val = 7414) (x : State) (e : Event) (dr : Ring12) : tag.val = 7414 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07415 (tag : Fin 10000) (htag : tag.val = 7415) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7415 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07416 (tag : Fin 10000) (htag : tag.val = 7416) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7416 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07417 (tag : Fin 10000) (htag : tag.val = 7417) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7417 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07418 (tag : Fin 10000) (htag : tag.val = 7418) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7418 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07419 (tag : Fin 10000) (htag : tag.val = 7419) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7419 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07420 (tag : Fin 10000) (htag : tag.val = 7420) (k : Ring12) : tag.val = 7420 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07421 (tag : Fin 10000) (htag : tag.val = 7421) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7421 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07422 (tag : Fin 10000) (htag : tag.val = 7422) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7422 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07423 (tag : Fin 10000) (htag : tag.val = 7423) (x : State) (e : Event) (dr : Ring12) : tag.val = 7423 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07424 (tag : Fin 10000) (htag : tag.val = 7424) (x : State) (e : Event) (dr : Ring12) : tag.val = 7424 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07425 (tag : Fin 10000) (htag : tag.val = 7425) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7425 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07426 (tag : Fin 10000) (htag : tag.val = 7426) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7426 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07427 (tag : Fin 10000) (htag : tag.val = 7427) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7427 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07428 (tag : Fin 10000) (htag : tag.val = 7428) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7428 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07429 (tag : Fin 10000) (htag : tag.val = 7429) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7429 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07430 (tag : Fin 10000) (htag : tag.val = 7430) (k : Ring12) : tag.val = 7430 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07431 (tag : Fin 10000) (htag : tag.val = 7431) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7431 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07432 (tag : Fin 10000) (htag : tag.val = 7432) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7432 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07433 (tag : Fin 10000) (htag : tag.val = 7433) (x : State) (e : Event) (dr : Ring12) : tag.val = 7433 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07434 (tag : Fin 10000) (htag : tag.val = 7434) (x : State) (e : Event) (dr : Ring12) : tag.val = 7434 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07435 (tag : Fin 10000) (htag : tag.val = 7435) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7435 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07436 (tag : Fin 10000) (htag : tag.val = 7436) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7436 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07437 (tag : Fin 10000) (htag : tag.val = 7437) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7437 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07438 (tag : Fin 10000) (htag : tag.val = 7438) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7438 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07439 (tag : Fin 10000) (htag : tag.val = 7439) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7439 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07440 (tag : Fin 10000) (htag : tag.val = 7440) (k : Ring12) : tag.val = 7440 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07441 (tag : Fin 10000) (htag : tag.val = 7441) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7441 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07442 (tag : Fin 10000) (htag : tag.val = 7442) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7442 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07443 (tag : Fin 10000) (htag : tag.val = 7443) (x : State) (e : Event) (dr : Ring12) : tag.val = 7443 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07444 (tag : Fin 10000) (htag : tag.val = 7444) (x : State) (e : Event) (dr : Ring12) : tag.val = 7444 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07445 (tag : Fin 10000) (htag : tag.val = 7445) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7445 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07446 (tag : Fin 10000) (htag : tag.val = 7446) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7446 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07447 (tag : Fin 10000) (htag : tag.val = 7447) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7447 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07448 (tag : Fin 10000) (htag : tag.val = 7448) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7448 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07449 (tag : Fin 10000) (htag : tag.val = 7449) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7449 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07450 (tag : Fin 10000) (htag : tag.val = 7450) (k : Ring12) : tag.val = 7450 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07451 (tag : Fin 10000) (htag : tag.val = 7451) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7451 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07452 (tag : Fin 10000) (htag : tag.val = 7452) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7452 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07453 (tag : Fin 10000) (htag : tag.val = 7453) (x : State) (e : Event) (dr : Ring12) : tag.val = 7453 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07454 (tag : Fin 10000) (htag : tag.val = 7454) (x : State) (e : Event) (dr : Ring12) : tag.val = 7454 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07455 (tag : Fin 10000) (htag : tag.val = 7455) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7455 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07456 (tag : Fin 10000) (htag : tag.val = 7456) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7456 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07457 (tag : Fin 10000) (htag : tag.val = 7457) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7457 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07458 (tag : Fin 10000) (htag : tag.val = 7458) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7458 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07459 (tag : Fin 10000) (htag : tag.val = 7459) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7459 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07460 (tag : Fin 10000) (htag : tag.val = 7460) (k : Ring12) : tag.val = 7460 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07461 (tag : Fin 10000) (htag : tag.val = 7461) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7461 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07462 (tag : Fin 10000) (htag : tag.val = 7462) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7462 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07463 (tag : Fin 10000) (htag : tag.val = 7463) (x : State) (e : Event) (dr : Ring12) : tag.val = 7463 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07464 (tag : Fin 10000) (htag : tag.val = 7464) (x : State) (e : Event) (dr : Ring12) : tag.val = 7464 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07465 (tag : Fin 10000) (htag : tag.val = 7465) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7465 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07466 (tag : Fin 10000) (htag : tag.val = 7466) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7466 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07467 (tag : Fin 10000) (htag : tag.val = 7467) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7467 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07468 (tag : Fin 10000) (htag : tag.val = 7468) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7468 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07469 (tag : Fin 10000) (htag : tag.val = 7469) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7469 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07470 (tag : Fin 10000) (htag : tag.val = 7470) (k : Ring12) : tag.val = 7470 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07471 (tag : Fin 10000) (htag : tag.val = 7471) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7471 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07472 (tag : Fin 10000) (htag : tag.val = 7472) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7472 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07473 (tag : Fin 10000) (htag : tag.val = 7473) (x : State) (e : Event) (dr : Ring12) : tag.val = 7473 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07474 (tag : Fin 10000) (htag : tag.val = 7474) (x : State) (e : Event) (dr : Ring12) : tag.val = 7474 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07475 (tag : Fin 10000) (htag : tag.val = 7475) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7475 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07476 (tag : Fin 10000) (htag : tag.val = 7476) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7476 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07477 (tag : Fin 10000) (htag : tag.val = 7477) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7477 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07478 (tag : Fin 10000) (htag : tag.val = 7478) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7478 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07479 (tag : Fin 10000) (htag : tag.val = 7479) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7479 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07480 (tag : Fin 10000) (htag : tag.val = 7480) (k : Ring12) : tag.val = 7480 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07481 (tag : Fin 10000) (htag : tag.val = 7481) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7481 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07482 (tag : Fin 10000) (htag : tag.val = 7482) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7482 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07483 (tag : Fin 10000) (htag : tag.val = 7483) (x : State) (e : Event) (dr : Ring12) : tag.val = 7483 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07484 (tag : Fin 10000) (htag : tag.val = 7484) (x : State) (e : Event) (dr : Ring12) : tag.val = 7484 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07485 (tag : Fin 10000) (htag : tag.val = 7485) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7485 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07486 (tag : Fin 10000) (htag : tag.val = 7486) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7486 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07487 (tag : Fin 10000) (htag : tag.val = 7487) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7487 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07488 (tag : Fin 10000) (htag : tag.val = 7488) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7488 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07489 (tag : Fin 10000) (htag : tag.val = 7489) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7489 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07490 (tag : Fin 10000) (htag : tag.val = 7490) (k : Ring12) : tag.val = 7490 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07491 (tag : Fin 10000) (htag : tag.val = 7491) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7491 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07492 (tag : Fin 10000) (htag : tag.val = 7492) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7492 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07493 (tag : Fin 10000) (htag : tag.val = 7493) (x : State) (e : Event) (dr : Ring12) : tag.val = 7493 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07494 (tag : Fin 10000) (htag : tag.val = 7494) (x : State) (e : Event) (dr : Ring12) : tag.val = 7494 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07495 (tag : Fin 10000) (htag : tag.val = 7495) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7495 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07496 (tag : Fin 10000) (htag : tag.val = 7496) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7496 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07497 (tag : Fin 10000) (htag : tag.val = 7497) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7497 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07498 (tag : Fin 10000) (htag : tag.val = 7498) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7498 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07499 (tag : Fin 10000) (htag : tag.val = 7499) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7499 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
