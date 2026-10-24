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
theorem generated_06400 (tag : Fin 10000) (htag : tag.val = 6400) (k : Ring12) : tag.val = 6400 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06401 (tag : Fin 10000) (htag : tag.val = 6401) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6401 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06402 (tag : Fin 10000) (htag : tag.val = 6402) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6402 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06403 (tag : Fin 10000) (htag : tag.val = 6403) (x : State) (e : Event) (dr : Ring12) : tag.val = 6403 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06404 (tag : Fin 10000) (htag : tag.val = 6404) (x : State) (e : Event) (dr : Ring12) : tag.val = 6404 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06405 (tag : Fin 10000) (htag : tag.val = 6405) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6405 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06406 (tag : Fin 10000) (htag : tag.val = 6406) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6406 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06407 (tag : Fin 10000) (htag : tag.val = 6407) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6407 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06408 (tag : Fin 10000) (htag : tag.val = 6408) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6408 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06409 (tag : Fin 10000) (htag : tag.val = 6409) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6409 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06410 (tag : Fin 10000) (htag : tag.val = 6410) (k : Ring12) : tag.val = 6410 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06411 (tag : Fin 10000) (htag : tag.val = 6411) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6411 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06412 (tag : Fin 10000) (htag : tag.val = 6412) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6412 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06413 (tag : Fin 10000) (htag : tag.val = 6413) (x : State) (e : Event) (dr : Ring12) : tag.val = 6413 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06414 (tag : Fin 10000) (htag : tag.val = 6414) (x : State) (e : Event) (dr : Ring12) : tag.val = 6414 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06415 (tag : Fin 10000) (htag : tag.val = 6415) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6415 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06416 (tag : Fin 10000) (htag : tag.val = 6416) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6416 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06417 (tag : Fin 10000) (htag : tag.val = 6417) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6417 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06418 (tag : Fin 10000) (htag : tag.val = 6418) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6418 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06419 (tag : Fin 10000) (htag : tag.val = 6419) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6419 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06420 (tag : Fin 10000) (htag : tag.val = 6420) (k : Ring12) : tag.val = 6420 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06421 (tag : Fin 10000) (htag : tag.val = 6421) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6421 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06422 (tag : Fin 10000) (htag : tag.val = 6422) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6422 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06423 (tag : Fin 10000) (htag : tag.val = 6423) (x : State) (e : Event) (dr : Ring12) : tag.val = 6423 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06424 (tag : Fin 10000) (htag : tag.val = 6424) (x : State) (e : Event) (dr : Ring12) : tag.val = 6424 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06425 (tag : Fin 10000) (htag : tag.val = 6425) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6425 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06426 (tag : Fin 10000) (htag : tag.val = 6426) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6426 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06427 (tag : Fin 10000) (htag : tag.val = 6427) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6427 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06428 (tag : Fin 10000) (htag : tag.val = 6428) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6428 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06429 (tag : Fin 10000) (htag : tag.val = 6429) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6429 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06430 (tag : Fin 10000) (htag : tag.val = 6430) (k : Ring12) : tag.val = 6430 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06431 (tag : Fin 10000) (htag : tag.val = 6431) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6431 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06432 (tag : Fin 10000) (htag : tag.val = 6432) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6432 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06433 (tag : Fin 10000) (htag : tag.val = 6433) (x : State) (e : Event) (dr : Ring12) : tag.val = 6433 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06434 (tag : Fin 10000) (htag : tag.val = 6434) (x : State) (e : Event) (dr : Ring12) : tag.val = 6434 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06435 (tag : Fin 10000) (htag : tag.val = 6435) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6435 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06436 (tag : Fin 10000) (htag : tag.val = 6436) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6436 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06437 (tag : Fin 10000) (htag : tag.val = 6437) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6437 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06438 (tag : Fin 10000) (htag : tag.val = 6438) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6438 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06439 (tag : Fin 10000) (htag : tag.val = 6439) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6439 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06440 (tag : Fin 10000) (htag : tag.val = 6440) (k : Ring12) : tag.val = 6440 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06441 (tag : Fin 10000) (htag : tag.val = 6441) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6441 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06442 (tag : Fin 10000) (htag : tag.val = 6442) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6442 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06443 (tag : Fin 10000) (htag : tag.val = 6443) (x : State) (e : Event) (dr : Ring12) : tag.val = 6443 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06444 (tag : Fin 10000) (htag : tag.val = 6444) (x : State) (e : Event) (dr : Ring12) : tag.val = 6444 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06445 (tag : Fin 10000) (htag : tag.val = 6445) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6445 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06446 (tag : Fin 10000) (htag : tag.val = 6446) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6446 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06447 (tag : Fin 10000) (htag : tag.val = 6447) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6447 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06448 (tag : Fin 10000) (htag : tag.val = 6448) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6448 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06449 (tag : Fin 10000) (htag : tag.val = 6449) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6449 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06450 (tag : Fin 10000) (htag : tag.val = 6450) (k : Ring12) : tag.val = 6450 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06451 (tag : Fin 10000) (htag : tag.val = 6451) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6451 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06452 (tag : Fin 10000) (htag : tag.val = 6452) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6452 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06453 (tag : Fin 10000) (htag : tag.val = 6453) (x : State) (e : Event) (dr : Ring12) : tag.val = 6453 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06454 (tag : Fin 10000) (htag : tag.val = 6454) (x : State) (e : Event) (dr : Ring12) : tag.val = 6454 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06455 (tag : Fin 10000) (htag : tag.val = 6455) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6455 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06456 (tag : Fin 10000) (htag : tag.val = 6456) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6456 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06457 (tag : Fin 10000) (htag : tag.val = 6457) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6457 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06458 (tag : Fin 10000) (htag : tag.val = 6458) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6458 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06459 (tag : Fin 10000) (htag : tag.val = 6459) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6459 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06460 (tag : Fin 10000) (htag : tag.val = 6460) (k : Ring12) : tag.val = 6460 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06461 (tag : Fin 10000) (htag : tag.val = 6461) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6461 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06462 (tag : Fin 10000) (htag : tag.val = 6462) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6462 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06463 (tag : Fin 10000) (htag : tag.val = 6463) (x : State) (e : Event) (dr : Ring12) : tag.val = 6463 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06464 (tag : Fin 10000) (htag : tag.val = 6464) (x : State) (e : Event) (dr : Ring12) : tag.val = 6464 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06465 (tag : Fin 10000) (htag : tag.val = 6465) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6465 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06466 (tag : Fin 10000) (htag : tag.val = 6466) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6466 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06467 (tag : Fin 10000) (htag : tag.val = 6467) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6467 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06468 (tag : Fin 10000) (htag : tag.val = 6468) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6468 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06469 (tag : Fin 10000) (htag : tag.val = 6469) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6469 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06470 (tag : Fin 10000) (htag : tag.val = 6470) (k : Ring12) : tag.val = 6470 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06471 (tag : Fin 10000) (htag : tag.val = 6471) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6471 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06472 (tag : Fin 10000) (htag : tag.val = 6472) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6472 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06473 (tag : Fin 10000) (htag : tag.val = 6473) (x : State) (e : Event) (dr : Ring12) : tag.val = 6473 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06474 (tag : Fin 10000) (htag : tag.val = 6474) (x : State) (e : Event) (dr : Ring12) : tag.val = 6474 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06475 (tag : Fin 10000) (htag : tag.val = 6475) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6475 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06476 (tag : Fin 10000) (htag : tag.val = 6476) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6476 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06477 (tag : Fin 10000) (htag : tag.val = 6477) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6477 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06478 (tag : Fin 10000) (htag : tag.val = 6478) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6478 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06479 (tag : Fin 10000) (htag : tag.val = 6479) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6479 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06480 (tag : Fin 10000) (htag : tag.val = 6480) (k : Ring12) : tag.val = 6480 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06481 (tag : Fin 10000) (htag : tag.val = 6481) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6481 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06482 (tag : Fin 10000) (htag : tag.val = 6482) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6482 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06483 (tag : Fin 10000) (htag : tag.val = 6483) (x : State) (e : Event) (dr : Ring12) : tag.val = 6483 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06484 (tag : Fin 10000) (htag : tag.val = 6484) (x : State) (e : Event) (dr : Ring12) : tag.val = 6484 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06485 (tag : Fin 10000) (htag : tag.val = 6485) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6485 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06486 (tag : Fin 10000) (htag : tag.val = 6486) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6486 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06487 (tag : Fin 10000) (htag : tag.val = 6487) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6487 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06488 (tag : Fin 10000) (htag : tag.val = 6488) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6488 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06489 (tag : Fin 10000) (htag : tag.val = 6489) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6489 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_06490 (tag : Fin 10000) (htag : tag.val = 6490) (k : Ring12) : tag.val = 6490 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_06491 (tag : Fin 10000) (htag : tag.val = 6491) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6491 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_06492 (tag : Fin 10000) (htag : tag.val = 6492) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6492 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_06493 (tag : Fin 10000) (htag : tag.val = 6493) (x : State) (e : Event) (dr : Ring12) : tag.val = 6493 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_06494 (tag : Fin 10000) (htag : tag.val = 6494) (x : State) (e : Event) (dr : Ring12) : tag.val = 6494 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_06495 (tag : Fin 10000) (htag : tag.val = 6495) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6495 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_06496 (tag : Fin 10000) (htag : tag.val = 6496) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 6496 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_06497 (tag : Fin 10000) (htag : tag.val = 6497) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 6497 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_06498 (tag : Fin 10000) (htag : tag.val = 6498) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 6498 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_06499 (tag : Fin 10000) (htag : tag.val = 6499) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 6499 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
