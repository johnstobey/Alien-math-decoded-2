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
theorem generated_05400 (tag : Fin 10000) (htag : tag.val = 5400) (k : Ring12) : tag.val = 5400 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05401 (tag : Fin 10000) (htag : tag.val = 5401) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5401 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05402 (tag : Fin 10000) (htag : tag.val = 5402) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5402 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05403 (tag : Fin 10000) (htag : tag.val = 5403) (x : State) (e : Event) (dr : Ring12) : tag.val = 5403 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05404 (tag : Fin 10000) (htag : tag.val = 5404) (x : State) (e : Event) (dr : Ring12) : tag.val = 5404 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05405 (tag : Fin 10000) (htag : tag.val = 5405) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5405 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05406 (tag : Fin 10000) (htag : tag.val = 5406) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5406 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05407 (tag : Fin 10000) (htag : tag.val = 5407) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5407 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05408 (tag : Fin 10000) (htag : tag.val = 5408) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5408 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05409 (tag : Fin 10000) (htag : tag.val = 5409) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5409 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05410 (tag : Fin 10000) (htag : tag.val = 5410) (k : Ring12) : tag.val = 5410 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05411 (tag : Fin 10000) (htag : tag.val = 5411) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5411 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05412 (tag : Fin 10000) (htag : tag.val = 5412) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5412 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05413 (tag : Fin 10000) (htag : tag.val = 5413) (x : State) (e : Event) (dr : Ring12) : tag.val = 5413 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05414 (tag : Fin 10000) (htag : tag.val = 5414) (x : State) (e : Event) (dr : Ring12) : tag.val = 5414 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05415 (tag : Fin 10000) (htag : tag.val = 5415) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5415 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05416 (tag : Fin 10000) (htag : tag.val = 5416) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5416 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05417 (tag : Fin 10000) (htag : tag.val = 5417) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5417 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05418 (tag : Fin 10000) (htag : tag.val = 5418) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5418 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05419 (tag : Fin 10000) (htag : tag.val = 5419) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5419 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05420 (tag : Fin 10000) (htag : tag.val = 5420) (k : Ring12) : tag.val = 5420 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05421 (tag : Fin 10000) (htag : tag.val = 5421) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5421 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05422 (tag : Fin 10000) (htag : tag.val = 5422) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5422 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05423 (tag : Fin 10000) (htag : tag.val = 5423) (x : State) (e : Event) (dr : Ring12) : tag.val = 5423 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05424 (tag : Fin 10000) (htag : tag.val = 5424) (x : State) (e : Event) (dr : Ring12) : tag.val = 5424 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05425 (tag : Fin 10000) (htag : tag.val = 5425) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5425 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05426 (tag : Fin 10000) (htag : tag.val = 5426) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5426 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05427 (tag : Fin 10000) (htag : tag.val = 5427) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5427 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05428 (tag : Fin 10000) (htag : tag.val = 5428) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5428 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05429 (tag : Fin 10000) (htag : tag.val = 5429) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5429 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05430 (tag : Fin 10000) (htag : tag.val = 5430) (k : Ring12) : tag.val = 5430 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05431 (tag : Fin 10000) (htag : tag.val = 5431) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5431 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05432 (tag : Fin 10000) (htag : tag.val = 5432) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5432 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05433 (tag : Fin 10000) (htag : tag.val = 5433) (x : State) (e : Event) (dr : Ring12) : tag.val = 5433 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05434 (tag : Fin 10000) (htag : tag.val = 5434) (x : State) (e : Event) (dr : Ring12) : tag.val = 5434 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05435 (tag : Fin 10000) (htag : tag.val = 5435) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5435 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05436 (tag : Fin 10000) (htag : tag.val = 5436) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5436 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05437 (tag : Fin 10000) (htag : tag.val = 5437) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5437 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05438 (tag : Fin 10000) (htag : tag.val = 5438) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5438 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05439 (tag : Fin 10000) (htag : tag.val = 5439) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5439 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05440 (tag : Fin 10000) (htag : tag.val = 5440) (k : Ring12) : tag.val = 5440 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05441 (tag : Fin 10000) (htag : tag.val = 5441) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5441 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05442 (tag : Fin 10000) (htag : tag.val = 5442) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5442 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05443 (tag : Fin 10000) (htag : tag.val = 5443) (x : State) (e : Event) (dr : Ring12) : tag.val = 5443 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05444 (tag : Fin 10000) (htag : tag.val = 5444) (x : State) (e : Event) (dr : Ring12) : tag.val = 5444 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05445 (tag : Fin 10000) (htag : tag.val = 5445) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5445 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05446 (tag : Fin 10000) (htag : tag.val = 5446) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5446 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05447 (tag : Fin 10000) (htag : tag.val = 5447) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5447 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05448 (tag : Fin 10000) (htag : tag.val = 5448) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5448 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05449 (tag : Fin 10000) (htag : tag.val = 5449) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5449 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05450 (tag : Fin 10000) (htag : tag.val = 5450) (k : Ring12) : tag.val = 5450 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05451 (tag : Fin 10000) (htag : tag.val = 5451) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5451 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05452 (tag : Fin 10000) (htag : tag.val = 5452) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5452 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05453 (tag : Fin 10000) (htag : tag.val = 5453) (x : State) (e : Event) (dr : Ring12) : tag.val = 5453 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05454 (tag : Fin 10000) (htag : tag.val = 5454) (x : State) (e : Event) (dr : Ring12) : tag.val = 5454 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05455 (tag : Fin 10000) (htag : tag.val = 5455) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5455 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05456 (tag : Fin 10000) (htag : tag.val = 5456) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5456 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05457 (tag : Fin 10000) (htag : tag.val = 5457) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5457 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05458 (tag : Fin 10000) (htag : tag.val = 5458) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5458 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05459 (tag : Fin 10000) (htag : tag.val = 5459) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5459 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05460 (tag : Fin 10000) (htag : tag.val = 5460) (k : Ring12) : tag.val = 5460 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05461 (tag : Fin 10000) (htag : tag.val = 5461) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5461 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05462 (tag : Fin 10000) (htag : tag.val = 5462) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5462 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05463 (tag : Fin 10000) (htag : tag.val = 5463) (x : State) (e : Event) (dr : Ring12) : tag.val = 5463 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05464 (tag : Fin 10000) (htag : tag.val = 5464) (x : State) (e : Event) (dr : Ring12) : tag.val = 5464 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05465 (tag : Fin 10000) (htag : tag.val = 5465) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5465 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05466 (tag : Fin 10000) (htag : tag.val = 5466) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5466 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05467 (tag : Fin 10000) (htag : tag.val = 5467) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5467 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05468 (tag : Fin 10000) (htag : tag.val = 5468) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5468 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05469 (tag : Fin 10000) (htag : tag.val = 5469) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5469 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05470 (tag : Fin 10000) (htag : tag.val = 5470) (k : Ring12) : tag.val = 5470 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05471 (tag : Fin 10000) (htag : tag.val = 5471) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5471 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05472 (tag : Fin 10000) (htag : tag.val = 5472) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5472 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05473 (tag : Fin 10000) (htag : tag.val = 5473) (x : State) (e : Event) (dr : Ring12) : tag.val = 5473 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05474 (tag : Fin 10000) (htag : tag.val = 5474) (x : State) (e : Event) (dr : Ring12) : tag.val = 5474 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05475 (tag : Fin 10000) (htag : tag.val = 5475) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5475 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05476 (tag : Fin 10000) (htag : tag.val = 5476) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5476 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05477 (tag : Fin 10000) (htag : tag.val = 5477) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5477 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05478 (tag : Fin 10000) (htag : tag.val = 5478) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5478 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05479 (tag : Fin 10000) (htag : tag.val = 5479) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5479 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05480 (tag : Fin 10000) (htag : tag.val = 5480) (k : Ring12) : tag.val = 5480 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05481 (tag : Fin 10000) (htag : tag.val = 5481) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5481 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05482 (tag : Fin 10000) (htag : tag.val = 5482) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5482 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05483 (tag : Fin 10000) (htag : tag.val = 5483) (x : State) (e : Event) (dr : Ring12) : tag.val = 5483 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05484 (tag : Fin 10000) (htag : tag.val = 5484) (x : State) (e : Event) (dr : Ring12) : tag.val = 5484 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05485 (tag : Fin 10000) (htag : tag.val = 5485) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5485 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05486 (tag : Fin 10000) (htag : tag.val = 5486) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5486 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05487 (tag : Fin 10000) (htag : tag.val = 5487) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5487 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05488 (tag : Fin 10000) (htag : tag.val = 5488) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5488 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05489 (tag : Fin 10000) (htag : tag.val = 5489) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5489 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05490 (tag : Fin 10000) (htag : tag.val = 5490) (k : Ring12) : tag.val = 5490 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05491 (tag : Fin 10000) (htag : tag.val = 5491) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5491 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05492 (tag : Fin 10000) (htag : tag.val = 5492) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5492 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05493 (tag : Fin 10000) (htag : tag.val = 5493) (x : State) (e : Event) (dr : Ring12) : tag.val = 5493 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05494 (tag : Fin 10000) (htag : tag.val = 5494) (x : State) (e : Event) (dr : Ring12) : tag.val = 5494 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05495 (tag : Fin 10000) (htag : tag.val = 5495) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5495 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05496 (tag : Fin 10000) (htag : tag.val = 5496) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5496 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05497 (tag : Fin 10000) (htag : tag.val = 5497) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5497 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05498 (tag : Fin 10000) (htag : tag.val = 5498) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5498 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05499 (tag : Fin 10000) (htag : tag.val = 5499) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5499 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
