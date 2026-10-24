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
theorem generated_04400 (tag : Fin 10000) (htag : tag.val = 4400) (k : Ring12) : tag.val = 4400 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04401 (tag : Fin 10000) (htag : tag.val = 4401) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4401 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04402 (tag : Fin 10000) (htag : tag.val = 4402) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4402 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04403 (tag : Fin 10000) (htag : tag.val = 4403) (x : State) (e : Event) (dr : Ring12) : tag.val = 4403 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04404 (tag : Fin 10000) (htag : tag.val = 4404) (x : State) (e : Event) (dr : Ring12) : tag.val = 4404 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04405 (tag : Fin 10000) (htag : tag.val = 4405) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4405 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04406 (tag : Fin 10000) (htag : tag.val = 4406) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4406 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04407 (tag : Fin 10000) (htag : tag.val = 4407) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4407 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04408 (tag : Fin 10000) (htag : tag.val = 4408) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4408 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04409 (tag : Fin 10000) (htag : tag.val = 4409) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4409 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04410 (tag : Fin 10000) (htag : tag.val = 4410) (k : Ring12) : tag.val = 4410 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04411 (tag : Fin 10000) (htag : tag.val = 4411) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4411 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04412 (tag : Fin 10000) (htag : tag.val = 4412) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4412 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04413 (tag : Fin 10000) (htag : tag.val = 4413) (x : State) (e : Event) (dr : Ring12) : tag.val = 4413 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04414 (tag : Fin 10000) (htag : tag.val = 4414) (x : State) (e : Event) (dr : Ring12) : tag.val = 4414 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04415 (tag : Fin 10000) (htag : tag.val = 4415) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4415 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04416 (tag : Fin 10000) (htag : tag.val = 4416) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4416 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04417 (tag : Fin 10000) (htag : tag.val = 4417) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4417 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04418 (tag : Fin 10000) (htag : tag.val = 4418) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4418 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04419 (tag : Fin 10000) (htag : tag.val = 4419) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4419 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04420 (tag : Fin 10000) (htag : tag.val = 4420) (k : Ring12) : tag.val = 4420 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04421 (tag : Fin 10000) (htag : tag.val = 4421) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4421 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04422 (tag : Fin 10000) (htag : tag.val = 4422) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4422 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04423 (tag : Fin 10000) (htag : tag.val = 4423) (x : State) (e : Event) (dr : Ring12) : tag.val = 4423 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04424 (tag : Fin 10000) (htag : tag.val = 4424) (x : State) (e : Event) (dr : Ring12) : tag.val = 4424 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04425 (tag : Fin 10000) (htag : tag.val = 4425) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4425 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04426 (tag : Fin 10000) (htag : tag.val = 4426) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4426 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04427 (tag : Fin 10000) (htag : tag.val = 4427) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4427 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04428 (tag : Fin 10000) (htag : tag.val = 4428) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4428 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04429 (tag : Fin 10000) (htag : tag.val = 4429) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4429 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04430 (tag : Fin 10000) (htag : tag.val = 4430) (k : Ring12) : tag.val = 4430 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04431 (tag : Fin 10000) (htag : tag.val = 4431) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4431 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04432 (tag : Fin 10000) (htag : tag.val = 4432) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4432 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04433 (tag : Fin 10000) (htag : tag.val = 4433) (x : State) (e : Event) (dr : Ring12) : tag.val = 4433 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04434 (tag : Fin 10000) (htag : tag.val = 4434) (x : State) (e : Event) (dr : Ring12) : tag.val = 4434 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04435 (tag : Fin 10000) (htag : tag.val = 4435) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4435 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04436 (tag : Fin 10000) (htag : tag.val = 4436) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4436 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04437 (tag : Fin 10000) (htag : tag.val = 4437) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4437 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04438 (tag : Fin 10000) (htag : tag.val = 4438) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4438 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04439 (tag : Fin 10000) (htag : tag.val = 4439) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4439 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04440 (tag : Fin 10000) (htag : tag.val = 4440) (k : Ring12) : tag.val = 4440 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04441 (tag : Fin 10000) (htag : tag.val = 4441) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4441 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04442 (tag : Fin 10000) (htag : tag.val = 4442) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4442 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04443 (tag : Fin 10000) (htag : tag.val = 4443) (x : State) (e : Event) (dr : Ring12) : tag.val = 4443 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04444 (tag : Fin 10000) (htag : tag.val = 4444) (x : State) (e : Event) (dr : Ring12) : tag.val = 4444 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04445 (tag : Fin 10000) (htag : tag.val = 4445) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4445 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04446 (tag : Fin 10000) (htag : tag.val = 4446) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4446 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04447 (tag : Fin 10000) (htag : tag.val = 4447) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4447 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04448 (tag : Fin 10000) (htag : tag.val = 4448) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4448 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04449 (tag : Fin 10000) (htag : tag.val = 4449) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4449 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04450 (tag : Fin 10000) (htag : tag.val = 4450) (k : Ring12) : tag.val = 4450 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04451 (tag : Fin 10000) (htag : tag.val = 4451) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4451 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04452 (tag : Fin 10000) (htag : tag.val = 4452) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4452 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04453 (tag : Fin 10000) (htag : tag.val = 4453) (x : State) (e : Event) (dr : Ring12) : tag.val = 4453 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04454 (tag : Fin 10000) (htag : tag.val = 4454) (x : State) (e : Event) (dr : Ring12) : tag.val = 4454 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04455 (tag : Fin 10000) (htag : tag.val = 4455) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4455 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04456 (tag : Fin 10000) (htag : tag.val = 4456) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4456 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04457 (tag : Fin 10000) (htag : tag.val = 4457) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4457 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04458 (tag : Fin 10000) (htag : tag.val = 4458) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4458 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04459 (tag : Fin 10000) (htag : tag.val = 4459) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4459 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04460 (tag : Fin 10000) (htag : tag.val = 4460) (k : Ring12) : tag.val = 4460 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04461 (tag : Fin 10000) (htag : tag.val = 4461) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4461 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04462 (tag : Fin 10000) (htag : tag.val = 4462) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4462 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04463 (tag : Fin 10000) (htag : tag.val = 4463) (x : State) (e : Event) (dr : Ring12) : tag.val = 4463 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04464 (tag : Fin 10000) (htag : tag.val = 4464) (x : State) (e : Event) (dr : Ring12) : tag.val = 4464 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04465 (tag : Fin 10000) (htag : tag.val = 4465) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4465 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04466 (tag : Fin 10000) (htag : tag.val = 4466) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4466 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04467 (tag : Fin 10000) (htag : tag.val = 4467) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4467 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04468 (tag : Fin 10000) (htag : tag.val = 4468) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4468 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04469 (tag : Fin 10000) (htag : tag.val = 4469) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4469 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04470 (tag : Fin 10000) (htag : tag.val = 4470) (k : Ring12) : tag.val = 4470 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04471 (tag : Fin 10000) (htag : tag.val = 4471) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4471 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04472 (tag : Fin 10000) (htag : tag.val = 4472) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4472 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04473 (tag : Fin 10000) (htag : tag.val = 4473) (x : State) (e : Event) (dr : Ring12) : tag.val = 4473 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04474 (tag : Fin 10000) (htag : tag.val = 4474) (x : State) (e : Event) (dr : Ring12) : tag.val = 4474 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04475 (tag : Fin 10000) (htag : tag.val = 4475) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4475 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04476 (tag : Fin 10000) (htag : tag.val = 4476) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4476 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04477 (tag : Fin 10000) (htag : tag.val = 4477) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4477 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04478 (tag : Fin 10000) (htag : tag.val = 4478) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4478 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04479 (tag : Fin 10000) (htag : tag.val = 4479) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4479 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04480 (tag : Fin 10000) (htag : tag.val = 4480) (k : Ring12) : tag.val = 4480 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04481 (tag : Fin 10000) (htag : tag.val = 4481) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4481 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04482 (tag : Fin 10000) (htag : tag.val = 4482) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4482 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04483 (tag : Fin 10000) (htag : tag.val = 4483) (x : State) (e : Event) (dr : Ring12) : tag.val = 4483 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04484 (tag : Fin 10000) (htag : tag.val = 4484) (x : State) (e : Event) (dr : Ring12) : tag.val = 4484 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04485 (tag : Fin 10000) (htag : tag.val = 4485) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4485 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04486 (tag : Fin 10000) (htag : tag.val = 4486) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4486 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04487 (tag : Fin 10000) (htag : tag.val = 4487) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4487 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04488 (tag : Fin 10000) (htag : tag.val = 4488) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4488 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04489 (tag : Fin 10000) (htag : tag.val = 4489) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4489 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04490 (tag : Fin 10000) (htag : tag.val = 4490) (k : Ring12) : tag.val = 4490 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04491 (tag : Fin 10000) (htag : tag.val = 4491) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4491 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04492 (tag : Fin 10000) (htag : tag.val = 4492) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4492 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04493 (tag : Fin 10000) (htag : tag.val = 4493) (x : State) (e : Event) (dr : Ring12) : tag.val = 4493 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04494 (tag : Fin 10000) (htag : tag.val = 4494) (x : State) (e : Event) (dr : Ring12) : tag.val = 4494 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04495 (tag : Fin 10000) (htag : tag.val = 4495) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4495 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04496 (tag : Fin 10000) (htag : tag.val = 4496) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4496 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04497 (tag : Fin 10000) (htag : tag.val = 4497) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4497 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04498 (tag : Fin 10000) (htag : tag.val = 4498) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4498 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04499 (tag : Fin 10000) (htag : tag.val = 4499) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4499 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
