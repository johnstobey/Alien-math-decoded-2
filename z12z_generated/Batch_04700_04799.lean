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
theorem generated_04700 (tag : Fin 10000) (htag : tag.val = 4700) (k : Ring12) : tag.val = 4700 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04701 (tag : Fin 10000) (htag : tag.val = 4701) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4701 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04702 (tag : Fin 10000) (htag : tag.val = 4702) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4702 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04703 (tag : Fin 10000) (htag : tag.val = 4703) (x : State) (e : Event) (dr : Ring12) : tag.val = 4703 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04704 (tag : Fin 10000) (htag : tag.val = 4704) (x : State) (e : Event) (dr : Ring12) : tag.val = 4704 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04705 (tag : Fin 10000) (htag : tag.val = 4705) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4705 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04706 (tag : Fin 10000) (htag : tag.val = 4706) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4706 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04707 (tag : Fin 10000) (htag : tag.val = 4707) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4707 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04708 (tag : Fin 10000) (htag : tag.val = 4708) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4708 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04709 (tag : Fin 10000) (htag : tag.val = 4709) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4709 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04710 (tag : Fin 10000) (htag : tag.val = 4710) (k : Ring12) : tag.val = 4710 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04711 (tag : Fin 10000) (htag : tag.val = 4711) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4711 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04712 (tag : Fin 10000) (htag : tag.val = 4712) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4712 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04713 (tag : Fin 10000) (htag : tag.val = 4713) (x : State) (e : Event) (dr : Ring12) : tag.val = 4713 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04714 (tag : Fin 10000) (htag : tag.val = 4714) (x : State) (e : Event) (dr : Ring12) : tag.val = 4714 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04715 (tag : Fin 10000) (htag : tag.val = 4715) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4715 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04716 (tag : Fin 10000) (htag : tag.val = 4716) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4716 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04717 (tag : Fin 10000) (htag : tag.val = 4717) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4717 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04718 (tag : Fin 10000) (htag : tag.val = 4718) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4718 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04719 (tag : Fin 10000) (htag : tag.val = 4719) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4719 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04720 (tag : Fin 10000) (htag : tag.val = 4720) (k : Ring12) : tag.val = 4720 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04721 (tag : Fin 10000) (htag : tag.val = 4721) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4721 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04722 (tag : Fin 10000) (htag : tag.val = 4722) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4722 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04723 (tag : Fin 10000) (htag : tag.val = 4723) (x : State) (e : Event) (dr : Ring12) : tag.val = 4723 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04724 (tag : Fin 10000) (htag : tag.val = 4724) (x : State) (e : Event) (dr : Ring12) : tag.val = 4724 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04725 (tag : Fin 10000) (htag : tag.val = 4725) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4725 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04726 (tag : Fin 10000) (htag : tag.val = 4726) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4726 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04727 (tag : Fin 10000) (htag : tag.val = 4727) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4727 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04728 (tag : Fin 10000) (htag : tag.val = 4728) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4728 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04729 (tag : Fin 10000) (htag : tag.val = 4729) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4729 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04730 (tag : Fin 10000) (htag : tag.val = 4730) (k : Ring12) : tag.val = 4730 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04731 (tag : Fin 10000) (htag : tag.val = 4731) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4731 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04732 (tag : Fin 10000) (htag : tag.val = 4732) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4732 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04733 (tag : Fin 10000) (htag : tag.val = 4733) (x : State) (e : Event) (dr : Ring12) : tag.val = 4733 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04734 (tag : Fin 10000) (htag : tag.val = 4734) (x : State) (e : Event) (dr : Ring12) : tag.val = 4734 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04735 (tag : Fin 10000) (htag : tag.val = 4735) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4735 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04736 (tag : Fin 10000) (htag : tag.val = 4736) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4736 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04737 (tag : Fin 10000) (htag : tag.val = 4737) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4737 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04738 (tag : Fin 10000) (htag : tag.val = 4738) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4738 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04739 (tag : Fin 10000) (htag : tag.val = 4739) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4739 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04740 (tag : Fin 10000) (htag : tag.val = 4740) (k : Ring12) : tag.val = 4740 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04741 (tag : Fin 10000) (htag : tag.val = 4741) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4741 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04742 (tag : Fin 10000) (htag : tag.val = 4742) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4742 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04743 (tag : Fin 10000) (htag : tag.val = 4743) (x : State) (e : Event) (dr : Ring12) : tag.val = 4743 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04744 (tag : Fin 10000) (htag : tag.val = 4744) (x : State) (e : Event) (dr : Ring12) : tag.val = 4744 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04745 (tag : Fin 10000) (htag : tag.val = 4745) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4745 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04746 (tag : Fin 10000) (htag : tag.val = 4746) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4746 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04747 (tag : Fin 10000) (htag : tag.val = 4747) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4747 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04748 (tag : Fin 10000) (htag : tag.val = 4748) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4748 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04749 (tag : Fin 10000) (htag : tag.val = 4749) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4749 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04750 (tag : Fin 10000) (htag : tag.val = 4750) (k : Ring12) : tag.val = 4750 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04751 (tag : Fin 10000) (htag : tag.val = 4751) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4751 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04752 (tag : Fin 10000) (htag : tag.val = 4752) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4752 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04753 (tag : Fin 10000) (htag : tag.val = 4753) (x : State) (e : Event) (dr : Ring12) : tag.val = 4753 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04754 (tag : Fin 10000) (htag : tag.val = 4754) (x : State) (e : Event) (dr : Ring12) : tag.val = 4754 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04755 (tag : Fin 10000) (htag : tag.val = 4755) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4755 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04756 (tag : Fin 10000) (htag : tag.val = 4756) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4756 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04757 (tag : Fin 10000) (htag : tag.val = 4757) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4757 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04758 (tag : Fin 10000) (htag : tag.val = 4758) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4758 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04759 (tag : Fin 10000) (htag : tag.val = 4759) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4759 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04760 (tag : Fin 10000) (htag : tag.val = 4760) (k : Ring12) : tag.val = 4760 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04761 (tag : Fin 10000) (htag : tag.val = 4761) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4761 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04762 (tag : Fin 10000) (htag : tag.val = 4762) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4762 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04763 (tag : Fin 10000) (htag : tag.val = 4763) (x : State) (e : Event) (dr : Ring12) : tag.val = 4763 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04764 (tag : Fin 10000) (htag : tag.val = 4764) (x : State) (e : Event) (dr : Ring12) : tag.val = 4764 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04765 (tag : Fin 10000) (htag : tag.val = 4765) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4765 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04766 (tag : Fin 10000) (htag : tag.val = 4766) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4766 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04767 (tag : Fin 10000) (htag : tag.val = 4767) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4767 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04768 (tag : Fin 10000) (htag : tag.val = 4768) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4768 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04769 (tag : Fin 10000) (htag : tag.val = 4769) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4769 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04770 (tag : Fin 10000) (htag : tag.val = 4770) (k : Ring12) : tag.val = 4770 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04771 (tag : Fin 10000) (htag : tag.val = 4771) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4771 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04772 (tag : Fin 10000) (htag : tag.val = 4772) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4772 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04773 (tag : Fin 10000) (htag : tag.val = 4773) (x : State) (e : Event) (dr : Ring12) : tag.val = 4773 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04774 (tag : Fin 10000) (htag : tag.val = 4774) (x : State) (e : Event) (dr : Ring12) : tag.val = 4774 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04775 (tag : Fin 10000) (htag : tag.val = 4775) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4775 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04776 (tag : Fin 10000) (htag : tag.val = 4776) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4776 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04777 (tag : Fin 10000) (htag : tag.val = 4777) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4777 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04778 (tag : Fin 10000) (htag : tag.val = 4778) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4778 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04779 (tag : Fin 10000) (htag : tag.val = 4779) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4779 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04780 (tag : Fin 10000) (htag : tag.val = 4780) (k : Ring12) : tag.val = 4780 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04781 (tag : Fin 10000) (htag : tag.val = 4781) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4781 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04782 (tag : Fin 10000) (htag : tag.val = 4782) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4782 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04783 (tag : Fin 10000) (htag : tag.val = 4783) (x : State) (e : Event) (dr : Ring12) : tag.val = 4783 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04784 (tag : Fin 10000) (htag : tag.val = 4784) (x : State) (e : Event) (dr : Ring12) : tag.val = 4784 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04785 (tag : Fin 10000) (htag : tag.val = 4785) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4785 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04786 (tag : Fin 10000) (htag : tag.val = 4786) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4786 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04787 (tag : Fin 10000) (htag : tag.val = 4787) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4787 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04788 (tag : Fin 10000) (htag : tag.val = 4788) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4788 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04789 (tag : Fin 10000) (htag : tag.val = 4789) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4789 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_04790 (tag : Fin 10000) (htag : tag.val = 4790) (k : Ring12) : tag.val = 4790 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_04791 (tag : Fin 10000) (htag : tag.val = 4791) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4791 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_04792 (tag : Fin 10000) (htag : tag.val = 4792) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4792 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_04793 (tag : Fin 10000) (htag : tag.val = 4793) (x : State) (e : Event) (dr : Ring12) : tag.val = 4793 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_04794 (tag : Fin 10000) (htag : tag.val = 4794) (x : State) (e : Event) (dr : Ring12) : tag.val = 4794 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_04795 (tag : Fin 10000) (htag : tag.val = 4795) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4795 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_04796 (tag : Fin 10000) (htag : tag.val = 4796) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 4796 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_04797 (tag : Fin 10000) (htag : tag.val = 4797) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 4797 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_04798 (tag : Fin 10000) (htag : tag.val = 4798) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 4798 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_04799 (tag : Fin 10000) (htag : tag.val = 4799) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 4799 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
