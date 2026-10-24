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
theorem generated_05700 (tag : Fin 10000) (htag : tag.val = 5700) (k : Ring12) : tag.val = 5700 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05701 (tag : Fin 10000) (htag : tag.val = 5701) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5701 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05702 (tag : Fin 10000) (htag : tag.val = 5702) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5702 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05703 (tag : Fin 10000) (htag : tag.val = 5703) (x : State) (e : Event) (dr : Ring12) : tag.val = 5703 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05704 (tag : Fin 10000) (htag : tag.val = 5704) (x : State) (e : Event) (dr : Ring12) : tag.val = 5704 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05705 (tag : Fin 10000) (htag : tag.val = 5705) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5705 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05706 (tag : Fin 10000) (htag : tag.val = 5706) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5706 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05707 (tag : Fin 10000) (htag : tag.val = 5707) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5707 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05708 (tag : Fin 10000) (htag : tag.val = 5708) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5708 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05709 (tag : Fin 10000) (htag : tag.val = 5709) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5709 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05710 (tag : Fin 10000) (htag : tag.val = 5710) (k : Ring12) : tag.val = 5710 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05711 (tag : Fin 10000) (htag : tag.val = 5711) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5711 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05712 (tag : Fin 10000) (htag : tag.val = 5712) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5712 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05713 (tag : Fin 10000) (htag : tag.val = 5713) (x : State) (e : Event) (dr : Ring12) : tag.val = 5713 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05714 (tag : Fin 10000) (htag : tag.val = 5714) (x : State) (e : Event) (dr : Ring12) : tag.val = 5714 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05715 (tag : Fin 10000) (htag : tag.val = 5715) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5715 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05716 (tag : Fin 10000) (htag : tag.val = 5716) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5716 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05717 (tag : Fin 10000) (htag : tag.val = 5717) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5717 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05718 (tag : Fin 10000) (htag : tag.val = 5718) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5718 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05719 (tag : Fin 10000) (htag : tag.val = 5719) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5719 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05720 (tag : Fin 10000) (htag : tag.val = 5720) (k : Ring12) : tag.val = 5720 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05721 (tag : Fin 10000) (htag : tag.val = 5721) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5721 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05722 (tag : Fin 10000) (htag : tag.val = 5722) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5722 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05723 (tag : Fin 10000) (htag : tag.val = 5723) (x : State) (e : Event) (dr : Ring12) : tag.val = 5723 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05724 (tag : Fin 10000) (htag : tag.val = 5724) (x : State) (e : Event) (dr : Ring12) : tag.val = 5724 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05725 (tag : Fin 10000) (htag : tag.val = 5725) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5725 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05726 (tag : Fin 10000) (htag : tag.val = 5726) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5726 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05727 (tag : Fin 10000) (htag : tag.val = 5727) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5727 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05728 (tag : Fin 10000) (htag : tag.val = 5728) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5728 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05729 (tag : Fin 10000) (htag : tag.val = 5729) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5729 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05730 (tag : Fin 10000) (htag : tag.val = 5730) (k : Ring12) : tag.val = 5730 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05731 (tag : Fin 10000) (htag : tag.val = 5731) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5731 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05732 (tag : Fin 10000) (htag : tag.val = 5732) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5732 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05733 (tag : Fin 10000) (htag : tag.val = 5733) (x : State) (e : Event) (dr : Ring12) : tag.val = 5733 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05734 (tag : Fin 10000) (htag : tag.val = 5734) (x : State) (e : Event) (dr : Ring12) : tag.val = 5734 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05735 (tag : Fin 10000) (htag : tag.val = 5735) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5735 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05736 (tag : Fin 10000) (htag : tag.val = 5736) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5736 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05737 (tag : Fin 10000) (htag : tag.val = 5737) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5737 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05738 (tag : Fin 10000) (htag : tag.val = 5738) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5738 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05739 (tag : Fin 10000) (htag : tag.val = 5739) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5739 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05740 (tag : Fin 10000) (htag : tag.val = 5740) (k : Ring12) : tag.val = 5740 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05741 (tag : Fin 10000) (htag : tag.val = 5741) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5741 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05742 (tag : Fin 10000) (htag : tag.val = 5742) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5742 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05743 (tag : Fin 10000) (htag : tag.val = 5743) (x : State) (e : Event) (dr : Ring12) : tag.val = 5743 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05744 (tag : Fin 10000) (htag : tag.val = 5744) (x : State) (e : Event) (dr : Ring12) : tag.val = 5744 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05745 (tag : Fin 10000) (htag : tag.val = 5745) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5745 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05746 (tag : Fin 10000) (htag : tag.val = 5746) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5746 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05747 (tag : Fin 10000) (htag : tag.val = 5747) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5747 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05748 (tag : Fin 10000) (htag : tag.val = 5748) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5748 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05749 (tag : Fin 10000) (htag : tag.val = 5749) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5749 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05750 (tag : Fin 10000) (htag : tag.val = 5750) (k : Ring12) : tag.val = 5750 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05751 (tag : Fin 10000) (htag : tag.val = 5751) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5751 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05752 (tag : Fin 10000) (htag : tag.val = 5752) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5752 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05753 (tag : Fin 10000) (htag : tag.val = 5753) (x : State) (e : Event) (dr : Ring12) : tag.val = 5753 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05754 (tag : Fin 10000) (htag : tag.val = 5754) (x : State) (e : Event) (dr : Ring12) : tag.val = 5754 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05755 (tag : Fin 10000) (htag : tag.val = 5755) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5755 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05756 (tag : Fin 10000) (htag : tag.val = 5756) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5756 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05757 (tag : Fin 10000) (htag : tag.val = 5757) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5757 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05758 (tag : Fin 10000) (htag : tag.val = 5758) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5758 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05759 (tag : Fin 10000) (htag : tag.val = 5759) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5759 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05760 (tag : Fin 10000) (htag : tag.val = 5760) (k : Ring12) : tag.val = 5760 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05761 (tag : Fin 10000) (htag : tag.val = 5761) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5761 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05762 (tag : Fin 10000) (htag : tag.val = 5762) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5762 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05763 (tag : Fin 10000) (htag : tag.val = 5763) (x : State) (e : Event) (dr : Ring12) : tag.val = 5763 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05764 (tag : Fin 10000) (htag : tag.val = 5764) (x : State) (e : Event) (dr : Ring12) : tag.val = 5764 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05765 (tag : Fin 10000) (htag : tag.val = 5765) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5765 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05766 (tag : Fin 10000) (htag : tag.val = 5766) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5766 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05767 (tag : Fin 10000) (htag : tag.val = 5767) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5767 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05768 (tag : Fin 10000) (htag : tag.val = 5768) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5768 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05769 (tag : Fin 10000) (htag : tag.val = 5769) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5769 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05770 (tag : Fin 10000) (htag : tag.val = 5770) (k : Ring12) : tag.val = 5770 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05771 (tag : Fin 10000) (htag : tag.val = 5771) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5771 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05772 (tag : Fin 10000) (htag : tag.val = 5772) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5772 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05773 (tag : Fin 10000) (htag : tag.val = 5773) (x : State) (e : Event) (dr : Ring12) : tag.val = 5773 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05774 (tag : Fin 10000) (htag : tag.val = 5774) (x : State) (e : Event) (dr : Ring12) : tag.val = 5774 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05775 (tag : Fin 10000) (htag : tag.val = 5775) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5775 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05776 (tag : Fin 10000) (htag : tag.val = 5776) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5776 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05777 (tag : Fin 10000) (htag : tag.val = 5777) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5777 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05778 (tag : Fin 10000) (htag : tag.val = 5778) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5778 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05779 (tag : Fin 10000) (htag : tag.val = 5779) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5779 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05780 (tag : Fin 10000) (htag : tag.val = 5780) (k : Ring12) : tag.val = 5780 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05781 (tag : Fin 10000) (htag : tag.val = 5781) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5781 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05782 (tag : Fin 10000) (htag : tag.val = 5782) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5782 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05783 (tag : Fin 10000) (htag : tag.val = 5783) (x : State) (e : Event) (dr : Ring12) : tag.val = 5783 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05784 (tag : Fin 10000) (htag : tag.val = 5784) (x : State) (e : Event) (dr : Ring12) : tag.val = 5784 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05785 (tag : Fin 10000) (htag : tag.val = 5785) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5785 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05786 (tag : Fin 10000) (htag : tag.val = 5786) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5786 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05787 (tag : Fin 10000) (htag : tag.val = 5787) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5787 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05788 (tag : Fin 10000) (htag : tag.val = 5788) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5788 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05789 (tag : Fin 10000) (htag : tag.val = 5789) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5789 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_05790 (tag : Fin 10000) (htag : tag.val = 5790) (k : Ring12) : tag.val = 5790 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_05791 (tag : Fin 10000) (htag : tag.val = 5791) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5791 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_05792 (tag : Fin 10000) (htag : tag.val = 5792) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5792 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_05793 (tag : Fin 10000) (htag : tag.val = 5793) (x : State) (e : Event) (dr : Ring12) : tag.val = 5793 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_05794 (tag : Fin 10000) (htag : tag.val = 5794) (x : State) (e : Event) (dr : Ring12) : tag.val = 5794 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_05795 (tag : Fin 10000) (htag : tag.val = 5795) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5795 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_05796 (tag : Fin 10000) (htag : tag.val = 5796) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 5796 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_05797 (tag : Fin 10000) (htag : tag.val = 5797) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 5797 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_05798 (tag : Fin 10000) (htag : tag.val = 5798) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 5798 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_05799 (tag : Fin 10000) (htag : tag.val = 5799) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 5799 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
