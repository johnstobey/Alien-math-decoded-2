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
theorem generated_07700 (tag : Fin 10000) (htag : tag.val = 7700) (k : Ring12) : tag.val = 7700 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07701 (tag : Fin 10000) (htag : tag.val = 7701) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7701 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07702 (tag : Fin 10000) (htag : tag.val = 7702) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7702 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07703 (tag : Fin 10000) (htag : tag.val = 7703) (x : State) (e : Event) (dr : Ring12) : tag.val = 7703 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07704 (tag : Fin 10000) (htag : tag.val = 7704) (x : State) (e : Event) (dr : Ring12) : tag.val = 7704 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07705 (tag : Fin 10000) (htag : tag.val = 7705) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7705 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07706 (tag : Fin 10000) (htag : tag.val = 7706) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7706 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07707 (tag : Fin 10000) (htag : tag.val = 7707) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7707 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07708 (tag : Fin 10000) (htag : tag.val = 7708) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7708 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07709 (tag : Fin 10000) (htag : tag.val = 7709) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7709 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07710 (tag : Fin 10000) (htag : tag.val = 7710) (k : Ring12) : tag.val = 7710 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07711 (tag : Fin 10000) (htag : tag.val = 7711) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7711 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07712 (tag : Fin 10000) (htag : tag.val = 7712) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7712 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07713 (tag : Fin 10000) (htag : tag.val = 7713) (x : State) (e : Event) (dr : Ring12) : tag.val = 7713 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07714 (tag : Fin 10000) (htag : tag.val = 7714) (x : State) (e : Event) (dr : Ring12) : tag.val = 7714 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07715 (tag : Fin 10000) (htag : tag.val = 7715) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7715 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07716 (tag : Fin 10000) (htag : tag.val = 7716) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7716 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07717 (tag : Fin 10000) (htag : tag.val = 7717) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7717 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07718 (tag : Fin 10000) (htag : tag.val = 7718) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7718 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07719 (tag : Fin 10000) (htag : tag.val = 7719) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7719 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07720 (tag : Fin 10000) (htag : tag.val = 7720) (k : Ring12) : tag.val = 7720 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07721 (tag : Fin 10000) (htag : tag.val = 7721) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7721 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07722 (tag : Fin 10000) (htag : tag.val = 7722) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7722 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07723 (tag : Fin 10000) (htag : tag.val = 7723) (x : State) (e : Event) (dr : Ring12) : tag.val = 7723 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07724 (tag : Fin 10000) (htag : tag.val = 7724) (x : State) (e : Event) (dr : Ring12) : tag.val = 7724 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07725 (tag : Fin 10000) (htag : tag.val = 7725) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7725 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07726 (tag : Fin 10000) (htag : tag.val = 7726) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7726 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07727 (tag : Fin 10000) (htag : tag.val = 7727) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7727 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07728 (tag : Fin 10000) (htag : tag.val = 7728) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7728 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07729 (tag : Fin 10000) (htag : tag.val = 7729) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7729 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07730 (tag : Fin 10000) (htag : tag.val = 7730) (k : Ring12) : tag.val = 7730 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07731 (tag : Fin 10000) (htag : tag.val = 7731) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7731 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07732 (tag : Fin 10000) (htag : tag.val = 7732) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7732 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07733 (tag : Fin 10000) (htag : tag.val = 7733) (x : State) (e : Event) (dr : Ring12) : tag.val = 7733 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07734 (tag : Fin 10000) (htag : tag.val = 7734) (x : State) (e : Event) (dr : Ring12) : tag.val = 7734 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07735 (tag : Fin 10000) (htag : tag.val = 7735) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7735 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07736 (tag : Fin 10000) (htag : tag.val = 7736) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7736 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07737 (tag : Fin 10000) (htag : tag.val = 7737) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7737 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07738 (tag : Fin 10000) (htag : tag.val = 7738) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7738 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07739 (tag : Fin 10000) (htag : tag.val = 7739) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7739 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07740 (tag : Fin 10000) (htag : tag.val = 7740) (k : Ring12) : tag.val = 7740 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07741 (tag : Fin 10000) (htag : tag.val = 7741) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7741 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07742 (tag : Fin 10000) (htag : tag.val = 7742) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7742 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07743 (tag : Fin 10000) (htag : tag.val = 7743) (x : State) (e : Event) (dr : Ring12) : tag.val = 7743 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07744 (tag : Fin 10000) (htag : tag.val = 7744) (x : State) (e : Event) (dr : Ring12) : tag.val = 7744 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07745 (tag : Fin 10000) (htag : tag.val = 7745) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7745 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07746 (tag : Fin 10000) (htag : tag.val = 7746) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7746 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07747 (tag : Fin 10000) (htag : tag.val = 7747) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7747 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07748 (tag : Fin 10000) (htag : tag.val = 7748) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7748 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07749 (tag : Fin 10000) (htag : tag.val = 7749) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7749 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07750 (tag : Fin 10000) (htag : tag.val = 7750) (k : Ring12) : tag.val = 7750 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07751 (tag : Fin 10000) (htag : tag.val = 7751) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7751 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07752 (tag : Fin 10000) (htag : tag.val = 7752) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7752 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07753 (tag : Fin 10000) (htag : tag.val = 7753) (x : State) (e : Event) (dr : Ring12) : tag.val = 7753 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07754 (tag : Fin 10000) (htag : tag.val = 7754) (x : State) (e : Event) (dr : Ring12) : tag.val = 7754 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07755 (tag : Fin 10000) (htag : tag.val = 7755) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7755 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07756 (tag : Fin 10000) (htag : tag.val = 7756) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7756 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07757 (tag : Fin 10000) (htag : tag.val = 7757) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7757 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07758 (tag : Fin 10000) (htag : tag.val = 7758) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7758 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07759 (tag : Fin 10000) (htag : tag.val = 7759) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7759 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07760 (tag : Fin 10000) (htag : tag.val = 7760) (k : Ring12) : tag.val = 7760 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07761 (tag : Fin 10000) (htag : tag.val = 7761) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7761 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07762 (tag : Fin 10000) (htag : tag.val = 7762) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7762 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07763 (tag : Fin 10000) (htag : tag.val = 7763) (x : State) (e : Event) (dr : Ring12) : tag.val = 7763 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07764 (tag : Fin 10000) (htag : tag.val = 7764) (x : State) (e : Event) (dr : Ring12) : tag.val = 7764 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07765 (tag : Fin 10000) (htag : tag.val = 7765) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7765 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07766 (tag : Fin 10000) (htag : tag.val = 7766) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7766 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07767 (tag : Fin 10000) (htag : tag.val = 7767) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7767 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07768 (tag : Fin 10000) (htag : tag.val = 7768) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7768 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07769 (tag : Fin 10000) (htag : tag.val = 7769) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7769 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07770 (tag : Fin 10000) (htag : tag.val = 7770) (k : Ring12) : tag.val = 7770 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07771 (tag : Fin 10000) (htag : tag.val = 7771) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7771 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07772 (tag : Fin 10000) (htag : tag.val = 7772) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7772 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07773 (tag : Fin 10000) (htag : tag.val = 7773) (x : State) (e : Event) (dr : Ring12) : tag.val = 7773 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07774 (tag : Fin 10000) (htag : tag.val = 7774) (x : State) (e : Event) (dr : Ring12) : tag.val = 7774 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07775 (tag : Fin 10000) (htag : tag.val = 7775) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7775 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07776 (tag : Fin 10000) (htag : tag.val = 7776) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7776 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07777 (tag : Fin 10000) (htag : tag.val = 7777) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7777 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07778 (tag : Fin 10000) (htag : tag.val = 7778) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7778 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07779 (tag : Fin 10000) (htag : tag.val = 7779) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7779 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07780 (tag : Fin 10000) (htag : tag.val = 7780) (k : Ring12) : tag.val = 7780 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07781 (tag : Fin 10000) (htag : tag.val = 7781) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7781 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07782 (tag : Fin 10000) (htag : tag.val = 7782) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7782 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07783 (tag : Fin 10000) (htag : tag.val = 7783) (x : State) (e : Event) (dr : Ring12) : tag.val = 7783 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07784 (tag : Fin 10000) (htag : tag.val = 7784) (x : State) (e : Event) (dr : Ring12) : tag.val = 7784 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07785 (tag : Fin 10000) (htag : tag.val = 7785) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7785 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07786 (tag : Fin 10000) (htag : tag.val = 7786) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7786 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07787 (tag : Fin 10000) (htag : tag.val = 7787) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7787 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07788 (tag : Fin 10000) (htag : tag.val = 7788) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7788 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07789 (tag : Fin 10000) (htag : tag.val = 7789) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7789 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

theorem generated_07790 (tag : Fin 10000) (htag : tag.val = 7790) (k : Ring12) : tag.val = 7790 ∧ antipode (antipode k) = k := by
  refine ⟨htag, ?_⟩
  have h : (6 : Ring12) + 6 = 0 := by decide
  simp only [antipode, add_assoc, h, add_zero]

theorem generated_07791 (tag : Fin 10000) (htag : tag.val = 7791) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7791 ∧ Coherent (delta x e dr lawful) := by
  exact ⟨htag, rfl⟩

theorem generated_07792 (tag : Fin 10000) (htag : tag.val = 7792) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7792 ∧ (delta x e dr lawful).n = x.n + 1 := by
  exact ⟨htag, rfl⟩

theorem generated_07793 (tag : Fin 10000) (htag : tag.val = 7793) (x : State) (e : Event) (dr : Ring12) : tag.val = 7793 ∧ (delta x e dr true).r = x.r + dr := by
  exact ⟨htag, rfl⟩

theorem generated_07794 (tag : Fin 10000) (htag : tag.val = 7794) (x : State) (e : Event) (dr : Ring12) : tag.val = 7794 ∧ (delta x e dr false).r = x.r := by
  exact ⟨htag, rfl⟩

theorem generated_07795 (tag : Fin 10000) (htag : tag.val = 7795) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7795 ∧ (delta x e dr lawful).P = insert e.constraint x.P := by
  exact ⟨htag, rfl⟩

theorem generated_07796 (tag : Fin 10000) (htag : tag.val = 7796) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) : tag.val = 7796 ∧ (delta x e dr lawful).E = x.E ++ [e] := by
  exact ⟨htag, rfl⟩

theorem generated_07797 (tag : Fin 10000) (htag : tag.val = 7797) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hs : Antipodal x.S) (hp : Antipodal e.constraint) : tag.val = 7797 ∧ Antipodal (delta x e dr lawful).S := by
  exact ⟨htag, intersection_antipodal x.S e.constraint hs hp⟩

theorem generated_07798 (tag : Fin 10000) (htag : tag.val = 7798) (T : Set (Ring12 × Ring12)) (s : Constraint) (a b : Ring12) : tag.val = 7798 ∧ ((a, b) ∈ tighten T s ↔ (a, b) ∈ T ∧ a ∈ s ∧ b ∈ s) := by
  exact ⟨htag, Iff.rfl⟩

theorem generated_07799 (tag : Fin 10000) (htag : tag.val = 7799) (x : State) (e : Event) (dr : Ring12) (lawful : Bool) (hx : Consistent x) : tag.val = 7799 ∧ Consistent (delta x e dr lawful) := by
  exact ⟨htag, delta_consistent x e dr lawful hx⟩

end Z12ZCompilerV4
