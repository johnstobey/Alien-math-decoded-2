import IndependentDuodenary.ModularCore
import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-! Cyclic geometry and explicit symmetries from the independent structural ledger. -/
namespace IndependentDuodenary

/-- CRT is an isomorphism of rings, not just a numerical coincidence. -/
def twelveCRT : ZMod 12 ≃+* ZMod 4 × ZMod 3 :=
  ZMod.chineseRemainder (m := 4) (n := 3) (by decide)

def crtReconstruct (p : ZMod 4 × ZMod 3) : ZMod 12 :=
  9 * (p.1.val : ZMod 12) + 4 * (p.2.val : ZMod 12)

theorem twelveCRT_bijective : Function.Bijective twelveCRT := twelveCRT.bijective

theorem crt_reconstruct_coordinates : ∀ p, twelveCRT (crtReconstruct p) = p := by decide

theorem twelveCRT_inverse_formula (p : ZMod 4 × ZMod 3) :
    twelveCRT.symm p = crtReconstruct p := by
  apply twelveCRT.injective
  rw [twelveCRT.apply_symm_apply, crt_reconstruct_coordinates]

theorem crt_reconstruct_original (x : ZMod 12) : crtReconstruct (twelveCRT x) = x := by
  rw [← twelveCRT_inverse_formula, twelveCRT.symm_apply_apply]

def rotateStation (x : ZMod 12) : ZMod 12 := x + 1

def reflectStation (x : ZMod 12) : ZMod 12 := -x

theorem rotation_twelve_returns : ∀ x, (rotateStation^[12]) x = x := by decide

theorem rotation_no_shorter_period :
    ∀ k : Fin 12, (∀ x, (rotateStation^[k.val]) x = x) ↔ k = 0 := by decide

theorem reflection_involution (x : ZMod 12) : reflectStation (reflectStation x) = x := by
  simp [reflectStation]

theorem reflection_rotation_relation (x : ZMod 12) :
    reflectStation (rotateStation (reflectStation x)) = x - 1 := by
  simp [reflectStation, rotateStation, sub_eq_add_neg, add_comm]

def antipode (x : ZMod 12) : ZMod 12 := x + 6

theorem antipode_involution : ∀ x, antipode (antipode x) = x := by decide

theorem antipode_fixed_point_free : ∀ x, antipode x ≠ x := by decide

def antipodalPair (i : Fin 6) : Finset (ZMod 12) :=
  {(i.val : ZMod 12), (i.val : ZMod 12) + 6}

theorem antipodal_pair_card : ∀ i, (antipodalPair i).card = 2 := by decide

theorem antipodal_pairs_cover : ∀ x : ZMod 12, ∃ i, x ∈ antipodalPair i := by decide

theorem antipodal_pairs_disjoint :
    ∀ i j : Fin 6, i ≠ j → Disjoint (antipodalPair i) (antipodalPair j) := by decide

theorem antipodal_pairs_injective : Function.Injective antipodalPair := by decide

theorem antipodal_pair_family_card :
    (Finset.univ.image antipodalPair).card = 6 := by
  rw [Finset.card_image_of_injective _ antipodal_pairs_injective]
  rfl

def directedDifference (a b : ZMod 12) : ZMod 12 := b - a

theorem directed_difference_translation (a b k : ZMod 12) :
    directedDifference (a + k) (b + k) = directedDifference a b := by
  simp [directedDifference]

def cyclicDistance (a b : ZMod 12) : ℕ :=
  min (b - a).val (12 - (b - a).val)

theorem cyclic_distance_translation (a b k : ZMod 12) :
    cyclicDistance (a + k) (b + k) = cyclicDistance a b := by
  simp [cyclicDistance]

theorem cyclic_distance_reflection :
    ∀ a b : ZMod 12, cyclicDistance (-a) (-b) = cyclicDistance a b := by decide

theorem cyclic_distance_bound : ∀ a b : ZMod 12, cyclicDistance a b ≤ 6 := by decide

theorem cyclic_distance_all_values :
    ∀ d : Fin 7, ∃ x : ZMod 12, cyclicDistance 0 x = d.val := by decide

/-- The standard dihedral group acts faithfully on the twelve station labels. -/
def dihedralStationAction : DihedralGroup 12 → ZMod 12 → ZMod 12
  | .r k, x => x + k
  | .sr k, x => -(x + k)

theorem dihedral_action_one (x : ZMod 12) : dihedralStationAction 1 x = x := by
  simp [DihedralGroup.one_def, dihedralStationAction]

theorem dihedral_action_mul (g h : DihedralGroup 12) (x : ZMod 12) :
    dihedralStationAction (g * h) x = dihedralStationAction g (dihedralStationAction h x) := by
  cases g <;> cases h <;> simp [dihedralStationAction] <;> ring

def dihedralStationPermutation (g : DihedralGroup 12) : Equiv.Perm (ZMod 12) where
  toFun := dihedralStationAction g
  invFun := dihedralStationAction g⁻¹
  left_inv x := by rw [← dihedral_action_mul, inv_mul_cancel, dihedral_action_one]
  right_inv x := by rw [← dihedral_action_mul, mul_inv_cancel, dihedral_action_one]

def dihedralStationHom : DihedralGroup 12 →* Equiv.Perm (ZMod 12) where
  toFun := dihedralStationPermutation
  map_one' := by ext x; exact dihedral_action_one x
  map_mul' g h := by ext x; exact dihedral_action_mul g h x

/-- Values at two adjacent stations separate the explicitly defined dihedral maps. -/
theorem dihedral_zero_one_separates : ∀ g h : DihedralGroup 12,
    dihedralStationAction g 0 = dihedralStationAction h 0 →
    dihedralStationAction g 1 = dihedralStationAction h 1 → g = h := by decide

theorem dihedral_station_hom_injective : Function.Injective dihedralStationHom := by
  intro g h heq
  apply dihedral_zero_one_separates g h
  · exact congrArg (fun f : Equiv.Perm (ZMod 12) => f 0) heq
  · exact congrArg (fun f : Equiv.Perm (ZMod 12) => f 1) heq

theorem dihedral_twelve_card : Fintype.card (DihedralGroup 12) = 24 := by
  rw [DihedralGroup.card]

theorem dihedral_preserves_cyclic_distance (g : DihedralGroup 12) (a b : ZMod 12) :
    cyclicDistance (dihedralStationAction g a) (dihedralStationAction g b) =
      cyclicDistance a b := by
  cases g with
  | r k => exact cyclic_distance_translation a b k
  | sr k =>
    exact (cyclic_distance_reflection (a + k) (b + k)).trans
      (cyclic_distance_translation a b k)

/-- Two distances to adjacent reference vertices distinguish every station. -/
theorem cyclic_zero_one_separates : ∀ x y : ZMod 12,
    cyclicDistance 0 x = cyclicDistance 0 y →
    cyclicDistance 1 x = cyclicDistance 1 y → x = y := by decide

theorem cyclic_distance_one_iff : ∀ a b : ZMod 12,
    cyclicDistance a b = 1 ↔ b = a + 1 ∨ b = a - 1 := by decide

theorem dihedral_matches_directed_edge (a b : ZMod 12) (hab : cyclicDistance a b = 1) :
    ∃ g : DihedralGroup 12, dihedralStationAction g 0 = a ∧ dihedralStationAction g 1 = b := by
  rcases (cyclic_distance_one_iff a b).mp hab with hb | hb
  · refine ⟨.r a, ?_, ?_⟩ <;> simp [dihedralStationAction, hb, add_comm]
  · refine ⟨.sr (-a), ?_, ?_⟩ <;>
      simp [dihedralStationAction, hb, sub_eq_add_neg, add_comm]

/-- Every symmetry of the labelled cyclic metric is one of the dihedral maps. -/
theorem cyclic_isometry_is_dihedral (f : ZMod 12 → ZMod 12)
    (hf : ∀ a b, cyclicDistance (f a) (f b) = cyclicDistance a b) :
    ∃ g : DihedralGroup 12, f = dihedralStationAction g := by
  have hedge : cyclicDistance (f 0) (f 1) = 1 :=
    (hf 0 1).trans (by decide : cyclicDistance 0 1 = 1)
  obtain ⟨g, hg0, hg1⟩ := dihedral_matches_directed_edge (f 0) (f 1) hedge
  refine ⟨g, ?_⟩
  funext x
  let y := dihedralStationAction g⁻¹ (f x)
  have hinv : dihedralStationAction g y = f x := by
    dsimp [y]
    rw [← dihedral_action_mul, mul_inv_cancel, dihedral_action_one]
  have hzero : cyclicDistance 0 y = cyclicDistance 0 x := by
    calc
      _ = cyclicDistance (dihedralStationAction g 0) (dihedralStationAction g y) :=
        (dihedral_preserves_cyclic_distance g 0 y).symm
      _ = cyclicDistance (f 0) (f x) := by rw [hg0, hinv]
      _ = _ := hf 0 x
  have hone : cyclicDistance 1 y = cyclicDistance 1 x := by
    calc
      _ = cyclicDistance (dihedralStationAction g 1) (dihedralStationAction g y) :=
        (dihedral_preserves_cyclic_distance g 1 y).symm
      _ = cyclicDistance (f 1) (f x) := by rw [hg1, hinv]
      _ = _ := hf 1 x
  have hy : y = x := cyclic_zero_one_separates y x hzero hone
  exact hinv.symm.trans (congrArg (dihedralStationAction g) hy)

abbrev CyclicStationIsometry := {f : ZMod 12 → ZMod 12 //
  ∀ a b, cyclicDistance (f a) (f b) = cyclicDistance a b}

noncomputable def dihedralCyclicIsometryEquiv : DihedralGroup 12 ≃ CyclicStationIsometry := by
  apply Equiv.ofBijective (fun g => ⟨dihedralStationAction g, dihedral_preserves_cyclic_distance g⟩)
  constructor
  · intro g h heq
    have hf := congrArg Subtype.val heq
    apply dihedral_zero_one_separates g h
    · exact congrFun hf 0
    · exact congrFun hf 1
  · rintro ⟨f, hf⟩
    obtain ⟨g, hg⟩ := cyclic_isometry_is_dihedral f hf
    exact ⟨g, Subtype.ext hg.symm⟩

theorem cyclic_station_isometry_card : Nat.card CyclicStationIsometry = 24 := by
  rw [← Nat.card_congr dihedralCyclicIsometryEquiv, Nat.card_eq_fintype_card,
    dihedral_twelve_card]

end IndependentDuodenary
