import IndependentDuodenary.MappingBoundary

/-!
# Restricted binary-to-residue bridges and their obstruction

These independently defined additive maps require a chosen binary-valued
homomorphism. They do not formalize the full source table/key construction.
-/
namespace IndependentDuodenary

/-- Embed the additive binary group into the order-two subgroup modulo 12. -/
def bitToTwelve : ZMod 2 →+ ZMod 12 where
  toFun x := if x = 0 then 0 else 6
  map_zero' := by decide
  map_add' := by decide

/-- Embed the additive binary group into the order-two subgroup modulo 144. -/
def bitTo144 : ZMod 2 →+ ZMod 144 where
  toFun x := if x = 0 then 0 else 72
  map_zero' := by decide
  map_add' := by decide

theorem bitToTwelve_values : bitToTwelve 0 = 0 ∧ bitToTwelve 1 = 6 := by decide

theorem bitTo144_values : bitTo144 0 = 0 ∧ bitTo144 1 = 72 := by decide

theorem bitToTwelve_injective : Function.Injective bitToTwelve := by decide

theorem bitTo144_injective : Function.Injective bitTo144 := by decide

theorem binary_double_zero : ∀ x : ZMod 2, x + x = 0 := by decide

theorem twelve_two_torsion :
    ∀ x : ZMod 12, x + x = 0 ↔ x = 0 ∨ x = 6 := by decide

set_option maxRecDepth 4096 in
theorem mod144_two_torsion :
    ∀ x : ZMod 144, x + x = 0 ↔ x = 0 ∨ x = 72 := by decide

/-- Binary vector addition has exponent two, in every dimension. -/
theorem binary_vector_double_zero {ℓ : ℕ} (v : Fin ℓ → ZMod 2) : v + v = 0 := by
  funext i
  exact binary_double_zero (v i)

/-- Any additive image of an exponent-two monoid is two-torsion. -/
theorem image_double_zero {K B : Type*} [AddMonoid K] [AddMonoid B]
    (hK : ∀ x : K, x + x = 0) (f : K →+ B) (x : K) : f x + f x = 0 := by
  rw [← map_add, hK, map_zero]

theorem image_in_two_stations {K : Type*} [AddMonoid K]
    (hK : ∀ x : K, x + x = 0) (f : K →+ ZMod 12) (x : K) :
    f x = 0 ∨ f x = 6 :=
  (twelve_two_torsion (f x)).mp (image_double_zero hK f x)

theorem image_in_two_superstations {K : Type*} [AddMonoid K]
    (hK : ∀ x : K, x + x = 0) (f : K →+ ZMod 144) (x : K) :
    f x = 0 ∨ f x = 72 :=
  (mod144_two_torsion (f x)).mp (image_double_zero hK f x)

theorem binary_map_not_surjective_twelve {K : Type*} [AddMonoid K]
    (hK : ∀ x : K, x + x = 0) (f : K →+ ZMod 12) :
    ¬ Function.Surjective f := by
  intro hs
  obtain ⟨x, hx⟩ := hs 1
  have h := image_in_two_stations hK f x
  rw [hx] at h
  exact (by decide : ¬ ((1 : ZMod 12) = 0 ∨ (1 : ZMod 12) = 6)) h

theorem binary_map_not_surjective_144 {K : Type*} [AddMonoid K]
    (hK : ∀ x : K, x + x = 0) (f : K →+ ZMod 144) :
    ¬ Function.Surjective f := by
  intro hs
  obtain ⟨x, hx⟩ := hs 1
  have h := image_in_two_superstations hK f x
  rw [hx] at h
  exact (by decide : ¬ ((1 : ZMod 144) = 0 ∨ (1 : ZMod 144) = 72)) h

/-- Choosing a coordinate supplies one explicit binary-valued functional. -/
def binaryCoordinate {ℓ : ℕ} (i : Fin ℓ) : (Fin ℓ → ZMod 2) →+ ZMod 2 where
  toFun v := v i
  map_zero' := rfl
  map_add' _ _ := rfl

theorem binaryCoordinate_surjective {ℓ : ℕ} (i : Fin ℓ) :
    Function.Surjective (binaryCoordinate i) := by
  intro b
  exact ⟨fun _ => b, rfl⟩

theorem binaryCoordinate_not_injective {ℓ : ℕ} (i j : Fin ℓ) (hij : i ≠ j) :
    ¬ Function.Injective (binaryCoordinate i) := by
  intro h
  let v : Fin ℓ → ZMod 2 := fun k => if k = j then 1 else 0
  have hv : binaryCoordinate i v = binaryCoordinate i 0 := by
    simp [binaryCoordinate, v, hij]
  have heq : v = 0 := h hv
  have hj := congrFun heq j
  simp [v] at hj

/-- The bridge depends on the supplied choice of functional χ. -/
def bridgeTwelve {K : Type*} [AddMonoid K] (χ : K →+ ZMod 2) : K →+ ZMod 12 :=
  bitToTwelve.comp χ

def bridge144 {K : Type*} [AddMonoid K] (χ : K →+ ZMod 2) : K →+ ZMod 144 :=
  bitTo144.comp χ

theorem bridgeTwelve_preserves_addition {K : Type*} [AddMonoid K]
    (χ : K →+ ZMod 2) :
    PreservesOperation (fun x y : K => x + y)
      (fun x y : ZMod 12 => x + y) (bridgeTwelve χ) := by
  intro x y
  exact map_add (bridgeTwelve χ) x y

theorem bridge144_preserves_addition {K : Type*} [AddMonoid K]
    (χ : K →+ ZMod 2) :
    PreservesOperation (fun x y : K => x + y)
      (fun x y : ZMod 144 => x + y) (bridge144 χ) := by
  intro x y
  exact map_add (bridge144 χ) x y

theorem bridgeTwelve_range {K : Type*} [AddMonoid K]
    (χ : K →+ ZMod 2) (hχ : Function.Surjective χ) (y : ZMod 12) :
    (∃ x, bridgeTwelve χ x = y) ↔ y = 0 ∨ y = 6 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact (by decide : ∀ b : ZMod 2, bitToTwelve b = 0 ∨ bitToTwelve b = 6) (χ x)
  · intro hy
    rcases hy with rfl | rfl
    · obtain ⟨x, hx⟩ := hχ 0
      exact ⟨x, by change bitToTwelve (χ x) = 0; rw [hx]; exact bitToTwelve_values.1⟩
    · obtain ⟨x, hx⟩ := hχ 1
      exact ⟨x, by change bitToTwelve (χ x) = 6; rw [hx]; exact bitToTwelve_values.2⟩

theorem bridge144_range {K : Type*} [AddMonoid K]
    (χ : K →+ ZMod 2) (hχ : Function.Surjective χ) (y : ZMod 144) :
    (∃ x, bridge144 χ x = y) ↔ y = 0 ∨ y = 72 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact (by decide : ∀ b : ZMod 2, bitTo144 b = 0 ∨ bitTo144 b = 72) (χ x)
  · intro hy
    rcases hy with rfl | rfl
    · obtain ⟨x, hx⟩ := hχ 0
      exact ⟨x, by change bitTo144 (χ x) = 0; rw [hx]; exact bitTo144_values.1⟩
    · obtain ⟨x, hx⟩ := hχ 1
      exact ⟨x, by change bitTo144 (χ x) = 72; rw [hx]; exact bitTo144_values.2⟩

theorem bridgeTwelve_injective_iff {K : Type*} [AddMonoid K]
    (χ : K →+ ZMod 2) :
    Function.Injective (bridgeTwelve χ) ↔ Function.Injective χ := by
  constructor
  · intro h x y hxy
    apply h
    change bitToTwelve (χ x) = bitToTwelve (χ y)
    rw [hxy]
  · intro h
    exact bitToTwelve_injective.comp h

theorem bridge144_injective_iff {K : Type*} [AddMonoid K]
    (χ : K →+ ZMod 2) :
    Function.Injective (bridge144 χ) ↔ Function.Injective χ := by
  constructor
  · intro h x y hxy
    apply h
    change bitTo144 (χ x) = bitTo144 (χ y)
    rw [hxy]
  · intro h
    exact bitTo144_injective.comp h

theorem coordinate_bridgeTwelve_range {ℓ : ℕ} (i : Fin ℓ) (y : ZMod 12) :
    (∃ v, bridgeTwelve (binaryCoordinate i) v = y) ↔ y = 0 ∨ y = 6 :=
  bridgeTwelve_range _ (binaryCoordinate_surjective i) y

theorem coordinate_bridge144_range {ℓ : ℕ} (i : Fin ℓ) (y : ZMod 144) :
    (∃ v, bridge144 (binaryCoordinate i) v = y) ↔ y = 0 ∨ y = 72 :=
  bridge144_range _ (binaryCoordinate_surjective i) y

/-- Additive embeddings above cannot be promoted to unital ring maps. -/
theorem no_binary_ring_hom_twelve : ¬ Nonempty (ZMod 2 →+* ZMod 12) := by
  rintro ⟨f⟩
  have h : (1 : ZMod 12) + 1 = 0 := by
    calc
      (1 : ZMod 12) + 1 = f (1 + 1) := by rw [map_add, map_one]
      _ = 0 := by rw [binary_double_zero, map_zero]
  exact (by decide : (1 : ZMod 12) + 1 ≠ 0) h

theorem no_binary_ring_hom_144 : ¬ Nonempty (ZMod 2 →+* ZMod 144) := by
  rintro ⟨f⟩
  have h : (1 : ZMod 144) + 1 = 0 := by
    calc
      (1 : ZMod 144) + 1 = f (1 + 1) := by rw [map_add, map_one]
      _ = 0 := by rw [binary_double_zero, map_zero]
  exact (by decide : (1 : ZMod 144) + 1 ≠ 0) h

end IndependentDuodenary
