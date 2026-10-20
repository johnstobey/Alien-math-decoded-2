import IndependentDuodenary.ModularCore

/-! Concrete presheaves on finite index sets and their natural maps. -/
namespace IndependentDuodenary

structure RegisterFamily where
  Carrier : ℕ → Type
  restrict : {r s : ℕ} → (Fin s → Fin r) → Carrier r → Carrier s
  restrict_identity : ∀ {r} (x : Carrier r), restrict id x = x
  restrict_composition : ∀ {r s t} (a : Fin s → Fin r) (b : Fin t → Fin s) (x : Carrier r),
    restrict b (restrict a x) = restrict (a ∘ b) x

structure RegisterNaturalMap (F G : RegisterFamily) where
  app : (r : ℕ) → F.Carrier r → G.Carrier r
  naturality : ∀ {r s} (select : Fin s → Fin r) (x : F.Carrier r),
    G.restrict select (app r x) = app s (F.restrict select x)

def pointwiseFamily (A : Type) : RegisterFamily where
  Carrier r := Fin r → A
  restrict select x := x ∘ select
  restrict_identity _ := rfl
  restrict_composition _ _ _ := rfl

def productRegisterFamily (F G : RegisterFamily) : RegisterFamily where
  Carrier r := F.Carrier r × G.Carrier r
  restrict select x := (F.restrict select x.1, G.restrict select x.2)
  restrict_identity x := by simp only [F.restrict_identity, G.restrict_identity]
  restrict_composition a b x := by simp only [F.restrict_composition, G.restrict_composition]

def pointwiseNaturalMap {A B : Type} (f : A → B) :
    RegisterNaturalMap (pointwiseFamily A) (pointwiseFamily B) where
  app _ x := f ∘ x
  naturality _ _ := rfl

def pointwiseBinaryNaturalMap {A B C : Type} (f : A → B → C) :
    RegisterNaturalMap (productRegisterFamily (pointwiseFamily A) (pointwiseFamily B))
      (pointwiseFamily C) where
  app _ x := fun i => f (x.1 i) (x.2 i)
  naturality _ _ := rfl

def composeRegisterNatural {F G H : RegisterFamily}
    (g : RegisterNaturalMap G H) (f : RegisterNaturalMap F G) : RegisterNaturalMap F H where
  app r x := g.app r (f.app r x)
  naturality select x := by rw [g.naturality, f.naturality]

/-- Retain the input whenever an observation may discard information. -/
def retainRegisterNatural {F G : RegisterFamily} (f : RegisterNaturalMap F G) :
    RegisterNaturalMap F (productRegisterFamily F G) where
  app r x := (x, f.app r x)
  naturality select x := by
    change (F.restrict select x, G.restrict select (f.app _ x)) = _
    rw [f.naturality]

theorem retained_register_natural_injective {F G : RegisterFamily}
    (f : RegisterNaturalMap F G) (r : ℕ) :
    Function.Injective ((retainRegisterNatural f).app r) := by
  intro x y h
  exact congrArg Prod.fst h

/-- Naturality of a parameterized iteration; the parameter restricts with its subsystem. -/
theorem register_natural_parameter_iterate {F H : RegisterFamily}
    (A : RegisterNaturalMap (productRegisterFamily H F) F)
    {r s : ℕ} (select : Fin s → Fin r) (h : H.Carrier r) (n : ℕ) (x : F.Carrier r) :
    F.restrict select (((fun y => A.app r (h, y))^[n]) x) =
      (((fun y => A.app s (H.restrict select h, y))^[n]) (F.restrict select x)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', A.naturality]
    change A.app s (H.restrict select h,
      F.restrict select (((fun y => A.app r (h, y))^[n]) x)) = _
    rw [ih]

theorem successor_period_left_inverse {A : Type} (T : A → A) (n : ℕ)
    (hperiod : ∀ x, (T^[n + 1]) x = x) : Function.LeftInverse (T^[n]) T := by
  intro x
  rw [← Function.iterate_succ_apply]
  exact hperiod x

theorem successor_period_injective {A : Type} (T : A → A) (n : ℕ)
    (hperiod : ∀ x, (T^[n + 1]) x = x) : Function.Injective T :=
  (successor_period_left_inverse T n hperiod).injective

end IndependentDuodenary
