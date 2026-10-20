import IndependentDuodenary.AffineStations

/-! A typed operation language with an independently evaluated permutation semantics. -/
namespace IndependentDuodenary

inductive StationExpr where
  | identity
  | shift (amount : ZMod 12)
  | reflect
  | scale (multiplier : (ZMod 12)ˣ)
  | compose (outer inner : StationExpr)
  | invert (body : StationExpr)
  deriving DecidableEq

/-- `compose outer inner` executes inner first, then outer. -/
def stationMeaning : StationExpr → Equiv.Perm (ZMod 12)
  | .identity => 1
  | .shift k => affineStationPermutation (1, k)
  | .reflect => affineStationPermutation (-1, 0)
  | .scale a => affineStationPermutation (a, 0)
  | .compose outer inner => stationMeaning outer * stationMeaning inner
  | .invert body => (stationMeaning body)⁻¹

/-- Compilation computes a canonical affine parameter pair. -/
def compileStation : StationExpr → AffineStationParameter
  | .identity => (1, 0)
  | .shift k => (1, k)
  | .reflect => (-1, 0)
  | .scale a => (a, 0)
  | .compose outer inner => affineStationCompose (compileStation outer) (compileStation inner)
  | .invert body => affineStationInverse (compileStation body)

def stationSemanticSetoid : Setoid StationExpr where
  r e f := stationMeaning e = stationMeaning f
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

abbrev StationMeaningClass := Quotient stationSemanticSetoid

theorem affine_permutation_compose (p q : AffineStationParameter) :
    affineStationPermutation (affineStationCompose p q) =
      affineStationPermutation p * affineStationPermutation q := by
  ext x
  exact affine_station_composition p q x

theorem affine_permutation_inverse (p : AffineStationParameter) :
    affineStationPermutation (affineStationInverse p) = (affineStationPermutation p)⁻¹ := by
  ext x
  change affineStationApply (affineStationInverse p) x =
    (((p.1⁻¹ : (ZMod 12)ˣ) : ZMod 12)) * (x - p.2)
  simp [affineStationApply, affineStationInverse, mul_sub, sub_eq_add_neg, mul_add]

theorem station_compile_correct (e : StationExpr) :
    affineStationPermutation (compileStation e) = stationMeaning e := by
  induction e with
  | identity => ext x; simp [compileStation, stationMeaning, affineStationPermutation, affineStationApply]
  | shift k => rfl
  | reflect => rfl
  | scale a => rfl
  | compose outer inner ho hi =>
    simp only [compileStation, stationMeaning, affine_permutation_compose, ho, hi]
  | invert body h =>
    simp only [compileStation, stationMeaning, affine_permutation_inverse, h]

/-- Canonical decoding is an expression with the same operation, not the original syntax tree. -/
def expressionFromParameter (p : AffineStationParameter) : StationExpr :=
  .compose (.shift p.2) (.scale p.1)

theorem compile_parameter_expression (p : AffineStationParameter) :
    compileStation (expressionFromParameter p) = p := by
  rcases p with ⟨a, b⟩
  simp [expressionFromParameter, compileStation, affineStationCompose]

def normalizeStation (e : StationExpr) : StationExpr := expressionFromParameter (compileStation e)

theorem station_normalization_meaning (e : StationExpr) :
    stationMeaning (normalizeStation e) = stationMeaning e := by
  rw [← station_compile_correct, normalizeStation, compile_parameter_expression, station_compile_correct]

theorem station_normalization_idempotent (e : StationExpr) :
    normalizeStation (normalizeStation e) = normalizeStation e := by
  simp [normalizeStation, compile_parameter_expression]

theorem station_meaning_iff_compiled (e f : StationExpr) :
    stationMeaning e = stationMeaning f ↔ compileStation e = compileStation f := by
  constructor
  · intro h
    apply affine_station_permutation_injective
    rw [station_compile_correct, station_compile_correct, h]
  · intro h
    rw [← station_compile_correct, ← station_compile_correct, h]

/-- A decision procedure is justified by the compiler-correctness proof. -/
def sameStationMeaning (e f : StationExpr) : Bool := decide (compileStation e = compileStation f)

theorem same_station_meaning_correct (e f : StationExpr) :
    sameStationMeaning e f = true ↔ stationMeaning e = stationMeaning f := by
  simp [sameStationMeaning, station_meaning_iff_compiled]

def compileMeaningClass : StationMeaningClass → AffineStationParameter :=
  Quotient.lift compileStation (fun e f h => (station_meaning_iff_compiled e f).mp h)

def parameterMeaningClass (p : AffineStationParameter) : StationMeaningClass :=
  Quotient.mk stationSemanticSetoid (expressionFromParameter p)

theorem meaning_parameter_roundtrip (p : AffineStationParameter) :
    compileMeaningClass (parameterMeaningClass p) = p := compile_parameter_expression p

theorem parameter_meaning_roundtrip (q : StationMeaningClass) :
    parameterMeaningClass (compileMeaningClass q) = q := by
  refine Quotient.inductionOn q ?_
  intro e
  apply Quotient.sound
  exact station_normalization_meaning e

def stationMeaningEquiv : StationMeaningClass ≃ AffineStationParameter where
  toFun := compileMeaningClass
  invFun := parameterMeaningClass
  left_inv := parameter_meaning_roundtrip
  right_inv := meaning_parameter_roundtrip

theorem station_meaning_class_card : Nat.card StationMeaningClass = 48 := by
  rw [Nat.card_congr stationMeaningEquiv, Nat.card_eq_fintype_card, affine_station_parameter_card]

/-- The ledger's s*r*s relation, with right-to-left execution stated explicitly. -/
def reflectionConjugationExample : StationExpr :=
  .compose .reflect (.compose (.shift 1) .reflect)

theorem reflection_example_parameters : compileStation reflectionConjugationExample = (1, 11) := by decide

theorem reflection_example_meaning :
    stationMeaning reflectionConjugationExample = stationMeaning (.shift 11) := by
  apply (station_meaning_iff_compiled _ _).mpr
  exact reflection_example_parameters

def scaleAfterShiftExample : StationExpr := .compose (.scale multiplyFiveParameter.1) (.shift 3)

theorem scale_shift_example_parameters : compileStation scaleAfterShiftExample = (multiplyFiveParameter.1, 3) := by decide

theorem scale_shift_example_at_two : stationMeaning scaleAfterShiftExample 2 = 1 := by decide

end IndependentDuodenary
