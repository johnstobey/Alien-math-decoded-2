import IndependentDuodenary.StationGrammar
import IndependentDuodenary.EncodingIntegrity
import IndependentDuodenary.SourceKeys

/-! A checked two-symbol codec, operation transport, and bounded-error recovery. -/
namespace IndependentDuodenary

abbrev StationWireCode := ZMod 12 × ZMod 12

def sevenStationUnit : (ZMod 12)ˣ := ⟨7, 7, by decide, by decide⟩

def parseStationUnit (x : ZMod 12) : Option (ZMod 12)ˣ :=
  if x = 1 then some 1
  else if x = 5 then some multiplyFiveParameter.1
  else if x = 7 then some sevenStationUnit
  else if x = 11 then some (-1)
  else none

theorem parse_station_unit_roundtrip : ∀ u : (ZMod 12)ˣ,
    parseStationUnit (u : ZMod 12) = some u := by decide

theorem parse_station_unit_sound : ∀ x : ZMod 12, ∀ u : (ZMod 12)ˣ,
    parseStationUnit x = some u → (u : ZMod 12) = x := by decide

def encodeStationParameter (p : AffineStationParameter) : StationWireCode :=
  ((p.1 : ZMod 12), p.2)

def parseStationParameter (c : StationWireCode) : Option AffineStationParameter :=
  (parseStationUnit c.1).map (fun u => (u, c.2))

theorem parse_station_parameter_roundtrip (p : AffineStationParameter) :
    parseStationParameter (encodeStationParameter p) = some p := by
  simp [parseStationParameter, encodeStationParameter, parse_station_unit_roundtrip]

theorem encode_parsed_station_parameter (c : StationWireCode) (p : AffineStationParameter)
    (h : parseStationParameter c = some p) : encodeStationParameter p = c := by
  rcases c with ⟨x, b⟩
  cases hp : parseStationUnit x with
  | none => simp [parseStationParameter, hp] at h
  | some u =>
    have heq : (u, b) = p := by simpa [parseStationParameter, hp] using h
    subst p
    exact Prod.ext (parse_station_unit_sound x u hp) rfl

def encodeStationExpression (e : StationExpr) : StationWireCode :=
  encodeStationParameter (compileStation e)

def decodeStationExpression (c : StationWireCode) : Option StationExpr :=
  (parseStationParameter c).map expressionFromParameter

theorem station_expression_decode_encode (e : StationExpr) :
    decodeStationExpression (encodeStationExpression e) = some (normalizeStation e) := by
  simp [decodeStationExpression, encodeStationExpression, parse_station_parameter_roundtrip,
    normalizeStation]

def encodeStationMeaning (q : StationMeaningClass) : StationWireCode :=
  encodeStationParameter (compileMeaningClass q)

def decodeStationMeaning (c : StationWireCode) : Option StationMeaningClass :=
  (parseStationParameter c).map parameterMeaningClass

theorem station_meaning_decode_encode (q : StationMeaningClass) :
    decodeStationMeaning (encodeStationMeaning q) = some q := by
  simp [decodeStationMeaning, encodeStationMeaning, parse_station_parameter_roundtrip,
    parameter_meaning_roundtrip]

theorem station_expression_semantic_roundtrip (e : StationExpr) :
    decodeStationMeaning (encodeStationExpression e) = some (Quotient.mk stationSemanticSetoid e) :=
  station_meaning_decode_encode (Quotient.mk stationSemanticSetoid e)

theorem station_parameter_encoding_injective : Function.Injective encodeStationParameter := by
  intro p q h
  have hfirst : (p.1 : ZMod 12) = (q.1 : ZMod 12) :=
    congrArg (fun c : StationWireCode => c.1) h
  have hsecond : p.2 = q.2 := congrArg (fun c : StationWireCode => c.2) h
  exact Prod.ext (Units.ext hfirst) hsecond

theorem station_code_collision_iff (e f : StationExpr) :
    encodeStationExpression e = encodeStationExpression f ↔ stationMeaning e = stationMeaning f := by
  constructor
  · intro h
    exact (station_meaning_iff_compiled e f).mpr (station_parameter_encoding_injective h)
  · intro h
    exact congrArg encodeStationParameter ((station_meaning_iff_compiled e f).mp h)

abbrev ValidStationCode := {c : StationWireCode // (parseStationParameter c).isSome = true}

def encodeValidStationMeaning (q : StationMeaningClass) : ValidStationCode :=
  ⟨encodeStationMeaning q, by simp [encodeStationMeaning, parse_station_parameter_roundtrip]⟩

def decodeValidStationMeaning (c : ValidStationCode) : StationMeaningClass :=
  parameterMeaningClass ((parseStationParameter c.1).get c.2)

theorem valid_station_decode_encode (q : StationMeaningClass) :
    decodeValidStationMeaning (encodeValidStationMeaning q) = q := by
  simp [decodeValidStationMeaning, encodeValidStationMeaning, encodeStationMeaning,
    parse_station_parameter_roundtrip, parameter_meaning_roundtrip]

theorem valid_station_encode_decode (c : ValidStationCode) :
    encodeValidStationMeaning (decodeValidStationMeaning c) = c := by
  apply Subtype.ext
  change encodeStationParameter (compileMeaningClass
    (parameterMeaningClass ((parseStationParameter c.1).get c.2))) = c.1
  rw [meaning_parameter_roundtrip]
  exact encode_parsed_station_parameter c.1 _ (Option.some_get c.2).symm

def stationValidCodeEquiv : StationMeaningClass ≃ ValidStationCode where
  toFun := encodeValidStationMeaning
  invFun := decodeValidStationMeaning
  left_inv := valid_station_decode_encode
  right_inv := valid_station_encode_decode

theorem valid_station_code_card : Nat.card ValidStationCode = 48 := by
  rw [← Nat.card_congr stationValidCodeEquiv, station_meaning_class_card]

theorem raw_station_code_card : Fintype.card StationWireCode = 144 := by
  rw [Fintype.card_prod, ZMod.card]

def composeStationWire (outer inner : StationWireCode) : Option StationWireCode := do
  let p ← parseStationParameter outer
  let q ← parseStationParameter inner
  pure (encodeStationParameter (affineStationCompose p q))

def invertStationWire (c : StationWireCode) : Option StationWireCode := do
  let p ← parseStationParameter c
  pure (encodeStationParameter (affineStationInverse p))

theorem station_wire_composition (outer inner : StationExpr) :
    composeStationWire (encodeStationExpression outer) (encodeStationExpression inner) =
      some (encodeStationExpression (.compose outer inner)) := by
  simp [composeStationWire, encodeStationExpression, parse_station_parameter_roundtrip,
    compileStation]

theorem station_wire_inverse (e : StationExpr) :
    invertStationWire (encodeStationExpression e) = some (encodeStationExpression (.invert e)) := by
  simp [invertStationWire, encodeStationExpression, parse_station_parameter_roundtrip,
    compileStation]

theorem reject_nonunit_station_code : parseStationParameter (2, 0) = none := by decide

theorem reflection_example_wire : encodeStationExpression reflectionConjugationExample = (1, 11) := by decide

theorem scale_shift_example_wire : encodeStationExpression scaleAfterShiftExample = (5, 3) := by decide

abbrev ProtectedStationCode := (Fin 3 → ZMod 12) × (Fin 3 → ZMod 12)

def protectStationWire (c : StationWireCode) : ProtectedStationCode :=
  (repetitionWord 3 c.1, repetitionWord 3 c.2)

def recoverStationWire (received : ProtectedStationCode) : StationWireCode :=
  (tripleMajority received.1, tripleMajority received.2)

theorem protected_station_wire_recovery (c : StationWireCode) (received : ProtectedStationCode)
    (hfirst : wordDistance (protectStationWire c).1 received.1 ≤ 1)
    (hsecond : wordDistance (protectStationWire c).2 received.2 ≤ 1) :
    recoverStationWire received = c := by
  exact Prod.ext (repetition_majority_recovery c.1 received.1 hfirst)
    (repetition_majority_recovery c.2 received.2 hsecond)

/-- The full expression-to-wire-to-corrupted-word-to-meaning path. -/
theorem protected_station_semantic_recovery (e : StationExpr) (received : ProtectedStationCode)
    (hfirst : wordDistance (protectStationWire (encodeStationExpression e)).1 received.1 ≤ 1)
    (hsecond : wordDistance (protectStationWire (encodeStationExpression e)).2 received.2 ≤ 1) :
    decodeStationMeaning (recoverStationWire received) = some (Quotient.mk stationSemanticSetoid e) := by
  rw [protected_station_wire_recovery (encodeStationExpression e) received hfirst hsecond]
  exact station_expression_semantic_roundtrip e

def reflectionExampleCorruption : ProtectedStationCode :=
  ((fun i => if i = 1 then 5 else 1), (fun i => if i = 2 then 0 else 11))

theorem reflection_example_corruption_bound :
    wordDistance (protectStationWire (encodeStationExpression reflectionConjugationExample)).1
      reflectionExampleCorruption.1 ≤ 1 ∧
    wordDistance (protectStationWire (encodeStationExpression reflectionConjugationExample)).2
      reflectionExampleCorruption.2 ≤ 1 := by decide

theorem reflection_example_corruption_recovery :
    decodeStationMeaning (recoverStationWire reflectionExampleCorruption) =
      some (Quotient.mk stationSemanticSetoid reflectionConjugationExample) :=
  protected_station_semantic_recovery _ _ reflection_example_corruption_bound.1
    reflection_example_corruption_bound.2

theorem worked_examples_same_output_at_two :
    stationMeaning reflectionConjugationExample 2 = stationMeaning scaleAfterShiftExample 2 := by decide

/-- A single matching output is insufficient to establish equality of operations. -/
theorem worked_examples_different_meanings :
    stationMeaning reflectionConjugationExample ≠ stationMeaning scaleAfterShiftExample := by
  intro h
  have hc := (station_code_collision_iff reflectionConjugationExample scaleAfterShiftExample).mpr h
  exact (by decide : encodeStationExpression reflectionConjugationExample ≠
    encodeStationExpression scaleAfterShiftExample) hc

/-- An explicit, chosen binary functional induces a grammar operation on observed residues. -/
def sourceShiftExpression {K : Type*} [AddMonoid K] (χ : K →+ ZMod 2) (h : K) : StationExpr :=
  .shift (bridgeTwelve χ h)

theorem source_shift_expression_add {K : Type*} [AddMonoid K]
    (χ : K →+ ZMod 2) (h g : K) :
    stationMeaning (sourceShiftExpression χ (h + g)) =
      stationMeaning (.compose (sourceShiftExpression χ h) (sourceShiftExpression χ g)) := by
  apply (station_meaning_iff_compiled _ _).mpr
  simp [sourceShiftExpression, compileStation, affineStationCompose, map_add, add_comm]

theorem source_shift_observable_equivariance {M K W : Type*} [AddMonoid K]
    (χ : K →+ ZMod 2) (label : M × W → ZMod 12) (h : K) (q : ExactKey M K W) :
    stationMeaning (sourceShiftExpression χ h) (residueAnswerTwelve χ label q) =
      residueAnswerTwelve χ label (translateKey h q) := by
  change affineStationApply (1, bridgeTwelve χ h) (residueAnswerTwelve χ label q) = _
  simp only [affineStationApply, Units.val_one, one_mul]
  exact (residue_folding_twelve χ label h q).symm

end IndependentDuodenary
