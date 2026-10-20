import IndependentDuodenary.RegisterBridge
import IndependentDuodenary.SourceProjection

/-! Canonical finite algebraic substrate and a bounded-error operational envelope.
No biological or historical interpretation is part of these definitions.
Naturality does not imply injectivity: lossy observations retain their input. -/
namespace IndependentDuodenary

structure CanonicalSubstrate (r : ℕ) where
  state : RegisterState r
  deriving DecidableEq

def canonicalPack {r : ℕ} (q : RegisterState r) : CanonicalSubstrate r := ⟨q⟩

def canonicalFamily : RegisterFamily where
  Carrier := CanonicalSubstrate
  restrict select x := canonicalPack (projectRegisters select x.state)
  restrict_identity x := by cases x; rfl
  restrict_composition _ _ _ := rfl

def canonicalStateEquiv (r : ℕ) : CanonicalSubstrate r ≃ RegisterState r where
  toFun := CanonicalSubstrate.state
  invFun := canonicalPack
  left_inv x := by cases x; rfl
  right_inv _ := rfl

def canonicalCycleNatural : RegisterNaturalMap canonicalFamily canonicalFamily where
  app _ x := canonicalPack (registerCycle x.state)
  naturality _ _ := rfl

def canonicalTranslationNatural :
    RegisterNaturalMap (productRegisterFamily (pointwiseFamily KeyBinary) canonicalFamily) canonicalFamily where
  app _ x := canonicalPack (registerTranslate x.1 x.2.state)
  naturality _ _ := rfl

def canonicalStepNatural :
    RegisterNaturalMap (productRegisterFamily (pointwiseFamily KeyBinary) canonicalFamily) canonicalFamily where
  app _ x := canonicalPack (registerStep x.1 x.2.state)
  naturality _ _ := rfl

def canonicalPhaseNatural : RegisterNaturalMap canonicalFamily (pointwiseFamily (ZMod 12)) where
  app _ x := registerPhases x.state
  naturality _ _ := rfl

abbrev CanonicalCoefficients := KeyMetadata × KeyBinary × KeyComplement

def canonicalCoefficientNatural :
    RegisterNaturalMap canonicalFamily (pointwiseFamily CanonicalCoefficients) where
  app _ x := fun i => ((x.state i).metadata, (x.state i).binaryIntercept, (x.state i).complementIntercept)
  naturality _ _ := rfl

def canonicalFromCoefficients {r : ℕ} (c : Fin r → CanonicalCoefficients) : CanonicalSubstrate r :=
  canonicalPack (fun i => ⟨(c i).1, (c i).2.1, (c i).2.2⟩)

theorem canonical_coefficient_roundtrip {r : ℕ} (x : CanonicalSubstrate r) :
    canonicalFromCoefficients (canonicalCoefficientNatural.app r x) = x := by
  cases x
  rfl

theorem canonical_coefficient_encoding_injective (r : ℕ) :
    Function.Injective (canonicalCoefficientNatural.app r) := by
  intro x y h
  have hc := congrArg canonicalFromCoefficients h
  simpa only [canonical_coefficient_roundtrip] using hc

def canonicalEncodingNatural :
    RegisterNaturalMap canonicalFamily (pointwiseFamily (List (ZMod 12))) where
  app _ x := encodeRegisterState x.state
  naturality _ _ := rfl

def canonicalDecode (r : ℕ) (words : RegisterWords r) : Option (CanonicalSubstrate r) :=
  (decodeRegisterWords r words).map canonicalPack

theorem canonical_decode_encode {r : ℕ} (x : CanonicalSubstrate r) :
    canonicalDecode r (canonicalEncodingNatural.app r x) = some x := by
  cases x
  simp [canonicalDecode, canonicalEncodingNatural, register_decode_encode, canonicalPack]

theorem canonical_encoding_injective (r : ℕ) :
    Function.Injective (canonicalEncodingNatural.app r) := by
  intro x y h
  have hc := congrArg (canonicalDecode r) h
  simpa only [canonical_decode_encode, Option.some.injEq] using hc

theorem canonical_cycle_translation_commute {r : ℕ} (h : RegisterTranslation r)
    (x : CanonicalSubstrate r) :
    canonicalCycleNatural.app r (canonicalTranslationNatural.app r (h, x)) =
      canonicalTranslationNatural.app r (h, canonicalCycleNatural.app r x) := by
  exact congrArg canonicalPack (register_cycle_commutes_translation h x.state)

theorem canonical_cycle_injective (r : ℕ) :
    Function.Injective (canonicalCycleNatural.app r) := by
  have hcycle : ∀ q : RegisterState r, (registerCycle^[12]) q = q := by
    intro q
    funext i
    rw [register_cycle_iterate]
    exact key_cycle_period_twelve (q i)
  have hinj := successor_period_injective (@registerCycle r) 11 hcycle
  intro x y heq
  have hs := congrArg CanonicalSubstrate.state heq
  exact (canonicalStateEquiv r).injective (hinj hs)

theorem canonical_translation_injective {r : ℕ} (h : RegisterTranslation r) :
    Function.Injective (fun x : CanonicalSubstrate r => canonicalTranslationNatural.app r (h, x)) := by
  have ht : ∀ q : RegisterState r, registerTranslate h (registerTranslate h q) = q := by
    intro q
    funext i
    exact (translateKey_add (h i) (h i) (q i)).trans
      (by rw [binary_vector_double_zero, translateKey_zero])
  have hinj : Function.Injective (registerTranslate h) := (show Function.LeftInverse
    (registerTranslate h) (registerTranslate h) from ht).injective
  intro x y heq
  have hs := congrArg CanonicalSubstrate.state heq
  exact (canonicalStateEquiv r).injective (hinj hs)

theorem canonical_step_injective {r : ℕ} (h : RegisterTranslation r) :
    Function.Injective (fun x : CanonicalSubstrate r => canonicalStepNatural.app r (h, x)) := by
  have hinj := successor_period_injective (registerStep h) 11 (register_step_period_twelve h)
  intro x y heq
  have hs := congrArg CanonicalSubstrate.state heq
  exact (canonicalStateEquiv r).injective (hinj hs)

theorem canonical_phase_translation_invariant {r : ℕ} (h : RegisterTranslation r)
    (x : CanonicalSubstrate r) :
    canonicalPhaseNatural.app r (canonicalTranslationNatural.app r (h, x)) =
      canonicalPhaseNatural.app r x := rfl

theorem canonical_phase_projection_not_injective :
    ¬ Function.Injective (canonicalPhaseNatural.app 1) := by
  intro hinj
  let q : CanonicalSubstrate 1 := canonicalPack (fun _ => keyCycleWitness)
  let h : RegisterTranslation 1 := fun _ => ![1, 0]
  have heq : canonicalPhaseNatural.app 1 q =
      canonicalPhaseNatural.app 1 (canonicalTranslationNatural.app 1 (h, q)) := rfl
  have hs := congrArg CanonicalSubstrate.state (hinj heq)
  have hb := congrArg (fun p : RegisterState 1 => (p 0).binaryIntercept 0) hs
  change (0 : ZMod 2) = 1 at hb
  exact (by decide : (0 : ZMod 2) ≠ 1) hb

theorem canonical_retained_phase_injective (r : ℕ) :
    Function.Injective ((retainRegisterNatural canonicalPhaseNatural).app r) :=
  retained_register_natural_injective canonicalPhaseNatural r

/-- Source coefficient pullback is natural under register reindexing. -/
def coefficientPullbackNatural {k : ℕ} {E X V : Type} [AddCommMonoid V] :
    RegisterNaturalMap (pointwiseFamily (ProjectedTable k E X V))
      (pointwiseFamily (FullTable k E X V)) := pointwiseNaturalMap pullbackTable

theorem retained_coefficient_pullback_injective {k : ℕ} {E X V : Type}
    [AddCommMonoid V] (r : ℕ) :
    Function.Injective ((retainRegisterNatural
      (coefficientPullbackNatural (k := k) (E := E) (X := X) (V := V))).app r) :=
  retained_register_natural_injective _ r

theorem canonical_coefficient_semantics {k r : ℕ} {E X V : Type}
    [AddCommMonoid V] [Module (ZMod 2) V]
    (t : Fin r → ProjectedTable k E X V)
    (p : Fin r → ZMod 2 × (Fin k → ZMod 2 × ZMod 2)) :
    (fun i => evaluateFullTable (pullbackTable (t i)) (p i)) =
      fun i => evaluateProjectedTable (t i) (permittedProjection (t i) (p i)) := by
  funext i
  exact source_table_pullback_evaluation (t i) (p i)

/-- Minimal nonredundant fields; relative-phase preservation is derived below. -/
structure CanonicalInvariant {r : ℕ} (initial : RegisterState r) (n : ℕ) (final : RegisterState r) : Prop where
  regular : PhaseRegular final
  metadata : ∀ i, (final i).metadata = (initial i).metadata
  phases : registerPhases final = fun i => registerPhases initial i + (n : ZMod 12)

theorem canonical_master_induction {r : ℕ} (h : RegisterTranslation r)
    (initial : RegisterState r) (hregular : PhaseRegular initial) (n : ℕ) :
    CanonicalInvariant initial n (((registerStep h)^[n]) initial) := by
  induction n with
  | zero =>
    refine ⟨hregular, fun _ => rfl, ?_⟩
    simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨register_regular_step h _ ih.regular, ?_, ?_⟩
    · intro i
      exact ih.metadata i
    · rw [register_step_phase h _ ih.regular, ih.phases]
      funext i
      simp [phaseAdvance, add_assoc]

theorem canonical_invariant_relative {r n : ℕ} {initial final : RegisterState r}
    (h : CanonicalInvariant initial n final) :
    ExternalRelativeEquivalent (registerPhases initial) (registerPhases final) := by
  intro i j
  rw [h.phases]
  simp [relativePhases]

theorem canonical_master_period {r : ℕ} (h : RegisterTranslation r)
    (initial : RegisterState r) : ((registerStep h)^[12]) initial = initial :=
  register_step_period_twelve h initial

/-- Aligned substitution channel: at most one changed symbol in each triple. -/
def AlignedTripleNoise (word : List (ZMod 12)) (received : List (Fin 3 → ZMod 12)) : Prop :=
  List.Forall₂ (fun a triple => wordDistance (repetitionWord 3 a) triple ≤ 1) word received

abbrev ProtectedRegisterWords (r : ℕ) := Fin r → List (Fin 3 → ZMod 12)

def protectRegisterWords {r : ℕ} (words : RegisterWords r) : ProtectedRegisterWords r :=
  fun i => (words i).map (repetitionWord 3)

def recoverRegisterWords {r : ℕ} (received : ProtectedRegisterWords r) : RegisterWords r :=
  fun i => (received i).map tripleMajority

def RegisterNoiseBound {r : ℕ} (words : RegisterWords r) (received : ProtectedRegisterWords r) : Prop :=
  ∀ i, AlignedTripleNoise (words i) (received i)

theorem aligned_triple_noise_recovery (word : List (ZMod 12))
    (received : List (Fin 3 → ZMod 12)) (h : AlignedTripleNoise word received) :
    received.map tripleMajority = word := by
  induction h with
  | nil => rfl
  | @cons a triple word received hhead _ ih =>
    change tripleMajority triple :: received.map tripleMajority = a :: word
    rw [repetition_majority_recovery a triple hhead, ih]

theorem aligned_triple_noise_length (word : List (ZMod 12))
    (received : List (Fin 3 → ZMod 12)) (h : AlignedTripleNoise word received) :
    word.length = received.length := h.length_eq

theorem protected_register_words_recovery {r : ℕ} (words : RegisterWords r)
    (received : ProtectedRegisterWords r) (h : RegisterNoiseBound words received) :
    recoverRegisterWords received = words := by
  funext i
  exact aligned_triple_noise_recovery (words i) (received i) (h i)

theorem aligned_triple_noise_protect (word : List (ZMod 12)) :
    AlignedTripleNoise word (word.map (repetitionWord 3)) := by
  induction word with
  | nil => exact .nil
  | cons a word ih => exact .cons (by simp [word_distance_self]) ih

theorem protected_register_noise_bound {r : ℕ} (words : RegisterWords r) :
    RegisterNoiseBound words (protectRegisterWords words) :=
  fun i => aligned_triple_noise_protect (words i)

/-- A reversible station grammar operation is applied to every encoded symbol. -/
def stationWordAction (e : StationExpr) {r : ℕ} (words : RegisterWords r) : RegisterWords r :=
  fun i => (words i).map (stationMeaning e)

def undoStationWordAction (e : StationExpr) {r : ℕ} (words : RegisterWords r) : RegisterWords r :=
  fun i => (words i).map (stationMeaning e).symm

def stationWordNatural (e : StationExpr) :
    RegisterNaturalMap (pointwiseFamily (List (ZMod 12))) (pointwiseFamily (List (ZMod 12))) :=
  pointwiseNaturalMap (fun word => word.map (stationMeaning e))

theorem station_word_action_inverse (e : StationExpr) {r : ℕ} (words : RegisterWords r) :
    undoStationWordAction e (stationWordAction e words) = words := by
  funext i
  simp [undoStationWordAction, stationWordAction, List.map_map, Function.comp_def]

theorem canonical_transmitted_word_length {r : ℕ} (A : RegisterState r → RegisterState r)
    (n : ℕ) (e : StationExpr) (x : CanonicalSubstrate r) (i : Fin r) :
    (stationWordAction e (((transportRegisterWords A)^[n])
      (canonicalEncodingNatural.app r x)) i).length = 17 := by
  change (stationWordAction e (((transportRegisterWords A)^[n]) (encodeRegisterState x.state)) i).length = 17
  rw [register_transport_iterate]
  simp [stationWordAction, encodeRegisterState, exact_key_encode_length]

theorem canonical_received_word_length {r : ℕ} (A : RegisterState r → RegisterState r)
    (n : ℕ) (e : StationExpr) (x : CanonicalSubstrate r) (received : ProtectedRegisterWords r)
    (hnoise : RegisterNoiseBound
      (stationWordAction e (((transportRegisterWords A)^[n]) (canonicalEncodingNatural.app r x))) received)
    (i : Fin r) : (received i).length = 17 := by
  rw [← aligned_triple_noise_length _ _ (hnoise i)]
  exact canonical_transmitted_word_length A n e x i

theorem canonical_station_encoding_injective (r : ℕ) (e : StationExpr) :
    Function.Injective (fun x : CanonicalSubstrate r =>
      stationWordAction e (canonicalEncodingNatural.app r x)) := by
  intro x y heq
  have hu := congrArg (undoStationWordAction e) heq
  rw [station_word_action_inverse, station_word_action_inverse] at hu
  exact canonical_encoding_injective r hu

/-- A concrete channel changes the first position of every symbol triple. -/
def successorCorruption {r : ℕ} (words : RegisterWords r) : ProtectedRegisterWords r :=
  fun i => (words i).map (fun a => ![a + 1, a, a])

theorem successor_triple_noise : ∀ a : ZMod 12,
    wordDistance (repetitionWord 3 a) ![a + 1, a, a] ≤ 1 := by decide

theorem successor_word_noise (word : List (ZMod 12)) :
    AlignedTripleNoise word (word.map (fun a => ![a + 1, a, a])) := by
  induction word with
  | nil => exact .nil
  | cons a word ih => exact .cons (successor_triple_noise a) ih

theorem successor_register_noise {r : ℕ} (words : RegisterWords r) :
    RegisterNoiseBound words (successorCorruption words) :=
  fun i => successor_word_noise (words i)

def recoverCanonicalOperational (e : StationExpr) {r : ℕ} (received : ProtectedRegisterWords r) :
    Option (CanonicalSubstrate r) :=
  canonicalDecode r (undoStationWordAction e (recoverRegisterWords received))

/-- Closed path: exact base encoding, structural execution, station action,
triple substitution noise, majority recovery, inverse station action, exact decode. -/
theorem canonical_operational_recovery {r : ℕ} (A : RegisterState r → RegisterState r)
    (n : ℕ) (e : StationExpr) (x : CanonicalSubstrate r) (received : ProtectedRegisterWords r)
    (hnoise : RegisterNoiseBound
      (stationWordAction e (((transportRegisterWords A)^[n]) (canonicalEncodingNatural.app r x))) received) :
    recoverCanonicalOperational e received = some (canonicalPack ((A^[n]) x.state)) := by
  unfold recoverCanonicalOperational
  rw [protected_register_words_recovery _ received hnoise, station_word_action_inverse]
  change (decodeRegisterWords r (((transportRegisterWords A)^[n])
    (encodeRegisterState x.state))).map canonicalPack = _
  rw [register_decoded_transport_iterate]
  rfl

theorem canonical_operational_envelope {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (e : StationExpr) (x : CanonicalSubstrate r) (hregular : PhaseRegular x.state)
    (received : ProtectedRegisterWords r)
    (hnoise : RegisterNoiseBound
      (stationWordAction e (((transportRegisterWords (registerStep h))^[n])
        (canonicalEncodingNatural.app r x))) received) :
    recoverCanonicalOperational e received = some (canonicalPack (((registerStep h)^[n]) x.state)) ∧
    CanonicalInvariant x.state n (((registerStep h)^[n]) x.state) ∧
    ExternalRelativeEquivalent (registerPhases x.state)
      (registerPhases (((registerStep h)^[n]) x.state)) := by
  have hinvariant := canonical_master_induction h x.state hregular n
  exact ⟨canonical_operational_recovery (registerStep h) n e x received hnoise,
    hinvariant, canonical_invariant_relative hinvariant⟩

/-- Concrete nonzero-error channel: no noise premise remains to be assumed. -/
theorem canonical_successor_channel_recovery {r : ℕ} (A : RegisterState r → RegisterState r)
    (n : ℕ) (e : StationExpr) (x : CanonicalSubstrate r) :
    recoverCanonicalOperational e (successorCorruption (stationWordAction e
      (((transportRegisterWords A)^[n]) (canonicalEncodingNatural.app r x)))) =
      some (canonicalPack ((A^[n]) x.state)) :=
  canonical_operational_recovery A n e x _ (successor_register_noise _)

def undoCanonicalDynamics {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (x : CanonicalSubstrate r) : CanonicalSubstrate r :=
  canonicalPack ((((registerStep h)^[11])^[n]) x.state)

theorem canonical_undo_run {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (x : CanonicalSubstrate r) :
    undoCanonicalDynamics h n (canonicalPack (((registerStep h)^[n]) x.state)) = x := by
  apply (canonicalStateEquiv r).injective
  exact ((successor_period_left_inverse (registerStep h) 11
    (register_step_period_twelve h)).iterate n) x.state

def recoverCanonicalInitial {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (e : StationExpr) (received : ProtectedRegisterWords r) : Option (CanonicalSubstrate r) :=
  (recoverCanonicalOperational e received).map (undoCanonicalDynamics h n)

theorem canonical_initial_recovery {r : ℕ} (h : RegisterTranslation r) (n : ℕ)
    (e : StationExpr) (x : CanonicalSubstrate r) (received : ProtectedRegisterWords r)
    (hnoise : RegisterNoiseBound
      (stationWordAction e (((transportRegisterWords (registerStep h))^[n])
        (canonicalEncodingNatural.app r x))) received) :
    recoverCanonicalInitial h n e received = some x := by
  change (recoverCanonicalOperational e received).map (undoCanonicalDynamics h n) = some x
  have hr := canonical_operational_recovery (registerStep h) n e x received hnoise
  calc
    _ = some (undoCanonicalDynamics h n (canonicalPack (((registerStep h)^[n]) x.state))) :=
      congrArg (fun y => y.map (undoCanonicalDynamics h n)) hr
    _ = some x := congrArg some (canonical_undo_run h n x)

end IndependentDuodenary
