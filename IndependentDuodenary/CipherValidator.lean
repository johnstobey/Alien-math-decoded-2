import IndependentDuodenary.StationCodec

/-! Exact nonnegative rational semantics for the supplied calculator's arithmetic.
The numerator and denominator describe a positive period; JavaScript floating-point
parsing and rounding are outside these semantics. -/
namespace IndependentDuodenary

structure CipherPeriod where
  numerator : ℕ
  denominator : ℕ
  numerator_pos : 0 < numerator
  denominator_pos : 0 < denominator

/-- The numerator of `(12 P) mod 360`, with the original denominator. -/
def cipherRemainderNumerator (p : CipherPeriod) : ℕ :=
  (12 * p.numerator) % (360 * p.denominator)

/-- Floor after taking the rational remainder. -/
def cipherStage (p : CipherPeriod) : ℕ :=
  cipherRemainderNumerator p / p.denominator

/-- The HTML pipeline, interpreted in exact arithmetic with a natural harmonic. -/
def cipherCalculate (p : CipherPeriod) (harmonic : ℕ) : ℕ :=
  (cipherStage p * harmonic) % 144

/-- An equivalent implementation that floors before reducing modulo 360. -/
def cipherNormalized (p : CipherPeriod) (harmonic : ℕ) : ℕ :=
  (((12 * p.numerator) / p.denominator % 360) * harmonic) % 144

theorem cipher_stage_normal_form (p : CipherPeriod) :
    cipherStage p = (12 * p.numerator / p.denominator) % 360 := by
  exact Nat.mod_mul_left_div_self _ _ _

theorem cipher_pipeline_correct (p : CipherPeriod) (h : ℕ) :
    cipherCalculate p h = cipherNormalized p h := by
  simp [cipherCalculate, cipherNormalized, cipher_stage_normal_form]

theorem cipher_stage_bound (p : CipherPeriod) : cipherStage p < 360 := by
  rw [cipher_stage_normal_form]
  exact Nat.mod_lt _ (by decide)

theorem cipher_output_bound (p : CipherPeriod) (h : ℕ) :
    cipherCalculate p h < 144 := Nat.mod_lt _ (by decide)

theorem cipher_zero_iff_divides (p : CipherPeriod) (h : ℕ) :
    cipherCalculate p h = 0 ↔ 144 ∣ cipherStage p * h := by
  exact Nat.dvd_iff_mod_eq_zero.symm

theorem cipher_same_stage (p q : CipherPeriod) (h : ℕ)
    (heq : cipherStage p = cipherStage q) :
    cipherCalculate p h = cipherCalculate q h := by
  simp [cipherCalculate, heq]

/-- Add exactly thirty years, represented over the same denominator. -/
def cipherShiftThirty (p : CipherPeriod) : CipherPeriod where
  numerator := p.numerator + 30 * p.denominator
  denominator := p.denominator
  numerator_pos := by have := p.numerator_pos; omega
  denominator_pos := p.denominator_pos

theorem cipher_shift_thirty_stage (p : CipherPeriod) :
    cipherStage (cipherShiftThirty p) = cipherStage p := by
  unfold cipherStage cipherRemainderNumerator cipherShiftThirty
  have heq : 12 * (p.numerator + 30 * p.denominator) =
      12 * p.numerator + 360 * p.denominator := by ring
  rw [heq, Nat.add_mod]
  simp

theorem cipher_shift_thirty_output (p : CipherPeriod) (h : ℕ) :
    cipherCalculate (cipherShiftThirty p) h = cipherCalculate p h :=
  cipher_same_stage _ _ _ (cipher_shift_thirty_stage p)

theorem cipher_shift_thirty_distinct (p : CipherPeriod) :
    cipherShiftThirty p ≠ p := by
  intro heq
  have hn := congrArg CipherPeriod.numerator heq
  have hd := p.denominator_pos
  change p.numerator + 30 * p.denominator = p.numerator at hn
  omega

theorem cipher_calculate_not_injective (h : ℕ) :
    ¬ Function.Injective (fun p : CipherPeriod => cipherCalculate p h) := by
  intro hinj
  let p : CipherPeriod := ⟨1, 1, by decide, by decide⟩
  exact cipher_shift_thirty_distinct p (hinj (cipher_shift_thirty_output p h))

/-- Result payloads have all 144 possibilities; they are distinct from operation codes. -/
structure CipherPayload where
  high : ZMod 12
  low : ZMod 12
  deriving DecidableEq

def encodeCipherResult (r : ZMod 144) : CipherPayload :=
  ⟨(r.val / 12 : ℕ), (r.val % 12 : ℕ)⟩

def decodeCipherResult (c : CipherPayload) : ZMod 144 :=
  (12 * c.high.val + c.low.val : ℕ)

set_option maxRecDepth 4096 in
theorem cipher_result_roundtrip : ∀ r : ZMod 144,
    decodeCipherResult (encodeCipherResult r) = r := by decide

set_option maxRecDepth 4096 in
theorem cipher_payload_roundtrip (c : CipherPayload) :
    encodeCipherResult (decodeCipherResult c) = c := by
  rcases c with ⟨high, low⟩
  revert high low
  decide

def cipherPayloadEquiv : ZMod 144 ≃ CipherPayload where
  toFun := encodeCipherResult
  invFun := decodeCipherResult
  left_inv := cipher_result_roundtrip
  right_inv := cipher_payload_roundtrip

theorem cipher_result_encoding_injective : Function.Injective encodeCipherResult :=
  cipherPayloadEquiv.injective

def cipherPayloadWire (c : CipherPayload) : StationWireCode := (c.high, c.low)

def cipherReceivedResult (r : ProtectedStationCode) : ZMod 144 :=
  decodeCipherResult ⟨(recoverStationWire r).1, (recoverStationWire r).2⟩

theorem cipher_protected_result_recovery (result : ZMod 144) (received : ProtectedStationCode)
    (hfirst : wordDistance (protectStationWire (cipherPayloadWire (encodeCipherResult result))).1
      received.1 ≤ 1)
    (hsecond : wordDistance (protectStationWire (cipherPayloadWire (encodeCipherResult result))).2
      received.2 ≤ 1) :
    cipherReceivedResult received = result := by
  unfold cipherReceivedResult
  rw [protected_station_wire_recovery _ received hfirst hsecond]
  exact cipher_result_roundtrip result

theorem cipher_pipeline_protected_recovery (p : CipherPeriod) (h : ℕ)
    (received : ProtectedStationCode)
    (hfirst : wordDistance (protectStationWire (cipherPayloadWire
      (encodeCipherResult (cipherCalculate p h : ZMod 144)))).1 received.1 ≤ 1)
    (hsecond : wordDistance (protectStationWire (cipherPayloadWire
      (encodeCipherResult (cipherCalculate p h : ZMod 144)))).2 received.2 ≤ 1) :
    cipherReceivedResult received = (cipherNormalized p h : ZMod 144) := by
  rw [← cipher_pipeline_correct]
  exact cipher_protected_result_recovery _ received hfirst hsecond

/-- Positive finite decimals, stored as integer hundredths. -/
def cipherHundredths (n : ℕ) (hn : 0 < n) : CipherPeriod := ⟨n, 100, hn, by decide⟩

theorem cipher_eris_fixture : cipherCalculate (cipherHundredths 55800 (by decide)) 12 = 0 := by decide

theorem cipher_haumea_fixture : cipherCalculate (cipherHundredths 28400 (by decide)) 5 = 120 := by decide

theorem cipher_makemake_fixture : cipherCalculate (cipherHundredths 30604 (by decide)) 5 = 72 := by decide

theorem cipher_gonggong_fixture : cipherCalculate (cipherHundredths 55287 (by decide)) 5 = 50 := by decide

theorem cipher_orcus_fixture : cipherCalculate (cipherHundredths 24753 (by decide)) 5 = 18 := by decide

end IndependentDuodenary
