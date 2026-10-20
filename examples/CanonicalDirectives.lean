import IndependentDuodenary

open IndependentDuodenary

-- M: finite-index naturality, exact representations, and an explicit obstruction.
example {r s : ℕ} (select : Fin s → Fin r) (x : CanonicalSubstrate r) :
    (pointwiseFamily (ZMod 12)).restrict select (canonicalPhaseNatural.app r x) =
      canonicalPhaseNatural.app s (canonicalFamily.restrict select x) :=
  canonicalPhaseNatural.naturality select x

example {r : ℕ} (x : CanonicalSubstrate r) :
    canonicalDecode r (canonicalEncodingNatural.app r x) = some x :=
  canonical_decode_encode x

example : ¬ Function.Injective (canonicalPhaseNatural.app 1) :=
  canonical_phase_projection_not_injective

-- N: master induction, exact final-state recovery and exact initial-state recovery.
example {r : ℕ} (h : RegisterTranslation r) (q : RegisterState r)
    (hq : PhaseRegular q) (n : ℕ) :
    CanonicalInvariant q n (((registerStep h)^[n]) q) :=
  canonical_master_induction h q hq n

example {r : ℕ} (h : RegisterTranslation r) (n : ℕ) (e : StationExpr)
    (x : CanonicalSubstrate r) (received : ProtectedRegisterWords r)
    (hnoise : RegisterNoiseBound
      (stationWordAction e (((transportRegisterWords (registerStep h))^[n])
        (canonicalEncodingNatural.app r x))) received) :
    recoverCanonicalInitial h n e received = some x :=
  canonical_initial_recovery h n e x received hnoise

def canonicalFixture : CanonicalSubstrate 2 := canonicalPack (phaseRegisterState ![2, 9])
def canonicalFixtureTranslation : RegisterTranslation 2 := ![![1, 0], ![0, 1]]
def canonicalFixtureStation : StationExpr := .compose .reflect (.shift 3)
def canonicalFixtureFinal : RegisterState 2 := registerStep canonicalFixtureTranslation canonicalFixture.state

def canonicalFixtureSent : RegisterWords 2 := stationWordAction canonicalFixtureStation
  (transportRegisterWords (registerStep canonicalFixtureTranslation)
    (canonicalEncodingNatural.app 2 canonicalFixture))

def canonicalFixtureReceived := successorCorruption canonicalFixtureSent

def canonicalFixtureBad : ProtectedRegisterWords 2 := fun i =>
  if i = 0 then ![0, 0, 10] :: (protectRegisterWords canonicalFixtureSent i).tail
  else protectRegisterWords canonicalFixtureSent i

#guard canonicalDecode 2 (canonicalEncodingNatural.app 2 canonicalFixture) = some canonicalFixture
#guard canonicalFromCoefficients (canonicalCoefficientNatural.app 2 canonicalFixture) = canonicalFixture
#guard (canonicalCycleNatural.app 2
  (canonicalTranslationNatural.app 2 (canonicalFixtureTranslation, canonicalFixture))).state =
  (canonicalTranslationNatural.app 2
    (canonicalFixtureTranslation, canonicalCycleNatural.app 2 canonicalFixture)).state
#guard (canonicalFixtureSent 0).length = 17
#guard (canonicalFixtureReceived 0).length = 17
#guard (canonicalFixtureReceived 0).head? = some ![11, 10, 10]
#guard (recoverRegisterWords canonicalFixtureReceived 0).head? = some 10
#guard (undoStationWordAction canonicalFixtureStation
  (recoverRegisterWords canonicalFixtureReceived) 0).head? = some 11
#guard recoverCanonicalOperational canonicalFixtureStation canonicalFixtureReceived =
  some (canonicalPack canonicalFixtureFinal)
#guard (recoverCanonicalOperational canonicalFixtureStation canonicalFixtureReceived).map
  (fun x => registerPhases x.state) = some ![3, 10]
#guard (recoverCanonicalOperational canonicalFixtureStation canonicalFixtureReceived).map
  (fun x => (x.state 0).binaryIntercept 0) = some 1
#guard recoverCanonicalInitial canonicalFixtureTranslation 1 canonicalFixtureStation
  canonicalFixtureReceived = some canonicalFixture
#guard recoverCanonicalOperational canonicalFixtureStation
  (protectRegisterWords canonicalFixtureSent) = some (canonicalPack canonicalFixtureFinal)
#guard wordDistance (repetitionWord 3 (10 : ZMod 12)) ![0, 0, 10] = 2
#guard recoverCanonicalOperational canonicalFixtureStation canonicalFixtureBad = none
