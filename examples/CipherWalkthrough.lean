import IndependentDuodenary

open IndependentDuodenary

def erisPeriod := cipherHundredths 55800 (by decide)
def haumeaPeriod := cipherHundredths 28400 (by decide)
def receivedHaumea : ProtectedStationCode := (![10, 3, 10], ![0, 0, 7])

#eval ("period-harmonic-result", [(55800, 12), (28400, 5), (30604, 5),
  (55287, 5), (24753, 5)].map (fun (n, h) =>
    (n, h, ((12 * n % (360 * 100)) / 100 * h) % 144)))
#eval ("haumea-payload", cipherPayloadWire (encodeCipherResult (cipherCalculate haumeaPeriod 5)))
#eval ("recovered-result", cipherReceivedResult receivedHaumea)
#eval ("thirty-year-shift", cipherCalculate (cipherShiftThirty erisPeriod) 12)

#guard cipherCalculate erisPeriod 12 = 0
#guard cipherCalculate haumeaPeriod 5 = 120
#guard cipherCalculate (cipherHundredths 30604 (by decide)) 5 = 72
#guard cipherCalculate (cipherHundredths 55287 (by decide)) 5 = 50
#guard cipherCalculate (cipherHundredths 24753 (by decide)) 5 = 18
#guard wordDistance (protectStationWire (10, 0)).1 receivedHaumea.1 = 1
#guard wordDistance (protectStationWire (10, 0)).2 receivedHaumea.2 = 1
#guard cipherReceivedResult receivedHaumea = 120
#guard cipherCalculate (cipherShiftThirty erisPeriod) 12 = 0
