import IndependentDuodenary

open IndependentDuodenary

-- The worked operation is reflect, shift by one, then reflect.
#eval ("reflection-code", encodeStationExpression reflectionConjugationExample)
#eval ("reflection-input-output", ([0, 1, 2, 6, 11] : List (ZMod 12)).map
  (fun x => (x, stationMeaning reflectionConjugationExample x)))
#eval ("scale-after-shift-code", encodeStationExpression scaleAfterShiftExample)
#eval ("received-triples", ([reflectionExampleCorruption.1 0,
  reflectionExampleCorruption.1 1, reflectionExampleCorruption.1 2],
  [reflectionExampleCorruption.2 0, reflectionExampleCorruption.2 1,
    reflectionExampleCorruption.2 2]))
#eval ("recovered-code", recoverStationWire reflectionExampleCorruption)
#eval ("decoded-action-at-2", (decodeStationExpression
  (recoverStationWire reflectionExampleCorruption)).map (fun e => stationMeaning e 2))
#eval ("nonunit-code", match decodeStationExpression (2, 0) with
  | none => "rejected"
  | some _ => "accepted")

#guard encodeStationExpression reflectionConjugationExample = (1, 11)
#guard encodeStationExpression scaleAfterShiftExample = (5, 3)
#guard recoverStationWire reflectionExampleCorruption = (1, 11)
#guard ((decodeStationExpression (recoverStationWire reflectionExampleCorruption)).map
  (fun e => stationMeaning e 2)) = some 1
#guard parseStationParameter (2, 0) = none
