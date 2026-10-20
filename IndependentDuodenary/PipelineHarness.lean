import IndependentDuodenary.PipelineSynthesis

/-! Executable boundary fixtures; the universal guarantees are proved in PipelineSynthesis. -/
namespace IndependentDuodenary

def pipelineFixture : CanonicalSubstrate 2 := canonicalPack (phaseRegisterState ![2, 9])
def pipelineFixtureH : RegisterTranslation 2 := ![![1, 0], ![0, 1]]
def pipelineFixtureProgram : List StationExpr :=
  [.shift 3, .reflect, .scale multiplyFiveParameter.1, .invert (.shift 7)]
def pipelineFixtureBase := canonicalEncodingNatural.app 2 pipelineFixture
def pipelineFixtureSent := pipelineTransmit pipelineFixtureH 1 pipelineFixtureProgram pipelineFixture
def pipelineFixtureReceived := successorCorruption pipelineFixtureSent

def doubleHeaderCorruption {r : ℕ} (words : RegisterWords r) : ProtectedRegisterWords r := fun i =>
  match words i with
  | [] => []
  | a :: tail => ![a + 1, a + 1, a] :: tail.map (repetitionWord 3)

def pipelineEmptyFixture : CanonicalSubstrate 0 := canonicalPack Fin.elim0

def pipelineIrregularFixture : CanonicalSubstrate 1 := canonicalPack (fun _ => ⟨1, ![1, 1], 0⟩)

def pipelineBoundaryChecks : List (String × Bool) :=
  [ ("empty station program", decide (runStationProgram [] pipelineFixtureBase = pipelineFixtureBase)),
    ("sequential/compiled station order", decide (runStationProgram pipelineFixtureProgram pipelineFixtureBase =
      stationWordAction (compileStationProgram pipelineFixtureProgram) pipelineFixtureBase)),
    ("inverse station program", decide (undoStationWordAction (compileStationProgram pipelineFixtureProgram)
      (runStationProgram pipelineFixtureProgram pipelineFixtureBase) = pipelineFixtureBase)),
    ("noiseless original-state recovery", decide (recoverCanonicalInitial pipelineFixtureH 1
      (compileStationProgram pipelineFixtureProgram) (protectRegisterWords pipelineFixtureSent) = some pipelineFixture)),
    ("one substitution in every triple", decide (recoverCanonicalInitial pipelineFixtureH 1
      (compileStationProgram pipelineFixtureProgram) pipelineFixtureReceived = some pipelineFixture)),
    ("complete key fields recovered", decide ((recoverCanonicalInitial pipelineFixtureH 1
      (compileStationProgram pipelineFixtureProgram) pipelineFixtureReceived).map CanonicalSubstrate.state =
        some pipelineFixture.state)),
    ("transformed phase vector", decide ((recoverCanonicalOperational
      (compileStationProgram pipelineFixtureProgram) pipelineFixtureReceived).map
        (fun x => registerPhases x.state) = some ![3, 10])),
    ("seventeen protected blocks", decide ((pipelineFixtureReceived 0).length = 17)),
    ("empty transmission rejected", decide (recoverCanonicalInitial pipelineFixtureH 1
      (compileStationProgram pipelineFixtureProgram) (fun _ => []) = none)),
    ("two header errors rejected", decide (recoverCanonicalInitial pipelineFixtureH 1
      (compileStationProgram pipelineFixtureProgram) (doubleHeaderCorruption pipelineFixtureSent) = none)),
    ("zero-register boundary", decide (recoverCanonicalInitial (r := 0) Fin.elim0 0
      (compileStationProgram pipelineFixtureProgram)
      (successorCorruption (pipelineTransmit Fin.elim0 0 pipelineFixtureProgram pipelineEmptyFixture)) =
        some pipelineEmptyFixture)),
    ("irregular-state exact recovery", decide (recoverCanonicalInitial (r := 1) 0 1
      (compileStationProgram pipelineFixtureProgram)
      (successorCorruption (pipelineTransmit 0 1 pipelineFixtureProgram pipelineIrregularFixture)) =
        some pipelineIrregularFixture)),
    ("truncated framing rejected", decide (decodeExactKey [11, 0, 10] = none)) ]

end IndependentDuodenary
