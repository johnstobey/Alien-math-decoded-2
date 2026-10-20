import IndependentDuodenary.PipelineHarness

open IndependentDuodenary

example {r : ℕ} (h : RegisterTranslation r) (n : ℕ) (ops : List StationExpr)
    (x : CanonicalSubstrate r) (received : ProtectedRegisterWords r)
    (hnoise : RegisterNoiseBound (pipelineTransmit h n ops x) received) :
    recoverCanonicalInitial h n (compileStationProgram ops) received = some x := by
  apply canonical_initial_recovery h n (compileStationProgram ops) x received
  simpa only [pipelineTransmit, station_program_compilation] using hnoise

example {r : ℕ} (h : RegisterTranslation r) (n : ℕ) (ops : List StationExpr)
    (x : CanonicalSubstrate r) :
    recoverCanonicalInitial h n (compileStationProgram ops)
      (successorCorruption (pipelineTransmit h n ops x)) = some x :=
  pipeline_master_composition h n ops x _ (successor_register_noise _)

#guard pipelineBoundaryChecks.all Prod.snd
