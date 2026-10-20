import IndependentDuodenary.PipelineHarness

open IndependentDuodenary

def main : IO UInt32 := do
  for (name, passed) in pipelineBoundaryChecks do
    if passed then
      IO.println s!"PASS {name}"
    else
      throw (IO.userError s!"FAIL {name}")
  IO.println s!"PIPELINE PASS: {pipelineBoundaryChecks.length} checks"
  return 0
