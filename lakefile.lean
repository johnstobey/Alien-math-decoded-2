import Lake
open Lake DSL

package independent_duodenary where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "4bbdccd9c5f862bf90ff12f0a9e2c8be032b9a84"

@[default_target]
lean_lib IndependentDuodenary

@[default_target]
lean_exe verifyPipeline where
  root := `PipelineMain
