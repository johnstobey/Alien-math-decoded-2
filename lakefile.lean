import Lake
open Lake DSL

package independent_duodenary where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "4bbdccd9c5f862bf90ff12f0a9e2c8be032b9a84"

-- DCC-01 Stage 4: consume the canonical certified interface. The package
-- lives in the `closed_ring_z12_mathlib` subdirectory of the Atlas repo;
-- its own path deps (`..`, `../closed_ring_z12`) resolve inside the same
-- checkout. Pinned to the Atlas main commit carrying CP-00/01/02.
require closed_ring_z12_mathlib from git
  "https://github.com/johnstobey/The-Duodenary-Mathematical-Proof-Atlas-"
  @ "2d84d17ebf849525b8ae0155cc646b6ed7a58f2e" /
  "closed_ring_z12_mathlib"

@[default_target]
lean_lib IndependentDuodenary

@[default_target]
lean_exe verifyPipeline where
  root := `PipelineMain

@[default_target]
lean_lib extended_modules

@[default_target]
lean_lib AtlasConsumption
