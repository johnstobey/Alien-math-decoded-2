import Lean

/-- Run the checked Lean pipeline harness and propagate its exact exit status. -/
def main : IO UInt32 := do
  let result ← IO.Process.output {
    cmd := "lake"
    args := #["env", "lean", "--run", "examples/PipelineRunner.lean"] }
  IO.print result.stdout
  IO.eprint result.stderr
  return result.exitCode
