# Verification evidence

- Lean: 4.14.0, compiler commit `410fab728470` (Linux release).
- mathlib: v4.14.0, Git commit `4bbdccd9c5f862bf90ff12f0a9e2c8be032b9a84`.
- Project library: four modules; 27 theorem declarations.
- `lake build`: passed, exit status 0; see `local-build.txt`.
- `python3 scripts/audit.py`: passed, exit status 0; see
  `axioms-and-proofs.txt` and the per-theorem index `THEOREMS.md`.
- Axiom union: `propext`, `Classical.choice`, `Quot.sound`; no custom axioms,
  placeholders, or native evaluation. `conditional_closure` and
  `number_372_multiple` have no axioms.
- The reusable cloud setup script was executed successfully, including a
  repeat build and audit. No application services or credentials are needed.
- `lake update` succeeded with the supported
  `MATHLIB_NO_CACHE_ON_UPDATE=1` setting. The independent `lake exe cache get`
  attempt failed because the environment proxy returned HTTP 403 for the cache.
  Dependencies were successfully compiled from locked sources instead.

## Remote verification

The committed workflow runs the library build, theorem/axiom audit, and lockfile
stability check on pushes and pull requests. Remote results must be checked
against the exact pushed commit at
<https://github.com/johnstobey/Alien-math-decoded-2/actions>.
A workflow file or a successful local build alone is not CI certification.

## Open mathematical obligations

No external source structure or paper-to-model correspondence has been supplied.
Such a claim requires separately specified source operations, an explicit map,
and operation-preservation proofs. `conditional_closure` assumes preservation,
source closure, and the specified image characterization. `conditional_level_return`
assumes exactly 12 levels and step 3. Neither theorem establishes those hypotheses
for an external construction. There are no incomplete proof obligations within
the 27 stated Lean theorems.
