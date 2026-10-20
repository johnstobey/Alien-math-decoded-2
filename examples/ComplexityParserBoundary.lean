import IndependentDuodenary.ComplexityEncoding

open IndependentDuodenary

example : prizeDecodeWord [] = some [] := rfl
example : prizeDecodePair [3] = some ([], []) := by decide
example : prizeDecodePair [1, 2, 3, 2, 1] = some ([false, true], [true, false]) := by decide
example : prizeDecodePair [1, 2] = none := by decide
example : prizeDecodePair [3, 3] = none := by decide
example : prizeDecodePair [1, 3, 0] = none := by decide
example : prizeDecodePair [0, 3, 1] = none := by decide
-- Additional bit symbols form a longer certificate; they are consumed.
example : prizeDecodePair [1, 3, 2, 1] = some ([false], [true, false]) := by decide
example {states : ℕ} (M : PrizeMachine states) (input : List (Fin 4))
    (h : prizeHalted M input 0) : prizeRun M input 100 = prizeRun M input 0 := by
  exact prize_halted_run_stable M input 0 h 100
