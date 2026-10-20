import IndependentDuodenary.MillenniumBridge

/-! Total input parsers and persistence of the actual machine's halted configuration. -/
namespace IndependentDuodenary

def prizeDecodeWord : List (Fin 4) → Option PrizeBinaryWord
  | [] => some []
  | a :: rest =>
    if a = 1 then (List.cons false) <$> prizeDecodeWord rest
    else if a = 2 then (List.cons true) <$> prizeDecodeWord rest
    else none

def prizeDecodePair : List (Fin 4) → Option (PrizeBinaryWord × PrizeBinaryWord)
  | [] => none
  | a :: rest =>
    if a = 3 then (fun w => ([], w)) <$> prizeDecodeWord rest
    else if a = 1 then (fun p => (false :: p.1, p.2)) <$> prizeDecodePair rest
    else if a = 2 then (fun p => (true :: p.1, p.2)) <$> prizeDecodePair rest
    else none

theorem prize_word_decode_encode (x : PrizeBinaryWord) :
    prizeDecodeWord (prizeEncodeWord x) = some x := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    simp only [prizeEncodeWord] at ih
    cases b <;> simp [prizeEncodeWord, prizeDecodeWord, ih]

theorem prize_word_encode_decode (raw : List (Fin 4)) (x : PrizeBinaryWord)
    (h : prizeDecodeWord raw = some x) : prizeEncodeWord x = raw := by
  induction raw generalizing x with
  | nil => simp [prizeDecodeWord] at h; subst x; rfl
  | cons a raw ih =>
    fin_cases a
    · simp [prizeDecodeWord] at h
    · cases hd : prizeDecodeWord raw with
      | none => simp [prizeDecodeWord, hd] at h
      | some xs =>
        simp [prizeDecodeWord, hd] at h
        subst x
        simpa [prizeEncodeWord] using congrArg (List.cons (1 : Fin 4)) (ih xs hd)
    · cases hd : prizeDecodeWord raw with
      | none => simp [prizeDecodeWord, hd] at h
      | some xs =>
        simp [prizeDecodeWord, hd] at h
        subst x
        simpa [prizeEncodeWord] using congrArg (List.cons (2 : Fin 4)) (ih xs hd)
    · simp [prizeDecodeWord] at h

theorem prize_word_encoding_injective : Function.Injective prizeEncodeWord := by
  intro x y h
  have hd := congrArg prizeDecodeWord h
  simpa [prize_word_decode_encode] using hd

theorem prize_word_decode_blank_rejected (raw : List (Fin 4)) :
    prizeDecodeWord (0 :: raw) = none := by simp [prizeDecodeWord]

theorem prize_word_decode_separator_rejected (raw : List (Fin 4)) :
    prizeDecodeWord (3 :: raw) = none := by simp [prizeDecodeWord]

theorem prize_word_decode_prefix (x : PrizeBinaryWord) (raw : List (Fin 4)) :
    prizeDecodeWord (prizeEncodeWord x ++ raw) =
      (fun y => x ++ y) <$> prizeDecodeWord raw := by
  induction x with
  | nil => simp [prizeEncodeWord]
  | cons b x ih =>
    simp only [prizeEncodeWord] at ih
    cases b <;> cases hd : prizeDecodeWord raw <;>
      simp [prizeEncodeWord, prizeDecodeWord, ih, hd]

theorem prize_pair_decode_prefix (x : PrizeBinaryWord) (raw : List (Fin 4)) :
    prizeDecodePair (prizeEncodeWord x ++ 3 :: raw) =
      (fun w => (x, w)) <$> prizeDecodeWord raw := by
  induction x with
  | nil => simp [prizeEncodeWord, prizeDecodePair]
  | cons b x ih =>
    simp only [prizeEncodeWord] at ih
    cases b <;> cases hd : prizeDecodeWord raw <;>
      simp [prizeEncodeWord, prizeDecodePair, ih, hd]

theorem prize_pair_decode_encode (x w : PrizeBinaryWord) :
    prizeDecodePair (prizeEncodePair x w) = some (x, w) := by
  simpa [prizeEncodePair] using
    (prize_pair_decode_prefix x (prizeEncodeWord w)).trans
      (by rw [prize_word_decode_encode]; rfl)

theorem prize_pair_encode_decode (raw : List (Fin 4)) (p : PrizeBinaryWord × PrizeBinaryWord)
    (h : prizeDecodePair raw = some p) : prizeEncodePair p.1 p.2 = raw := by
  induction raw generalizing p with
  | nil => simp [prizeDecodePair] at h
  | cons a raw ih =>
    fin_cases a
    · simp [prizeDecodePair] at h
    · cases hd : prizeDecodePair raw with
      | none => simp [prizeDecodePair, hd] at h
      | some pair =>
        simp [prizeDecodePair, hd] at h
        subst p
        simpa [prizeEncodePair, prizeEncodeWord] using
          congrArg (List.cons (1 : Fin 4)) (ih pair hd)
    · cases hd : prizeDecodePair raw with
      | none => simp [prizeDecodePair, hd] at h
      | some pair =>
        simp [prizeDecodePair, hd] at h
        subst p
        simpa [prizeEncodePair, prizeEncodeWord] using
          congrArg (List.cons (2 : Fin 4)) (ih pair hd)
    · cases hd : prizeDecodeWord raw with
      | none => simp [prizeDecodePair, hd] at h
      | some w =>
        simp [prizeDecodePair, hd] at h
        subst p
        simpa [prizeEncodePair, prizeEncodeWord] using
          congrArg (List.cons (3 : Fin 4)) (prize_word_encode_decode raw w hd)

theorem prize_pair_encoding_injective :
    Function.Injective (fun p : PrizeBinaryWord × PrizeBinaryWord => prizeEncodePair p.1 p.2) := by
  intro x y h
  have hd := congrArg prizeDecodePair h
  simpa [prize_pair_decode_encode] using hd

theorem prize_pair_missing_separator_rejected (x : PrizeBinaryWord) :
    prizeDecodePair (prizeEncodeWord x) = none := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    simp only [prizeEncodeWord] at ih
    cases b <;> simp [prizeEncodeWord, prizeDecodePair, ih]

theorem prize_pair_extra_separator_rejected (x w : PrizeBinaryWord) (raw : List (Fin 4)) :
    prizeDecodePair (prizeEncodePair x w ++ 3 :: raw) = none := by
  simp [prizeEncodePair, List.append_assoc, prize_pair_decode_prefix,
    prize_word_decode_prefix, prize_word_decode_separator_rejected]

theorem prize_pair_trailing_blank_rejected (x w : PrizeBinaryWord) (raw : List (Fin 4)) :
    prizeDecodePair (prizeEncodePair x w ++ 0 :: raw) = none := by
  simp [prizeEncodePair, List.append_assoc, prize_pair_decode_prefix,
    prize_word_decode_prefix, prize_word_decode_blank_rejected]

theorem prize_run_succ {states : ℕ} (M : PrizeMachine states) (input : List (Fin 4)) (t : ℕ) :
    prizeRun M input (t + 1) =
      (Turing.TM0.step M (prizeRun M input t)).getD (prizeRun M input t) := by
  exact Function.iterate_succ_apply' _ _ _

theorem prize_halted_run_stable {states : ℕ} (M : PrizeMachine states)
    (input : List (Fin 4)) (t : ℕ) (halt : prizeHalted M input t) (s : ℕ) :
    prizeRun M input (t + s) = prizeRun M input t := by
  induction s with
  | zero => simp
  | succ s ih =>
    change prizeRun M input ((t + s) + 1) = prizeRun M input t
    rw [prize_run_succ, ih]
    change (Turing.TM0.step M (prizeRun M input t)).getD _ = _
    rw [halt]
    rfl

theorem prize_halted_status_stable {states : ℕ} (M : PrizeMachine states)
    (input : List (Fin 4)) (t : ℕ) (halt : prizeHalted M input t) (s : ℕ) :
    prizeHalted M input (t + s) := by
  unfold prizeHalted
  rw [prize_halted_run_stable M input t halt s]
  exact halt

theorem prize_halted_acceptance_stable {states : ℕ} (M : PrizeMachine states)
    (input : List (Fin 4)) (t : ℕ) (halt : prizeHalted M input t) (s : ℕ) :
    prizeAccepts M input (t + s) ↔ prizeAccepts M input t := by
  unfold prizeAccepts
  rw [prize_halted_run_stable M input t halt s]

theorem prize_halted_boolean_output_stable {states : ℕ} (M : PrizeMachine states)
    (input : List (Fin 4)) (t : ℕ) (halt : prizeHalted M input t) (s : ℕ) :
    prizeBooleanOutput M input (t + s) ↔ prizeBooleanOutput M input t := by
  unfold prizeBooleanOutput
  rw [prize_halted_run_stable M input t halt s]

theorem prize_accepts_by_bound_iff {states : ℕ} (M : PrizeMachine states)
    (input : List (Fin 4)) (bound : ℕ) :
    (prizeHalted M input bound ∧ prizeAccepts M input bound) ↔
      ∃ t ≤ bound, prizeHalted M input t ∧ prizeAccepts M input t := by
  constructor
  · intro h
    exact ⟨bound, le_rfl, h⟩
  · rintro ⟨t, hle, halt, accepts⟩
    have stable := prize_halted_run_stable M input t halt (bound - t)
    rw [Nat.add_sub_of_le hle] at stable
    constructor
    · simpa only [prizeHalted, stable] using halt
    · simpa only [prizeAccepts, stable] using accepts

end IndependentDuodenary
