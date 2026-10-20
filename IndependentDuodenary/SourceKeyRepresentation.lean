import IndependentDuodenary.StationCodec

/-! A constructed coordinate operator and a framed codec on a finite exact-key carrier.
The coordinate cycle is an additional chosen operation, not an identification
of an operator in the external source. -/
namespace IndependentDuodenary

abbrev KeyMetadata := Fin 3
abbrev KeyBinary := Fin 2 → ZMod 2
abbrev KeyComplement := ZMod 12 → ZMod 2
abbrev RepresentedKey := ExactKey KeyMetadata KeyBinary KeyComplement

/-- A coordinate permutation, leaving metadata and the binary intercept fixed. -/
def keyCoordinateCycle (q : RepresentedKey) : RepresentedKey :=
  ⟨q.metadata, q.binaryIntercept, fun i => q.complementIntercept (i + 1)⟩

/-- An observable of the vertex, independent of its translated binary intercept. -/
def keyVertexObservable (v : KeyMetadata × KeyComplement) : KeyComplement := v.2

theorem key_cycle_vertex_observable (q : RepresentedKey) :
    keyVertexObservable (keyVertex (keyCoordinateCycle q)) =
      fun i => keyVertexObservable (keyVertex q) (i + 1) := rfl

theorem key_cycle_iterate (n : ℕ) (q : RepresentedKey) :
    (keyCoordinateCycle^[n]) q =
      ⟨q.metadata, q.binaryIntercept, fun i => q.complementIntercept (i + (n : ZMod 12))⟩ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [keyCoordinateCycle, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm]

def keyOneHot (a : ZMod 12) : KeyComplement := fun i => if i + a = 0 then 1 else 0

def keyCycleWitness : RepresentedKey := ⟨0, 0, keyOneHot 0⟩

/-- A station-valued vertex labeling; on one-hot vertices it records the phase. -/
def keyPhaseLabel (v : KeyMetadata × KeyComplement) : ZMod 12 :=
  ∑ i : ZMod 12, if v.2 i = 1 then -i else 0

theorem key_one_hot_phase : ∀ a : ZMod 12,
    keyPhaseLabel (0, keyOneHot a) = a := by
  intro a
  simp [keyPhaseLabel, keyOneHot, add_eq_zero_iff_eq_neg]

theorem key_cycle_witness_phase (n : ℕ) :
    keyPhaseLabel (keyVertex ((keyCoordinateCycle^[n]) keyCycleWitness)) = (n : ZMod 12) := by
  rw [key_cycle_iterate]
  change keyPhaseLabel (0, fun i => keyOneHot 0 (i + (n : ZMod 12))) = _
  have hw : (fun i => keyOneHot 0 (i + (n : ZMod 12))) = keyOneHot (n : ZMod 12) := by
    funext i
    simp [keyOneHot]
  rw [hw]
  exact key_one_hot_phase (n : ZMod 12)

theorem key_cycle_period_iff (n : ℕ) :
    (∀ q : RepresentedKey, (keyCoordinateCycle^[n]) q = q) ↔ 12 ∣ n := by
  constructor
  · intro h
    have hp := congrArg (fun q => keyPhaseLabel (keyVertex q)) (h keyCycleWitness)
    change keyPhaseLabel (keyVertex ((keyCoordinateCycle^[n]) keyCycleWitness)) =
      keyPhaseLabel (keyVertex keyCycleWitness) at hp
    rw [key_cycle_witness_phase] at hp
    have hz : keyPhaseLabel (keyVertex keyCycleWitness) = 0 := key_one_hot_phase 0
    rw [hz] at hp
    exact (ZMod.natCast_zmod_eq_zero_iff_dvd n 12).mp hp
  · intro h q
    rw [key_cycle_iterate, (ZMod.natCast_zmod_eq_zero_iff_dvd n 12).mpr h]
    simp

theorem key_cycle_period_twelve :
    ∀ q : RepresentedKey, (keyCoordinateCycle^[12]) q = q :=
  (key_cycle_period_iff 12).mpr (dvd_refl 12)

theorem key_cycle_witness_period_iff (n : ℕ) :
    (keyCoordinateCycle^[n]) keyCycleWitness = keyCycleWitness ↔ 12 ∣ n := by
  constructor
  · intro h
    have hp := congrArg (fun q => keyPhaseLabel (keyVertex q)) h
    change keyPhaseLabel (keyVertex ((keyCoordinateCycle^[n]) keyCycleWitness)) =
      keyPhaseLabel (keyVertex keyCycleWitness) at hp
    rw [key_cycle_witness_phase] at hp
    have hz : keyPhaseLabel (keyVertex keyCycleWitness) = 0 := key_one_hot_phase 0
    rw [hz] at hp
    exact (ZMod.natCast_zmod_eq_zero_iff_dvd n 12).mp hp
  · intro h
    exact (key_cycle_period_iff n).mpr h keyCycleWitness

theorem key_cycle_orbit_equivariance (n : ℕ) :
    keyPhaseLabel (keyVertex (keyCoordinateCycle ((keyCoordinateCycle^[n]) keyCycleWitness))) =
      keyPhaseLabel (keyVertex ((keyCoordinateCycle^[n]) keyCycleWitness)) + 1 := by
  rw [← Function.iterate_succ_apply' keyCoordinateCycle n keyCycleWitness,
    key_cycle_witness_phase, key_cycle_witness_phase]
  simp

theorem key_cycle_commutes_translation (h : KeyBinary) (q : RepresentedKey) :
    keyCoordinateCycle (translateKey h q) = translateKey h (keyCoordinateCycle q) := rfl

theorem key_cycle_no_shorter_positive_period (n : ℕ) (hn : 0 < n) (hlt : n < 12) :
    ¬ (∀ q : RepresentedKey, (keyCoordinateCycle^[n]) q = q) := by
  intro h
  have hd := (key_cycle_period_iff n).mp h
  have := Nat.le_of_dvd hn hd
  omega

theorem key_cycle_distinct_from_translation (h : KeyBinary) :
    keyCoordinateCycle ≠ translateKey h := by
  intro heq
  have hc := congrArg (fun q : RepresentedKey => q.complementIntercept)
    (congrFun heq keyCycleWitness)
  have hv := congrFun hc 0
  change (if (0 : ZMod 12) + 1 + 0 = 0 then (1 : ZMod 2) else 0) =
    (if (0 : ZMod 12) + 0 = 0 then (1 : ZMod 2) else 0) at hv
  norm_num at hv
  exact (by decide : (1 : ZMod 12) ≠ 0) hv

/-- Fixed points prevent a global shift-by-one observable on the entire carrier. -/
theorem key_cycle_no_global_station_shift :
    ¬ ∃ f : RepresentedKey → ZMod 12, ∀ q, f (keyCoordinateCycle q) = f q + 1 := by
  rintro ⟨f, hf⟩
  let q : RepresentedKey := ⟨0, 0, 0⟩
  have hfix : keyCoordinateCycle q = q := rfl
  have heq := hf q
  rw [hfix] at heq
  have hzero : (0 : ZMod 12) = 1 := by
    apply add_left_cancel (a := f q)
    simpa using heq
  exact (by decide : (0 : ZMod 12) ≠ 1) hzero

/-- Metadata and bit parsers reject digits outside their respective alphabets. -/
def encodeKeyMetadata (m : KeyMetadata) : ZMod 12 := (m.val : ℕ)

def decodeKeyMetadata (x : ZMod 12) : Option KeyMetadata :=
  if h : x.val < 3 then some ⟨x.val, h⟩ else none

theorem key_metadata_roundtrip : ∀ m : KeyMetadata,
    decodeKeyMetadata (encodeKeyMetadata m) = some m := by decide

theorem key_metadata_parse_sound : ∀ x : ZMod 12, ∀ m : KeyMetadata,
    decodeKeyMetadata x = some m → encodeKeyMetadata m = x := by decide

def encodeKeyBit (b : ZMod 2) : ZMod 12 := if b = 0 then 0 else 1

def decodeKeyBit (x : ZMod 12) : Option (ZMod 2) :=
  if x = 0 then some 0 else if x = 1 then some 1 else none

theorem key_bit_roundtrip : ∀ b : ZMod 2,
    decodeKeyBit (encodeKeyBit b) = some b := by decide

theorem key_bit_parse_sound : ∀ x : ZMod 12, ∀ b : ZMod 2,
    decodeKeyBit x = some b → encodeKeyBit b = x := by decide

def encodeKeyBits {n : ℕ} (b : Fin n → ZMod 2) : List (ZMod 12) :=
  List.ofFn (fun i => encodeKeyBit (b i))

/-- Exactly n binary digits followed by the single terminator 10. -/
def decodeFramedKeyBits : (n : ℕ) → List (ZMod 12) → Option (Fin n → ZMod 2)
  | 0, xs => if xs = [10] then some Fin.elim0 else none
  | _ + 1, [] => none
  | n + 1, x :: xs => do
    let b ← decodeKeyBit x
    let bs ← decodeFramedKeyBits n xs
    pure (Fin.cons b bs)

theorem framed_key_bits_suffix (n : ℕ) (b : Fin n → ZMod 2) (tail : List (ZMod 12)) :
    decodeFramedKeyBits n (encodeKeyBits b ++ tail) =
      if tail = [10] then some b else none := by
  induction n with
  | zero =>
    have hb : b = Fin.elim0 := Subsingleton.elim _ _
    simp [encodeKeyBits, decodeFramedKeyBits, hb]
  | succ n ih =>
    rw [encodeKeyBits, List.ofFn_succ, List.cons_append]
    simp only [decodeFramedKeyBits, key_bit_roundtrip, Option.some_bind]
    change (decodeFramedKeyBits n (encodeKeyBits (fun i => b i.succ) ++ tail)).bind
      (fun bs : Fin n → ZMod 2 => some (Fin.cons (α := fun _ => ZMod 2) (b 0) bs)) = _
    rw [ih]
    split
    · simpa only [Option.some_bind, Option.some.injEq] using (Fin.cons_self_tail b)
    · rfl

theorem framed_key_bits_roundtrip (n : ℕ) (b : Fin n → ZMod 2) :
    decodeFramedKeyBits n (encodeKeyBits b ++ [10]) = some b := by
  simp [framed_key_bits_suffix]

theorem framed_key_bits_parse_sound (n : ℕ) (xs : List (ZMod 12))
    (b : Fin n → ZMod 2) (h : decodeFramedKeyBits n xs = some b) :
    xs = encodeKeyBits b ++ [10] := by
  induction n generalizing xs with
  | zero =>
    simp only [decodeFramedKeyBits] at h
    split at h
    · simpa [encodeKeyBits] using ‹xs = [10]›
    · contradiction
  | succ n ih =>
    cases xs with
    | nil => simp [decodeFramedKeyBits] at h
    | cons x xs =>
      cases hx : decodeKeyBit x with
      | none => simp [decodeFramedKeyBits, hx] at h
      | some bit =>
        cases ht : decodeFramedKeyBits n xs with
        | none => simp [decodeFramedKeyBits, hx, ht] at h
        | some bits =>
          have hb : Fin.cons (α := fun _ => ZMod 2) bit bits = b := by
            simpa [decodeFramedKeyBits, hx, ht] using h
          subst b
          rw [ih xs bits ht]
          simp only [encodeKeyBits, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
            List.cons_append, key_bit_parse_sound x bit hx]

def packKeyBits (q : RepresentedKey) : Fin 14 → ZMod 2 :=
  Fin.append q.binaryIntercept (fun i : Fin 12 => q.complementIntercept (i.val : ZMod 12))

def unpackKeyBits (m : KeyMetadata) (b : Fin 14 → ZMod 2) : RepresentedKey :=
  ⟨m, fun i => b (Fin.castAdd 12 i), fun i => b (Fin.natAdd 2 ⟨i.val, i.val_lt⟩)⟩

theorem key_bits_unpack_pack (q : RepresentedKey) :
    unpackKeyBits q.metadata (packKeyBits q) = q := by
  cases q
  simp only [unpackKeyBits, packKeyBits, Fin.append_left, Fin.append_right,
    ZMod.natCast_zmod_val]

theorem key_bits_pack_unpack (m : KeyMetadata) (b : Fin 14 → ZMod 2) :
    packKeyBits (unpackKeyBits m b) = b := by
  funext i
  refine Fin.addCases (m := 2) (n := 12) (fun j => ?_) (fun j => ?_) i
  · simp [packKeyBits, unpackKeyBits, Fin.append_left]
  · simp only [packKeyBits, unpackKeyBits, Fin.append_right, ZMod.val_natCast,
      Nat.mod_eq_of_lt j.isLt]

/-- Header 11, one metadata digit, fourteen binary digits, terminator 10. -/
def encodeExactKey (q : RepresentedKey) : List (ZMod 12) :=
  11 :: encodeKeyMetadata q.metadata :: (encodeKeyBits (packKeyBits q) ++ [10])

def decodeExactKey : List (ZMod 12) → Option RepresentedKey
  | header :: metadata :: body =>
    if header = 11 then do
      let m ← decodeKeyMetadata metadata
      let b ← decodeFramedKeyBits 14 body
      pure (unpackKeyBits m b)
    else none
  | _ => none

theorem exact_key_decode_encode (q : RepresentedKey) :
    decodeExactKey (encodeExactKey q) = some q := by
  simp [encodeExactKey, decodeExactKey, key_metadata_roundtrip,
    framed_key_bits_roundtrip, key_bits_unpack_pack]

theorem exact_key_parse_sound (xs : List (ZMod 12)) (q : RepresentedKey)
    (h : decodeExactKey xs = some q) : xs = encodeExactKey q := by
  cases xs with
  | nil => simp [decodeExactKey] at h
  | cons header xs =>
    cases xs with
    | nil => simp [decodeExactKey] at h
    | cons metadata body =>
      by_cases hh : header = 11
      · subst header
        cases hm : decodeKeyMetadata metadata with
        | none => simp [decodeExactKey, hm] at h
        | some m =>
          cases hb : decodeFramedKeyBits 14 body with
          | none => simp [decodeExactKey, hm, hb] at h
          | some b =>
            have hq : unpackKeyBits m b = q := by simpa [decodeExactKey, hm, hb] using h
            subst q
            rw [framed_key_bits_parse_sound 14 body b hb]
            change 11 :: metadata :: (encodeKeyBits b ++ [10]) =
              11 :: encodeKeyMetadata m :: (encodeKeyBits (packKeyBits (unpackKeyBits m b)) ++ [10])
            rw [key_bits_pack_unpack, key_metadata_parse_sound metadata m hm]
      · simp [decodeExactKey, hh] at h

theorem exact_key_reject_malformed (xs : List (ZMod 12))
    (h : ∀ q : RepresentedKey, xs ≠ encodeExactKey q) : decodeExactKey xs = none := by
  cases hd : decodeExactKey xs with
  | none => rfl
  | some q => exact False.elim (h q (exact_key_parse_sound xs q hd))

theorem exact_key_encode_length (q : RepresentedKey) : (encodeExactKey q).length = 17 := by
  simp [encodeExactKey, encodeKeyBits]

theorem exact_key_reject_length (xs : List (ZMod 12)) (h : xs.length ≠ 17) :
    decodeExactKey xs = none := by
  apply exact_key_reject_malformed
  intro q heq
  apply h
  rw [heq, exact_key_encode_length]

theorem exact_key_encode_injective : Function.Injective encodeExactKey := by
  intro q r heq
  have h := congrArg decodeExactKey heq
  simpa [exact_key_decode_encode] using h

theorem exact_key_reject_header (header metadata : ZMod 12) (body : List (ZMod 12))
    (h : header ≠ 11) : decodeExactKey (header :: metadata :: body) = none := by
  simp [decodeExactKey, h]

theorem exact_key_reject_metadata (metadata : ZMod 12) (body : List (ZMod 12))
    (h : ¬ metadata.val < 3) : decodeExactKey (11 :: metadata :: body) = none := by
  simp [decodeExactKey, decodeKeyMetadata, h]

theorem exact_key_reject_suffix (q : RepresentedKey) (tail : List (ZMod 12))
    (h : tail ≠ [10]) :
    decodeExactKey (11 :: encodeKeyMetadata q.metadata ::
      (encodeKeyBits (packKeyBits q) ++ tail)) = none := by
  simp [decodeExactKey, key_metadata_roundtrip, framed_key_bits_suffix, h]

theorem exact_key_reject_nonbinary_first (metadata x : ZMod 12) (xs : List (ZMod 12))
    (hzero : x ≠ 0) (hone : x ≠ 1) :
    decodeExactKey (11 :: metadata :: x :: xs) = none := by
  simp [decodeExactKey, decodeFramedKeyBits, decodeKeyBit, hzero, hone]

/-- Invalid words are mapped to the empty word, which the decoder rejects. -/
def translateKeyWord (h : KeyBinary) (word : List (ZMod 12)) : List (ZMod 12) :=
  match decodeExactKey word with
  | none => []
  | some q => encodeExactKey (translateKey h q)

theorem exact_key_word_translation (h : KeyBinary) (q : RepresentedKey) :
    translateKeyWord h (encodeExactKey q) = encodeExactKey (translateKey h q) := by
  simp [translateKeyWord, exact_key_decode_encode]

theorem exact_key_word_translation_invalid (h : KeyBinary) (word : List (ZMod 12))
    (hinvalid : decodeExactKey word = none) : translateKeyWord h word = [] := by
  simp [translateKeyWord, hinvalid]

theorem exact_key_word_translation_involution (h : KeyBinary) (q : RepresentedKey) :
    translateKeyWord h (translateKeyWord h (encodeExactKey q)) = encodeExactKey q := by
  rw [exact_key_word_translation, exact_key_word_translation, translateKey_add,
    binary_vector_double_zero, translateKey_zero]

end IndependentDuodenary
