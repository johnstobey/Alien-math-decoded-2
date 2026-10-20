import IndependentDuodenary

open IndependentDuodenary

abbrev Q := RepresentedKey
abbrev T : Q → Q := keyCoordinateCycle
abbrev f : KeyMetadata × KeyComplement → ZMod 12 := keyPhaseLabel
abbrev E : Q → List (ZMod 12) := encodeExactKey
abbrev D : List (ZMod 12) → Option Q := decodeExactKey
abbrev U_h : KeyBinary → List (ZMod 12) → List (ZMod 12) := translateKeyWord

example (n : ℕ) : (∀ q : Q, (T^[n]) q = q) ↔ 12 ∣ n :=
  key_cycle_period_iff n

example (n : ℕ) (hn : 0 < n) (hlt : n < 12) :
    ¬ (∀ q : Q, (T^[n]) q = q) :=
  key_cycle_no_shorter_positive_period n hn hlt

example (h : KeyBinary) : T ≠ translateKey h :=
  key_cycle_distinct_from_translation h

example (n : ℕ) : f (keyVertex ((T^[n]) keyCycleWitness)) = (n : ZMod 12) :=
  key_cycle_witness_phase n

example (n : ℕ) :
    f (keyVertex (T ((T^[n]) keyCycleWitness))) =
      f (keyVertex ((T^[n]) keyCycleWitness)) + 1 :=
  key_cycle_orbit_equivariance n

example (q : Q) : D (E q) = some q := by
  simp [D, E, encodeExactKey, decodeExactKey, key_metadata_roundtrip,
    framed_key_bits_roundtrip, key_bits_unpack_pack]

example (xs : List (ZMod 12)) (h : ∀ q : Q, xs ≠ E q) : D xs = none :=
  exact_key_reject_malformed xs h

example (h : KeyBinary) (q : Q) : U_h h (E q) = E (translateKey h q) := by
  simp [U_h, E, translateKeyWord, exact_key_decode_encode]

example (h : KeyBinary) (q : Q) : U_h h (U_h h (E q)) = E q :=
  exact_key_word_translation_involution h q

def fixtureKey : Q := ⟨2, ![1, 0], keyOneHot 3⟩

#guard (E fixtureKey).length = 17
#guard D (E fixtureKey) = some fixtureKey
#guard D [] = none
#guard D (0 :: (E fixtureKey).drop 1) = none
#guard D (11 :: 3 :: (E fixtureKey).drop 2) = none
#guard D (11 :: 2 :: 2 :: (E fixtureKey).drop 3) = none
#guard D ((E fixtureKey).take 16 ++ [11]) = none
#guard D ((E fixtureKey).take 16) = none
#guard D (E fixtureKey ++ [0]) = none
#guard D (U_h ![1, 1] (E fixtureKey)) = some (translateKey ![1, 1] fixtureKey)
#guard f (keyVertex ((T^[11]) keyCycleWitness)) = 11
#guard (T^[12]) keyCycleWitness = keyCycleWitness
