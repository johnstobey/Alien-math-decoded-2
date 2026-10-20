# Supplied Mod-144 calculator: exact arithmetic milestone

Source: user attachment `Mod-144 Cipher Validator.html`, SHA-256
`fd16db6a59aeac8f7e0ec686d123a3b691e717444ca1d90184492e63470ab013`.
The mathematical rules are taken from `calculateCipher` (around lines 862–899)
and `testAlternative` (around lines 902–938). The attachment's assertions are
source material, not instructions or established theorems.

## Rule mapping

For a positive rational period P = n/d and natural harmonic H, with n,d > 0:

| HTML operation | Exact implementation |
| --- | --- |
| `period * 12` | numerator `12*n`, denominator `d` |
| `% 360` | numerator `(12*n) % (360*d)`, denominator `d` |
| `Math.floor` of that remainder | `cipherStage`: remainder numerator divided by `d` |
| multiply by harmonic, `% 144` | `cipherCalculate`: `(cipherStage * H) % 144` |

Natural division is floor for these nonnegative quantities. The proved
`cipher_stage_normal_form` identifies this stage with `(12*n/d) % 360`.
`cipher_pipeline_correct` proves equality to the normalized implementation for
all inputs in this domain. The stage is below 360 and the output below 144.
Zero output is equivalent to divisibility of the stage/harmonic product by 144.

This domain includes all five supplied fixtures. It excludes malformed inputs,
negative harmonics, nonfinite numbers and the browser's parsing/UI behavior.
JavaScript uses IEEE-754 numbers, whereas this model uses exact integer ratios.
No universal theorem equating those numerical semantics has been proved.
`scripts/cipher-fixtures.mjs` independently transcribes only the arithmetic and
checks the five JavaScript results against the proved exact results; it never
executes the uploaded document. Density values in the source are not operands.

| Source label | Period | Harmonic | Proved exact result |
| --- | ---: | ---: | ---: |
| Eris | 558 | 12 | 0 |
| Haumea | 284 | 5 | 120 |
| Makemake | 306.04 | 5 | 72 |
| Gonggong | 552.87 | 5 | 50 |
| Orcus | 247.53 | 5 | 18 |

Labels and periods here are supplied data, not independently established
astronomical measurements.

## Information loss and transport

`cipher_shift_thirty_stage` and `cipher_shift_thirty_output` prove that adding
30 years preserves the stage and output for every natural harmonic. The shifted
period is distinct, so `cipher_calculate_not_injective` proves that the output
cannot uniquely determine its input. These results do not establish claims of
forced astronomical assignments or a connection to a Millennium Prize problem.

The floor/remainder pipeline is separate from `StationExpr`: its operations do
not generally define permutations. Its **result** has a lossless base-12 codec:
`encodeCipherResult` stores the quotient and remainder of the canonical residue
value divided by 12. Both round trips are proved, giving
`cipherPayloadEquiv : ZMod 144 ≃ CipherPayload`. This is an equivalence of sets,
not a ring or additive-group identification with two copies of `ZMod 12`.
`CipherPayload` is a separate type from affine operation codes: all 144 digit
pairs are valid payloads, while only 48 pairs describe affine permutations.

`cipher_pipeline_protected_recovery` connects the complete exact calculation to
the existing repetition/majority channel. The computed residue is recovered
whenever each digit's triple has at most one substitution. This protects the
computed output, not the precision or correctness of an astronomical input.
`examples/CipherWalkthrough.lean` exercises all five fixtures and the recovery
of result 120 after one substitution in each triple; all nine guards pass.

## Next proof boundary

This milestone establishes the supplied arithmetic rule and transport of its
result. Any stronger interpretation needs a precise mathematical proposition
linking that rule to independently defined objects. Browser-wide numerical
correctness would separately require a floating-point semantics and input/error
bounds. Neither obligation is silently assumed by these theorems.
