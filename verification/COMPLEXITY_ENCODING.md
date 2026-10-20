# Total parsers and halted-run persistence

Source: `IndependentDuodenary/ComplexityEncoding.lean`.
Boundary examples: `examples/ComplexityParserBoundary.lean`.

This extension adds 19 named theorems to the 354-declaration baseline, for 373.
It closes three atomic obligations: 1.10, 1.11 and 1.12. Including the five
previous checked encoding examples, 8 of 77 obligations are discharged and 69
remain open. These are obligation counts, not counts of library theorems.

## Word and pair parsers

`prizeDecodeWord` and `prizeDecodePair` are structurally recursive total functions
returning `Option`. Word symbols are 1 and 2, encoding false and true. A pair
contains exactly one separator 3; blank 0 is invalid input data.

For both parsers, decoding an encoding returns its original value. Conversely,
whenever decoding raw input succeeds, re-encoding the result equals the entire
raw input. Consequently the encoders are injective, parsing has no ambiguous
separator split, and successful decoding cannot ignore a suffix. The prefix
lemmas prove rejection of invalid symbols anywhere after a valid prefix; the
pair-specific lemmas reject missing separators, extra separators and trailing
blanks. Leading invalid symbols are rejected directly by the definitions.
Additional valid bit symbols after the separator extend the certificate; they
are consumed and are not malformed padding. Boundary examples check this case.

## Halting and acceptance

`prize_run_succ` connects the saturated iterator to one actual TM0 transition.
Induction proves that a configuration halted at t stays identical at every
`t+s`. Halting status, acceptance and Boolean-output validity therefore persist.
`prize_accepts_by_bound_iff` proves that halted acceptance at a bound is equivalent
to halted acceptance at some earlier or equal time. It does not supply any bound
for a machine that has not already been proved to halt.

## Remaining scope

These proofs use the existing Fin-4 TM0 model and its existing acceptance
convention. They do not prove correspondence with conventional complexity
classes, construct the general SAT-to-protocol reduction, establish polynomial
running time, or resolve P versus NP. The historical administrative dossier
continues to identify its original 350-theorem revision.
