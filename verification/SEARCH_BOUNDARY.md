# Search-boundary results and the unresolved prize bridge

## Verified deliverable

`IndependentDuodenary/SearchBoundary.lean` adds four proved declarations to the
350-declaration baseline. It imports the existing period, exact state cardinality
and codec library. No custom axioms or proof placeholders are introduced.

`protocolReachabilityCheck h q x` evaluates the twelve possible phase indices
and compares the resulting full register states with x. The correctness theorem
is

```lean
protocolReachabilityCheck h q x = true ↔
  ∃ n : ℕ, ((registerStep h)^[n]) q = x
```

The rejection theorem proves that false is equivalent to absence of every
natural-number iterate, not merely failure within a heuristic cutoff. The
period theorem justifies the finite cutoff. The accompanying fixture checks a
reachable state, a metadata-mismatched unreachable state, the zero-register
boundary, and a rotated one-hot state.

## Global orbit-cover bound

Let seeds be a finite set of initial states and suppose every full state lies
in the orbit of at least one seed under the same fixed operator. There is a
surjection

    {q : RegisterState r | q ∈ seeds} × Fin 12 → RegisterState r
    (q,k) ↦ (registerStep h)^k(q).

Finite cardinality monotonicity under this surjection gives

    49152^r ≤ 12 * seeds.card.

For r = 1 this requires at least 4096 seeds. Generally the bound is
`seeds.card ≥ ceil(49152^r / 12)`. Thus twelve candidates suffice for one fixed
orbit, while a complete explicit cover of all full states requires many seeds.
The proof does not assume that orbits are disjoint, regular or of full length.
It also handles r = 0.

This is a lower bound for explicit orbit covers. It is not a lower bound against
all algorithms, implicit representations, Boolean circuits or Turing machines.
A decision procedure need not enumerate every state or orbit. No conclusion
about P versus NP follows from counting covers alone.

## Direction of the proposed complexity argument

The current `PVersusNPConjecture` definition asserts inequality between the
explicit deterministic and certificate-based polynomial language classes.
A valid polynomial reduction of a complete certificate-verification problem
to a proved polynomial-time protocol decision procedure would instead support
a class-equality result, after the necessary completeness and machine-model
bridges were proved. Equality and the currently defined inequality are opposite
claims. A finite search-compression argument cannot silently serve as a proof
of the inequality.

The Boolean reachability checker is not yet implemented and cost-certified in
the formal Turing-machine model used by those language-class definitions.
Neither a runtime theorem for that model nor a general-problem reduction is
present. In particular, computing a suitable starting seed may itself contain
the original hard problem; it must not be assumed available without a proved
construction and resource bound.

To prove inequality, a candidate language in the certificate class must be
shown absent from every deterministic polynomial-time machine in the defined
model, with the conventional-model correspondence established. The orbit-cover
bound does not quantify over those machines and supplies no such separation.

## Proof-obligation register

`packaging/prize_proof_obligations.json` records the missing bridges explicitly.
These are research obligations, not assumptions added to Lean to make a desired
conclusion compile. The prize proposition remains unproved. No institutional
eligibility or legal certification is created by the new declarations.

## Evidence and historical dossier

The current library has 354 named theorem declarations. Exact statements,
terms and foundational dependencies are in `THEOREMS.md` and
`axioms-and-proofs.txt`. The new module and fixture are checked for zero
compiler diagnostics; full builds retain the documented upstream Mathlib
warnings. The existing thirteen-check end-to-end guard remains a separate
protocol validation fixture.

The 350-theorem `claim_manifest.json`, its administrative correspondence and
its checksum ledger are historical records for audited commit 65e0db1. Their
original contents remain available in the corresponding intake archive and
pinned Git history. They do not certify subsequent research files under the
old hashes. Use the new research release's `BUNDLE.json`, SHA256SUMS, current
catalog and audit log for this extension. The historical intake builder must
be run from its archived revision to regenerate that historical packet.

Build and reproduce the new research package with the existing pinned toolchain:

```sh
lake build
lake env lean IndependentDuodenary/SearchBoundary.lean
lake env lean examples/SearchBoundary.lean
python3 scripts/audit.py
lake exe verifyPipeline
scripts/perfect_claim_bundle.sh --output dist
```

The final command generates a proof-and-monograph audit archive. Its name does
not certify a prize claim. A clean commit is required for a release export.
