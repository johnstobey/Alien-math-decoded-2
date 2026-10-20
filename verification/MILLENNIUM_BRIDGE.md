# Formal alignment and audit specification (Nodes Q and R)

## Mathematical boundary

This is an audit package for a finite algebraic protocol. It does not establish
a Millennium Prize conjecture or submission eligibility. The name of the bridge
module identifies an alignment obligation, not a proved bridge to a prize result.

The complete theorem inventory is `THEOREMS.md`; elaborated propositions, proof
terms, direct dependencies and transitive axiom lists are in
`axioms-and-proofs.txt`. The machine-readable index is
`../packaging/theorem_alignment.json`. Each entry identifies its actual domain;
no entry asserts an implication to an external prize conjecture.

## Q: exact finite bounds

For a register count r, a state is a function from Fin r to a represented key.
A key contains a three-valued metadata field, two binary coordinates and twelve
binary complement coordinates. The coefficient equivalence proves

    |RepresentedKey| = 3 * 2^2 * 2^12 = 49152
    |RegisterState r| = 49152^r.

For the previously defined structural step S_h, S_h^12 is the identity. Division
with remainder therefore gives, for every natural n and every state q,

    S_h^n(q) = S_h^(n mod 12)(q).

The explicit candidate set { S_h^k(q) : k in Fin 12 } contains every iterate and
has cardinality at most twelve. This bound concerns one orbit of one fixed
operator from one initial state. It is compatible with an exponentially growing
full state space. It is not a bound on arbitrary combinatorial search.

Each transmitted register frame has seventeen symbols. Triple repetition uses
fifty-one symbol positions per register. The identity 51r = 3(17r) counts channel
positions; it is not an implementation-level polynomial-time theorem. Station
composition, inverse dynamics, lossless parsing and bounded aligned substitution
recovery are the established protocol invariants described in
`PIPELINE_DEPLOYMENT.md`. Their explicit noise and framing conditions remain.
Phase projection alone loses information; no global phase isomorphism is claimed.

## Complexity statement and remaining obligations

`MillenniumBridge.lean` defines finite Post-Turing machines using Mathlib's TM0,
a binary input encoding, a certificate separator, a halted-configuration time
iteration, Boolean outputs and natural polynomial bounds. It defines classes
`PrizeDeterministicPolynomial` and `PrizeCertificatePolynomial` and the proposition
`PVersusNPConjecture` that these classes differ.

This proposition has no proof in the package. The definitions give an explicit
verifier-based machine model; equivalence to conventional presentations of P and
NP is not formalized here. No reduction connects the finite protocol to arbitrary
languages in those classes. Neither a class separation nor a class equality
follows from the finite orbit theorem. No topological Millennium conjecture is
formalized or proved. Such missing bridges cannot be replaced by naming an
invariant or by making the desired conclusion a hypothesis.

The new proofs introduce no custom axioms. The project audit permits only Lean's
standard propext, Classical.choice and Quot.sound. Absence of custom axioms does
not mean the development is entirely constructive: existing proofs use standard
classical reasoning. There is no proof of intelligence or historical attribution.

## R: build and export contract

The root `lakefile.lean`, `lean-toolchain` and `lake-manifest.json` pin Lean 4.14.0
and the full Mathlib dependency closure. This is not a zero-dependency package.
A source archive downloads pinned dependencies when necessary. Vendor mode copies
pinned dependency source trees and available compiled caches, with an explicit
local-path Lake overlay; original Git configuration is retained. Both modes
require an installed matching Lean/Lake toolchain, Python 3 and a native linker.
Dependency licensing notices remain in the archived source trees.

From a clean committed checkout:

```sh
scripts/export_proof_bundle.sh --output dist
scripts/export_proof_bundle.sh --vendor --output dist
```

Use `--ci-url https://github.com/OWNER/REPO/actions/runs/ID` to include public
successful run/job evidence for precisely the exported commit. This is rejected
for dirty sources or mismatched/unsuccessful runs. Public HTML evidence is
identified as such; raw CI download logs are not claimed to be included.
`--allow-dirty` creates explicitly marked development archives only.

The exporter reruns the build, theorem audit, strict zero-diagnostic bridge and
boundary checks, and executable guard. It includes their actual logs, source,
pinned configuration, alignment metadata, full theorem index and SHA256SUMS.
The archive receives a separate SHA-256 sidecar. Extract and run:

```sh
python3 scripts/verify_bundle.py --all
```

The verifier first hashes payload files, then builds, audits and executes the
pipeline guard. After a build mutates caches, `--sources-only` checks immutable
payload files. Hashes establish integrity relative to the supplied manifest;
they are not a third-party signature. Archive ordering and timestamps are fixed,
but verification log contents may vary between runs.

## External standards status

`packaging/problem_alignment.json` records the unresolved prize alignment.
The official rules endpoint at https://www.claymath.org/millennium-problems/rules/
returned HTTP 403 in this environment. Its text was not retrieved or audited.
No CMI compliance certification, acceptance, publication status or prize
eligibility is asserted. This package is suitable for independent inspection of
its stated finite mathematics; a complete Millennium submission remains
unestablished.

## S/T monograph and claim-audit export

`../MillenniumPrizeTranslation.tex` states the finite mathematics, the exact
bounded-reachability equivalence and the unresolved P-versus-NP bridge. Its
appendix is generated from the complete source-matched theorem catalog. Build
and archive it with:

```sh
python3 scripts/build_translation.py
scripts/perfect_claim_bundle.sh --output dist
```

The build needs pdfLaTeX with amsmath, amssymb, geometry and hyperref (on Ubuntu,
`texlive-latex-base texlive-latex-recommended`). Two passes resolve references;
undefined references and overfull boxes fail the builder. `--vendor` and
`--ci-url` retain the exporter's existing meanings. The resulting filename ends
in `-translation.tar.gz`. The archive contains `publication/` with the PDF,
all generated TeX inputs, source, compilation logs and a translation manifest.
The ordinary build manifests remain pinned and unchanged.

The new equivalence has domain `RegisterState r` for a fixed `registerStep h`.
It reduces its unbounded iteration count to Fin 12. It is not an equivalence to
a Clay conjecture. The public repository is a source record only: no deposit
receipt, DOI, peer review, institutional submission or prize registration is
asserted or produced. The audit package is ready for inspection of its stated
finite results; an institutional prize claim is not established.
