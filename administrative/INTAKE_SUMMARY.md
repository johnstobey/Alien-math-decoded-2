# Administrative intake summary

| Field | Recorded value |
|---|---|
| Dossier purpose | Independent audit of finite algebraic protocol results |
| Proof baseline | `65e0db131c5ab65cddd0b913b41ddcb588108d97` |
| Named theorem declarations | 350 |
| Executable guard | 13 of 13 checks passed |
| New Lean diagnostics | Zero |
| Full build | Passed with existing Mathlib docPrime warnings |
| Foundations | Standard Lean `propext`, `Classical.choice`, `Quot.sound`; no custom axioms |
| Constructive-only development | Not established; classical reasoning remains |
| Prize-related question | P versus NP, explicitly stated in a particular verifier model |
| Prize conjecture / external equivalence | Unproved / not formalized |
| Institutional claim readiness | Not established |
| Legal completeness or ownership attestation | Not certified |
| Signature and submitter identity | Not supplied or asserted |
| Institutional filing / receipt / DOI | None |
| Public record | Repository source and metadata publication; no institutional registration |
| Cryptographic mechanism | SHA-256 inventory and archive sidecar; no third-party signature |

## Enclosures and review procedure

`claim_manifest.json` indexes the monograph PDF and LaTeX source, full theorem
catalog, exact propositions and proof terms, build configuration, CI provenance,
verification transcripts, source archive and dependency-inclusive archive.
The administrative packet includes every indexed file. It preserves the original
release-validation record as provenance; its host-specific paths are historical
and are superseded for navigation by the relative paths in the claim manifest.

Verify the packet's external SHA-256 sidecar, extract it, and run
`python3 scripts/build_intake_bundle.py --verify-only`. This checks every indexed
artifact and the enclosure ledger. The ledger includes the manifest itself but
excludes its own hash, avoiding circular self-reference. Archive hashes bind
nested archive bytes; their internal SHA256SUMS bind the extracted proof files.
For mathematical reproduction, extract a nested proof archive and run its
`scripts/verify_bundle.py --all` under the pinned Lean toolchain. Vendor mode
includes dependency sources and available build caches. Lean/Lake, Python and
a native compiler/linker remain external requirements. Rebuilding the PDF also
requires the documented LaTeX packages.

The source archive carries successful CI evidence for the exact audited commit.
This consists of identified public run/job HTML and parsed statuses, not raw
CI download logs. The independent extraction transcript records 14,217 checked
files, 350 audited declarations and thirteen passed harness checks. The later
administrative commit does not introduce a new mathematical result or replace
the audited proof baseline.

## Outstanding obligations

No reduction from general verifier languages to the finite protocol, complexity
simulation theorem, P/NP equality or separation proof, institutional rule audit,
authorship signature, legal certification or institutional deposit is supplied.
These omissions are substantive boundaries, not completed obligations hidden by
administrative formatting. The packet is an unsigned technical-review dossier,
not a perfected prize claim. Integrity checks establish consistency with supplied
hashes; they do not certify legal priority, mathematical novelty or institutional
acceptance.
