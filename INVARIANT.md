# Preservation of geometric identity

**Across the supported representations, the same structured object retains its identity: its defining relationships and permitted operations remain consistent through translation and execution.**

## This repository's role: Formal correspondence and recovery

The published station grammar gives expressions whole-permutation meanings, compilation and decoding. Register naturality and the canonical envelope express compatibility of operations and views. These provide formal instances of the invariant.

Local evidence and definitions: [verification/STATION_CODEC.md](verification/STATION_CODEC.md) and [verification/CANONICAL_ENVELOPE.md](verification/CANONICAL_ENVELOPE.md).

## The executable correspondence

For a declared source operation f, representation h and target operation g:

    h(f(x)) = g(h(x))
    decode(h(x)) = x

The first equation checks operation correspondence; the second checks exact
recovery for the specified object. Identify the carrier, maps and preserved
relationships before applying these equations. Twelve matching labels or a
single matching example are insufficient. Different operations can preserve
different invariants; the exact contract determines which relationships must hold.

The [shared invariant definition and complete worked example](https://github.com/johnstobey/The-Duodenary-Mathematical-Proof-Atlas-/blob/atlas-workbench-01/INVARIANT.md)
connects station, glyph, exact rational angle and lattice views. Its one-command
finite verifier emits explicit mapping and transformation tables and rejects
broken endpoints, lexical padding and a bijective but operation-incompatible map.
Run it in the Atlas workbench branch:

    python3 03_ENGINE/invariant.py

This link does not assert that every module here already uses the new admission
bridge. Structural admission requires actual computed witnesses. BB's locked
scores and canonical identifiers are not changed by this documentation.
The existing per-repository implementations and their evidence retain their
recorded scope. The new documentation makes their common purpose explicit.
