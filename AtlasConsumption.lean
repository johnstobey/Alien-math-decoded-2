import ZMod12Transport
import C12ZModBridge
import CRTMathlib
import IndependentDuodenary.ModularCore

/-!
# Atlas-certified interface consumption (DCC-01 Stage 4)

This module consumes the canonical certification published by
`The-Duodenary-Mathematical-Proof-Atlas-` (`closed_ring_z12_mathlib`,
pinned at `2d84d17ebf849525b8ae0155cc646b6ed7a58f2e`) rather than
maintaining independent foundational proofs of the same `ZMod 12`
structure.

Every theorem below is a direct application of a certified declaration —
`exact`/`apply` only, no reproved mathematics. The axiom surface is
therefore inherited unchanged: `[propext, Classical.choice, Quot.sound]`,
zero `sorryAx` (see `#print axioms` reports at the foot of this file).

Certified sources consumed:

* `ZMod12Transport` — `ZMod 12` residue presentation, unit group,
  seven distances, six antipodal pairs, admissible-slope closure.
* `C12ZModBridge` — `C12 ≃+* ZMod 12` and `C12 ≃+* ZMod 4 × ZMod 3`.
* `CRTMathlib` — `crt12 : ZMod 12 ≃+* ZMod 4 × ZMod 3` with `phi`/`phiInv`
  agreement lemmas.
-/

namespace IndependentDuodenary.AtlasConsumption

open Duodenary
open Duodenary.C12Mathlib
open ClosedRingZ12.MathlibCRT
open ClosedRingZ12.ZMod12Transport
open IndependentDuodenary

/-- Inherited: the unit group of `ZMod 12` has order `φ 12 = 4`
(`ZMod.card_units_eq_totient` transported by the Atlas certification). -/
theorem station_unit_group_card : Fintype.card (ZMod 12)ˣ = 4 :=
  zmod12_units_card

/-- Inherited: `station` residues that are units are exactly the residues
coprime to 12 — the `ZMod.unitsEquivCoprime` characterization, applied to
this repository's own `station` map. -/
theorem station_unit_iff_coprime (u : ℕ) (hu : u < 12) :
    IsUnit (station u) ↔ Nat.Coprime u 12 :=
  zmod12_unit_iff_coprime u hu

/-- Inherited: the certified CRT decomposition applies to `station`
residues — `station u` splits as `(u mod 4, u mod 3)` under `crt12`. -/
theorem station_crt_decomp (u : ℕ) (hu : u < 12) :
    crt12 (station u) = (((u % 4 : ℕ) : ZMod 4), ((u % 3 : ℕ) : ZMod 3)) := by
  show crt12 ((u : ℕ) : ZMod 12) = _
  exact crt12_apply_lt u hu

/-- Inherited: the Duodenary carrier `C12` has exactly four units, through
the CP-01 `C12 ≃+* ZMod 12` bridge. -/
theorem atlas_c12_units : Fintype.card C12ˣ = 4 :=
  c12_units_card

/-- Inherited: six antipodal pairs, certified complete and `J`-involutive. -/
theorem atlas_six_antipodal_pairs : antipodalPairs.length = 6 :=
  antipodalPairs_length

/-- Inherited: `dist` attains exactly the seven values `0,…,6`. -/
theorem atlas_seven_distances (d : ℕ) (hd : d < 7) :
    ∃ x < 12, ∃ y < 12, ClosedRingZ12.dist x y = d :=
  dist_attains_all d hd

/-- Inherited: admissible affine slopes `{1,5,7,11}` are closed under
multiplication mod 12 — composition of admissible transformations. -/
theorem atlas_slopes_closed :
    ∀ u ∈ ([1, 5, 7, 11] : List Nat),
      ∀ v ∈ ([1, 5, 7, 11] : List Nat),
        (u * v) % 12 ∈ ([1, 5, 7, 11] : List Nat) :=
  unit_slopes_closed

end IndependentDuodenary.AtlasConsumption

#print axioms IndependentDuodenary.AtlasConsumption.station_unit_group_card
#print axioms IndependentDuodenary.AtlasConsumption.station_unit_iff_coprime
#print axioms IndependentDuodenary.AtlasConsumption.station_crt_decomp
#print axioms IndependentDuodenary.AtlasConsumption.atlas_c12_units
#print axioms IndependentDuodenary.AtlasConsumption.atlas_six_antipodal_pairs
#print axioms IndependentDuodenary.AtlasConsumption.atlas_seven_distances
#print axioms IndependentDuodenary.AtlasConsumption.atlas_slopes_closed
