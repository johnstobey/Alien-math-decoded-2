import Mathlib.Data.ZMod.Basic

/-!
# Modular Core

This file establishes arithmetic facts about two independently defined residue rings.
No theorem in this file asserts anything about an external research paper.
-/

namespace IndependentDuodenary

def station (n : ℕ) : ZMod 12 := (n : ZMod 12)
def superstation (n : ℕ) : ZMod 144 := (n : ZMod 144)

theorem twelve_returns : station 12 = 0 := by decide
theorem predecessor_is_nonzero : station 11 ≠ 0 := by decide
theorem predecessor_successor_returns : station (11 + 1) = 0 := by decide
theorem three_times_twelve_returns : station (3 * 12) = 0 := by decide
theorem twelve_squared_returns : superstation (12 * 12) = 0 := by decide
theorem twelve_nonzero_mod_144 : superstation 12 ≠ 0 := by decide
theorem number_372_multiple : 372 = 12 * 31 := by decide
theorem number_719_predecessor : station 719 = 11 := by decide
theorem number_10800_multiple : superstation 10800 = 0 := by decide

end IndependentDuodenary

namespace IndependentDuodenary

/-- Natural-number reduction preserves addition in the twelve-element ring. -/
theorem station_add (m n : ℕ) : station (m + n) = station m + station n := by
  exact Nat.cast_add m n

/-- Natural-number reduction preserves addition in the 144-element ring. -/
theorem superstation_add (m n : ℕ) : superstation (m + n) = superstation m + superstation n := by
  exact Nat.cast_add m n

theorem predecessor_add_one : (11 : ZMod 12) + 1 = 0 := by decide
theorem predecessor_eq_neg_one : (11 : ZMod 12) = -1 := by decide

theorem station_add_closed (m n : ℕ) :
    ∃ k : ℕ, station m + station n = station k :=
  ⟨m + n, (station_add m n).symm⟩

theorem superstation_add_closed (m n : ℕ) :
    ∃ k : ℕ, superstation m + superstation n = superstation k :=
  ⟨m + n, (superstation_add m n).symm⟩

/-- Two nonzero residues multiply to zero in Z/12Z. -/
theorem zero_divisors_mod_twelve :
    (3 : ZMod 12) ≠ 0 ∧ (4 : ZMod 12) ≠ 0 ∧ (3 : ZMod 12) * 4 = 0 := by decide

/-- The nonzero residue 12 squares to zero in Z/144Z. -/
theorem zero_divisor_mod_144 :
    (12 : ZMod 144) ≠ 0 ∧ (12 : ZMod 144) * 12 = 0 := by decide

end IndependentDuodenary
