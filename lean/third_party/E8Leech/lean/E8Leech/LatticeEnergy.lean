import E8Leech.E8Lattice
import E8Leech.Target
import Mathlib.Algebra.Module.ZLattice.Summable

/-!
# Finite Riesz energy for lattices

An existing Mathlib lattice summability theorem avoids a new shell-counting argument.
The diagonal is removed explicitly: an ENNReal negative power at zero is infinite,
whereas Real.rpow at zero is zero for the nonzero exponent used here.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal

theorem latticeRieszEnergy_coe_eq {d : ℕ} (L : Submodule ℤ (Ambient d))
    {s : ℝ} (hs : 0 < s) :
    latticeRieszEnergy (L : Set (Ambient d)) s =
      ∑' y : L, ENNReal.ofReal (‖(y : Ambient d)‖ ^ (-s)) := by
  unfold latticeRieszEnergy
  apply tsum_congr
  intro y
  by_cases hy : (y : Ambient d) = 0
  · simp [hy, Real.zero_rpow (neg_ne_zero.mpr hs.ne')]
  · simp only [hy, ↓reduceIte, rieszPotential, dist_zero_left]
    exact ENNReal.ofReal_rpow_of_pos (norm_pos_iff.mpr hy)

theorem latticeRieszEnergy_ne_top {d : ℕ} (L : Submodule ℤ (Ambient d))
    [DiscreteTopology L] [IsZLattice ℝ L]
    {s : ℝ} (hs : (Module.finrank ℤ L : ℝ) < s) :
    latticeRieszEnergy (L : Set (Ambient d)) s ≠ ∞ := by
  have hspos : 0 < s := lt_of_le_of_lt (Nat.cast_nonneg _) hs
  rw [latticeRieszEnergy_coe_eq L hspos]
  have hsum := ZLattice.summable_norm_rpow L (-s) (neg_lt_neg hs)
  simpa only [Submodule.norm_coe] using hsum.tsum_ofReal_ne_top

theorem e8_latticeRieszEnergy_ne_top {s : ℝ} (hs : 8 < s) :
    latticeRieszEnergy e8Set s ≠ ∞ := by
  rw [← coe_e8Lattice]
  apply latticeRieszEnergy_ne_top
  simpa [e8Lattice_rank] using hs

end E8Leech
