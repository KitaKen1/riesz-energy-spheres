import E8Leech.GaussianPotentialMixtures
import E8Leech.LeechLattice

/-!
# Gaussian lattice finiteness from one known finite integer Riesz moment

Use the already checked factorial Gaussian bound and a nonzero-vector division.
No theta-series convergence or new lattice shell count is required. This proves
the finiteness needed before converting the actual Gaussian baseline to real.
-/

noncomputable section
namespace E8Leech
open Set MeasureTheory
open scoped ENNReal

theorem gaussianKernel_riesz_integer_upper {d : ℕ} {α : ℝ} (hα : 0 < α)
    (n : ℕ) (v : Ambient d) (hne : v ≠ 0) :
    gaussianKernel α v ≤ (1 + (n.factorial : ℝ) / α ^ n) * ‖v‖ ^ (-(n : ℝ)) := by
  have hp := weighted_gaussianKernel_bound hα n v
  rw [abs_of_pos (gaussianKernel_pos α v)] at hp
  rw [Real.rpow_neg (norm_nonneg v), Real.rpow_natCast, ← div_eq_mul_inv]
  exact (le_div_iff₀ (pow_pos (norm_pos_iff.mpr hne) n)).mpr
    (by simpa only [mul_comm] using hp)

theorem gaussianPotential_riesz_integer_upper {d : ℕ} {α : ℝ} (hα : 0 < α)
    (n : ℕ) (x y : Ambient d) (hne : x ≠ y) :
    gaussianPotential α x y ≤ ENNReal.ofReal (1 + (n.factorial : ℝ) / α ^ n) *
      rieszPotential (n : ℝ) x y := by
  have hB : 0 ≤ 1 + (n.factorial : ℝ) / α ^ n := by positivity
  have heq : rieszPotential (n : ℝ) x y = ENNReal.ofReal (‖x - y‖ ^ (-(n : ℝ))) := by
    unfold rieszPotential
    rw [dist_eq_norm]
    exact ENNReal.ofReal_rpow_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  rw [heq, ← ENNReal.ofReal_mul hB]
  exact ENNReal.ofReal_le_ofReal (gaussianKernel_riesz_integer_upper hα n (x - y)
    (sub_ne_zero.mpr hne))

theorem gaussian_lattice_energy_upper_of_riesz {d : ℕ} {α : ℝ} (hα : 0 < α)
    (Λ : Set (Ambient d)) (n : ℕ) :
    latticePotentialEnergy Λ (gaussianPotential α) ≤
      ENNReal.ofReal (1 + (n.factorial : ℝ) / α ^ n) * latticeRieszEnergy Λ (n : ℝ) := by
  unfold latticePotentialEnergy latticeRieszEnergy
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro y
  by_cases hy : (y : Ambient d) = 0
  · simp [hy]
  · simp only [if_neg hy]
    exact gaussianPotential_riesz_integer_upper (d := d) hα n (0 : Ambient d)
      (y : Ambient d) (Ne.symm hy)

theorem gaussian_lattice_energy_ne_top_of_riesz {d : ℕ} {α : ℝ} (hα : 0 < α)
    (Λ : Set (Ambient d)) (n : ℕ) (hfinite : latticeRieszEnergy Λ (n : ℝ) ≠ ∞) :
    latticePotentialEnergy Λ (gaussianPotential α) ≠ ∞ := by
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite)
    (gaussian_lattice_energy_upper_of_riesz hα Λ n)

theorem e8_gaussian_lattice_energy_ne_top {α : ℝ} (hα : 0 < α) :
    latticePotentialEnergy e8Set (gaussianPotential α) ≠ ∞ :=
  gaussian_lattice_energy_ne_top_of_riesz hα e8Set 9
    (e8_latticeRieszEnergy_ne_top (by norm_num))

theorem leech_gaussian_lattice_energy_ne_top {α : ℝ} (hα : 0 < α) :
    latticePotentialEnergy leechSet (gaussianPotential α) ≠ ∞ :=
  gaussian_lattice_energy_ne_top_of_riesz hα leechSet 25
    (leech_latticeRieszEnergy_ne_top (by norm_num))

end E8Leech
