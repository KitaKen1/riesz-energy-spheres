import FCDefinitionBridge
import FCBackgroundBridge
import FCE8CoefficientBridge
import Riesz.SphereOptimalMain24
import Riesz.SphereMain8

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RieszSphereFC
open SphericalRiesz

theorem riesz_energy_lattice.variants.dimension_two {s : ℝ}
    (hs : -2 < s) (hsd : s < 2) (hs0 : s ≠ 0) :
    Tendsto (fun N : ℕ =>
      (rieszEnergy 2 s N - rieszBackground 2 s * (N : ℝ) ^ 2) /
        (N : ℝ) ^ (1 + s / 2))
      atTop (𝓝 (area 2 ^ (-s / 2) * (epstein 2 (latticeTheta 2) s).re)) := by
  rw [rieszBackground_two_eq hsd, area_eq, sphereArea2_univ_real,
    epstein_two_eq_of_ne_zero (by exact_mod_cast hs0)]
  rcases lt_or_gt_of_ne hs0 with hn | hp
  · simp only [rieszEnergy_eq_max hn, uniform_eq]
    change Tendsto (normalizedMaximumRieszEnergyD 2 s) atTop _
    simpa only [rieszEnergy_eq_max hn, normalizedMaximumRieszEnergyD,
      continuousRieszEnergyD, uniform_eq, Nat.cast_ofNat, neg_div,
      Complex.ofReal_div, Complex.ofReal_ofNat] using
      sphere2_maximum_riesz_tendsto hs hn
  · simp only [rieszEnergy_eq_min hp.le, uniform_eq]
    change Tendsto (normalizedMinimumRieszEnergyD 2 s) atTop _
    simpa only [rieszEnergy_eq_min hp.le, normalizedMinimumRieszEnergyD,
      continuousRieszEnergyD, uniform_eq, Nat.cast_ofNat, neg_div,
      Complex.ofReal_div, Complex.ofReal_ofNat] using
      sphere2_minimum_riesz_tendsto hp hsd

theorem riesz_energy_lattice.variants.dimension_eight {s : ℝ}
    (hs : -2 < s) (hsd : s < 8) (hs0 : s ≠ 0) :
    Tendsto (fun N : ℕ =>
      (rieszEnergy 8 s N - rieszBackground 8 s * (N : ℝ) ^ 2) /
        (N : ℝ) ^ (1 + s / 8))
      atTop (𝓝 (area 8 ^ (-s / 8) * (epstein 8 (latticeTheta 8) s).re)) := by
  rw [rieszBackground_eight_eq hsd, area_eq, sphereAreaD_eight]
  rcases lt_or_gt_of_ne hs0 with hn | hp
  · rw [epstein_eight_eq_candidate_neg hs hn]
    simp only [rieszEnergy_eq_max hn, uniform_eq]
    change Tendsto (normalizedMaximumRieszEnergyD 8 s) atTop _
    simpa only [rieszEnergy_eq_max hn, normalizedMaximumRieszEnergyD,
      continuousRieszEnergyD, uniform_eq, Nat.cast_ofNat, neg_div] using
      sphere8_maximum_riesz_tendsto_unconditional hs hn
  · by_cases htwo : s = 2
    · subst s
      simp only [Complex.ofReal_ofNat]
      rw [epstein_eight_at_two]
      have hc : (120 * deriv riemannZeta (-2) : ℂ).re =
          120 * (deriv riemannZeta (-2)).re := by norm_num [Complex.mul_re]
      rw [hc]
      simp only [rieszEnergy_eq_min (by norm_num : (0 : ℝ) ≤ 2), uniform_eq]
      change Tendsto (normalizedMinimumRieszEnergyD 8 2) atTop _
      simpa only [rieszEnergy_eq_min (by norm_num : (0 : ℝ) ≤ 2),
        normalizedMinimumRieszEnergyD, continuousRieszEnergyD, uniform_eq,
        Nat.cast_ofNat, neg_div, Complex.mul_re, Complex.natCast_re,
        Complex.natCast_im, RCLike.ofNat_re, RCLike.ofNat_im, zero_mul, sub_zero] using
        sphere8_minimum_riesz_two_tendsto_unconditional
    · rw [epstein_eight_eq_candidate_pos hp hsd htwo]
      simp only [rieszEnergy_eq_min hp.le, uniform_eq]
      change Tendsto (normalizedMinimumRieszEnergyD 8 s) atTop _
      simpa only [rieszEnergy_eq_min hp.le, normalizedMinimumRieszEnergyD,
        continuousRieszEnergyD, uniform_eq, Nat.cast_ofNat, neg_div] using
        sphere8_minimum_riesz_tendsto_epstein_unconditional hp hsd htwo

theorem riesz_energy_lattice.variants.dimension_twenty_four {s : ℝ}
    (hs : -2 < s) (hsd : s < 24) (hs0 : s ≠ 0) :
    Tendsto (fun N : ℕ =>
      (rieszEnergy 24 s N - rieszBackground 24 s * (N : ℝ) ^ 2) /
        (N : ℝ) ^ (1 + s / 24))
      atTop (𝓝 (area 24 ^ (-s / 24) * (epstein 24 (latticeTheta 24) s).re)) := by
  rw [rieszBackground_twenty_four_eq hsd, area_eq,
    epstein_twenty_four_eq_of_ne_zero (by exact_mod_cast hs0)]
  rcases lt_or_gt_of_ne hs0 with hn | hp
  · simp only [rieszEnergy_eq_max hn, uniform_eq]
    change Tendsto (normalizedMaximumRieszEnergyD 24 s) atTop _
    simpa only [rieszEnergy_eq_max hn, normalizedMaximumRieszEnergyD,
      continuousRieszEnergyD, uniform_eq, Nat.cast_ofNat, neg_div,
      Complex.ofReal_div, Complex.ofReal_ofNat] using
      sphere24_maximum_riesz_tendsto_unconditional hs hn
  · simp only [rieszEnergy_eq_min hp.le, uniform_eq]
    change Tendsto (normalizedMinimumRieszEnergyD 24 s) atTop _
    simpa only [rieszEnergy_eq_min hp.le, normalizedMinimumRieszEnergyD,
      continuousRieszEnergyD, uniform_eq, Nat.cast_ofNat, neg_div,
      Complex.ofReal_div, Complex.ofReal_ofNat] using
      sphere24_minimum_riesz_tendsto_unconditional hp hsd

theorem log_energy_lattice.variants.dimension_two :
    let W := ∫ p : Sphere 2 × Sphere 2, -Real.log (dist p.1 p.2)
      ∂((uniform 2).prod (uniform 2))
    Tendsto (fun N : ℕ =>
      (logEnergy 2 N - W * (N : ℝ) ^ 2 + (N : ℝ) / 2 * Real.log N) / (N : ℝ))
      atTop (𝓝 ((deriv (epstein 2 (latticeTheta 2)) 0).re +
        (1 / 2) * Real.log (area 2))) := by
  dsimp only
  rw [epstein_two_deriv_re, area_eq, sphereArea2_univ_real]
  simp only [logEnergy_eq, uniform_eq]
  change Tendsto (normalizedMinimumLogEnergyD 2) atTop _
  simpa only [logEnergy_eq, normalizedMinimumLogEnergyD, continuousLogEnergyD,
    uniform_eq, Nat.cast_ofNat] using sphere2_minimum_log_tendsto

theorem log_energy_lattice.variants.dimension_eight :
    let W := ∫ p : Sphere 8 × Sphere 8, -Real.log (dist p.1 p.2)
      ∂((uniform 8).prod (uniform 8))
    Tendsto (fun N : ℕ =>
      (logEnergy 8 N - W * (N : ℝ) ^ 2 + (N : ℝ) / 8 * Real.log N) / (N : ℝ))
      atTop (𝓝 ((deriv (epstein 8 (latticeTheta 8)) 0).re +
        (1 / 8) * Real.log (area 8))) := by
  dsimp only
  rw [epstein_eight_deriv_re, area_eq, sphereAreaD_eight,
    ← sphereLogCoefficient8_eq_epstein, sphereLogCoefficient8_eq_zeta]
  simp only [logEnergy_eq, uniform_eq]
  change Tendsto (normalizedMinimumLogEnergyD 8) atTop _
  simpa only [logEnergy_eq, normalizedMinimumLogEnergyD, continuousLogEnergyD,
    uniform_eq, Nat.cast_ofNat] using sphere8_minimum_log_tendsto_unconditional

theorem log_energy_lattice.variants.dimension_twenty_four :
    let W := ∫ p : Sphere 24 × Sphere 24, -Real.log (dist p.1 p.2)
      ∂((uniform 24).prod (uniform 24))
    Tendsto (fun N : ℕ =>
      (logEnergy 24 N - W * (N : ℝ) ^ 2 + (N : ℝ) / 24 * Real.log N) / (N : ℝ))
      atTop (𝓝 ((deriv (epstein 24 (latticeTheta 24)) 0).re +
        (1 / 24) * Real.log (area 24))) := by
  dsimp only
  rw [epstein_twenty_four_deriv_re, area_eq]
  simp only [logEnergy_eq, uniform_eq]
  change Tendsto (normalizedMinimumLogEnergyD 24) atTop _
  simpa only [logEnergy_eq, normalizedMinimumLogEnergyD, continuousLogEnergyD,
    uniform_eq, Nat.cast_ofNat] using sphere24_minimum_log_tendsto_unconditional

theorem cap_discrepancy_lattice.variants.dimension_two :
    Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2 + 1 / 4) *
      sInf (range fun X : Fin N ↪ Sphere 2 => capDiscrepancy 2 X))
      atTop (𝓝 (Real.sqrt (-(1 / 4 : ℝ) * area 2 ^ ((1 : ℝ) / 2) *
        (epstein 2 (latticeTheta 2) (-1)).re))) := by
  rw [epstein_two_eq_of_ne_zero (by norm_num), area_eq]
  simpa only [capDiscrepancy_two_eq, minimumCapDiscrepancy2,
    sphereCapDiscrepancyConst2, neg_mul, mul_neg, mul_assoc, Complex.ofReal_div,
    Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat] using
    sphere2_minimum_cap_discrepancy_tendsto

theorem cap_discrepancy_lattice.variants.dimension_eight :
    Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2 + 1 / 16) *
      sInf (range fun X : Fin N ↪ Sphere 8 => capDiscrepancy 8 X))
      atTop (𝓝 (Real.sqrt (-(35 / 256 : ℝ) * area 8 ^ ((1 : ℝ) / 8) *
        (epstein 8 (latticeTheta 8) (-1)).re))) := by
  have h := epstein_eight_eq_candidate_neg (s := -1) (by norm_num) (by norm_num)
  norm_num only [Complex.ofReal_neg, Complex.ofReal_one] at h
  rw [h, area_eq,
    sphereAreaD_eight]
  simpa only [capDiscrepancy_eight_eq, minimumCapDiscrepancy8,
    sphereCapDiscrepancyConst8, neg_mul, mul_neg, mul_assoc, neg_div,
    Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
    sphere8_minimum_cap_discrepancy_tendsto_unconditional

theorem cap_discrepancy_lattice.variants.dimension_twenty_four :
    Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2 + 1 / 48) *
      sInf (range fun X : Fin N ↪ Sphere 24 => capDiscrepancy 24 X))
      atTop (𝓝 (Real.sqrt (-(676039 / 8388608 : ℝ) * area 24 ^ ((1 : ℝ) / 24) *
        (epstein 24 (latticeTheta 24) (-1)).re))) := by
  rw [epstein_twenty_four_eq_of_ne_zero (by norm_num), area_eq]
  simpa only [capDiscrepancy_twenty_four_eq, minimumCapDiscrepancy24,
    sphereCapDiscrepancyConst24, neg_mul, mul_neg, mul_assoc, Complex.ofReal_div,
    Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat] using
    sphere24_minimum_cap_discrepancy_tendsto_unconditional

end RieszSphereFC
