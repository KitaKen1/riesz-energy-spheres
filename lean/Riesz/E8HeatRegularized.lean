import Riesz.E8HeatLattice

/-!
# The actual E8 Gaussian heat regularization

The unchanged inverse-fourth lattice sum, damped by exp(-pi epsilon norm²),
minus pi²/(6 epsilon²), equals the already checked cutoff theta integral.
Its limit is -5 pi²/6. Comparison with weighted spherical cell defects remains
an independent proof obligation.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace SphericalRiesz

theorem e8HeatBackground_decomposition (ε : ℝ) {t : ℝ} (ht : 0 < t) :
    ((t-ε : ℝ) : ℂ)*((t : ℂ)^4)⁻¹ =
      ((t^(-(3 : ℝ)) : ℝ) : ℂ) - (ε : ℂ)*((t^(-(4 : ℝ)) : ℝ) : ℂ) := by
  have ht0 := Complex.ofReal_ne_zero.mpr ht.ne'
  rw [Real.rpow_neg ht.le, Real.rpow_ofNat, Real.rpow_neg ht.le, Real.rpow_ofNat]
  push_cast
  field_simp

theorem e8HeatBackground_integrable {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => ((t-ε : ℝ) : ℂ)*((t : ℂ)^4)⁻¹) (Ioi ε) := by
  have h3 := (integrableOn_Ioi_rpow_of_lt (a := -(3 : ℝ)) (by norm_num) hε).ofReal (𝕜 := ℂ)
  have h4 := (integrableOn_Ioi_rpow_of_lt (a := -(4 : ℝ)) (by norm_num) hε).ofReal (𝕜 := ℂ)
  apply (h3.sub (h4.const_mul (ε : ℂ))).congr_fun _ measurableSet_Ioi
  intro t ht
  change ((t^(-(3 : ℝ)) : ℝ) : ℂ) - (ε : ℂ)*((t^(-(4 : ℝ)) : ℝ) : ℂ) = _
  exact (e8HeatBackground_decomposition ε (hε.trans ht)).symm

theorem e8HeatBackground_integral {ε : ℝ} (hε : 0 < ε) :
    (∫ t : ℝ in Ioi ε, ((t-ε : ℝ) : ℂ)*((t : ℂ)^4)⁻¹) = 1/(6*(ε : ℂ)^2) := by
  have h3 := integrableOn_Ioi_rpow_of_lt (a := -(3 : ℝ)) (by norm_num) hε
  have h4 := integrableOn_Ioi_rpow_of_lt (a := -(4 : ℝ)) (by norm_num) hε
  calc
    _ = ∫ t : ℝ in Ioi ε, ((t^(-(3 : ℝ)) - ε*t^(-(4 : ℝ)) : ℝ) : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      simpa only [Complex.ofReal_sub, Complex.ofReal_mul] using
        e8HeatBackground_decomposition ε (hε.trans ht)
    _ = _ := by
      rw [integral_complex_ofReal, integral_sub h3 (h4.const_mul ε), integral_const_mul,
        integral_Ioi_rpow_of_lt (by norm_num : -(3 : ℝ) < -1) hε,
        integral_Ioi_rpow_of_lt (by norm_num : -(4 : ℝ) < -1) hε]
      norm_num [Real.rpow_neg hε.le, Real.rpow_ofNat]
      push_cast
      field_simp
      ring

theorem e8ThetaRegularized_shifted_integrable {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => ((t-ε : ℝ) : ℂ)*e8ThetaRegularized t) (Ioi ε) := by
  have hbase := e8ThetaRegularized_weighted_integrable.mono_set (Ioi_subset_Ioi hε.le)
  apply MeasureTheory.Integrable.mono hbase
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    exact (show ContinuousOn (fun t : ℝ => ((t-ε : ℝ) : ℂ)) (Ioi ε) by fun_prop).mul
      (e8ThetaRegularized_continuousOn.mono (Ioi_subset_Ioi hε.le))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htε : ε < t := ht
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (sub_pos.mpr htε), abs_of_pos (hε.trans htε)]
    exact mul_le_mul_of_nonneg_right (sub_le_self _ hε.le) (norm_nonneg _)

theorem e8ThetaTail_shifted_integrable {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => ((t-ε : ℝ) : ℂ)*e8ThetaTail t) (Ioi ε) := by
  apply ((e8ThetaRegularized_shifted_integrable hε).add
    (e8HeatBackground_integrable hε)).congr_fun _ measurableSet_Ioi
  intro t _
  change ((t-ε : ℝ) : ℂ)*e8ThetaRegularized t +
    ((t-ε : ℝ) : ℂ)*((t : ℂ)^4)⁻¹ = _
  unfold e8ThetaRegularized
  ring

theorem e8SmoothCutoffEnergy_eq_tail_integral {ε : ℝ} (hε : 0 < ε) :
    e8SmoothCutoffEnergy ε = (Real.pi : ℂ)^2 *
      ∫ t : ℝ in Ioi ε, ((t-ε : ℝ) : ℂ)*e8ThetaRegularized t := by
  unfold e8SmoothCutoffEnergy
  congr 1
  calc
    _ = ∫ t : ℝ in Ioi 0, (Ioi ε).indicator
        (fun t : ℝ => ((t-ε : ℝ) : ℂ)*e8ThetaRegularized t) t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp only
      by_cases ht : ε < t
      · rw [max_eq_left (sub_nonneg.mpr ht.le),
          indicator_of_mem (show t ∈ Ioi ε from ht), Complex.real_smul]
      · rw [max_eq_right (sub_nonpos.mpr (le_of_not_gt ht)),
          indicator_of_notMem (show t ∉ Ioi ε from ht)]
        simp
    _ = _ := by rw [setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi hε.le)]

theorem e8SmoothCutoffEnergy_eq_heat {ε : ℝ} (hε : 0 < ε) :
    e8SmoothCutoffEnergy ε = (e8HeatEnergy ε : ℂ) - (Real.pi : ℂ)^2/(6*(ε : ℂ)^2) := by
  have h : (∫ t : ℝ in Ioi ε, ((t-ε : ℝ) : ℂ)*e8ThetaRegularized t) =
      (∫ t : ℝ in Ioi ε, ((t-ε : ℝ) : ℂ)*e8ThetaTail t) -
      ∫ t : ℝ in Ioi ε, ((t-ε : ℝ) : ℂ)*((t : ℂ)^4)⁻¹ := by
    calc
      _ = ∫ t : ℝ in Ioi ε, ((t-ε : ℝ) : ℂ)*e8ThetaTail t -
          ((t-ε : ℝ) : ℂ)*((t : ℂ)^4)⁻¹ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t _
        unfold e8ThetaRegularized
        ring
      _ = _ := integral_sub (e8ThetaTail_shifted_integrable hε) (e8HeatBackground_integrable hε)
  rw [e8SmoothCutoffEnergy_eq_tail_integral hε, h, e8HeatBackground_integral hε,
    mul_sub, ← e8HeatEnergy_cast_eq_tail_integral hε]
  ring

def e8HeatRegularizedEnergy (ε : ℝ) : ℝ := e8HeatEnergy ε - Real.pi^2/(6*ε^2)

theorem e8HeatRegularizedEnergy_cast {ε : ℝ} (hε : 0 < ε) :
    (e8HeatRegularizedEnergy ε : ℂ) = e8SmoothCutoffEnergy ε := by
  unfold e8HeatRegularizedEnergy
  push_cast
  exact (e8SmoothCutoffEnergy_eq_heat hε).symm

theorem e8HeatRegularizedEnergy_limit :
    Tendsto e8HeatRegularizedEnergy (𝓝[>] (0 : ℝ)) (𝓝 (-5*Real.pi^2/6)) := by
  have h := (Complex.continuous_re.tendsto e8SmoothEnergy).comp e8SmoothCutoffEnergy_tendsto
  rw [e8SmoothEnergy_real_value] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change (e8SmoothCutoffEnergy ε).re = e8HeatRegularizedEnergy ε
  rw [← e8HeatRegularizedEnergy_cast hε, Complex.ofReal_re]

theorem e8HeatRegularizedEnergy_normalized_limit :
    Tendsto (fun ε : ℝ => e8HeatRegularizedEnergy ε / Real.sqrt (sphereArea8.real univ))
      (𝓝[>] (0 : ℝ)) (𝓝 predictedCoefficient) := by
  rw [predictedCoefficient_area_normalization]
  exact e8HeatRegularizedEnergy_limit.div_const _

#print axioms e8HeatBackground_decomposition
#print axioms e8HeatBackground_integrable
#print axioms e8HeatBackground_integral
#print axioms e8ThetaRegularized_shifted_integrable
#print axioms e8ThetaTail_shifted_integrable
#print axioms e8SmoothCutoffEnergy_eq_tail_integral
#print axioms e8SmoothCutoffEnergy_eq_heat
#print axioms e8HeatRegularizedEnergy_cast
#print axioms e8HeatRegularizedEnergy_limit
#print axioms e8HeatRegularizedEnergy_normalized_limit

end SphericalRiesz
