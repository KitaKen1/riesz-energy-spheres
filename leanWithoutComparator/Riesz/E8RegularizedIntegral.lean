import Riesz.E8Regularized
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Symmetric integral and removal of a smooth cutoff

Poisson symmetry replaces the integral near zero by a second copy of the
exponentially decaying tail on `(1,infinity)`. Dominated convergence removes
the positive-part cutoff. Identification with the lattice heat sum and the
Epstein continuation remains a separate obligation.
-/

set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace SphericalRiesz

theorem e8ThetaRegularized_transform {t : ℝ} (ht : 0 < t) :
    e8ThetaRegularized t⁻¹ = (t : ℂ)^4 * e8ThetaRegularized t := by
  have h0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  unfold e8ThetaRegularized e8ThetaTail
  rw [e8ThetaImag_transform ht]
  simp only [Complex.ofReal_inv, inv_pow]
  field_simp
  ring

theorem e8ThetaRegularized_weighted_inv {t : ℝ} (ht : 0 < t) :
    (t^(-(2 : ℝ))) • ((t⁻¹ : ℝ) : ℂ) * e8ThetaRegularized t⁻¹ =
      (t : ℂ)*e8ThetaRegularized t := by
  rw [e8ThetaRegularized_transform ht, Real.rpow_neg ht.le, Real.rpow_ofNat]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow]
  field_simp

theorem e8ThetaRegularized_small_eq_large :
    (∫ t : ℝ in Ioo 0 1, (t : ℂ)*e8ThetaRegularized t) =
      ∫ t : ℝ in Ioi 1, (t : ℂ)*e8ThetaRegularized t := by
  let f : ℝ → ℂ := fun t => (t : ℂ)*e8ThetaRegularized t
  let g : ℝ → ℂ := (Ioi 1).indicator f
  have h := integral_comp_rpow_Ioi g (p := -1) (by norm_num)
  have hleft : (∫ t : ℝ in Ioi 0, (|-1| * t^((-1 : ℝ)-1)) • g (t^(-1 : ℝ))) =
      ∫ t : ℝ in Ioo 0 1, f t := by
    calc
      _ = ∫ t : ℝ in Ioi 0, (Ioo 0 1).indicator f t := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        have ht0 : 0 < t := ht
        rw [show (-1 : ℝ)-1 = -2 by norm_num]
        simp only [abs_neg, abs_one, one_mul, Real.rpow_neg_one]
        by_cases ht1 : t < 1
        · rw [show g t⁻¹ = f t⁻¹ from indicator_of_mem ((one_lt_inv₀ ht0).mpr ht1) f,
            show (Ioo (0 : ℝ) 1).indicator f t = f t from
              indicator_of_mem (show t ∈ Ioo (0 : ℝ) 1 from ⟨ht0, ht1⟩) f]
          change (t^(-(2 : ℝ))) • (((t⁻¹ : ℝ) : ℂ)*e8ThetaRegularized t⁻¹) = _
          rw [← smul_mul_assoc]
          exact e8ThetaRegularized_weighted_inv ht0
        · rw [show g t⁻¹ = 0 from indicator_of_notMem
              (by simpa only [mem_Ioi, one_lt_inv₀ ht0] using ht1) f,
            indicator_of_notMem (by simp [ht1])]
          simp
      _ = _ := by rw [setIntegral_indicator measurableSet_Ioo, inter_eq_right.mpr
        (show Ioo (0 : ℝ) 1 ⊆ Ioi 0 from fun _ h => h.1)]
  have hright : (∫ t : ℝ in Ioi 0, g t) = ∫ t : ℝ in Ioi 1, f t := by
    rw [show g = (Ioi 1).indicator f from rfl, setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))]
  exact hleft.symm.trans (h.trans hright)

theorem e8ThetaRegularized_integral_double :
    (∫ t : ℝ in Ioi 0, (t : ℂ)*e8ThetaRegularized t) =
      2 * ∫ t : ℝ in Ioi 1, (t : ℂ)*e8ThetaRegularized t := by
  have h := intervalIntegral.integral_interval_add_Ioi e8ThetaRegularized_weighted_integrable
    (e8ThetaRegularized_weighted_integrable.mono_set
      (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)))
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo, e8ThetaRegularized_small_eq_large] at h
  rw [← h]
  ring

theorem e8ThetaRegularized_weighted_decomposition {t : ℝ} (ht : 0 < t) :
    (t : ℂ)*e8ThetaRegularized t = (t : ℂ)*e8ThetaTail t - (t^(-(3 : ℝ)) : ℝ) := by
  have h0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  unfold e8ThetaRegularized
  rw [Real.rpow_neg ht.le, Real.rpow_ofNat]
  push_cast
  field_simp

theorem e8ThetaTail_weighted_integrable :
    IntegrableOn (fun t : ℝ => (t : ℂ)*e8ThetaTail t) (Ioi 1) := by
  have hψ := e8ThetaRegularized_weighted_integrable.mono_set
    (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  have hp := (integrableOn_Ioi_rpow_of_lt (a := -(3 : ℝ)) (c := 1)
    (by norm_num) (by norm_num)).ofReal (𝕜 := ℂ)
  apply (hψ.add hp).congr_fun _ measurableSet_Ioi
  intro t ht
  change (t : ℂ)*e8ThetaRegularized t + ((t^(-(3 : ℝ)) : ℝ) : ℂ) =
    (t : ℂ)*e8ThetaTail t
  rw [e8ThetaRegularized_weighted_decomposition
    (lt_trans (by norm_num) (show (1 : ℝ) < t from ht))]
  simp

theorem e8Theta_background_integral :
    (∫ t : ℝ in Ioi 1, ((t^(-(3 : ℝ)) : ℝ) : ℂ)) = 1/2 := by
  rw [integral_complex_ofReal, integral_Ioi_rpow_of_lt (by norm_num : -(3 : ℝ) < -1)
    (by norm_num : (0 : ℝ) < 1)]
  norm_num

theorem e8SmoothEnergy_symmetric :
    e8SmoothEnergy = (Real.pi : ℂ)^2 *
      (2 * (∫ t : ℝ in Ioi 1, (t : ℂ)*e8ThetaTail t) - 1) := by
  have hp := (integrableOn_Ioi_rpow_of_lt (a := -(3 : ℝ)) (c := 1)
    (by norm_num) (by norm_num)).ofReal (𝕜 := ℂ)
  unfold e8SmoothEnergy
  rw [e8ThetaRegularized_integral_double]
  have h : (∫ t : ℝ in Ioi 1, (t : ℂ)*e8ThetaRegularized t) =
      (∫ t : ℝ in Ioi 1, (t : ℂ)*e8ThetaTail t) - 1/2 := by
    calc
      _ = ∫ t : ℝ in Ioi 1, (t : ℂ)*e8ThetaTail t - ((t^(-(3 : ℝ)) : ℝ) : ℂ) :=
        setIntegral_congr_fun measurableSet_Ioi
          (fun t ht => e8ThetaRegularized_weighted_decomposition
            (lt_trans (by norm_num) (show (1 : ℝ) < t from ht)))
      _ = _ := (integral_sub e8ThetaTail_weighted_integrable hp).trans
        (congrArg ((∫ t : ℝ in Ioi 1, (t : ℂ)*e8ThetaTail t) - ·)
          e8Theta_background_integral)
  rw [h]
  ring

def e8SmoothCutoffEnergy (ε : ℝ) : ℂ := (Real.pi : ℂ)^2 *
  ∫ t : ℝ in Ioi 0, (max (t-ε) 0 : ℝ) • e8ThetaRegularized t

theorem e8SmoothCutoffEnergy_tendsto :
    Tendsto e8SmoothCutoffEnergy (𝓝[>] (0 : ℝ)) (𝓝 e8SmoothEnergy) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[>] (0 : ℝ))
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun ε t : ℝ => max (t-ε) 0 • e8ThetaRegularized t)
    (f := fun t : ℝ => (t : ℂ)*e8ThetaRegularized t)
    (fun t : ℝ => ‖(t : ℂ)*e8ThetaRegularized t‖) ?_ ?_
    e8ThetaRegularized_weighted_integrable.norm ?_
  · exact h.const_mul ((Real.pi : ℂ)^2)
  · apply Eventually.of_forall
    intro ε
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    exact (show ContinuousOn (fun t : ℝ => max (t-ε) 0) (Ioi 0) by fun_prop).smul
      e8ThetaRegularized_continuousOn
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _), abs_of_pos ht]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact max_le (sub_le_self _ hε.le) ht.le
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hε : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hsub : Tendsto (fun ε : ℝ => t-ε) (𝓝[>] 0) (𝓝 t) := by
      simpa using tendsto_const_nhds.sub hε
    have hmax : Tendsto (fun ε : ℝ => max (t-ε) 0) (𝓝[>] 0) (𝓝 t) := by
      simpa [max_eq_left ht0.le] using
        hsub.max (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0))
    simpa [Complex.real_smul] using hmax.smul_const (e8ThetaRegularized t)

#print axioms e8ThetaRegularized_transform
#print axioms e8ThetaRegularized_weighted_inv
#print axioms e8ThetaRegularized_small_eq_large
#print axioms e8ThetaRegularized_integral_double
#print axioms e8ThetaRegularized_weighted_decomposition
#print axioms e8ThetaTail_weighted_integrable
#print axioms e8Theta_background_integral
#print axioms e8SmoothEnergy_symmetric
#print axioms e8SmoothCutoffEnergy_tendsto

end SphericalRiesz
