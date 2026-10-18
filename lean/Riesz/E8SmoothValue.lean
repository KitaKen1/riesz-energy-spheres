import Riesz.E8MellinContinuation
import Riesz.SphereArea8

/-!
# The value of the actual E8 smooth regularization

The integral, not just an abstract continuation candidate, equals -5 pi² / 6.
The positive-part cutoff has the same limit. The lattice heat-sum identity
and the weighted spherical cell-defect comparison remain open.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace SphericalRiesz

theorem e8ThetaFEPair_modified_weighted_ae :
    (fun t : ℝ => (t : ℂ)*e8ThetaFEPair.f_modif t) =ᵐ[volume.restrict (Ioi 0)]
      (fun t : ℝ => (t : ℂ)*e8ThetaRegularized t +
        (Ioo 0 1).indicator (fun t : ℝ => (t : ℂ)) t +
        (Ioi 1).indicator (fun t : ℝ => ((t^(-(3 : ℝ)) : ℝ) : ℂ)) t) := by
  have hne : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), t ≠ 1 := by
    apply Filter.Eventually.mono (compl_mem_ae_iff.mpr (measure_singleton (1 : ℝ)) :
      ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), t ∈ ({1} : Set ℝ)ᶜ)
    intro t ht
    simpa using ht
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hne] with t ht ht1
  have ht0 : 0 < t := ht
  simp only [WeakFEPair.f_modif, e8ThetaFEPair, one_mul, smul_eq_mul, mul_one, Pi.add_apply]
  rcases lt_or_gt_of_ne ht1 with hsmall | hlarge
  · rw [indicator_of_notMem (show t ∉ Ioi 1 by simpa using hsmall.le),
      indicator_of_mem (show t ∈ Ioo 0 1 from ⟨ht0, hsmall⟩),
      indicator_of_mem (show t ∈ Ioo 0 1 from ⟨ht0, hsmall⟩),
      indicator_of_notMem (show t ∉ Ioi 1 by simpa using hsmall.le)]
    simp only [zero_add, add_zero, Real.rpow_neg ht0.le, Real.rpow_ofNat,
      Complex.ofReal_inv, Complex.ofReal_pow]
    unfold e8ThetaRegularized e8ThetaTail
    ring
  · rw [indicator_of_mem (show t ∈ Ioi 1 from hlarge),
      indicator_of_notMem (notMem_Ioo_of_ge hlarge.le),
      indicator_of_notMem (notMem_Ioo_of_ge hlarge.le),
      indicator_of_mem (show t ∈ Ioi 1 from hlarge)]
    rw [e8ThetaRegularized_weighted_decomposition ht0]
    unfold e8ThetaTail
    ring

theorem e8ThetaCompleted_two_eq_integral :
    e8ThetaCompleted 2 = ∫ t : ℝ in Ioi 0, (t : ℂ)*e8ThetaRegularized t := by
  have hsmall : IntegrableOn (fun t : ℝ => (t : ℂ)) (Ioo 0 1) :=
    (Complex.continuous_ofReal.integrableOn_Icc (a := 0) (b := 1)).mono_set Ioo_subset_Icc_self
  have hlarge := (integrableOn_Ioi_rpow_of_lt (a := -(3 : ℝ)) (c := 1)
    (by norm_num) (by norm_num)).ofReal (𝕜 := ℂ)
  have hs := (hsmall.integrable_indicator measurableSet_Ioo).integrableOn (s := Ioi 0)
  have hl := (hlarge.integrable_indicator measurableSet_Ioi).integrableOn (s := Ioi 0)
  have Ismall : (∫ t : ℝ in Ioi 0, (Ioo 0 1).indicator (fun t : ℝ => (t : ℂ)) t) = 1/2 := by
    rw [setIntegral_indicator measurableSet_Ioo, inter_eq_right.mpr Ioo_subset_Ioi_self,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_ofReal, integral_id]
    norm_num
  have Ilarge : (∫ t : ℝ in Ioi 0,
      (Ioi 1).indicator (fun t : ℝ => ((t^(-(3 : ℝ)) : ℝ) : ℂ)) t) = 1/2 := by
    rw [setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))]
    exact e8Theta_background_integral
  have hm : mellin e8ThetaFEPair.f_modif (2 : ℂ) =
      (∫ t : ℝ in Ioi 0, (t : ℂ)*e8ThetaRegularized t) + 1 := by
    unfold mellin
    simp only [show (2 : ℂ)-1 = 1 by norm_num, Complex.cpow_one, smul_eq_mul]
    rw [integral_congr_ae e8ThetaFEPair_modified_weighted_ae]
    calc
      _ = (∫ t : ℝ in Ioi 0, (t : ℂ)*e8ThetaRegularized t +
            (Ioo 0 1).indicator (fun t : ℝ => (t : ℂ)) t) +
          ∫ t : ℝ in Ioi 0,
            (Ioi 1).indicator (fun t : ℝ => ((t^(-(3 : ℝ)) : ℝ) : ℂ)) t :=
        integral_add (e8ThetaRegularized_weighted_integrable.add hs) hl
      _ = ((∫ t : ℝ in Ioi 0, (t : ℂ)*e8ThetaRegularized t) +
          ∫ t : ℝ in Ioi 0, (Ioo 0 1).indicator (fun t : ℝ => (t : ℂ)) t) +
          ∫ t : ℝ in Ioi 0,
            (Ioi 1).indicator (fun t : ℝ => ((t^(-(3 : ℝ)) : ℝ) : ℂ)) t :=
        congrArg (· + (∫ t : ℝ in Ioi 0,
          (Ioi 1).indicator (fun t : ℝ => ((t^(-(3 : ℝ)) : ℝ) : ℂ)) t))
            (integral_add e8ThetaRegularized_weighted_integrable hs)
      _ = _ := by rw [Ismall, Ilarge]; ring
  change mellin e8ThetaFEPair.f_modif 2 - (1/(2 : ℂ))*1 - (1/(4-2 : ℂ))*1 = _
  rw [hm]
  ring

theorem e8SmoothEnergy_value : e8SmoothEnergy = -(5*(Real.pi : ℂ)^2/6) := by
  unfold e8SmoothEnergy
  rw [← e8ThetaCompleted_two_eq_integral, e8ThetaCompleted_at_two]
  ring

theorem e8SmoothCutoffEnergy_limit_value :
    Tendsto e8SmoothCutoffEnergy (𝓝[>] (0 : ℝ)) (𝓝 (-(5*(Real.pi : ℂ)^2/6))) := by
  rw [← e8SmoothEnergy_value]
  exact e8SmoothCutoffEnergy_tendsto

theorem e8SmoothEnergy_real_value : e8SmoothEnergy.re = -5*Real.pi^2/6 := by
  rw [e8SmoothEnergy_value]
  norm_num [Complex.div_ofReal_re, ← Complex.ofReal_pow] <;> ring

/-- This is the area normalization of the checked integral. The spherical
asymptotic theorem still needs the sharp lower bound and cell comparison. -/
theorem predictedCoefficient_eq_smoothEnergy :
    predictedCoefficient = e8SmoothEnergy.re / Real.sqrt (sphereArea8.real univ) := by
  rw [e8SmoothEnergy_real_value]
  exact predictedCoefficient_area_normalization

#print axioms e8ThetaFEPair_modified_weighted_ae
#print axioms e8ThetaCompleted_two_eq_integral
#print axioms e8SmoothEnergy_value
#print axioms e8SmoothCutoffEnergy_limit_value
#print axioms e8SmoothEnergy_real_value
#print axioms predictedCoefficient_eq_smoothEnergy

end SphericalRiesz
