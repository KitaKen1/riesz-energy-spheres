import Riesz.E8SmoothValue
import Riesz.E8HeatLattice

/-! The actual E8 Gaussian theta sum as a real, integrable sharp target
profile. The original integer basis and Gaussian normalization are retained.
Its weighted integral is -5/6. No spherical profile lower is asserted. -/

set_option autoImplicit false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace SphericalRiesz

def e8GaussianThetaReal8 (α : ℝ) : ℝ := (e8ThetaImag α).re

def e8GaussianRieszProfile8 (α : ℝ) : ℝ :=
  α*(e8GaussianThetaReal8 α-(α^4)⁻¹-1)

theorem e8GaussianThetaReal8_hasSum {α : ℝ} (hα : 0 < α) :
    HasSum (fun z : Fin 8 → ℤ => Real.exp (-Real.pi*‖e8EuclideanPoint z‖^2*α))
      (e8GaussianThetaReal8 α) := by
  have h := Complex.hasSum_re
    (e8Theta_hasSum (τ := (α:ℂ)*Complex.I) (by simpa using hα))
  apply h.congr_fun
  intro z
  have he : (Real.pi:ℂ)*Complex.I*(‖e8EuclideanPoint z‖^2:ℝ)*((α:ℂ)*Complex.I) =
      ((-Real.pi*‖e8EuclideanPoint z‖^2*α:ℝ):ℂ) := by
    push_cast
    ring_nf
    simp [Complex.I_sq]
  rw [he,Complex.exp_ofReal_re]

theorem e8GaussianThetaReal8_eq_tsum {α : ℝ} (hα : 0 < α) :
    e8GaussianThetaReal8 α =
      ∑' z : Fin 8 → ℤ, Real.exp (-Real.pi*‖e8EuclideanPoint z‖^2*α) :=
  (e8GaussianThetaReal8_hasSum hα).tsum_eq.symm

theorem e8GaussianThetaReal8_ge_one {α : ℝ} (hα : 0 < α) :
    1 ≤ e8GaussianThetaReal8 α := by
  have h : 0 ≤ (e8ThetaTail α).re := by
    rw [← (e8ThetaTail_real_gaussian_hasSum hα).tsum_eq]
    apply tsum_nonneg
    intro z
    split_ifs <;> positivity
  simpa only [e8ThetaTail,Complex.sub_re,Complex.one_re,sub_nonneg,e8GaussianThetaReal8]
    using h

theorem e8GaussianRieszProfile8_eq_re (α : ℝ) :
    e8GaussianRieszProfile8 α = ((α:ℂ)*e8ThetaRegularized α).re := by
  simp only [e8GaussianRieszProfile8,e8GaussianThetaReal8,e8ThetaRegularized,e8ThetaTail,
    ← Complex.ofReal_pow,← Complex.ofReal_inv,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,Complex.sub_re,Complex.one_re,mul_zero,sub_zero]
  ring

theorem e8GaussianRieszProfile8_continuousOn :
    ContinuousOn e8GaussianRieszProfile8 (Ioi 0) := by
  have h := Complex.continuous_re.comp_continuousOn
    (Complex.continuous_ofReal.continuousOn.mul e8ThetaRegularized_continuousOn)
  simpa only [Function.comp_def,Pi.mul_apply,← e8GaussianRieszProfile8_eq_re] using h

theorem e8GaussianRieszProfile8_integrable :
    IntegrableOn e8GaussianRieszProfile8 (Ioi 0) := by
  have h := e8ThetaRegularized_weighted_integrable.re
  apply h.congr_fun _ measurableSet_Ioi
  intro α _
  exact (e8GaussianRieszProfile8_eq_re α).symm

theorem e8GaussianRieszProfile8_integral :
    (∫ α : ℝ in Ioi 0, e8GaussianRieszProfile8 α) = -5/6 := by
  have he : e8GaussianRieszProfile8 =
      (fun α : ℝ => ((α:ℂ)*e8ThetaRegularized α).re) := by
    ext α
    exact e8GaussianRieszProfile8_eq_re α
  have h := integral_re e8ThetaRegularized_weighted_integrable
  change (∫ α : ℝ in Ioi 0, ((α:ℂ)*e8ThetaRegularized α).re) =
    (∫ α : ℝ in Ioi 0, (α:ℂ)*e8ThetaRegularized α).re at h
  rw [he]
  change (∫ α : ℝ in Ioi 0, ((α:ℂ)*e8ThetaRegularized α).re) = -5/6
  rw [h,← e8ThetaCompleted_two_eq_integral,e8ThetaCompleted_at_two]
  norm_num

end SphericalRiesz
