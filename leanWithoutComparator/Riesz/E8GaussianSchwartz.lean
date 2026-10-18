import Riesz.E8ThetaSchwartz
import Riesz.E8CoordinateHeat
import Riesz.SchwartzDilation

/-! Actual real Gaussian in the unchanged E8 basis, with a uniform dilation bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped SchwartzMap ContDiff
namespace SphericalRiesz

def e8CoordinateLinearEquiv : (Fin 8 → ℝ) ≃L[ℝ] E8Ambient :=
  e8Basis.equivFun.symm.toContinuousLinearEquiv.trans
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 8 => ℝ)).symm

theorem e8CoordinateLinearEquiv_apply (v : Fin 8 → ℝ) :
    e8CoordinateLinearEquiv v = WithLp.toLp 2 (e8Map v) := rfl

def e8CoordinateGaussianSchwartz : 𝓢((Fin 8 → ℝ), ℝ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ e8CoordinateLinearEquiv
    ((e8ThetaSchwartzKernel Complex.I (by simp)).postcompCLM Complex.reCLM)

theorem e8CoordinateGaussianSchwartz_apply (v : Fin 8 → ℝ) :
    e8CoordinateGaussianSchwartz v = e8CoordinateGaussian 1 v := by
  change (e8ThetaSchwartzKernel Complex.I (by simp) (e8CoordinateLinearEquiv v)).re = _
  rw [e8ThetaSchwartzKernel_apply, e8CoordinateLinearEquiv_apply]
  have hc : (Real.pi : ℂ)*Complex.I*Complex.I*
      ((‖(WithLp.toLp 2 (e8Map v) : E8Ambient)‖^2 : ℝ) : ℂ) =
      ((-Real.pi*‖(WithLp.toLp 2 (e8Map v) : E8Ambient)‖^2 : ℝ) : ℂ) := by
    push_cast
    rw [mul_assoc (Real.pi : ℂ) Complex.I Complex.I, Complex.I_mul_I]
    ring
  rw [hc, ← Complex.ofReal_exp]
  change Real.exp (-Real.pi*‖(WithLp.toLp 2 (e8Map v) : E8Ambient)‖^2) =
    Real.exp (-Real.pi*1*‖(WithLp.toLp 2 (e8Map v) : E8Ambient)‖^2)
  congr 1
  ring

theorem e8CoordinateGaussian_dilation {u : ℝ} (hu : 0 ≤ u) (v : Fin 8 → ℝ) :
    e8CoordinateGaussian u v = e8CoordinateGaussianSchwartz (Real.sqrt u • v) := by
  rw [e8CoordinateGaussianSchwartz_apply]
  unfold e8CoordinateGaussian
  rw [map_smul, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg u), mul_pow, Real.sq_sqrt hu]
  congr 1
  ring

theorem e8CoordinateGaussian_contDiff {u : ℝ} (hu : 0 ≤ u) :
    ContDiff ℝ ∞ (e8CoordinateGaussian u) := by
  have heq : e8CoordinateGaussian u =
      fun v => e8CoordinateGaussianSchwartz (Real.sqrt u • v) :=
    funext (e8CoordinateGaussian_dilation hu)
  rw [heq]
  exact e8CoordinateGaussianSchwartz.smooth'.comp (by fun_prop)

theorem e8CoordinateGaussian_derivatives_uniform (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u → ∀ n : ℕ, n ≤ N →
      ∀ v : Fin 8 → ℝ, δ ≤ ‖v‖ → ‖iteratedFDeriv ℝ n (e8CoordinateGaussian u) v‖ ≤ C := by
  refine ⟨schwartzDilationBound e8CoordinateGaussianSchwartz N δ,
    schwartzDilationBound_nonneg _ N hδ, ?_⟩
  intro u hu n hn v hv
  have heq : e8CoordinateGaussian u =
      fun y => e8CoordinateGaussianSchwartz (Real.sqrt u • y) :=
    funext (e8CoordinateGaussian_dilation hu)
  rw [heq]
  exact schwartzDilation_derivatives_uniform _ N hδ _ (Real.sqrt_nonneg u) v hv n hn

theorem e8CoordinateGaussian_smul (u a : ℝ) (v : Fin 8 → ℝ) :
    e8CoordinateGaussian u (a • v) = e8CoordinateGaussian (u*a^2) v := by
  unfold e8CoordinateGaussian
  rw [map_smul, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  congr 1
  ring

#print axioms e8CoordinateGaussian_smul
#print axioms e8CoordinateLinearEquiv_apply
#print axioms e8CoordinateGaussianSchwartz_apply
#print axioms e8CoordinateGaussian_dilation
#print axioms e8CoordinateGaussian_contDiff
#print axioms e8CoordinateGaussian_derivatives_uniform
end SphericalRiesz
