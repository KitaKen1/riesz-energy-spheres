import Riesz.E8DampedAnnulus

/-! Scaling the actual damped E8 annulus; uniform C/r^10 derivatives. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped ContDiff
namespace SphericalRiesz

def e8ScaledDampedAnnulus (u r : ℝ) (x v : Fin 8 → ℝ) : ℝ :=
  (r⁻¹)^4 * e8UnitDampedAnnulus u (r⁻¹ • (v-x))

theorem e8ScaledDampedAnnulus_contDiff {u : ℝ} (hu : 0 ≤ u) (r : ℝ)
    (x : Fin 8 → ℝ) : ContDiff ℝ ∞ (e8ScaledDampedAnnulus u r x) := by
  unfold e8ScaledDampedAnnulus
  exact contDiff_const.mul ((e8UnitDampedAnnulus_contDiff hu).comp (by fun_prop))

theorem e8ScaledDampedAnnulus_eq_heat (ε r : ℝ) (hr : 0 < r) (x v : Fin 8 → ℝ) :
    e8ScaledDampedAnnulus (ε*r^2) r x v = obliqueRieszFour 8 e8Map x v *
      unitAnnularCutoff 8 (r⁻¹ • (v-x)) * e8CoordinateGaussian ε (v-x) := by
  have hparam : ε*r^2*(r⁻¹)^2 = ε := by field_simp
  calc
    _ = scaledObliqueAnnularRieszFour 8 e8Map r x v *
        e8CoordinateGaussian (ε*r^2) (r⁻¹ • (v-x)) := by
      unfold e8ScaledDampedAnnulus e8UnitDampedAnnulus scaledObliqueAnnularRieszFour
      ring
    _ = _ := by rw [scaledObliqueAnnularRieszFour_eq_kernel 8 e8Map r hr,
      e8CoordinateGaussian_smul, hparam]

theorem e8ScaledDampedAnnulus_sixth_identity {u : ℝ} (hu : 0 ≤ u) (r : ℝ)
    (x v : Fin 8 → ℝ) :
    iteratedFDeriv ℝ 6 (e8ScaledDampedAnnulus u r x) v =
      (r⁻¹)^10 • iteratedFDeriv ℝ 6 (e8UnitDampedAnnulus u) (r⁻¹ • (v-x)) := by
  have hf : ContDiff ℝ 6 (e8UnitDampedAnnulus u) :=
    (e8UnitDampedAnnulus_contDiff hu).of_le (by simp)
  have hg : ContDiff ℝ 6 (fun z : Fin 8 → ℝ => e8UnitDampedAnnulus u (r⁻¹ • z)) :=
    hf.comp (by fun_prop)
  have hh : ContDiff ℝ 6 (fun z : Fin 8 → ℝ => e8UnitDampedAnnulus u (r⁻¹ • (z-x))) :=
    hg.comp (contDiff_id.sub contDiff_const)
  change iteratedFDeriv ℝ 6 (fun z => (r⁻¹)^4 • e8UnitDampedAnnulus u (r⁻¹ • (z-x))) v = _
  rw [iteratedFDeriv_const_smul_apply' hh.contDiffAt,
    iteratedFDeriv_comp_sub (f := fun z : Fin 8 → ℝ => e8UnitDampedAnnulus u (r⁻¹ • z)) 6 x v,
    iteratedFDeriv_comp_const_smul r⁻¹ hf, smul_smul, ← pow_add]

theorem e8ScaledDampedAnnulus_sixth_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 ≤ u → ∀ r : ℝ, 0 < r →
      ∀ x v : Fin 8 → ℝ, ‖iteratedFDeriv ℝ 6 (e8ScaledDampedAnnulus u r x) v‖ ≤ C/r^10 := by
  obtain ⟨C, hC, hb⟩ := e8UnitDampedAnnulus_derivatives_uniform
  refine ⟨C, hC, ?_⟩
  intro u hu r hr x v
  rw [e8ScaledDampedAnnulus_sixth_identity hu, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (r⁻¹)^10)]
  calc
    _ ≤ (r⁻¹)^10*C := mul_le_mul_of_nonneg_left (hb u hu 6 (by rfl) _) (by positivity)
    _ = C/r^10 := by rw [inv_pow, div_eq_mul_inv]; ring

theorem e8ScaledDampedAnnulus_zero_outside (u r : ℝ) (hr : 0 < r)
    (x v : Fin 8 → ℝ) (hn : ¬ ∀ i, |v i-x i| ≤ 2*r) :
    e8ScaledDampedAnnulus u r x v = 0 := by
  rw [e8ScaledDampedAnnulus, e8UnitDampedAnnulus, unitObliqueAnnularRieszFour,
    unitAnnularCutoff_zero_outside 8 _ (scaled_annular_argument_norm 8 r hr x v hn).le,
    mul_zero, zero_mul, mul_zero]

theorem e8ScaledDampedAnnulus_sixth_zero_outside {u : ℝ} (hu : 0 ≤ u)
    (r : ℝ) (hr : 0 < r) (x v : Fin 8 → ℝ) (hn : ¬ ∀ i, |v i-x i| ≤ 2*r) :
    iteratedFDeriv ℝ 6 (e8ScaledDampedAnnulus u r x) v = 0 := by
  have hv : r⁻¹ • (v-x) ∉ tsupport (e8UnitDampedAnnulus u) := by
    intro h
    have hh := e8UnitDampedAnnulus_tsupport_subset u h
    rw [Metric.mem_closedBall, dist_zero_right] at hh
    exact (scaled_annular_argument_norm 8 r hr x v hn).not_ge hh
  have hz : iteratedFDeriv ℝ 6 (e8UnitDampedAnnulus u) (r⁻¹ • (v-x)) = 0 := by
    apply Function.notMem_support.mp
    intro h
    exact hv (support_iteratedFDeriv_subset 6 h)
  rw [e8ScaledDampedAnnulus_sixth_identity hu, hz, smul_zero]

#print axioms e8ScaledDampedAnnulus_contDiff
#print axioms e8ScaledDampedAnnulus_eq_heat
#print axioms e8ScaledDampedAnnulus_sixth_identity
#print axioms e8ScaledDampedAnnulus_sixth_bounded
#print axioms e8ScaledDampedAnnulus_zero_outside
#print axioms e8ScaledDampedAnnulus_sixth_zero_outside
end SphericalRiesz
