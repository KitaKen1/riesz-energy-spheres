import Riesz.FlatKernel
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# A fixed smooth annular inverse-fourth kernel

Multiplying the actual flat kernel by the difference of two fixed bumps
removes its singularity near zero. Compact support bounds all derivatives
through order six at once. Scaling and the coordinate-slice connection
are deliberately separate from this fixed-function certificate.
-/

set_option autoImplicit false
noncomputable section
open scoped ContDiff

namespace SphericalRiesz

def outerUnitBump (d : ℕ) : ContDiffBump (0 : Fin d → ℝ) :=
  ⟨1, 2, by norm_num, by norm_num⟩

def innerUnitBump (d : ℕ) : ContDiffBump (0 : Fin d → ℝ) :=
  ⟨1/2, 1, by norm_num, by norm_num⟩

def unitAnnularCutoff (d : ℕ) (v : Fin d → ℝ) : ℝ :=
  outerUnitBump d v-innerUnitBump d v

def unitAnnularRieszFour (d : ℕ) (v : Fin d → ℝ) : ℝ :=
  flatRieszFour d 0 v*unitAnnularCutoff d v

theorem squaredDistance_zero_iff (d : ℕ) (v : Fin d → ℝ) :
    squaredDistance d 0 v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hsum : (∑ i : Fin d, (v i)^2) = 0 := by simpa [squaredDistance] using h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (v i))).mp hsum
    funext i
    simpa only [sq_eq_zero_iff, Pi.zero_apply] using hz i (Finset.mem_univ i)
  · rintro rfl
    simp [squaredDistance]

theorem unitAnnularCutoff_eventually_zero (d : ℕ) :
    unitAnnularCutoff d =ᶠ[nhds (0 : Fin d → ℝ)] 0 := by
  filter_upwards [(outerUnitBump d).eventuallyEq_one, (innerUnitBump d).eventuallyEq_one]
    with v ho hi
  simp only [unitAnnularCutoff, ho, hi, Pi.one_apply, Pi.zero_apply, sub_self]

theorem unitAnnularRieszFour_contDiff (d : ℕ) :
    ContDiff ℝ ∞ (unitAnnularRieszFour d) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : v = 0
  · subst v
    apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [unitAnnularCutoff_eventually_zero d] with v hv
    simp only [unitAnnularRieszFour, hv, Pi.zero_apply, mul_zero]
  · have hq : squaredDistance d 0 v ≠ 0 :=
      fun h => hv ((squaredDistance_zero_iff d v).mp h)
    unfold unitAnnularRieszFour flatRieszFour unitAnnularCutoff
    apply ContDiffAt.mul
    · apply ContDiffAt.div contDiffAt_const
      · unfold squaredDistance
        fun_prop
      · exact pow_ne_zero 2 hq
    · exact (outerUnitBump d).contDiffAt.sub (innerUnitBump d).contDiffAt

theorem unitAnnularRieszFour_hasCompactSupport (d : ℕ) :
    HasCompactSupport (unitAnnularRieszFour d) := by
  have h : HasCompactSupport (unitAnnularCutoff d) :=
    (outerUnitBump d).hasCompactSupport.sub (innerUnitBump d).hasCompactSupport
  exact h.mul_left

theorem unitAnnularRieszFour_zero_outside (d : ℕ) (v : Fin d → ℝ)
    (hv : 2 ≤ ‖v‖) : unitAnnularRieszFour d v = 0 := by
  have ho : outerUnitBump d v = 0 := (outerUnitBump d).zero_of_le_dist (by
    simpa only [outerUnitBump, dist_zero_right] using hv)
  have hi : innerUnitBump d v = 0 := (innerUnitBump d).zero_of_le_dist (by
    simp only [innerUnitBump, dist_zero_right]
    linarith)
  simp only [unitAnnularRieszFour, unitAnnularCutoff, ho, hi, sub_self, mul_zero]

/-- The constant exists for the actual fixed kernel, not as an extra axiom. -/
theorem unitAnnularRieszFour_derivatives_bounded (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n ≤ 6, ∀ v : Fin d → ℝ,
      ‖iteratedFDeriv ℝ n (unitAnnularRieszFour d) v‖ ≤ C :=
  (unitAnnularRieszFour_hasCompactSupport d).exists_bound_iteratedFDeriv
    (unitAnnularRieszFour_contDiff d) 6

def scaledAnnularRieszFour (d : ℕ) (r : ℝ) (x v : Fin d → ℝ) : ℝ :=
  (r⁻¹)^4*unitAnnularRieszFour d (r⁻¹ • (v-x))

theorem squaredDistance_scaled (d : ℕ) (r : ℝ) (x v : Fin d → ℝ) :
    squaredDistance d 0 (r⁻¹ • (v-x)) = (r⁻¹)^2*squaredDistance d x v := by
  simp only [squaredDistance, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, Pi.zero_apply,
    sub_zero, mul_pow, ← Finset.mul_sum]

/-- Scaling is the actual inverse-fourth kernel times the rescaled cutoff. -/
theorem scaledAnnularRieszFour_eq_kernel (d : ℕ) (r : ℝ) (hr : 0 < r)
    (x v : Fin d → ℝ) : scaledAnnularRieszFour d r x v =
      flatRieszFour d x v*unitAnnularCutoff d (r⁻¹ • (v-x)) := by
  unfold scaledAnnularRieszFour unitAnnularRieszFour flatRieszFour
  rw [squaredDistance_scaled, mul_pow, ← pow_mul]
  simp only [one_div, mul_inv, inv_pow, inv_inv]
  have hc : (r⁻¹)^4*r^4 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hr.ne', one_pow]
  calc
    _ = ((r⁻¹)^4*r^4)*((squaredDistance d x v)^2)⁻¹*
        unitAnnularCutoff d (r⁻¹ • (v-x)) := by ring
    _ = _ := by rw [hc, one_mul]

theorem scaledAnnularRieszFour_contDiff (d : ℕ) (r : ℝ) (x : Fin d → ℝ) :
    ContDiff ℝ ∞ (scaledAnnularRieszFour d r x) := by
  unfold scaledAnnularRieszFour
  apply ContDiff.mul contDiff_const
  exact (unitAnnularRieszFour_contDiff d).comp (by fun_prop)

theorem scaledAnnularRieszFour_sixth_identity (d : ℕ) (r : ℝ) (x v : Fin d → ℝ) :
    iteratedFDeriv ℝ 6 (scaledAnnularRieszFour d r x) v =
      (r⁻¹)^10 • iteratedFDeriv ℝ 6 (unitAnnularRieszFour d) (r⁻¹ • (v-x)) := by
  have hf : ContDiff ℝ 6 (unitAnnularRieszFour d) :=
    (unitAnnularRieszFour_contDiff d).of_le (by simp)
  have hg : ContDiff ℝ 6 (fun z : Fin d → ℝ => unitAnnularRieszFour d (r⁻¹ • z)) :=
    hf.comp (by fun_prop)
  have hh : ContDiff ℝ 6 (fun z : Fin d → ℝ => unitAnnularRieszFour d (r⁻¹ • (z-x))) :=
    hg.comp (contDiff_id.sub contDiff_const)
  change iteratedFDeriv ℝ 6 (fun z => (r⁻¹)^4 • unitAnnularRieszFour d (r⁻¹ • (z-x))) v = _
  rw [iteratedFDeriv_const_smul_apply' hh.contDiffAt,
    iteratedFDeriv_comp_sub (f := fun z : Fin d → ℝ => unitAnnularRieszFour d (r⁻¹ • z)) 6 x v]
  rw [iteratedFDeriv_comp_const_smul r⁻¹ hf]
  rw [smul_smul, ← pow_add]

/-- One constant works at every radius and center for the actual cutoff kernel. -/
theorem scaledAnnularRieszFour_sixth_bounded (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ x v : Fin d → ℝ,
      ‖iteratedFDeriv ℝ 6 (scaledAnnularRieszFour d r x) v‖ ≤ C/r^10 := by
  obtain ⟨C, hC, hb⟩ := unitAnnularRieszFour_derivatives_bounded d
  refine ⟨C, hC, ?_⟩
  intro r hr x v
  rw [scaledAnnularRieszFour_sixth_identity, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (r⁻¹)^10)]
  calc
    _ ≤ (r⁻¹)^10*C := mul_le_mul_of_nonneg_left (hb 6 (by rfl) _) (by positivity)
    _ = C/r^10 := by rw [inv_pow, div_eq_mul_inv]; ring

theorem unitAnnularRieszFour_tsupport_subset (d : ℕ) :
    tsupport (unitAnnularRieszFour d) ⊆ Metric.closedBall 0 2 := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro v hv
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hn
  exact (Function.mem_support.mp hv) (unitAnnularRieszFour_zero_outside d v (not_le.mp hn).le)

theorem scaled_annular_argument_norm (d : ℕ) (r : ℝ) (hr : 0 < r)
    (x v : Fin d → ℝ) (hn : ¬ ∀ i, |v i-x i| ≤ 2*r) :
    2 < ‖r⁻¹ • (v-x)‖ := by
  push Not at hn
  obtain ⟨i, hi⟩ := hn
  have hnorm : 2*r < ‖v-x‖ := hi.trans_le (by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (v-x) i)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), ← div_eq_inv_mul]
  exact (lt_div_iff₀ hr).mpr hnorm

theorem scaledAnnularRieszFour_zero_outside (d : ℕ) (r : ℝ) (hr : 0 < r)
    (x v : Fin d → ℝ) (hn : ¬ ∀ i, |v i-x i| ≤ 2*r) :
    scaledAnnularRieszFour d r x v = 0 := by
  unfold scaledAnnularRieszFour
  rw [unitAnnularRieszFour_zero_outside d _ (scaled_annular_argument_norm d r hr x v hn).le,
    mul_zero]

theorem scaledAnnularRieszFour_sixth_zero_outside (d : ℕ) (r : ℝ) (hr : 0 < r)
    (x v : Fin d → ℝ) (hn : ¬ ∀ i, |v i-x i| ≤ 2*r) :
    iteratedFDeriv ℝ 6 (scaledAnnularRieszFour d r x) v = 0 := by
  have hv : r⁻¹ • (v-x) ∉ tsupport (unitAnnularRieszFour d) := by
    intro h
    have hh := unitAnnularRieszFour_tsupport_subset d h
    rw [Metric.mem_closedBall, dist_zero_right] at hh
    exact (scaled_annular_argument_norm d r hr x v hn).not_ge hh
  have hz : iteratedFDeriv ℝ 6 (unitAnnularRieszFour d) (r⁻¹ • (v-x)) = 0 := by
    apply Function.notMem_support.mp
    intro h
    exact hv (support_iteratedFDeriv_subset 6 h)
  rw [scaledAnnularRieszFour_sixth_identity, hz, smul_zero]

#print axioms unitAnnularRieszFour_contDiff
#print axioms unitAnnularRieszFour_derivatives_bounded
#print axioms scaledAnnularRieszFour_eq_kernel
#print axioms scaledAnnularRieszFour_sixth_identity
#print axioms scaledAnnularRieszFour_sixth_bounded
#print axioms scaledAnnularRieszFour_sixth_zero_outside

end SphericalRiesz
