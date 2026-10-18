import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
The actual autocorrelation of a compact continuous cutoff.  Ordinary
convolution continuity and elementary integrated squares give the sharp
uniform bound by its L2 mass.  This avoids a general L2 translation theorem.
The resulting dominated-convergence statement concerns the actual kernel
integrals, not an assumed correlation-limit witness.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology Convolution
namespace SphericalRiesz

variable {d : ℕ}

def compactCutoffSquareMass (q : (EuclideanSpace ℝ (Fin d)) → ℝ) : ℝ := ∫ u, (q u)^2

def compactCutoffCorrelation (q : (EuclideanSpace ℝ (Fin d)) → ℝ) (h : (EuclideanSpace ℝ (Fin d))) : ℝ := ∫ u, q u*q (u-h)

theorem compactCutoffSquareMass_nonneg (q : (EuclideanSpace ℝ (Fin d)) → ℝ) :
    0 ≤ compactCutoffSquareMass q := integral_nonneg fun _u => sq_nonneg _

theorem compactCutoffSquare_integrable (q : (EuclideanSpace ℝ (Fin d)) → ℝ) (hq : Continuous q)
    (hqs : HasCompactSupport q) : Integrable (fun u => (q u)^2) := by
  have hs : HasCompactSupport (fun u => q u*q u) := hqs.mul_right
  have hi : Integrable (fun u => q u*q u) :=
    (hq.mul hq).integrable_of_hasCompactSupport hs
  simpa only [pow_two] using hi

theorem compactCutoffCorrelation_integrable (q : (EuclideanSpace ℝ (Fin d)) → ℝ) (hq : Continuous q)
    (hqs : HasCompactSupport q) (h : (EuclideanSpace ℝ (Fin d))) : Integrable (fun u => q u*q (u-h)) := by
  have hs : HasCompactSupport (fun u => q u*q (u-h)) := hqs.mul_right
  exact (hq.mul (hq.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport hs

theorem compactCutoffCorrelation_zero (q : (EuclideanSpace ℝ (Fin d)) → ℝ) :
    compactCutoffCorrelation q 0 = compactCutoffSquareMass q := by
  simp only [compactCutoffCorrelation, compactCutoffSquareMass, sub_zero, pow_two]

theorem compactCutoffCorrelation_eq_convolution (q : (EuclideanSpace ℝ (Fin d)) → ℝ) :
    compactCutoffCorrelation q =
      q ⋆[ContinuousLinearMap.mul ℝ ℝ] (fun u => q (-u)) := by
  ext h
  simp only [compactCutoffCorrelation, convolution, ContinuousLinearMap.mul_apply', neg_sub]

theorem compactCutoffCorrelation_continuous (q : (EuclideanSpace ℝ (Fin d)) → ℝ) (hq : Continuous q)
    (hqs : HasCompactSupport q) : Continuous (compactCutoffCorrelation q) := by
  rw [compactCutoffCorrelation_eq_convolution]
  exact hqs.continuous_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hq
    (hq.comp continuous_neg).locallyIntegrable

theorem compactCutoffSquare_shift_integral (q : (EuclideanSpace ℝ (Fin d)) → ℝ) (h : (EuclideanSpace ℝ (Fin d))) :
    (∫ u, (q (u-h))^2) = compactCutoffSquareMass q := by
  exact integral_sub_right_eq_self (fun u => (q u)^2) h

theorem compactCutoffCorrelation_abs_le (q : (EuclideanSpace ℝ (Fin d)) → ℝ) (hq : Continuous q)
    (hqs : HasCompactSupport q) (h : (EuclideanSpace ℝ (Fin d))) :
    |compactCutoffCorrelation q h| ≤ compactCutoffSquareMass q := by
  have hq2 := compactCutoffSquare_integrable q hq hqs
  have hshift : Integrable (fun u => (q (u-h))^2) := by
    simpa only [sub_eq_add_neg] using hq2.comp_add_right (-h)
  have hcross := compactCutoffCorrelation_integrable q hq hqs h
  have hminus : 0 ≤ (∫ u, (q u)^2 - 2*(q u*q (u-h)) + (q (u-h))^2) := by
    apply integral_nonneg
    intro u
    change 0 ≤ (q u)^2 - 2*(q u*q (u-h)) + (q (u-h))^2
    nlinarith [sq_nonneg (q u-q (u-h))]
  have hplus : 0 ≤ (∫ u, (q u)^2 + 2*(q u*q (u-h)) + (q (u-h))^2) := by
    apply integral_nonneg
    intro u
    change 0 ≤ (q u)^2 + 2*(q u*q (u-h)) + (q (u-h))^2
    nlinarith [sq_nonneg (q u+q (u-h))]
  have hsub : Integrable (fun u => (q u)^2 - 2*(q u*q (u-h))) :=
    hq2.sub (hcross.const_mul 2)
  have hadd : Integrable (fun u => (q u)^2 + 2*(q u*q (u-h))) :=
    hq2.add (hcross.const_mul 2)
  rw [integral_add hsub hshift, integral_sub hq2 (hcross.const_mul 2),
    integral_const_mul, compactCutoffSquare_shift_integral] at hminus
  rw [integral_add hadd hshift, integral_add hq2 (hcross.const_mul 2),
    integral_const_mul, compactCutoffSquare_shift_integral] at hplus
  change 0 ≤ compactCutoffSquareMass q - 2*compactCutoffCorrelation q h +
    compactCutoffSquareMass q at hminus
  change 0 ≤ compactCutoffSquareMass q + 2*compactCutoffCorrelation q h +
    compactCutoffSquareMass q at hplus
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem compactCutoffCorrelation_tendsto_zero (q : (EuclideanSpace ℝ (Fin d)) → ℝ) (hq : Continuous q)
    (hqs : HasCompactSupport q) :
    Tendsto (compactCutoffCorrelation q) (𝓝 0) (𝓝 (compactCutoffSquareMass q)) := by
  simpa only [compactCutoffCorrelation_zero] using
    (compactCutoffCorrelation_continuous q hq hqs).continuousAt.tendsto (x := 0)

theorem compactCutoffCorrelation_kernel_integrable (q : (EuclideanSpace ℝ (Fin d)) → ℝ) (hq : Continuous q)
    (hqs : HasCompactSupport q) {k : (EuclideanSpace ℝ (Fin d)) → ℝ} (hk : Integrable k)
    {v : (EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d))} (hv : Measurable v) :
    Integrable (fun z => k z*compactCutoffCorrelation q (v z)) := by
  apply (hk.norm.mul_const (compactCutoffSquareMass q)).mono'
    (hk.aestronglyMeasurable.mul
      ((compactCutoffCorrelation_continuous q hq hqs).measurable.comp hv).aestronglyMeasurable)
  filter_upwards [] with z
  change ‖k z*compactCutoffCorrelation q (v z)‖ ≤ ‖k z‖*compactCutoffSquareMass q
  rw [norm_mul, Real.norm_eq_abs (compactCutoffCorrelation q (v z))]
  exact mul_le_mul_of_nonneg_left (compactCutoffCorrelation_abs_le q hq hqs _) (norm_nonneg _)

theorem compactCutoffCorrelation_kernel_integral_tendsto (q : (EuclideanSpace ℝ (Fin d)) → ℝ) (hq : Continuous q)
    (hqs : HasCompactSupport q) {k : (EuclideanSpace ℝ (Fin d)) → ℝ} (hk : Integrable k)
    (v : ℕ → (EuclideanSpace ℝ (Fin d)) → (EuclideanSpace ℝ (Fin d))) (hv : ∀ n, Measurable (v n))
    (hv0 : ∀ z, Tendsto (fun n => v n z) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z, k z*compactCutoffCorrelation q (v n z)) atTop
      (𝓝 (compactCutoffSquareMass q * ∫ z, k z)) := by
  have h : Tendsto (fun n => ∫ z, k z*compactCutoffCorrelation q (v n z)) atTop
      (𝓝 (∫ z, k z*compactCutoffSquareMass q)) := by
    apply tendsto_integral_of_dominated_convergence (fun z => ‖k z‖*compactCutoffSquareMass q)
    · intro n
      exact (compactCutoffCorrelation_kernel_integrable q hq hqs hk (hv n)).aestronglyMeasurable
    · exact hk.norm.mul_const _
    · intro n
      filter_upwards [] with z
      rw [norm_mul, Real.norm_eq_abs (compactCutoffCorrelation q (v n z))]
      exact mul_le_mul_of_nonneg_left (compactCutoffCorrelation_abs_le q hq hqs _) (norm_nonneg _)
    · filter_upwards [] with z
      exact tendsto_const_nhds.mul ((compactCutoffCorrelation_tendsto_zero q hq hqs).comp (hv0 z))
  simpa only [integral_mul_const, mul_comm] using h

theorem compactCutoffCorrelation_kernel_dilation_tendsto (q : (EuclideanSpace ℝ (Fin d)) → ℝ) (hq : Continuous q)
    (hqs : HasCompactSupport q) {k : (EuclideanSpace ℝ (Fin d)) → ℝ} (hk : Integrable k)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) :
    Tendsto (fun n => ∫ z, k z*compactCutoffCorrelation q ((a n)⁻¹ • z)) atTop
      (𝓝 (compactCutoffSquareMass q * ∫ z, k z)) := by
  apply compactCutoffCorrelation_kernel_integral_tendsto q hq hqs hk _ (fun n => by fun_prop)
  intro z
  simpa only [Function.comp_apply, zero_smul] using (tendsto_inv_atTop_zero.comp ha).smul (tendsto_const_nhds (x := z))

end SphericalRiesz
