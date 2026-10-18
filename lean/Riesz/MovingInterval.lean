import Riesz.QuadraticKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Translation converts interval derivatives to endpoint values

For J(t) = integral_0^1 g(s-t) ds the first derivative is g(-t)-g(1-t).
The sixth derivative is the difference of the fifth kernel derivatives
at the two endpoints. This is a genuine FTC identity, not an assumed
interchange of six derivatives and a possibly singular volume integral.
It will be used on smooth cutoff kernels before removing the cutoff.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace SphericalRiesz

def movingUnitIntegral (g : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0:ℝ)..1, g (s-t)

theorem movingUnitIntegral_eq_primitive {g : ℝ → ℝ} (hg : Continuous g) (t : ℝ) :
    movingUnitIntegral g t = (∫ s in (0:ℝ)..1-t, g s)-(∫ s in (0:ℝ)..-t, g s) := by
  rw [movingUnitIntegral, intervalIntegral.integral_comp_sub_right,
    intervalIntegral.integral_interval_sub_left (hg.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  simp only [zero_sub]

theorem movingUnitIntegral_hasDerivAt {g : ℝ → ℝ} (hg : Continuous g) (t : ℝ) :
    HasDerivAt (movingUnitIntegral g) (g (-t)-g (1-t)) t := by
  have h1 := (hg.integral_hasStrictDerivAt 0 (1-t)).hasDerivAt.comp t
    ((hasDerivAt_const t 1).sub (hasDerivAt_id t))
  have h0 := (hg.integral_hasStrictDerivAt 0 (-t)).hasDerivAt.comp t
    (hasDerivAt_id t).neg
  convert h1.sub h0 using 1
  · funext u
    exact movingUnitIntegral_eq_primitive hg u
  · ring

theorem movingUnitIntegral_contDiff {g : ℝ → ℝ} {n : ℕ} (hg : ContDiff ℝ n g) :
    ContDiff ℝ (n+1 : ℕ) (movingUnitIntegral g) := by
  rw [show ((n+1:ℕ) : ℕ∞ω) = (n:ℕ∞ω)+1 by simp, contDiff_succ_iff_deriv]
  refine ⟨fun t => (movingUnitIntegral_hasDerivAt hg.continuous t).differentiableAt, by simp, ?_⟩
  have heq : deriv (movingUnitIntegral g) = fun t => g (-t)-g (1-t) :=
    funext fun t => (movingUnitIntegral_hasDerivAt hg.continuous t).deriv
  rw [heq]
  exact (hg.comp contDiff_neg).sub (hg.comp (contDiff_const.sub contDiff_id))

theorem movingUnitIntegral_iteratedDeriv {g : ℝ → ℝ} {n : ℕ}
    (hg : ContDiff ℝ n g) (t : ℝ) :
    iteratedDeriv (n+1) (movingUnitIntegral g) t =
      (-1:ℝ)^n*(iteratedDeriv n g (-t)-iteratedDeriv n g (1-t)) := by
  have heq : deriv (movingUnitIntegral g) = fun t => g (-t)-g (1-t) :=
    funext fun t => (movingUnitIntegral_hasDerivAt hg.continuous t).deriv
  rw [iteratedDeriv_succ', heq]
  change iteratedDeriv n ((fun u => g (-u))-(fun u => g (1-u))) t = _
  have hL : ContDiff ℝ n (fun u : ℝ => g (-u)) := hg.comp contDiff_neg
  have hR : ContDiff ℝ n (fun u : ℝ => g (1-u)) := hg.comp (contDiff_const.sub contDiff_id)
  rw [iteratedDeriv_sub hL.contDiffAt hR.contDiffAt]
  simp only [iteratedDeriv_comp_neg, iteratedDeriv_comp_const_sub, smul_eq_mul]
  ring

theorem movingUnitIntegral_sixth {g : ℝ → ℝ} (hg : ContDiff ℝ 5 g) (t : ℝ) :
    iteratedDeriv 6 (movingUnitIntegral g) t =
      iteratedDeriv 5 g (1-t)-iteratedDeriv 5 g (-t) := by
  have h := movingUnitIntegral_iteratedDeriv hg t
  norm_num at h
  linarith

#print axioms movingUnitIntegral_eq_primitive
#print axioms movingUnitIntegral_hasDerivAt
#print axioms movingUnitIntegral_contDiff
#print axioms movingUnitIntegral_iteratedDeriv
#print axioms movingUnitIntegral_sixth

end SphericalRiesz
