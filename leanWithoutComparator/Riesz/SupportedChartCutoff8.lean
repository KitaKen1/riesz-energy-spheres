import Riesz.CompactSchwartzBackground
import Riesz.SphereLocalizedSchwartzPSD8
import Riesz.SphereIntegrable8
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
An actual compact smooth coordinate bump and its measurable hemisphere
extension on the original Sphere8.  The first-coordinate test matters: the
explicit inverse coordinates alone would also select the antipodal sheet.
The coordinate square mass is positive and the original sphere PSD applies
without an assumed cutoff witness.  No rotation average or geometric
sphere-background change of variables is asserted in this file.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric
open scoped Topology SchwartzMap FourierTransform
namespace SphericalRiesz

variable {d : ℕ}

def coordinateCutoffBump (ρ : ℝ) (hρ : 0 < ρ) :
    ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) where
  rIn := ρ/2
  rOut := ρ
  rIn_pos := half_pos hρ
  rIn_lt_rOut := half_lt_self hρ

def coordinateCutoff (ρ : ℝ) (hρ : 0 < ρ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  coordinateCutoffBump ρ hρ

theorem coordinateCutoff_continuous (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (coordinateCutoff (d := d) ρ hρ) :=
  (coordinateCutoffBump ρ hρ).continuous

theorem coordinateCutoff_compactSupport (ρ : ℝ) (hρ : 0 < ρ) :
    HasCompactSupport (coordinateCutoff (d := d) ρ hρ) :=
  (coordinateCutoffBump ρ hρ).hasCompactSupport

theorem coordinateCutoff_nonneg (ρ : ℝ) (hρ : 0 < ρ) (u : EuclideanSpace ℝ (Fin d)) :
    0 ≤ coordinateCutoff ρ hρ u := (coordinateCutoffBump ρ hρ).nonneg

theorem coordinateCutoff_le_one (ρ : ℝ) (hρ : 0 < ρ) (u : EuclideanSpace ℝ (Fin d)) :
    coordinateCutoff ρ hρ u ≤ 1 := (coordinateCutoffBump ρ hρ).le_one

theorem coordinateCutoff_zero (ρ : ℝ) (hρ : 0 < ρ) :
    coordinateCutoff (d := d) ρ hρ 0 = 1 := by
  apply (coordinateCutoffBump ρ hρ).one_of_mem_closedBall
  exact mem_closedBall_self (half_pos hρ).le

theorem coordinateCutoff_support (ρ : ℝ) (hρ : 0 < ρ) :
    Function.support (coordinateCutoff (d := d) ρ hρ) = ball 0 ρ :=
  (coordinateCutoffBump ρ hρ).support_eq

theorem coordinateCutoff_zero_of_norm (ρ : ℝ) (hρ : 0 < ρ)
    (u : EuclideanSpace ℝ (Fin d)) (hu : ρ ≤ ‖u‖) : coordinateCutoff ρ hρ u = 0 := by
  apply (coordinateCutoffBump ρ hρ).zero_of_le_dist
  simpa only [coordinateCutoffBump, dist_zero_right] using hu

theorem coordinateCutoff_squareMass_pos (ρ : ℝ) (hρ : 0 < ρ) :
    0 < compactCutoffSquareMass (coordinateCutoff (d := d) ρ hρ) := by
  have hs : HasCompactSupport (fun u : EuclideanSpace ℝ (Fin d) =>
      coordinateCutoff ρ hρ u*coordinateCutoff ρ hρ u) :=
    (coordinateCutoff_compactSupport ρ hρ).mul_right
  have hc : Continuous (fun u : EuclideanSpace ℝ (Fin d) =>
      (coordinateCutoff ρ hρ u)^2) := (coordinateCutoff_continuous ρ hρ).pow 2
  have hs2 : HasCompactSupport (fun u : EuclideanSpace ℝ (Fin d) =>
      (coordinateCutoff ρ hρ u)^2) := by
    simpa only [pow_two] using hs
  apply hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hs2 (fun u => sq_nonneg _) (x := 0)
  change (coordinateCutoff ρ hρ (0 : EuclideanSpace ℝ (Fin d)))^2 ≠ 0
  rw [coordinateCutoff_zero, one_pow]
  exact one_ne_zero

theorem coordinateCutoff_schwartzBackground_tendsto (ρ : ℝ) (hρ : 0 < ρ)
    (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) (ha0 : ∀ n, 0 < a n) :
    Tendsto (fun n => (a n)^Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) *
      compactKernelBackground (coordinateCutoff ρ hρ) (fun z => (f z).re) (a n) /
        compactCutoffSquareMass (coordinateCutoff (d := d) ρ hρ)) atTop (𝓝 (((𝓕 f) 0).re)) :=
  compactSchwartzBackground_normalized_tendsto _ (coordinateCutoff_continuous ρ hρ)
    (coordinateCutoff_compactSupport ρ hρ) (coordinateCutoff_squareMass_pos ρ hρ) f ha ha0

def sphereChartCutoff8 (ρ : ℝ) (hρ : 0 < ρ) (x : Sphere8) : ℝ :=
  if 0 < (x : Ambient9) 0 then coordinateCutoff ρ hρ (sphereEqualAreaCoordinates8 x) else 0

theorem sphereChartCutoff8_measurable (ρ : ℝ) (hρ : 0 < ρ) :
    Measurable (sphereChartCutoff8 ρ hρ) := by
  apply Measurable.ite
    (measurableSet_lt measurable_const (by fun_prop))
    ((coordinateCutoff_continuous ρ hρ).measurable.comp sphereEqualAreaCoordinates8_measurable)
    measurable_const

theorem sphereChartCutoff8_nonneg (ρ : ℝ) (hρ : 0 < ρ) (x : Sphere8) :
    0 ≤ sphereChartCutoff8 ρ hρ x := by
  unfold sphereChartCutoff8
  split_ifs
  · exact coordinateCutoff_nonneg ρ hρ _
  · exact le_rfl

theorem sphereChartCutoff8_le_one (ρ : ℝ) (hρ : 0 < ρ) (x : Sphere8) :
    sphereChartCutoff8 ρ hρ x ≤ 1 := by
  unfold sphereChartCutoff8
  split_ifs
  · exact coordinateCutoff_le_one ρ hρ _
  · exact zero_le_one

theorem sphereEqualAreaCoordinates8_northPole : sphereEqualAreaCoordinates8 northPole8 = 0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [sphereEqualAreaCoordinates8, equalAreaInverse8, northPole8]
  · simp [sphereEqualAreaCoordinates8, equalAreaInverse8, northPole8]

theorem sphereChartCutoff8_northPole (ρ : ℝ) (hρ : 0 < ρ) :
    sphereChartCutoff8 ρ hρ northPole8 = 1 := by
  have hp : 0 < (northPole8 : Ambient9) 0 := by simp [northPole8]
  rw [sphereChartCutoff8, if_pos hp, sphereEqualAreaCoordinates8_northPole, coordinateCutoff_zero]

theorem sphereChartCutoff8_support (ρ : ℝ) (hρ : 0 < ρ) :
    Function.support (sphereChartCutoff8 ρ hρ) =
      {x : Sphere8 | 0 < (x : Ambient9) 0 ∧ ‖sphereEqualAreaCoordinates8 x‖ < ρ} := by
  ext x
  by_cases hx : 0 < (x : Ambient9) 0
  · simp only [Function.mem_support, sphereChartCutoff8, hx, ite_true,
      Set.mem_ofPred_eq, true_and]
    have h := Set.ext_iff.mp (coordinateCutoff_support (d := 8) ρ hρ)
      (sphereEqualAreaCoordinates8 x)
    simpa only [Function.mem_support, mem_ball, dist_zero_right] using h
  · simp only [Function.mem_support, sphereChartCutoff8, hx, ite_false,
      ne_eq, not_true_eq_false, Set.mem_ofPred_eq, false_and]

theorem sphereChartCutoff8_integrable (ρ : ℝ) (hρ : 0 < ρ)
    (μ : Measure Sphere8) [IsFiniteMeasure μ] : Integrable (sphereChartCutoff8 ρ hρ) μ :=
  sphereCutoff8_integrable _ (sphereChartCutoff8_measurable ρ hρ)
    (sphereChartCutoff8_nonneg ρ hρ) (sphereChartCutoff8_le_one ρ hρ) μ

theorem sphereChartCutoff8_schwartzDefect_nonneg {N : ℕ} (X : Fin N → Sphere8)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ))
    (hFnonneg : ∀ z, 0 ≤ ((𝓕 f) z).re) (hFreal : ∀ z, ((𝓕 f) z).im = 0)
    (a ρ : ℝ) (hρ : 0 < ρ) :
    0 ≤ sphereLocalizedSchwartzDefect8 X f a (sphereChartCutoff8 ρ hρ) :=
  sphereLocalizedSchwartzDefect8_nonneg X f hFnonneg hFreal a _
    (sphereChartCutoff8_measurable ρ hρ) (sphereChartCutoff8_nonneg ρ hρ)
    (sphereChartCutoff8_le_one ρ hρ)

end SphericalRiesz
