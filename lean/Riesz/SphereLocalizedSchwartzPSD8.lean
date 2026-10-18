import Riesz.LocalizedSchwartzPSD
import Riesz.EqualAreaInverse8
import Riesz.SphereMeasure8

/-!
The actual unit Sphere8, original point sums and actual uniform probability
background in the localized Schwartz positivity theorem.  The measurable
coordinate map is the known equal-area hemisphere inverse, extended by its
explicit formula everywhere.  A suitable supported cutoff and Haar averaging
are not constructed here.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped SchwartzMap FourierTransform
namespace SphericalRiesz

def sphereEqualAreaCoordinates8 (q : Sphere8) : EuclideanSpace ℝ (Fin 8) :=
  WithLp.toLp 2 (equalAreaInverse8 q)

theorem sphereEqualAreaCoordinates8_measurable : Measurable sphereEqualAreaCoordinates8 := by
  unfold sphereEqualAreaCoordinates8 equalAreaInverse8
  fun_prop

def spherePointMeasure8 {N : ℕ} (X : Fin N → Sphere8) : Measure Sphere8 :=
  ∑ i, Measure.dirac (X i)

instance spherePointMeasure8_finite {N : ℕ} (X : Fin N → Sphere8) :
    IsFiniteMeasure (spherePointMeasure8 X) := by
  unfold spherePointMeasure8
  infer_instance

theorem spherePointMeasure8_integral {N : ℕ} (X : Fin N → Sphere8)
    (g : Sphere8 → ℝ) : (∫ x, g x ∂spherePointMeasure8 X) = ∑ i, g (X i) := by
  unfold spherePointMeasure8
  rw [integral_finsetSum_measure (fun i _ => integrable_dirac (by simp))]
  simp only [integral_dirac]

theorem sphereCutoff8_integrable (χ : Sphere8 → ℝ) (hχmeas : Measurable χ)
    (hχnonneg : ∀ x, 0 ≤ χ x) (hχle : ∀ x, χ x ≤ 1)
    (μ : Measure Sphere8) [IsFiniteMeasure μ] : Integrable χ μ := by
  apply (integrable_const (1 : ℝ)).mono' hχmeas.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (hχnonneg x)]
  exact hχle x

theorem localizedSchwartzPair_spherePoint_left8 {N : ℕ} (X : Fin N → Sphere8)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a : ℝ) (χ : Sphere8 → ℝ)
    (ν : Measure Sphere8) :
    localizedSchwartzPair f a χ sphereEqualAreaCoordinates8 (spherePointMeasure8 X) ν =
      ∑ i, ∫ y, χ (X i)*χ y*
        (f (a • (sphereEqualAreaCoordinates8 (X i)-sphereEqualAreaCoordinates8 y))).re ∂ν := by
  exact spherePointMeasure8_integral X _

theorem localizedSchwartzPair_spherePoint_both8 {N : ℕ} (X : Fin N → Sphere8)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a : ℝ) (χ : Sphere8 → ℝ) :
    localizedSchwartzPair f a χ sphereEqualAreaCoordinates8
      (spherePointMeasure8 X) (spherePointMeasure8 X) =
      ∑ i, ∑ j, χ (X i)*χ (X j)*
        (f (a • (sphereEqualAreaCoordinates8 (X i)-sphereEqualAreaCoordinates8 (X j)))).re := by
  rw [localizedSchwartzPair_spherePoint_left8]
  simp_rw [spherePointMeasure8_integral]

def sphereLocalizedSchwartzDefect8 {N : ℕ} (X : Fin N → Sphere8)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a : ℝ) (χ : Sphere8 → ℝ) : ℝ :=
  (∑ i, ∑ j, χ (X i)*χ (X j)*
    (f (a • (sphereEqualAreaCoordinates8 (X i)-sphereEqualAreaCoordinates8 (X j)))).re) -
  2*(N : ℝ)*(∑ i, ∫ y, χ (X i)*χ y*
    (f (a • (sphereEqualAreaCoordinates8 (X i)-sphereEqualAreaCoordinates8 y))).re
    ∂sphereProbability8) +
  (N : ℝ)^2*(∫ x, ∫ y, χ x*χ y*
    (f (a • (sphereEqualAreaCoordinates8 x-sphereEqualAreaCoordinates8 y))).re
    ∂sphereProbability8 ∂sphereProbability8)

theorem sphereLocalizedSchwartzDefect8_eq_localized {N : ℕ} (X : Fin N → Sphere8)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a : ℝ) (χ : Sphere8 → ℝ) :
    sphereLocalizedSchwartzDefect8 X f a χ =
      localizedSchwartzDefect f a N χ sphereEqualAreaCoordinates8
        (spherePointMeasure8 X) sphereProbability8 := by
  unfold sphereLocalizedSchwartzDefect8 localizedSchwartzDefect
  rw [localizedSchwartzPair_spherePoint_both8, localizedSchwartzPair_spherePoint_left8]
  rfl

theorem sphereLocalizedSchwartzDefect8_nonneg {N : ℕ} (X : Fin N → Sphere8)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ))
    (hFnonneg : ∀ z, 0 ≤ ((𝓕 f) z).re) (hFreal : ∀ z, ((𝓕 f) z).im = 0)
    (a : ℝ) (χ : Sphere8 → ℝ) (hχmeas : Measurable χ)
    (hχnonneg : ∀ x, 0 ≤ χ x) (hχle : ∀ x, χ x ≤ 1) :
    0 ≤ sphereLocalizedSchwartzDefect8 X f a χ := by
  rw [sphereLocalizedSchwartzDefect8_eq_localized]
  exact localizedSchwartzDefect_nonneg f hFnonneg hFreal a N χ sphereEqualAreaCoordinates8
    (spherePointMeasure8 X) sphereProbability8 hχmeas hχnonneg
    sphereEqualAreaCoordinates8_measurable
    (sphereCutoff8_integrable χ hχmeas hχnonneg hχle _)
    (sphereCutoff8_integrable χ hχmeas hχnonneg hχle _)

end SphericalRiesz
