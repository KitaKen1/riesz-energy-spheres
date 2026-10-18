import Riesz.EqualAreaEuclideanTransport8

/-!
The actual original Sphere8 cutoff background equals the flat twofold
Schwartz background with the exact area normalization. The actual cutoff
square mass is Q/area, is positive, and the density-scaled sphere background
has limit Re Fourier(f)(0). Rotation averaging and its constant-row identity
are not supplied or assumed here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal SchwartzMap FourierTransform
namespace SphericalRiesz

def sphereChartCutoffSquareMass8 (ρ : ℝ) (hρ : 0 < ρ) : ℝ :=
  ∫ x, (sphereChartCutoff8 ρ hρ x)^2 ∂sphereProbability8

theorem sphereChartCutoffSquareMass8_eq (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ 1/8) :
    sphereChartCutoffSquareMass8 ρ hρ = (sphereArea8.real univ)⁻¹ *
      compactCutoffSquareMass (coordinateCutoff (d := 8) ρ hρ) := by
  have h : sphereChartCutoffSquareMass8 ρ hρ =
      ∫ x, sphereChartCutoff8 ρ hρ x*coordinateCutoff ρ hρ (sphereEqualAreaCoordinates8 x)
        ∂sphereProbability8 := by
    apply integral_congr_ae
    filter_upwards [] with x
    unfold sphereChartCutoff8
    split_ifs <;> simp only [pow_two, zero_mul, mul_zero]
  rw [h, sphereChartCutoff8_probability_integral ρ hρ hr]
  simp only [compactCutoffSquareMass, pow_two]

theorem sphereChartCutoffSquareMass8_pos (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ 1/8) :
    0 < sphereChartCutoffSquareMass8 ρ hρ := by
  rw [sphereChartCutoffSquareMass8_eq ρ hρ hr]
  apply mul_pos (inv_pos.mpr _) (coordinateCutoff_squareMass_pos ρ hρ)
  rw [sphereArea8_mass_real]
  positivity

theorem sphereChartSchwartzBackground8_eq_flat (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ 1/8)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a : ℝ) :
    localizedSchwartzPair f a (sphereChartCutoff8 ρ hρ) sphereEqualAreaCoordinates8
      sphereProbability8 sphereProbability8 = (sphereArea8.real univ)⁻¹^2 *
        compactKernelBackground (coordinateCutoff ρ hρ) (fun z => (f z).re) a := by
  let C : ℝ := (sphereArea8.real univ)⁻¹
  let q : EuclideanSpace ℝ (Fin 8) → ℝ := coordinateCutoff ρ hρ
  let g : EuclideanSpace ℝ (Fin 8) → ℝ := fun u => ∫ v, q v*(f (a • (u-v))).re
  have hi (x : Sphere8) :
      (∫ y, sphereChartCutoff8 ρ hρ y*
        (f (a • (sphereEqualAreaCoordinates8 x-sphereEqualAreaCoordinates8 y))).re
        ∂sphereProbability8) = C*g (sphereEqualAreaCoordinates8 x) :=
    sphereChartCutoff8_probability_integral ρ hρ hr
      (fun v => (f (a • (sphereEqualAreaCoordinates8 x-v))).re)
  have ho : (∫ x, sphereChartCutoff8 ρ hρ x*g (sphereEqualAreaCoordinates8 x)
        ∂sphereProbability8) = C*∫ u, q u*g u :=
    sphereChartCutoff8_probability_integral ρ hρ hr g
  calc
    _ = ∫ x, sphereChartCutoff8 ρ hρ x*(∫ y, sphereChartCutoff8 ρ hρ y*
          (f (a • (sphereEqualAreaCoordinates8 x-sphereEqualAreaCoordinates8 y))).re
          ∂sphereProbability8) ∂sphereProbability8 := by
      unfold localizedSchwartzPair
      simp_rw [mul_assoc, integral_const_mul]
    _ = ∫ x, sphereChartCutoff8 ρ hρ x*(C*g (sphereEqualAreaCoordinates8 x))
        ∂sphereProbability8 := by simp_rw [hi]
    _ = C*(∫ x, sphereChartCutoff8 ρ hρ x*g (sphereEqualAreaCoordinates8 x)
        ∂sphereProbability8) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = C*(C*∫ u, q u*g u) := by rw [ho]
    _ = _ := by
      dsimp only [C,g,q]
      unfold compactKernelBackground
      simp_rw [← integral_const_mul]
      ring

theorem sphereChartSchwartzBackground8_normalized_eq (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ 1/8)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a : ℝ) :
    a^8*(sphereArea8.real univ)*
      localizedSchwartzPair f a (sphereChartCutoff8 ρ hρ) sphereEqualAreaCoordinates8
        sphereProbability8 sphereProbability8 / sphereChartCutoffSquareMass8 ρ hρ =
      a^8*compactKernelBackground (coordinateCutoff ρ hρ) (fun z => (f z).re) a /
        compactCutoffSquareMass (coordinateCutoff (d := 8) ρ hρ) := by
  rw [sphereChartSchwartzBackground8_eq_flat ρ hρ hr,
    sphereChartCutoffSquareMass8_eq ρ hρ hr]
  have hA : sphereArea8.real univ ≠ 0 := by rw [sphereArea8_mass_real]; positivity
  have hQ := (coordinateCutoff_squareMass_pos (d := 8) ρ hρ).ne'
  field_simp [hA,hQ]

theorem sphereChartSchwartzBackground8_normalized_tendsto (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ 1/8)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ))
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) (ha0 : ∀ n, 0 < a n) :
    Tendsto (fun n => (a n)^8*(sphereArea8.real univ)*
      localizedSchwartzPair f (a n) (sphereChartCutoff8 ρ hρ) sphereEqualAreaCoordinates8
        sphereProbability8 sphereProbability8 / sphereChartCutoffSquareMass8 ρ hρ)
      atTop (𝓝 (((𝓕 f) 0).re)) := by
  simp_rw [sphereChartSchwartzBackground8_normalized_eq ρ hρ hr]
  simpa using
    coordinateCutoff_schwartzBackground_tendsto ρ hρ f ha ha0

end SphericalRiesz
