import Riesz.DiffuseGaussianBackground
import Riesz.SphereMeasure8

/-! Gaussian background subtraction on the actual unit Sphere8 and its
actual uniform probability measure.  There is no supplied PSD hypothesis. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ComplexConjugate
namespace SphericalRiesz

def sphereGaussianKernel8 (t : ℝ) (x y : Sphere8) : ℝ :=
  Real.exp (-(t*(dist x y)^2))

theorem sphereGaussianKernel8_eq_ambient (t : ℝ) (x y : Sphere8) :
    sphereGaussianKernel8 t x y = gaussianKernel t (x:Ambient9) (y:Ambient9) := by
  change Real.exp (-(t*(dist (x:Ambient9) (y:Ambient9))^2)) = _
  rw [dist_eq_norm]
  rfl

theorem sphereGaussianKernel8_nonneg (t : ℝ) (x y : Sphere8) :
    0 ≤ sphereGaussianKernel8 t x y := (Real.exp_pos _).le

theorem sphereGaussianKernel8_le_one {t : ℝ} (ht : 0 ≤ t) (x y : Sphere8) :
    sphereGaussianKernel8 t x y ≤ 1 := by
  rw [sphereGaussianKernel8_eq_ambient]
  exact gaussianKernel_le_one ht _ _

@[simp]
theorem sphereGaussianKernel8_self (t : ℝ) (x : Sphere8) :
    sphereGaussianKernel8 t x x = 1 := by simp [sphereGaussianKernel8]

theorem sphereGaussianKernel8_rotation (t : ℝ) (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (x y : Sphere8) :
    sphereGaussianKernel8 t (sphereRotation8 g x) (sphereRotation8 g y) =
      sphereGaussianKernel8 t x y := by
  unfold sphereGaussianKernel8
  rw [sphereRotation8_dist]

theorem sphereGaussianKernel8_integrable {t : ℝ} (ht : 0 ≤ t) (x : Sphere8) :
    Integrable (sphereGaussianKernel8 t x) sphereProbability8 := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold sphereGaussianKernel8; fun_prop)
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (sphereGaussianKernel8_nonneg _ _ _)]
  exact sphereGaussianKernel8_le_one ht x y

theorem sphereGaussianKernel8_pair_integrable {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun p : Sphere8 × Sphere8 => sphereGaussianKernel8 t p.1 p.2)
      (sphereProbability8.prod sphereProbability8) := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold sphereGaussianKernel8; fun_prop)
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (sphereGaussianKernel8_nonneg _ _ _)]
  exact sphereGaussianKernel8_le_one ht p.1 p.2

def sphereGaussianPotential8 (t : ℝ) (x : Sphere8) : ℝ :=
  ∫ y, sphereGaussianKernel8 t x y ∂sphereProbability8

def sphereGaussianBackground8 (t : ℝ) : ℝ :=
  ∫ p : Sphere8 × Sphere8, sphereGaussianKernel8 t p.1 p.2
    ∂sphereProbability8.prod sphereProbability8

theorem sphereGaussianPotential8_rotation (t : ℝ) (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (x : Sphere8) :
    sphereGaussianPotential8 t (sphereRotation8 g x) = sphereGaussianPotential8 t x := by
  unfold sphereGaussianPotential8
  rw [← sphereProbability8_integral_rotation g (sphereGaussianKernel8 t (sphereRotation8 g x))]
  simp_rw [sphereGaussianKernel8_rotation]

theorem sphereGaussianPotential8_constant (t : ℝ) (x y : Sphere8) :
    sphereGaussianPotential8 t x = sphereGaussianPotential8 t y := by
  obtain ⟨g, hg⟩ := sphereRotation8_transitive x y
  calc
    _ = sphereGaussianPotential8 t (sphereRotation8 g x) :=
      (sphereGaussianPotential8_rotation t g x).symm
    _ = _ := by rw [hg]

theorem sphereGaussianBackground8_iterated {t : ℝ} (ht : 0 ≤ t) :
    sphereGaussianBackground8 t = ∫ x, sphereGaussianPotential8 t x ∂sphereProbability8 := by
  exact integral_prod _ (sphereGaussianKernel8_pair_integrable ht)

theorem sphereGaussianBackground8_eq_potential {t : ℝ} (ht : 0 ≤ t) (p : Sphere8) :
    sphereGaussianBackground8 t = sphereGaussianPotential8 t p := by
  rw [sphereGaussianBackground8_iterated ht]
  calc
    _ = ∫ x : Sphere8, sphereGaussianPotential8 t p ∂sphereProbability8 :=
      integral_congr_ae (.of_forall fun x => sphereGaussianPotential8_constant t x p)
    _ = _ := by simp

theorem sphereGaussianBackground8_nonneg (t : ℝ) : 0 ≤ sphereGaussianBackground8 t :=
  integral_nonneg fun p => sphereGaussianKernel8_nonneg t p.1 p.2

theorem sphereGaussianBackground8_le_one {t : ℝ} (ht : 0 ≤ t) :
    sphereGaussianBackground8 t ≤ 1 := by
  calc
    sphereGaussianBackground8 t ≤
        ∫ _ : Sphere8 × Sphere8, (1:ℝ) ∂sphereProbability8.prod sphereProbability8 :=
      integral_mono (sphereGaussianKernel8_pair_integrable ht) (integrable_const (1:ℝ))
        (fun p => sphereGaussianKernel8_le_one ht p.1 p.2)
    _ = 1 := by simp

def ambientSphereProbability8 : Measure Ambient9 :=
  sphereProbability8.map (fun x : Sphere8 => (x:Ambient9))

instance ambientSphereProbability8_probability : IsProbabilityMeasure ambientSphereProbability8 := by
  unfold ambientSphereProbability8
  infer_instance

theorem ambientSphereProbability8_charFun (z : Ambient9) :
    charFun ambientSphereProbability8 z =
      ∫ y : Sphere8, Complex.exp (⟪(y:Ambient9), z⟫ * Complex.I) ∂sphereProbability8 := by
  rw [charFun_apply, ambientSphereProbability8, integral_map (by fun_prop) (by fun_prop)]

theorem ambientSphereProbability8_kernel_integral (t : ℝ) (x : Sphere8) :
    (∫ y : Ambient9, gaussianKernel t (x:Ambient9) y ∂ambientSphereProbability8) =
      sphereGaussianPotential8 t x := by
  rw [ambientSphereProbability8, integral_map (by fun_prop) (by unfold gaussianKernel; fun_prop)]
  simp only [sphereGaussianPotential8, sphereGaussianKernel8_eq_ambient]

theorem ambientSphereProbability8_kernel_pair (t : ℝ) :
    gaussianMeasurePair t ambientSphereProbability8 ambientSphereProbability8 =
      sphereGaussianBackground8 t := by
  unfold gaussianMeasurePair ambientSphereProbability8
  rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    integral_map (by fun_prop) (by unfold gaussianKernel; fun_prop)]
  simp only [sphereGaussianBackground8, sphereGaussianKernel8_eq_ambient,
    Prod.map_fst, Prod.map_snd]

def sphereGaussianDefect8 {N : ℕ} (t M : ℝ) (X : Configuration N) : ℝ :=
  (∑ i, ∑ j, sphereGaussianKernel8 t (X i) (X j)) -
    2*M*(∑ i, sphereGaussianPotential8 t (X i)) + M^2*sphereGaussianBackground8 t

theorem sphereGaussianDefect8_eq_diffuse {N : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (M : ℝ) (X : Configuration N) :
    sphereGaussianDefect8 t M X = diffuseGaussianDefect t M
      (fun i : Fin N => (X i:Ambient9)) ambientSphereProbability8 := by
  unfold sphereGaussianDefect8 diffuseGaussianDefect
  simp only [sphereGaussianKernel8_eq_ambient, ambientSphereProbability8_kernel_integral,
    ambientSphereProbability8_kernel_pair]

theorem sphereGaussianDefect8_eq_normSq {N : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (M : ℝ) (X : Configuration N) :
    sphereGaussianDefect8 t M X = ∫ z : Ambient9,
      Complex.normSq ((∑ i : Fin N,
        Complex.exp (⟪(X i:Ambient9), Real.sqrt (2*t) • z⟫ * Complex.I)) -
        (M:ℂ)*(∫ y : Sphere8,
          Complex.exp (⟪(y:Ambient9), Real.sqrt (2*t) • z⟫ * Complex.I) ∂sphereProbability8))
      ∂stdGaussian Ambient9 := by
  rw [sphereGaussianDefect8_eq_diffuse ht, diffuseGaussianDefect_eq_normSq ht]
  simp only [ambientSphereProbability8_charFun]

theorem sphereGaussianDefect8_nonneg {N : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (M : ℝ) (X : Configuration N) : 0 ≤ sphereGaussianDefect8 t M X := by
  rw [sphereGaussianDefect8_eq_diffuse ht]
  exact diffuseGaussianDefect_nonneg ht M _ _

theorem sphereGaussianDefect8_charge_N {N : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (X : Configuration N) :
    sphereGaussianDefect8 t (N:ℝ) X =
      (∑ i, ∑ j, sphereGaussianKernel8 t (X i) (X j)) - (N:ℝ)^2*sphereGaussianBackground8 t := by
  unfold sphereGaussianDefect8
  simp_rw [← sphereGaussianBackground8_eq_potential ht]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end SphericalRiesz
