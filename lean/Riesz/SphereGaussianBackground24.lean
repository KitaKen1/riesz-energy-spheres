import Riesz.DiffuseGaussianBackground
import Riesz.LeechProfileLower24

/-! Gaussian background subtraction on the actual unit (SphereD 24) and its
actual uniform probability measure.  There is no supplied PSD hypothesis. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ComplexConjugate
namespace SphericalRiesz

theorem sphereGaussianKernel24_eq_ambient (t : ℝ) (x y : (SphereD 24)) :
    sphereGaussianKernel24 t x y = gaussianKernel t (x:(AmbientD 24)) (y:(AmbientD 24)) := by
  change Real.exp (-(t*(dist (x:(AmbientD 24)) (y:(AmbientD 24)))^2)) = _
  rw [dist_eq_norm]
  rfl

theorem sphereGaussianKernel24_le_one {t : ℝ} (ht : 0 ≤ t) (x y : (SphereD 24)) :
    sphereGaussianKernel24 t x y ≤ 1 := by
  rw [sphereGaussianKernel24_eq_ambient]
  exact gaussianKernel_le_one ht _ _

theorem sphereGaussianKernel24_rotation (t : ℝ) (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (x y : (SphereD 24)) :
    sphereGaussianKernel24 t (sphereRotationD g x) (sphereRotationD g y) =
      sphereGaussianKernel24 t x y := by
  unfold sphereGaussianKernel24
  rw [sphereRotationD_dist]

theorem sphereGaussianKernel24_integrable {t : ℝ} (ht : 0 ≤ t) (x : (SphereD 24)) :
    Integrable (sphereGaussianKernel24 t x) (sphereProbabilityD 24) := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold sphereGaussianKernel24; fun_prop)
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (sphereGaussianKernel24_nonneg _ _ _)]
  exact sphereGaussianKernel24_le_one ht x y

theorem sphereGaussianKernel24_pair_integrable {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun p : (SphereD 24) × (SphereD 24) => sphereGaussianKernel24 t p.1 p.2)
      ((sphereProbabilityD 24).prod (sphereProbabilityD 24)) := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold sphereGaussianKernel24; fun_prop)
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (sphereGaussianKernel24_nonneg _ _ _)]
  exact sphereGaussianKernel24_le_one ht p.1 p.2

def sphereGaussianPotential24 (t : ℝ) (x : (SphereD 24)) : ℝ :=
  ∫ y, sphereGaussianKernel24 t x y ∂(sphereProbabilityD 24)

def sphereGaussianBackground24 (t : ℝ) : ℝ :=
  ∫ p : (SphereD 24) × (SphereD 24), sphereGaussianKernel24 t p.1 p.2
    ∂(sphereProbabilityD 24).prod (sphereProbabilityD 24)

theorem sphereGaussianPotential24_rotation (t : ℝ) (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (x : (SphereD 24)) :
    sphereGaussianPotential24 t (sphereRotationD g x) = sphereGaussianPotential24 t x := by
  unfold sphereGaussianPotential24
  rw [← sphereProbabilityD_integral_rotation g (sphereGaussianKernel24 t (sphereRotationD g x))]
  simp_rw [sphereGaussianKernel24_rotation]

theorem sphereGaussianPotential24_constant (t : ℝ) (x y : (SphereD 24)) :
    sphereGaussianPotential24 t x = sphereGaussianPotential24 t y := by
  obtain ⟨g, hg⟩ := sphereRotation24_transitive x y
  calc
    _ = sphereGaussianPotential24 t (sphereRotationD g x) :=
      (sphereGaussianPotential24_rotation t g x).symm
    _ = _ := by rw [hg]

theorem sphereGaussianBackground24_iterated {t : ℝ} (ht : 0 ≤ t) :
    sphereGaussianBackground24 t = ∫ x, sphereGaussianPotential24 t x ∂(sphereProbabilityD 24) := by
  exact integral_prod _ (sphereGaussianKernel24_pair_integrable ht)

theorem sphereGaussianBackground24_eq_potential {t : ℝ} (ht : 0 ≤ t) (p : (SphereD 24)) :
    sphereGaussianBackground24 t = sphereGaussianPotential24 t p := by
  rw [sphereGaussianBackground24_iterated ht]
  calc
    _ = ∫ x : (SphereD 24), sphereGaussianPotential24 t p ∂(sphereProbabilityD 24) :=
      integral_congr_ae (.of_forall fun x => sphereGaussianPotential24_constant t x p)
    _ = _ := by simp

theorem sphereGaussianBackground24_nonneg (t : ℝ) : 0 ≤ sphereGaussianBackground24 t :=
  integral_nonneg fun p => sphereGaussianKernel24_nonneg t p.1 p.2

theorem sphereGaussianBackground24_le_one {t : ℝ} (ht : 0 ≤ t) :
    sphereGaussianBackground24 t ≤ 1 := by
  calc
    sphereGaussianBackground24 t ≤
        ∫ _ : (SphereD 24) × (SphereD 24), (1:ℝ) ∂(sphereProbabilityD 24).prod (sphereProbabilityD 24) :=
      integral_mono (sphereGaussianKernel24_pair_integrable ht) (integrable_const (1:ℝ))
        (fun p => sphereGaussianKernel24_le_one ht p.1 p.2)
    _ = 1 := by simp

def ambientSphereProbability24 : Measure (AmbientD 24) :=
  (sphereProbabilityD 24).map (fun x : (SphereD 24) => (x:(AmbientD 24)))

instance ambientSphereProbability24_probability : IsProbabilityMeasure ambientSphereProbability24 := by
  unfold ambientSphereProbability24
  infer_instance

theorem ambientSphereProbability24_charFun (z : (AmbientD 24)) :
    charFun ambientSphereProbability24 z =
      ∫ y : (SphereD 24), Complex.exp (⟪(y:(AmbientD 24)), z⟫ * Complex.I) ∂(sphereProbabilityD 24) := by
  rw [charFun_apply, ambientSphereProbability24, integral_map (by fun_prop) (by fun_prop)]

theorem ambientSphereProbability24_kernel_integral (t : ℝ) (x : (SphereD 24)) :
    (∫ y : (AmbientD 24), gaussianKernel t (x:(AmbientD 24)) y ∂ambientSphereProbability24) =
      sphereGaussianPotential24 t x := by
  rw [ambientSphereProbability24, integral_map (by fun_prop) (by unfold gaussianKernel; fun_prop)]
  simp only [sphereGaussianPotential24, sphereGaussianKernel24_eq_ambient]

theorem ambientSphereProbability24_kernel_pair (t : ℝ) :
    gaussianMeasurePair t ambientSphereProbability24 ambientSphereProbability24 =
      sphereGaussianBackground24 t := by
  unfold gaussianMeasurePair ambientSphereProbability24
  rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    integral_map (by fun_prop) (by unfold gaussianKernel; fun_prop)]
  simp only [sphereGaussianBackground24, sphereGaussianKernel24_eq_ambient,
    Prod.map_fst, Prod.map_snd]

def sphereGaussianDefect24 {N : ℕ} (t M : ℝ) (X : (ConfigurationD 24) N) : ℝ :=
  (∑ i, ∑ j, sphereGaussianKernel24 t (X i) (X j)) -
    2*M*(∑ i, sphereGaussianPotential24 t (X i)) + M^2*sphereGaussianBackground24 t

theorem sphereGaussianDefect24_eq_diffuse {N : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (M : ℝ) (X : (ConfigurationD 24) N) :
    sphereGaussianDefect24 t M X = diffuseGaussianDefect t M
      (fun i : Fin N => (X i:(AmbientD 24))) ambientSphereProbability24 := by
  unfold sphereGaussianDefect24 diffuseGaussianDefect
  simp only [sphereGaussianKernel24_eq_ambient, ambientSphereProbability24_kernel_integral,
    ambientSphereProbability24_kernel_pair]

theorem sphereGaussianDefect24_eq_normSq {N : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (M : ℝ) (X : (ConfigurationD 24) N) :
    sphereGaussianDefect24 t M X = ∫ z : (AmbientD 24),
      Complex.normSq ((∑ i : Fin N,
        Complex.exp (⟪(X i:(AmbientD 24)), Real.sqrt (2*t) • z⟫ * Complex.I)) -
        (M:ℂ)*(∫ y : (SphereD 24),
          Complex.exp (⟪(y:(AmbientD 24)), Real.sqrt (2*t) • z⟫ * Complex.I) ∂(sphereProbabilityD 24)))
      ∂stdGaussian (AmbientD 24) := by
  rw [sphereGaussianDefect24_eq_diffuse ht, diffuseGaussianDefect_eq_normSq ht]
  simp only [ambientSphereProbability24_charFun]

theorem sphereGaussianDefect24_nonneg {N : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (M : ℝ) (X : (ConfigurationD 24) N) : 0 ≤ sphereGaussianDefect24 t M X := by
  rw [sphereGaussianDefect24_eq_diffuse ht]
  exact diffuseGaussianDefect_nonneg ht M _ _

theorem sphereGaussianDefect24_charge_N {N : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (X : (ConfigurationD 24) N) :
    sphereGaussianDefect24 t (N:ℝ) X =
      (∑ i, ∑ j, sphereGaussianKernel24 t (X i) (X j)) - (N:ℝ)^2*sphereGaussianBackground24 t := by
  unfold sphereGaussianDefect24
  simp_rw [← sphereGaussianBackground24_eq_potential ht]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

#print axioms sphereGaussianKernel24_eq_ambient
#print axioms sphereGaussianKernel24_le_one
#print axioms sphereGaussianKernel24_rotation
#print axioms sphereGaussianKernel24_integrable
#print axioms sphereGaussianKernel24_pair_integrable
#print axioms sphereGaussianPotential24_rotation
#print axioms sphereGaussianPotential24_constant
#print axioms sphereGaussianBackground24_iterated
#print axioms sphereGaussianBackground24_eq_potential
#print axioms sphereGaussianBackground24_nonneg
#print axioms sphereGaussianBackground24_le_one
#print axioms ambientSphereProbability24_charFun
#print axioms ambientSphereProbability24_kernel_integral
#print axioms ambientSphereProbability24_kernel_pair
#print axioms sphereGaussianDefect24_eq_diffuse
#print axioms sphereGaussianDefect24_eq_normSq
#print axioms sphereGaussianDefect24_nonneg
#print axioms sphereGaussianDefect24_charge_N

end SphericalRiesz
