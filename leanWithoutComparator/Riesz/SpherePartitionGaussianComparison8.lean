import Riesz.SpherePartitionSchwartzPSD8
import Riesz.SphereGaussianProfileLowerBridge8

/-! The original finite sphere Schwartz kernel is a pointwise Gaussian
minorant under explicit Euclidean minorization at beta=alpha*L^2 and the
actual supported chord bound. No nonnegativity of f is used. Exact diagonal
correction and the checked finite PSD give the original normalized Gaussian
point-sum lower bound. This does not construct a sharp E8 minorant. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology SchwartzMap FourierTransform
namespace SphericalRiesz

theorem sphereChartGaussian8_comparison (L α a : ℝ) (hL : 0 ≤ L) (hα : 0 ≤ α)
    (x y : Sphere8) (z : EuclideanSpace ℝ (Fin 8)) (hd : dist x y ≤ L*‖z‖) :
    Real.exp (-(Real.pi*(α*L^2)*‖a • z‖^2)) ≤
      sphereGaussianKernel8 (Real.pi*α*a^2) x y := by
  have hd2 : (dist x y)^2 ≤ (L*‖z‖)^2 := pow_le_pow_left₀ dist_nonneg hd 2
  have hm := mul_le_mul_of_nonneg_left hd2
    (mul_nonneg (mul_nonneg Real.pi_pos.le hα) (sq_nonneg a))
  apply Real.exp_le_exp.mpr
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, sphereGaussianKernel8] at *
  nlinarith

theorem spherePartitionSchwartzComponent8_gaussian_le {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (L α a : ℝ) (hL : 0 ≤ L) (hα : 0 ≤ α)
    (hLip : ∀ i x y, sphereFiniteCutoffWeight8 ρ hρ g i x ≠ 0 →
      sphereFiniteCutoffWeight8 ρ hρ g i y ≠ 0 →
      dist x y ≤ L*‖rotatedSphereEqualAreaCoordinates8 (g i) x-
        rotatedSphereEqualAreaCoordinates8 (g i) y‖)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ))
    (hminor : ∀ z, (f z).re ≤ Real.exp (-(Real.pi*(α*L^2)*‖z‖^2)))
    (i : Fin K) (x y : Sphere8) :
    spherePartitionSchwartzComponent8 ρ hρ g f a i x y ≤
      sphereFiniteCutoffWeight8 ρ hρ g i x*sphereFiniteCutoffWeight8 ρ hρ g i y*
        sphereGaussianKernel8 (Real.pi*α*a^2) x y := by
  by_cases hx : sphereFiniteCutoffWeight8 ρ hρ g i x = 0
  · simp [spherePartitionSchwartzComponent8, hx]
  by_cases hy : sphereFiniteCutoffWeight8 ρ hρ g i y = 0
  · simp [spherePartitionSchwartzComponent8, hy]
  have h := (hminor _).trans (sphereChartGaussian8_comparison L α a hL hα x y _ (hLip i x y hx hy))
  exact mul_le_mul_of_nonneg_left h
    (mul_nonneg (sphereFiniteCutoffWeight8_nonneg ρ hρ g i x)
      (sphereFiniteCutoffWeight8_nonneg ρ hρ g i y))

theorem spherePartitionSchwartzKernel8_gaussian_le {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x)
    (L α a : ℝ) (hL : 0 ≤ L) (hα : 0 ≤ α)
    (hLip : ∀ i x y, sphereFiniteCutoffWeight8 ρ hρ g i x ≠ 0 →
      sphereFiniteCutoffWeight8 ρ hρ g i y ≠ 0 →
      dist x y ≤ L*‖rotatedSphereEqualAreaCoordinates8 (g i) x-
        rotatedSphereEqualAreaCoordinates8 (g i) y‖)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ))
    (hminor : ∀ z, (f z).re ≤ Real.exp (-(Real.pi*(α*L^2)*‖z‖^2))) (x y : Sphere8) :
    spherePartitionSchwartzKernel8 ρ hρ g f a x y ≤ sphereGaussianKernel8 (Real.pi*α*a^2) x y := by
  classical
  calc
    _ ≤ ∑ i, sphereFiniteCutoffWeight8 ρ hρ g i x*sphereFiniteCutoffWeight8 ρ hρ g i y*
        sphereGaussianKernel8 (Real.pi*α*a^2) x y :=
      Finset.sum_le_sum fun i _ => spherePartitionSchwartzComponent8_gaussian_le ρ hρ g L α a hL hα hLip f hminor i x y
    _ = (∑ i, sphereFiniteCutoffWeight8 ρ hρ g i x*sphereFiniteCutoffWeight8 ρ hρ g i y)*
        sphereGaussianKernel8 (Real.pi*α*a^2) x y := (Finset.sum_mul _ _ _).symm
    _ ≤ 1*sphereGaussianKernel8 (Real.pi*α*a^2) x y :=
      mul_le_mul_of_nonneg_right (sphereFiniteCutoffWeight8_correlation_le_one ρ hρ g hpos x y)
        (sphereGaussianKernel8_nonneg _ _ _)
    _ = _ := one_mul _

theorem spherePartitionSchwartzKernel8_diagonal_corrected_sum_le {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x) (X : Fin N → Sphere8)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a t : ℝ)
    (hminor : ∀ x y, spherePartitionSchwartzKernel8 ρ hρ g f a x y ≤ sphereGaussianKernel8 t x y) :
    (∑ p, ∑ q, spherePartitionSchwartzKernel8 ρ hρ g f a (X p) (X q))+
      (N : ℝ)*(1-(f 0).re) ≤ ∑ p, ∑ q, sphereGaussianKernel8 t (X p) (X q) := by
  classical
  have hpq (p q : Fin N) : spherePartitionSchwartzKernel8 ρ hρ g f a (X p) (X q)+
      (if p=q then 1-(f 0).re else 0) ≤ sphereGaussianKernel8 t (X p) (X q) := by
    by_cases h : p=q
    · subst q
      simp only [spherePartitionSchwartzKernel8_diagonal ρ hρ g hpos,
        sphereGaussianKernel8_self, ↓reduceIte]
      linarith
    · simpa only [ite_eq_right h, add_zero] using hminor (X p) (X q)
  have hs := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset (Fin N))) =>
    Finset.sum_le_sum (fun q (_ : q ∈ (Finset.univ : Finset (Fin N))) => hpq p q))
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hs

theorem spherePartitionGaussian8_normalized_lower {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (hc : Continuous (sphereChartCutoff8 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x) (hN : 0 < N) (X : Fin N → Sphere8)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ))
    (hFnonneg : ∀ z, 0 ≤ ((𝓕 f) z).re) (hFreal : ∀ z, ((𝓕 f) z).im = 0) (a t : ℝ)
    (hminor : ∀ x y, spherePartitionSchwartzKernel8 ρ hρ g f a x y ≤ sphereGaussianKernel8 t x y) :
    2*(∑ p, spherePartitionSchwartzRow8 ρ hρ g f a (X p))-
      (N : ℝ)*spherePartitionSchwartzBackground8 ρ hρ g f a+1-(f 0).re ≤
      (∑ p, ∑ q, sphereGaussianKernel8 t (X p) (X q))/(N : ℝ) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hs := spherePartitionSchwartzKernel8_diagonal_corrected_sum_le ρ hρ g hpos X f a t hminor
  have hd := spherePartitionSchwartzKernel8_normalized_lower ρ hρ g hc hpos hN X f hFnonneg hFreal a
  have hs' := div_le_div_of_nonneg_right hs hNR.le
  have he : ((∑ p, ∑ q, spherePartitionSchwartzKernel8 ρ hρ g f a (X p) (X q))+
      (N : ℝ)*(1-(f 0).re))/(N : ℝ) =
      (∑ p, ∑ q, spherePartitionSchwartzKernel8 ρ hρ g f a (X p) (X q))/(N : ℝ)+1-(f 0).re := by
    field_simp [hNR.ne']
    <;> ring
  rw [he] at hs'
  linarith

theorem sphereGaussianScale8_eq_partition_density (N : ℕ) (α : ℝ) :
    sphereGaussianScale8 N α = Real.pi*α*(spherePartitionDensityScale8 N)^2 := by
  have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
  have hρ : 0 ≤ (N : ℝ)/sphereArea8.real univ := div_nonneg (Nat.cast_nonneg _) hA.le
  have hp : (spherePartitionDensityScale8 N)^2 = ((N : ℝ)/sphereArea8.real univ)^(1/4 : ℝ) := by
    unfold spherePartitionDensityScale8
    rw [← Real.rpow_mul_natCast hρ]
    norm_num
  rw [hp]
  rfl

end SphericalRiesz
