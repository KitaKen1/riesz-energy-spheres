import Riesz.SpherePartitionDensityRows8

/-! Positivity of the ORIGINAL finite localized sphere kernel defect.
Each component uses the explicit nonnegative Fourier-density measure from
Schwartz inversion. Its chart and normalized cutoff are actual functions;
no PSD witness is assumed. Finite-sum and integral identities assemble the
original point sums, sphere rows and double background. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped SchwartzMap FourierTransform
namespace SphericalRiesz

def spherePartitionSchwartzComponentDefect8 {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (X : Fin N → Sphere8)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a : ℝ) (i : Fin K) : ℝ :=
  (∑ p, ∑ q, spherePartitionSchwartzComponent8 ρ hρ g f a i (X p) (X q))-
    2*(N : ℝ)*(∑ p, ∫ y, spherePartitionSchwartzComponent8 ρ hρ g f a i (X p) y ∂sphereProbability8)+
    (N : ℝ)^2*(∫ x, ∫ y, spherePartitionSchwartzComponent8 ρ hρ g f a i x y
      ∂sphereProbability8 ∂sphereProbability8)

def spherePartitionSchwartzDefect8 {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (X : Fin N → Sphere8)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a : ℝ) : ℝ :=
  (∑ p, ∑ q, spherePartitionSchwartzKernel8 ρ hρ g f a (X p) (X q))-
    2*(N : ℝ)*(∑ p, spherePartitionSchwartzRow8 ρ hρ g f a (X p))+
    (N : ℝ)^2*spherePartitionSchwartzBackground8 ρ hρ g f a

theorem spherePartitionSchwartzComponentDefect8_eq_localized {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (X : Fin N → Sphere8)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a : ℝ) (i : Fin K) :
    spherePartitionSchwartzComponentDefect8 ρ hρ g X f a i =
      localizedSchwartzDefect f a N (sphereFiniteCutoffWeight8 ρ hρ g i)
        (rotatedSphereEqualAreaCoordinates8 (g i)) (spherePointMeasure8 X) sphereProbability8 := by
  unfold spherePartitionSchwartzComponentDefect8 localizedSchwartzDefect localizedSchwartzPair
    spherePartitionSchwartzComponent8
  simp only [spherePointMeasure8_integral]

theorem spherePartitionSchwartzComponentDefect8_nonneg {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (hc : Continuous (sphereChartCutoff8 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x) (X : Fin N → Sphere8)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ))
    (hFnonneg : ∀ z, 0 ≤ ((𝓕 f) z).re) (hFreal : ∀ z, ((𝓕 f) z).im = 0)
    (a : ℝ) (i : Fin K) :
    0 ≤ spherePartitionSchwartzComponentDefect8 ρ hρ g X f a i := by
  have hmeas := (sphereFiniteCutoffWeight8_continuous ρ hρ g hc hpos i).measurable
  have hn := sphereFiniteCutoffWeight8_nonneg ρ hρ g i
  have hle := sphereFiniteCutoffWeight8_le_one ρ hρ g hpos i
  rw [spherePartitionSchwartzComponentDefect8_eq_localized]
  exact localizedSchwartzDefect_nonneg f hFnonneg hFreal a N _ _ _ _ hmeas hn
    (rotatedSphereEqualAreaCoordinates8_measurable (g i))
    (sphereCutoff8_integrable _ hmeas hn hle _)
    (sphereCutoff8_integrable _ hmeas hn hle _)

theorem spherePartitionSchwartzKernel8_point_sum {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (X : Fin N → Sphere8)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a : ℝ) :
    (∑ p, ∑ q, spherePartitionSchwartzKernel8 ρ hρ g f a (X p) (X q)) =
      ∑ i, ∑ p, ∑ q, spherePartitionSchwartzComponent8 ρ hρ g f a i (X p) (X q) := by
  classical
  unfold spherePartitionSchwartzKernel8
  calc
    _ = ∑ p, ∑ i, ∑ q, spherePartitionSchwartzComponent8 ρ hρ g f a i (X p) (X q) := by
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem spherePartitionSchwartzRow8_point_sum {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (hc : Continuous (sphereChartCutoff8 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x) (X : Fin N → Sphere8)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a : ℝ) :
    (∑ p, spherePartitionSchwartzRow8 ρ hρ g f a (X p)) =
      ∑ i, ∑ p, ∫ y, spherePartitionSchwartzComponent8 ρ hρ g f a i (X p) y ∂sphereProbability8 := by
  classical
  simp_rw [spherePartitionSchwartzRow8_eq_sum ρ hρ g hc hpos]
  exact Finset.sum_comm

theorem spherePartitionSchwartzBackground8_eq_sum {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (hc : Continuous (sphereChartCutoff8 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a : ℝ) :
    spherePartitionSchwartzBackground8 ρ hρ g f a =
      ∑ i, ∫ x, ∫ y, spherePartitionSchwartzComponent8 ρ hρ g f a i x y ∂sphereProbability8 ∂sphereProbability8 := by
  classical
  change (∫ x, spherePartitionSchwartzRow8 ρ hρ g f a x ∂sphereProbability8) = _
  simp_rw [spherePartitionSchwartzRow8_eq_sum ρ hρ g hc hpos]
  exact integral_finsetSum _ fun i _ =>
    (spherePartitionSchwartzComponent8_product_integrable ρ hρ g hc hpos f a i).integral_prod_left

theorem spherePartitionSchwartzDefect8_eq_sum {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (hc : Continuous (sphereChartCutoff8 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x) (X : Fin N → Sphere8)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a : ℝ) :
    spherePartitionSchwartzDefect8 ρ hρ g X f a =
      ∑ i, spherePartitionSchwartzComponentDefect8 ρ hρ g X f a i := by
  classical
  rw [spherePartitionSchwartzDefect8, spherePartitionSchwartzKernel8_point_sum,
    spherePartitionSchwartzRow8_point_sum ρ hρ g hc hpos,
    spherePartitionSchwartzBackground8_eq_sum ρ hρ g hc hpos]
  simp only [spherePartitionSchwartzComponentDefect8, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum]

theorem spherePartitionSchwartzDefect8_nonneg {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (hc : Continuous (sphereChartCutoff8 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x) (X : Fin N → Sphere8)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ))
    (hFnonneg : ∀ z, 0 ≤ ((𝓕 f) z).re) (hFreal : ∀ z, ((𝓕 f) z).im = 0) (a : ℝ) :
    0 ≤ spherePartitionSchwartzDefect8 ρ hρ g X f a := by
  rw [spherePartitionSchwartzDefect8_eq_sum ρ hρ g hc hpos]
  exact Finset.sum_nonneg fun i _ =>
    spherePartitionSchwartzComponentDefect8_nonneg ρ hρ g hc hpos X f hFnonneg hFreal a i

theorem spherePartitionSchwartzKernel8_diagonal {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ)) (a : ℝ) (x : Sphere8) :
    spherePartitionSchwartzKernel8 ρ hρ g f a x x = (f 0).re := by
  classical
  simp only [spherePartitionSchwartzKernel8, spherePartitionSchwartzComponent8,
    sub_self, smul_zero, ← pow_two]
  rw [← Finset.sum_mul, sphereFiniteCutoffWeight8_sum_square ρ hρ g hpos, one_mul]

theorem spherePartitionSchwartzKernel8_normalized_lower {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (hc : Continuous (sphereChartCutoff8 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass8 ρ hρ g x) (hN : 0 < N) (X : Fin N → Sphere8)
    (f : 𝓢(EuclideanSpace ℝ (Fin 8), ℂ))
    (hFnonneg : ∀ z, 0 ≤ ((𝓕 f) z).re) (hFreal : ∀ z, ((𝓕 f) z).im = 0) (a : ℝ) :
    2*(∑ p, spherePartitionSchwartzRow8 ρ hρ g f a (X p))-
      (N : ℝ)*spherePartitionSchwartzBackground8 ρ hρ g f a ≤
      (∑ p, ∑ q, spherePartitionSchwartzKernel8 ρ hρ g f a (X p) (X q))/(N : ℝ) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hd := spherePartitionSchwartzDefect8_nonneg ρ hρ g hc hpos X f hFnonneg hFreal a
  unfold spherePartitionSchwartzDefect8 at hd
  apply (le_div_iff₀ hNR).mpr
  nlinarith

end SphericalRiesz
