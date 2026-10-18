import Riesz.LeechCommonBudget24

/-! Reduction of the Gaussian window of a combined configuration to its foreground.

Gaussian kernels are positive definite, so for every `ε > 0`

`Σ_{all} K_t ≤ (1+ε) Σ_{fg,fg} K_t + (1+1/ε) Σ_{res,res} K_t`.

The residual pair sum is nonincreasing in the scale.  Hence one residual Gaussian window at a
small scale `t₀` controls the residual part of every window `t ≥ t₀`, and no
residual/foreground cross estimate is needed for the sharp windows.  The sharp foreground
profile itself is not proved here. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
namespace SphericalRiesz

/-- Positive definiteness: the full Gaussian sum of a combined configuration is controlled by
the foreground sum and the residual sum. -/
theorem combinedConfiguration24_gaussian_young {ι : Type*} [Fintype ι] {n N : ℕ}
    (x : ι → SphereD 24) (z : Fin n → SphereD 24) (hcard : Fintype.card ι+n = N)
    (hx : Function.Injective x) (hz : Function.Injective z) (havoid : ∀ j, z j ∉ range x)
    {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε) :
    (∑ i, ∑ j, sphereGaussianKernel24 t (combinedConfiguration24 x z hcard hx hz havoid i)
      (combinedConfiguration24 x z hcard hx hz havoid j)) ≤
      (1+ε)*(∑ a, ∑ b, sphereGaussianKernel24 t (x a) (x b))+
        (1+1/ε)*cellPairSum (sphereGaussianKernel24 t) z := by
  rw [combinedConfiguration24_sum x z hcard hx hz havoid (sphereGaussianKernel24 t)
    (sphereGaussianKernel24_comm t)]
  have hpsd := gaussianMeasureDefect_nonneg ht (1/ε)
    (finitePointMeasure (fun a => (x a : AmbientD 24)))
    (finitePointMeasure (fun j => (z j : AmbientD 24)))
  have hff : gaussianMeasurePair t (finitePointMeasure (fun a => (x a : AmbientD 24)))
      (finitePointMeasure (fun a => (x a : AmbientD 24))) =
      ∑ a, ∑ b, sphereGaussianKernel24 t (x a) (x b) := by
    rw [gaussianMeasurePair_finite_both ht]
    simp_rw [← sphereGaussianKernel24_eq_ambient]
  have hrr : gaussianMeasurePair t (finitePointMeasure (fun j => (z j : AmbientD 24)))
      (finitePointMeasure (fun j => (z j : AmbientD 24))) =
      cellPairSum (sphereGaussianKernel24 t) z := by
    rw [gaussianMeasurePair_finite_both ht]
    simp_rw [← sphereGaussianKernel24_eq_ambient]
    rfl
  have hfr : gaussianMeasurePair t (finitePointMeasure (fun a => (x a : AmbientD 24)))
      (finitePointMeasure (fun j => (z j : AmbientD 24))) =
      ∑ j, ∑ a, sphereGaussianKernel24 t (z j) (x a) := by
    rw [gaussianMeasurePair_finite_left ht]
    simp_rw [finitePointMeasure_integral, ← sphereGaussianKernel24_eq_ambient]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ =>
      sphereGaussianKernel24_comm t _ _
  unfold gaussianMeasureDefect at hpsd
  rw [hff, hrr, hfr] at hpsd
  have hmul := mul_nonneg hε.le hpsd
  have he : ε*((∑ a, ∑ b, sphereGaussianKernel24 t (x a) (x b))-
      2*(1/ε)*(∑ j, ∑ a, sphereGaussianKernel24 t (z j) (x a))+
      (1/ε)^2*cellPairSum (sphereGaussianKernel24 t) z) =
      ε*(∑ a, ∑ b, sphereGaussianKernel24 t (x a) (x b))-
      2*(∑ j, ∑ a, sphereGaussianKernel24 t (z j) (x a))+
      (1/ε)*cellPairSum (sphereGaussianKernel24 t) z := by
    have h1 : ε*(1/ε) = 1 := mul_one_div_cancel hε.ne'
    calc _ = ε*(∑ a, ∑ b, sphereGaussianKernel24 t (x a) (x b))-
          2*(ε*(1/ε))*(∑ j, ∑ a, sphereGaussianKernel24 t (z j) (x a))+
          (ε*(1/ε))*(1/ε)*cellPairSum (sphereGaussianKernel24 t) z := by ring
      _ = _ := by rw [h1]; ring
  rw [he] at hmul
  unfold residualCrossSum
  linarith

/-- The residual Gaussian pair sum is nonincreasing in the scale. -/
theorem cellPairSum_gaussian_anti {n : ℕ} (z : Fin n → SphereD 24) {t₀ t : ℝ} (h : t₀ ≤ t) :
    cellPairSum (sphereGaussianKernel24 t) z ≤ cellPairSum (sphereGaussianKernel24 t₀) z := by
  unfold cellPairSum
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  unfold sphereGaussianKernel24
  apply Real.exp_le_exp.mpr
  have hd : 0 ≤ dist (z i) (z j)^2 := sq_nonneg _
  nlinarith [mul_nonneg (sub_nonneg.mpr h) hd]

/-- Full scaled Gaussian profile of a combined configuration: the foreground profile with a
factor `1+ε`, plus the residual window at any smaller scale with a factor `1+1/ε`. -/
theorem combinedConfiguration24_fullScaled_le {ι : Type*} [Fintype ι] {n N : ℕ} (hN : 0 < N)
    (x : ι → SphereD 24) (z : Fin n → SphereD 24) (hcard : Fintype.card ι+n = N)
    (hx : Function.Injective x) (hz : Function.Injective z) (havoid : ∀ j, z j ∉ range x)
    {α α₀ ε : ℝ} (hα₀ : 0 ≤ α₀) (hα : α₀ ≤ α) (hε : 0 < ε) :
    sphereGaussianFullScaled24 α (combinedConfiguration24 x z hcard hx hz havoid) ≤
      (1+ε)*((∑ a, ∑ b, sphereGaussianKernel24 (sphereGaussianScale24 N α) (x a) (x b))/(N:ℝ))+
        (1+1/ε)*(cellPairSum (sphereGaussianKernel24 (sphereGaussianScale24 N α₀)) z/(N:ℝ)) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hc := sphereGaussianDensityFactor24_pos hN
  have hs0 : 0 ≤ sphereGaussianScale24 N α := by
    rw [sphereGaussianScale24_eq_factor]
    exact mul_nonneg hc.le (hα₀.trans hα)
  have hmono : sphereGaussianScale24 N α₀ ≤ sphereGaussianScale24 N α := by
    rw [sphereGaussianScale24_eq_factor, sphereGaussianScale24_eq_factor]
    exact mul_le_mul_of_nonneg_left hα hc.le
  have hy := combinedConfiguration24_gaussian_young x z hcard hx hz havoid hs0 hε
  have ha := cellPairSum_gaussian_anti z hmono
  have h1ε : 0 ≤ 1+1/ε := by positivity
  unfold sphereGaussianFullScaled24
  rw [show (1+ε)*((∑ a, ∑ b, sphereGaussianKernel24 (sphereGaussianScale24 N α) (x a) (x b))/
        (N:ℝ))+(1+1/ε)*(cellPairSum (sphereGaussianKernel24 (sphereGaussianScale24 N α₀)) z/
        (N:ℝ)) =
      ((1+ε)*(∑ a, ∑ b, sphereGaussianKernel24 (sphereGaussianScale24 N α) (x a) (x b))+
        (1+1/ε)*cellPairSum (sphereGaussianKernel24 (sphereGaussianScale24 N α₀)) z)/(N:ℝ) by
    ring]
  exact div_le_div_of_nonneg_right
    (hy.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ha h1ε))) hNR.le

end SphericalRiesz
