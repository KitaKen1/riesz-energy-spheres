import Riesz.SphereBoundedKernelAssembly8
import Riesz.PatchGaussianDefect8

/-! The weighted long-range Gaussian kernel on the actual unit sphere.

`K(x,y) = ∫_{0<α≤1} α^p e^{-cα|x-y|²} dα` with `p > -1` is bounded by `1/(p+1)`, equal to
`1/(p+1)` on the diagonal, and its neutralized blocks are the `α^p`-averages of the Gaussian
blocks.  A Gaussian block is a diffuse Gaussian defect, hence nonnegative, so the full block of any
finite family against the uniform background is nonnegative.  The off-diagonal version (zero on the
diagonal) is the kernel used in the residual selection. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz

/-- The weighted long-range kernel. -/
def longRangeKernel8 (c p : ℝ) (x y : Sphere8) : ℝ :=
  ∫ α in Ioc (0:ℝ) 1, α^p*sphereGaussianKernel8 (c*α) x y

theorem longRange_weight_integrable {p : ℝ} (hp : -1 < p) :
    IntegrableOn (fun α : ℝ => α^p) (Ioc 0 1) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    (intervalIntegral.intervalIntegrable_rpow' hp)

theorem longRange_weight_integral {p : ℝ} (hp : -1 < p) :
    ∫ α in Ioc (0:ℝ) 1, α^p = 1/(p+1) := by
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl hp)]
  rw [Real.one_rpow, Real.zero_rpow (by linarith : p+1 ≠ 0)]
  ring

theorem longRange_integrand_measurable (c p : ℝ) :
    Measurable (fun z : ℝ × (Sphere8 × Sphere8) =>
      z.1^p*sphereGaussianKernel8 (c*z.1) z.2.1 z.2.2) := by
  unfold sphereGaussianKernel8
  apply Measurable.mul (measurable_fst.pow_const p)
  apply Real.measurable_exp.comp
  apply Measurable.neg
  apply Measurable.mul (measurable_const.mul measurable_fst)
  exact ((continuous_dist.comp (continuous_fst.comp continuous_snd |>.prodMk
    (continuous_snd.comp continuous_snd))).measurable).pow_const 2

theorem longRange_integrand_le {c p α : ℝ} (hc : 0 ≤ c) (hα : α ∈ Ioc (0:ℝ) 1) (x y : Sphere8) :
    |α^p*sphereGaussianKernel8 (c*α) x y| ≤ α^p := by
  have h0 : 0 ≤ α^p := Real.rpow_nonneg hα.1.le _
  rw [abs_of_nonneg (mul_nonneg h0 (sphereGaussianKernel8_nonneg _ _ _))]
  exact mul_le_of_le_one_right h0 (sphereGaussianKernel8_le_one (mul_nonneg hc hα.1.le) _ _)

theorem continuous_gaussian_param (c : ℝ) (x y : Sphere8) :
    Continuous (fun α : ℝ => sphereGaussianKernel8 (c*α) x y) := by
  unfold sphereGaussianKernel8
  fun_prop

theorem longRange_integrand_integrable {c p : ℝ} (hc : 0 ≤ c) (hp : -1 < p) (x y : Sphere8) :
    IntegrableOn (fun α : ℝ => α^p*sphereGaussianKernel8 (c*α) x y) (Ioc 0 1) := by
  refine (longRange_weight_integrable hp).mono' ?_ ?_
  · exact ((measurable_id.pow_const p).mul
      (continuous_gaussian_param c x y).measurable).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
    rw [Real.norm_eq_abs]
    exact longRange_integrand_le hc hα x y

theorem longRangeKernel8_symm (c p : ℝ) (x y : Sphere8) :
    longRangeKernel8 c p x y = longRangeKernel8 c p y x := by
  unfold longRangeKernel8 sphereGaussianKernel8
  simp_rw [dist_comm x y]

theorem longRangeKernel8_nonneg (c p : ℝ) (x y : Sphere8) : 0 ≤ longRangeKernel8 c p x y :=
  setIntegral_nonneg measurableSet_Ioc fun _α hα =>
    mul_nonneg (Real.rpow_nonneg hα.1.le _) (sphereGaussianKernel8_nonneg _ _ _)

theorem longRangeKernel8_self (c : ℝ) {p : ℝ} (hp : -1 < p) (x : Sphere8) :
    longRangeKernel8 c p x x = 1/(p+1) := by
  unfold longRangeKernel8
  simp only [sphereGaussianKernel8_self, mul_one]
  exact longRange_weight_integral hp

theorem longRangeKernel8_le {c p : ℝ} (hc : 0 ≤ c) (hp : -1 < p) (x y : Sphere8) :
    longRangeKernel8 c p x y ≤ 1/(p+1) := by
  unfold longRangeKernel8
  rw [← longRange_weight_integral hp]
  apply setIntegral_mono_on (longRange_integrand_integrable hc hp x y)
    (longRange_weight_integrable hp) measurableSet_Ioc
  intro α hα
  exact (le_abs_self _).trans (longRange_integrand_le hc hα x y)

theorem longRangeKernel8_abs_le {c p : ℝ} (hc : 0 ≤ c) (hp : -1 < p) (x y : Sphere8) :
    |longRangeKernel8 c p x y| ≤ 1/(p+1) := by
  rw [abs_of_nonneg (longRangeKernel8_nonneg c p x y)]
  exact longRangeKernel8_le hc hp x y

theorem longRangeKernel8_measurable (c p : ℝ) :
    StronglyMeasurable (fun q : Sphere8 × Sphere8 => longRangeKernel8 c p q.1 q.2) := by
  have hf : StronglyMeasurable (fun z : (Sphere8 × Sphere8) × ℝ =>
      z.2^p*sphereGaussianKernel8 (c*z.2) z.1.1 z.1.2) :=
    ((longRange_integrand_measurable c p).comp measurable_swap).stronglyMeasurable
  exact hf.integral_prod_right' (ν := volume.restrict (Ioc (0:ℝ) 1))

/-- The off-diagonal long-range kernel used in the residual selection. -/
def longRangeOffKernel8 (c p : ℝ) (x y : Sphere8) : ℝ :=
  Set.indicator ({x}ᶜ : Set Sphere8) (longRangeKernel8 c p x) y

theorem longRangeOffKernel8_of_ne (c p : ℝ) {x y : Sphere8} (h : x ≠ y) :
    longRangeOffKernel8 c p x y = longRangeKernel8 c p x y := by
  unfold longRangeOffKernel8
  exact Set.indicator_of_mem (show y ∈ ({x}ᶜ : Set Sphere8) from fun hy => h hy.symm) _

theorem longRangeOffKernel8_self (c p : ℝ) (x : Sphere8) : longRangeOffKernel8 c p x x = 0 := by
  unfold longRangeOffKernel8
  exact Set.indicator_of_notMem (by simp) _

theorem longRangeOffKernel8_symm (c p : ℝ) (x y : Sphere8) :
    longRangeOffKernel8 c p x y = longRangeOffKernel8 c p y x := by
  by_cases h : x = y
  · subst h; rfl
  · rw [longRangeOffKernel8_of_ne c p h, longRangeOffKernel8_of_ne c p (Ne.symm h),
      longRangeKernel8_symm]

theorem longRangeOffKernel8_nonneg (c p : ℝ) (x y : Sphere8) : 0 ≤ longRangeOffKernel8 c p x y := by
  unfold longRangeOffKernel8
  exact Set.indicator_nonneg (fun z _ => longRangeKernel8_nonneg c p x z) y

theorem longRangeOffKernel8_ae_eq (c p : ℝ) (μ : Measure Sphere8) [NullSingletonClass μ]
    (x : Sphere8) : longRangeOffKernel8 c p x =ᵐ[μ] longRangeKernel8 c p x := by
  have hnull : μ {x} = 0 := measure_singleton x
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with y hy
  exact longRangeOffKernel8_of_ne c p (fun h => hy (by rw [h]; rfl))

theorem longRangeKernel8_row_measurable (c p : ℝ) (x : Sphere8) :
    StronglyMeasurable (longRangeKernel8 c p x) := by
  have hg : Continuous (fun z : Sphere8 × ℝ => sphereGaussianKernel8 (c*z.2) x z.1) := by
    unfold sphereGaussianKernel8
    fun_prop
  have hf : StronglyMeasurable (fun z : Sphere8 × ℝ => z.2^p*sphereGaussianKernel8 (c*z.2) x z.1) :=
    ((measurable_snd.pow_const p).mul hg.measurable).stronglyMeasurable
  exact hf.integral_prod_right' (ν := volume.restrict (Ioc (0:ℝ) 1))

theorem longRangeOffKernel8_row_measurable (c p : ℝ) (x : Sphere8) :
    StronglyMeasurable (longRangeOffKernel8 c p x) := by
  unfold longRangeOffKernel8
  exact (longRangeKernel8_row_measurable c p x).indicator (measurableSet_singleton x).compl

end SphericalRiesz
