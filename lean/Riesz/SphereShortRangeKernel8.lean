import Riesz.SphereResidual8
import Riesz.SphereRieszShortRange8
import Riesz.ResidualJointSelection

/-! The weighted short-range kernel on the actual unit sphere.

`k(x,y) = ∫_{α>1} α^p e^{-cα|x-y|²} dα` dominates every short-range tail:
for `R ≥ 1` and `p = s/2-1+γ`, `∫_{α>R} α^(s/2-1) e^{-cα|x-y|²} dα ≤ R^(-γ) k(x,y)`.
Its rows are bounded by Tonelli and the actual sphere Gaussian background:
`∫ k(x,y) dσ(y) = ∫_{α>1} α^p B(cα) dα ≤ (105/32) c⁻⁴/(3-p)` for `p < 3`.
On the diagonal the integrand `α^p` is not integrable when `p ≥ -1`, so the kernel vanishes there. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace SphericalRiesz

/-- The weighted short-range kernel. -/
def shortRangeKernel8 (c p : ℝ) (x y : Sphere8) : ℝ :=
  ∫ α in Ioi (1:ℝ), α^p*sphereGaussianKernel8 (c*α) x y

theorem shortRangeKernel8_symm (c p : ℝ) (x y : Sphere8) :
    shortRangeKernel8 c p x y = shortRangeKernel8 c p y x := by
  unfold shortRangeKernel8 sphereGaussianKernel8
  simp_rw [dist_comm x y]

theorem shortRangeKernel8_nonneg (c p : ℝ) (x y : Sphere8) : 0 ≤ shortRangeKernel8 c p x y :=
  setIntegral_nonneg measurableSet_Ioi fun _α hα =>
    mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (le_of_lt hα)) _)
      (sphereGaussianKernel8_nonneg _ _ _)

theorem shortRangeKernel8_self (c : ℝ) {p : ℝ} (hp : -1 ≤ p) (x : Sphere8) :
    shortRangeKernel8 c p x x = 0 := by
  unfold shortRangeKernel8
  simp only [sphereGaussianKernel8_self, mul_one]
  apply integral_undef
  intro h
  have := (integrableOn_Ioi_rpow_iff (s := p) zero_lt_one).mp h
  linarith

theorem ofReal_setIntegral_Ioi_le_lintegral {f : ℝ → ℝ} {a : ℝ} (hf : ∀ α ∈ Ioi a, 0 ≤ f α) :
    ENNReal.ofReal (∫ α in Ioi a, f α) ≤ ∫⁻ α in Ioi a, ENNReal.ofReal (f α) := by
  by_cases hi : IntegrableOn f (Ioi a)
  · rw [ofReal_integral_eq_lintegral_ofReal hi]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
    exact hf α hα
  · rw [integral_undef hi, ENNReal.ofReal_zero]
    exact zero_le

theorem shortRangeKernel8_measurable (c p : ℝ) :
    StronglyMeasurable (fun q : Sphere8 × Sphere8 => shortRangeKernel8 c p q.1 q.2) := by
  have hf : StronglyMeasurable (fun z : (Sphere8 × Sphere8) × ℝ =>
      z.2^p*sphereGaussianKernel8 (c*z.2) z.1.1 z.1.2) := by
    apply Measurable.stronglyMeasurable
    unfold sphereGaussianKernel8
    apply Measurable.mul (measurable_snd.pow_const p)
    apply Real.measurable_exp.comp
    apply Measurable.neg
    apply Measurable.mul (measurable_const.mul measurable_snd)
    exact ((continuous_dist.comp (continuous_fst.comp continuous_fst |>.prodMk
      (continuous_snd.comp continuous_fst))).measurable).pow_const 2
  exact hf.integral_prod_right' (ν := volume.restrict (Ioi (1:ℝ)))

theorem shortRangeKernel8_row_measurable (c p : ℝ) (x : Sphere8) :
    StronglyMeasurable (shortRangeKernel8 c p x) := by
  have hf : StronglyMeasurable (fun z : Sphere8 × ℝ =>
      z.2^p*sphereGaussianKernel8 (c*z.2) x z.1) := by
    apply Measurable.stronglyMeasurable
    unfold sphereGaussianKernel8
    apply Measurable.mul (measurable_snd.pow_const p)
    apply Real.measurable_exp.comp
    apply Measurable.neg
    apply Measurable.mul (measurable_const.mul measurable_snd)
    exact ((continuous_dist.comp (continuous_const.prodMk continuous_fst)).measurable).pow_const 2
  exact hf.integral_prod_right' (ν := volume.restrict (Ioi (1:ℝ)))

/-- Tonelli bound of a row against the actual uniform probability. -/
theorem shortRangeKernel8_row_lintegral_le {c p : ℝ} (hc : 0 < c) (hp : p < 3) (x : Sphere8) :
    ∫⁻ y, ENNReal.ofReal (shortRangeKernel8 c p x y) ∂sphereProbability8 ≤
      ENNReal.ofReal ((105/32)/c^4/(3-p)) := by
  set F : ℝ → Sphere8 → ℝ≥0∞ := fun α y => ENNReal.ofReal (α^p*sphereGaussianKernel8 (c*α) x y)
    with hF
  have hFm : Measurable (Function.uncurry F) := by
    simp only [hF, Function.uncurry_def]
    apply ENNReal.measurable_ofReal.comp
    unfold sphereGaussianKernel8
    apply Measurable.mul (measurable_fst.pow_const p)
    apply Real.measurable_exp.comp
    apply Measurable.neg
    apply Measurable.mul (measurable_const.mul measurable_fst)
    exact ((continuous_dist.comp (continuous_const.prodMk continuous_snd)).measurable).pow_const 2
  have h1 : ∀ y, ENNReal.ofReal (shortRangeKernel8 c p x y) ≤ ∫⁻ α in Ioi 1, F α y := by
    intro y
    apply ofReal_setIntegral_Ioi_le_lintegral
    intro α hα
    exact mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (le_of_lt hα)) _)
      (sphereGaussianKernel8_nonneg _ _ _)
  have h2 : ∫⁻ y, ∫⁻ α in Ioi 1, F α y ∂volume ∂sphereProbability8 =
      ∫⁻ α in Ioi 1, ∫⁻ y, F α y ∂sphereProbability8 :=
    lintegral_lintegral_swap ((hFm.comp measurable_swap).aemeasurable)
  have h3 : ∀ α ∈ Ioi (1:ℝ), ∫⁻ y, F α y ∂sphereProbability8 =
      ENNReal.ofReal (α^p*sphereGaussianBackground8 (c*α)) := by
    intro α hα
    have hα0 : 0 < α := zero_lt_one.trans hα
    have ht : 0 ≤ c*α := (mul_pos hc hα0).le
    have hi : Integrable (fun y => α^p*sphereGaussianKernel8 (c*α) x y) sphereProbability8 :=
      (sphereGaussianKernel8_integrable ht x).const_mul _
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun y =>
      mul_nonneg (Real.rpow_nonneg hα0.le _) (sphereGaussianKernel8_nonneg _ _ _)),
      integral_const_mul, sphereGaussianBackground8_eq_potential ht x]
    rfl
  have h4 : ∀ α ∈ Ioi (1:ℝ), ENNReal.ofReal (α^p*sphereGaussianBackground8 (c*α)) ≤
      ENNReal.ofReal ((105/32)/c^4*α^(p-4)) := by
    intro α hα
    have hα0 : 0 < α := zero_lt_one.trans hα
    apply ENNReal.ofReal_le_ofReal
    have hB := sphereGaussianBackground8_decay (mul_pos hc hα0)
    have he : (105/32)/c^4*α^(p-4) = α^p*((105/32:ℝ)/(c*α)^4) := by
      rw [Real.rpow_sub hα0, show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast, mul_pow]
      field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hα0.le _)
  have hint : IntegrableOn (fun α : ℝ => (105/32)/c^4*α^(p-4)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
  have hval : ∫ α in Ioi (1:ℝ), (105/32)/c^4*α^(p-4) = (105/32)/c^4/(3-p) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
    have h3p : (3:ℝ)-p ≠ 0 := by linarith
    have hp1 : p-4+1 ≠ 0 := by linarith
    field_simp
    ring
  calc ∫⁻ y, ENNReal.ofReal (shortRangeKernel8 c p x y) ∂sphereProbability8
      ≤ ∫⁻ y, ∫⁻ α in Ioi 1, F α y ∂volume ∂sphereProbability8 := lintegral_mono h1
    _ = ∫⁻ α in Ioi 1, ∫⁻ y, F α y ∂sphereProbability8 := h2
    _ = ∫⁻ α in Ioi 1, ENNReal.ofReal (α^p*sphereGaussianBackground8 (c*α)) :=
        setLIntegral_congr_fun measurableSet_Ioi h3
    _ ≤ ∫⁻ α in Ioi 1, ENNReal.ofReal ((105/32)/c^4*α^(p-4)) :=
        setLIntegral_mono (by fun_prop) h4
    _ = ENNReal.ofReal ((105/32)/c^4/(3-p)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint, hval]
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
        exact mul_nonneg (by positivity) (Real.rpow_nonneg (zero_le_one.trans (le_of_lt hα)) _)

theorem shortRangeKernel8_row_integrable {c p : ℝ} (hc : 0 < c) (hp : p < 3) (x : Sphere8) :
    Integrable (shortRangeKernel8 c p x) sphereProbability8 := by
  refine ⟨(shortRangeKernel8_row_measurable c p x).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have he : ∀ y, ‖shortRangeKernel8 c p x y‖ₑ = ENNReal.ofReal (shortRangeKernel8 c p x y) :=
    fun y => Real.enorm_eq_ofReal (shortRangeKernel8_nonneg c p x y)
  simp_rw [he]
  exact (shortRangeKernel8_row_lintegral_le hc hp x).trans_lt ENNReal.ofReal_lt_top

theorem shortRangeKernel8_row_integral_le {c p : ℝ} (hc : 0 < c) (hp : p < 3) (x : Sphere8) :
    ∫ y, shortRangeKernel8 c p x y ∂sphereProbability8 ≤ (105/32)/c^4/(3-p) := by
  have h := shortRangeKernel8_row_lintegral_le hc hp x
  rw [← ofReal_integral_eq_lintegral_ofReal (shortRangeKernel8_row_integrable hc hp x)
    (Eventually.of_forall fun y => shortRangeKernel8_nonneg c p x y)] at h
  have h3 : 0 ≤ (105/32)/c^4/(3-p) := by
    have : 0 < 3-p := by linarith
    positivity
  exact (ENNReal.ofReal_le_ofReal_iff h3).mp h

theorem shortRangeKernel8_restricted_integrable {c p : ℝ} (hc : 0 < c) (hp : p < 3)
    (A : Set Sphere8) (x : Sphere8) :
    Integrable (shortRangeKernel8 c p x) (sphereRestrictedProbability8 A) := by
  simpa only [sphereRestrictedProbability8, Measure.restrict_apply_univ] using
    (shortRangeKernel8_row_integrable hc hp x).restrict (s := A) |>.to_average

theorem shortRangeKernel8_restricted_row_le {c p : ℝ} (hc : 0 < c) (hp : p < 3)
    (A : Set Sphere8) (x : Sphere8) :
    residualRowPotential (sphereRestrictedProbability8 A) (shortRangeKernel8 c p) x ≤
      ((sphereProbability8 A)⁻¹).toReal*((105/32)/c^4/(3-p)) := by
  unfold residualRowPotential sphereRestrictedProbability8
  rw [integral_smul_measure, smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  calc ∫ y in A, shortRangeKernel8 c p x y ∂sphereProbability8
      ≤ ∫ y, shortRangeKernel8 c p x y ∂sphereProbability8 :=
        setIntegral_le_integral (shortRangeKernel8_row_integrable hc hp x)
          (Eventually.of_forall fun y => shortRangeKernel8_nonneg c p x y)
    _ ≤ _ := shortRangeKernel8_row_integral_le hc hp x

theorem shortRangeKernel8_restricted_rowPotential_integrable {c p : ℝ} (hc : 0 < c) (hp : p < 3)
    (A : Set Sphere8) (hA : sphereProbability8 A ≠ 0) :
    Integrable (residualRowPotential (sphereRestrictedProbability8 A) (shortRangeKernel8 c p))
      (sphereRestrictedProbability8 A) := by
  let := sphereRestrictedProbability8_probability A hA
  have hm : StronglyMeasurable
      (residualRowPotential (sphereRestrictedProbability8 A) (shortRangeKernel8 c p)) :=
    (shortRangeKernel8_measurable c p).integral_prod_right'
      (ν := sphereRestrictedProbability8 A)
  apply Integrable.of_bound hm.aestronglyMeasurable
    (((sphereProbability8 A)⁻¹).toReal*((105/32)/c^4/(3-p)))
  refine Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (residualRowPotential_nonneg _
    (shortRangeKernel8_nonneg c p) x)]
  exact shortRangeKernel8_restricted_row_le hc hp A x

/-- Every short-range tail is dominated by the weighted short-range kernel. -/
theorem tail_le_shortRangeKernel8 {c s γ R : ℝ} (hc : 0 < c) (hs : 0 < s) (hγ : 0 ≤ γ)
    (hR : 1 ≤ R) {x y : Sphere8} (hxy : x ≠ y) :
    ∫ α in Ioi R, α^(s/2-1)*sphereGaussianKernel8 (c*α) x y ≤
      R^(-γ)*shortRangeKernel8 c (s/2-1+γ) x y := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hb : 0 < c*dist x y^2 := by positivity
  have hiγ : IntegrableOn (fun α : ℝ => α^(s/2-1+γ)*sphereGaussianKernel8 (c*α) x y) (Ioi 1) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := s/2-1+γ) (p := 1) (b := c*dist x y^2)
      (by linarith) one_pos hb
    apply (h.mono_set (Ioi_subset_Ioi zero_le_one)).congr_fun _ measurableSet_Ioi
    intro α _
    simp only [sphereGaussianKernel8, Real.rpow_one]
    congr 2
    ring
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hRγ : 0 ≤ R^(-γ) := (Real.rpow_pos_of_pos hR0 _).le
  have hpt : ∀ α ∈ Ioi R, α^(s/2-1)*sphereGaussianKernel8 (c*α) x y ≤
      R^(-γ)*(α^(s/2-1+γ)*sphereGaussianKernel8 (c*α) x y) := by
    intro α hα
    have hα0 : 0 < α := hR0.trans hα
    have hk := sphereGaussianKernel8_nonneg (c*α) x y
    have h1 : 1 ≤ R^(-γ)*α^γ := by
      rw [Real.rpow_neg hR0.le, inv_mul_eq_div, one_le_div (Real.rpow_pos_of_pos hR0 _)]
      exact Real.rpow_le_rpow hR0.le (le_of_lt hα) hγ
    have hpow : α^(s/2-1) ≤ R^(-γ)*α^(s/2-1+γ) := by
      rw [Real.rpow_add hα0]
      calc α^(s/2-1) = α^(s/2-1)*1 := (mul_one _).symm
        _ ≤ α^(s/2-1)*(R^(-γ)*α^γ) := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hα0.le _)
        _ = R^(-γ)*(α^(s/2-1)*α^γ) := by ring
    calc α^(s/2-1)*sphereGaussianKernel8 (c*α) x y
        ≤ R^(-γ)*α^(s/2-1+γ)*sphereGaussianKernel8 (c*α) x y :=
          mul_le_mul_of_nonneg_right hpow hk
      _ = _ := by ring
  have hRi : IntegrableOn (fun α : ℝ => R^(-γ)*(α^(s/2-1+γ)*sphereGaussianKernel8 (c*α) x y))
      (Ioi R) := (hiγ.mono_set (Ioi_subset_Ioi hR)).const_mul _
  have hLi : IntegrableOn (fun α : ℝ => α^(s/2-1)*sphereGaussianKernel8 (c*α) x y) (Ioi R) := by
    apply hRi.mono' (by
      apply Measurable.aestronglyMeasurable
      unfold sphereGaussianKernel8
      fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
    have hα0 : 0 < α := hR0.trans hα
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hα0.le _)
      (sphereGaussianKernel8_nonneg _ _ _))]
    exact hpt α hα
  unfold shortRangeKernel8
  rw [← integral_const_mul]
  calc ∫ α in Ioi R, α^(s/2-1)*sphereGaussianKernel8 (c*α) x y
      ≤ ∫ α in Ioi R, R^(-γ)*(α^(s/2-1+γ)*sphereGaussianKernel8 (c*α) x y) :=
        setIntegral_mono_on hLi hRi measurableSet_Ioi hpt
    _ ≤ ∫ α in Ioi 1, R^(-γ)*(α^(s/2-1+γ)*sphereGaussianKernel8 (c*α) x y) := by
        apply setIntegral_mono_set (hiγ.const_mul _)
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
          exact mul_nonneg hRγ (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (le_of_lt hα)) _)
            (sphereGaussianKernel8_nonneg _ _ _))
        · exact (Ioi_subset_Ioi hR).eventuallyLE

end SphericalRiesz
