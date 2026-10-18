import Riesz.SphereRieszLower24
import Riesz.CellFirstMoment
import Riesz.ResidualJointSelection
import Mathlib.Algebra.Order.Ring.Pow

/-! Gaussian-only upper tools on S²⁴: actual background lower asymptotic,
weighted Gaussian tail kernel, and upper transfer with explicit sequence premises.
The configuration sequence and its uniform integrability are separate construction tasks. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace SphericalRiesz

theorem polePolynomialGaussian24_ge_twelfth (t : ℝ) {v : ℝ} (hv : v ∈ Icc (0:ℝ) 2) :
    2048*(v^11*Real.exp (-(2*t*v)))-11264*(v^12*Real.exp (-(2*t*v))) ≤
      polePolynomialGaussian24 t v := by
  have hb := one_add_mul_le_pow (a := -v/2) (by linarith [hv.2] : -2 ≤ -v/2) 11
  have hp : 2048-11264*v ≤ (2-v)^11 := by
    calc 2048-11264*v = 2048*(1+11*(-v/2)) := by ring
      _ ≤ 2048*(1+(-v/2))^11 := mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = (2-v)^11 := by ring
  have hw : 0 ≤ Real.exp (-(2*t*v))*v^11 :=
    mul_nonneg (Real.exp_pos _).le (pow_nonneg hv.1 11)
  unfold polePolynomialGaussian24
  calc 2048*(v^11*Real.exp (-(2*t*v)))-11264*(v^12*Real.exp (-(2*t*v)))
      = Real.exp (-(2*t*v))*v^11*(2048-11264*v) := by ring
    _ ≤ Real.exp (-(2*t*v))*v^11*(2-v)^11 := mul_le_mul_of_nonneg_left hp hw

theorem twelfthGaussian24_integral {t : ℝ} (ht : 0 < t) :
    (∫ v : ℝ in Ioi 0, v^12*Real.exp (-(2*t*v))) = 467775/(8*t^13) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 13) (r := 2*t) (by norm_num) (by positivity)
  have h' : (∫ v : ℝ in Ioi 0, v^12*Real.exp (-(2*t*v))) = (1/(2*t))^13*479001600 := by
    simpa only [show (13:ℝ)-1 = 12 by norm_num, Real.rpow_ofNat,
      show Real.Gamma 13 = 479001600 by norm_num] using h
  rw [h']
  field_simp
  ring

theorem twelfthGaussian24_integrable {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun v : ℝ => v^12*Real.exp (-(2*t*v))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [twelfthGaussian24_integral ht]
  exact (by positivity : (0:ℝ) < 467775/(8*t^13)).ne'

theorem sphereGaussianBackground24_lower {t : ℝ} (ht : 0 < t) :
    (316234143225/8192:ℝ)/t^12-(10435726726425/8192:ℝ)/t^13 ≤
      sphereGaussianBackground24 t := by
  set h : ℝ → ℝ := fun v =>
    2048*(v^11*Real.exp (-(2*t*v)))-11264*(v^12*Real.exp (-(2*t*v))) with hh
  have hi : IntegrableOn h (Ioi 0) :=
    ((eleventhGaussian24_integrable ht).const_mul 2048).sub
      ((twelfthGaussian24_integrable ht).const_mul 11264)
  have hint : (∫ v in Ioi (0:ℝ), h v) = 19958400/t^12-658627200/t^13 := by
    rw [hh, integral_sub ((eleventhGaussian24_integrable ht).const_mul 2048)
      ((twelfthGaussian24_integrable ht).const_mul 11264), integral_const_mul,
      integral_const_mul, eleventhGaussian24_integral ht, twelfthGaussian24_integral ht]
    field_simp
    ring
  have hsplit := integral_inter_add_sdiff (μ := volume)
    (measurableSet_Ioo (a := (0:ℝ)) (b := 2)) hi
  rw [inter_eq_right.mpr Ioo_subset_Ioi_self] at hsplit
  have htail : (∫ v in Ioi (0:ℝ) \ Ioo 0 2, h v) ≤ 0 := by
    apply setIntegral_nonpos (measurableSet_Ioi.diff measurableSet_Ioo)
    intro v hv
    have hv2 : 2 ≤ v := by
      by_contra hlt
      exact hv.2 ⟨hv.1, lt_of_not_ge hlt⟩
    have hv0 : 0 ≤ v := by linarith
    simp only [hh]
    have he : 2048*(v^11*Real.exp (-(2*t*v)))-11264*(v^12*Real.exp (-(2*t*v))) =
        -(1024*v^11*(11*v-2)*Real.exp (-(2*t*v))) := by ring
    rw [he, neg_nonpos]
    have hvlin : 0 ≤ 11*v-2 := by linarith
    positivity
  have hlow : 19958400/t^12-658627200/t^13 ≤ ∫ v in Ioo (0:ℝ) 2, h v := by linarith
  have hg : IntegrableOn (polePolynomialGaussian24 t) (Ioo (0:ℝ) 2) :=
    (polePolynomialGaussian24_continuous t).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hcmp : (∫ v in Ioo (0:ℝ) 2, h v) ≤
      ∫ v in Ioo (0:ℝ) 2, polePolynomialGaussian24 t v :=
    setIntegral_mono_on (hi.mono_set Ioo_subset_Ioi_self) hg measurableSet_Ioo
      (fun v hv => polePolynomialGaussian24_ge_twelfth t ⟨hv.1.le, hv.2.le⟩)
  rw [sphereGaussianBackground24_polynomial_set ht.le]
  have hfin : (316234143225/8192:ℝ)/t^12-(10435726726425/8192:ℝ)/t^13 =
      (2028117/1048576:ℝ)*(19958400/t^12-658627200/t^13) := by ring
  rw [hfin]
  exact mul_le_mul_of_nonneg_left (hlow.trans hcmp) (by norm_num)

theorem sphereGaussianBackground24_scaled_lower {N : ℕ} (hN : 0 < N) {α : ℝ} (hα : 0 < α) :
    (α^12)⁻¹-33/(α^12*sphereGaussianScale24 N α) ≤
      (N:ℝ)*sphereGaussianBackground24 (sphereGaussianScale24 N α) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hA : (sphereAreaD 24).real univ = 8192*Real.pi^12/316234143225 := by
    rw [sphereArea24_univ_real]; norm_num
  have hs := sphereGaussianScale24_pos hN hα
  have h4 := sphereGaussianScale24_pow_twelve hN α
  set c := sphereGaussianScale24 N α with hc
  have hb := mul_le_mul_of_nonneg_left (sphereGaussianBackground24_lower hs) hNR.le
  have he : (N:ℝ)*((316234143225/8192:ℝ)/c^12-(10435726726425/8192:ℝ)/c^13) = (α^12)⁻¹-33/(α^12*c) := by
    rw [show c^13 = c^12*c by ring, h4, hA]
    have hp : Real.pi ≠ 0 := Real.pi_pos.ne'
    field_simp
    ring
  linarith

theorem sphereGaussianCenteredScaled24_le_full {N : ℕ} (hN : 0 < N) {α : ℝ} (hα : 0 < α)
    (X : (ConfigurationD 24) N) :
    sphereGaussianCenteredScaled24 α X ≤
      sphereGaussianFullScaled24 α X-(α^12)⁻¹-1+33/(α^12*sphereGaussianScale24 N α) := by
  have h := sphereGaussianBackground24_scaled_lower hN hα
  unfold sphereGaussianCenteredScaled24 sphereGaussianFullScaled24
  linarith

theorem sphereGaussianScale24_tendsto {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) {α : ℝ}
    (hα : 0 < α) : Tendsto (fun k => sphereGaussianScale24 (N k) α) atTop atTop := by
  have hA : 0 < (sphereAreaD 24).real univ := sphereAreaD_univ_pos 24
  have h1 : Tendsto (fun k => ((N k:ℕ):ℝ)/(sphereAreaD 24).real univ) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp hN).atTop_div_const hA
  have h2 := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/12)).comp h1
  unfold sphereGaussianScale24
  exact h2.const_mul_atTop (by positivity)

def sphereRestrictedProbability24 (A : Set (SphereD 24)) : Measure (SphereD 24) :=
  ((sphereProbabilityD 24) A)⁻¹ • (sphereProbabilityD 24).restrict A

theorem sphereRestrictedProbability24_probability (A : Set (SphereD 24))
    (hA : (sphereProbabilityD 24) A ≠ 0) :
    IsProbabilityMeasure (sphereRestrictedProbability24 A) := by
  refine ⟨?_⟩
  simp only [sphereRestrictedProbability24,Measure.smul_apply,smul_eq_mul,
    Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hA (measure_ne_top _ _)

instance sphereRestrictedProbability24_finite (A : Set (SphereD 24)) :
    IsFiniteMeasure (sphereRestrictedProbability24 A) := by
  by_cases hA : (sphereProbabilityD 24) A = 0
  · refine ⟨?_⟩
    simp [sphereRestrictedProbability24, Measure.smul_apply, hA]
  · let := sphereRestrictedProbability24_probability A hA
    infer_instance

instance sphereRestrictedProbability24_nullSingleton (A : Set (SphereD 24)) :
    NullSingletonClass (sphereRestrictedProbability24 A) := by
  refine ⟨fun p => ?_⟩
  simp [sphereRestrictedProbability24,Measure.smul_apply]

theorem sphereRestrictedProbability24_compl (A : Set (SphereD 24)) (hA : MeasurableSet A) :
    sphereRestrictedProbability24 A Aᶜ = 0 := by
  simp [sphereRestrictedProbability24,Measure.smul_apply,Measure.restrict_apply hA.compl]

/-- The weighted short-range kernel. -/
def shortRangeKernel24 (c p : ℝ) (x y : (SphereD 24)) : ℝ :=
  ∫ α in Ioi (1:ℝ), α^p*sphereGaussianKernel24 (c*α) x y

theorem shortRangeKernel24_symm (c p : ℝ) (x y : (SphereD 24)) :
    shortRangeKernel24 c p x y = shortRangeKernel24 c p y x := by
  unfold shortRangeKernel24 sphereGaussianKernel24
  simp_rw [dist_comm x y]

theorem shortRangeKernel24_nonneg (c p : ℝ) (x y : (SphereD 24)) : 0 ≤ shortRangeKernel24 c p x y :=
  setIntegral_nonneg measurableSet_Ioi fun _α hα =>
    mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (le_of_lt hα)) _)
      (sphereGaussianKernel24_nonneg _ _ _)

theorem shortRangeKernel24_self (c : ℝ) {p : ℝ} (hp : -1 ≤ p) (x : (SphereD 24)) :
    shortRangeKernel24 c p x x = 0 := by
  unfold shortRangeKernel24
  simp only [sphereGaussianKernel24_self, mul_one]
  apply integral_undef
  intro h
  have := (integrableOn_Ioi_rpow_iff (s := p) zero_lt_one).mp h
  linarith

theorem ofReal_setIntegral_Ioi_le_lintegral24 {f : ℝ → ℝ} {a : ℝ} (hf : ∀ α ∈ Ioi a, 0 ≤ f α) :
    ENNReal.ofReal (∫ α in Ioi a, f α) ≤ ∫⁻ α in Ioi a, ENNReal.ofReal (f α) := by
  by_cases hi : IntegrableOn f (Ioi a)
  · rw [ofReal_integral_eq_lintegral_ofReal hi]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
    exact hf α hα
  · rw [integral_undef hi, ENNReal.ofReal_zero]
    exact zero_le

theorem shortRangeKernel24_measurable (c p : ℝ) :
    StronglyMeasurable (fun q : (SphereD 24) × (SphereD 24) => shortRangeKernel24 c p q.1 q.2) := by
  have hf : StronglyMeasurable (fun z : ((SphereD 24) × (SphereD 24)) × ℝ =>
      z.2^p*sphereGaussianKernel24 (c*z.2) z.1.1 z.1.2) := by
    apply Measurable.stronglyMeasurable
    unfold sphereGaussianKernel24
    apply Measurable.mul (measurable_snd.pow_const p)
    apply Real.measurable_exp.comp
    apply Measurable.neg
    apply Measurable.mul (measurable_const.mul measurable_snd)
    exact ((continuous_dist.comp (continuous_fst.comp continuous_fst |>.prodMk
      (continuous_snd.comp continuous_fst))).measurable).pow_const 2
  exact hf.integral_prod_right' (ν := volume.restrict (Ioi (1:ℝ)))

theorem shortRangeKernel24_row_measurable (c p : ℝ) (x : (SphereD 24)) :
    StronglyMeasurable (shortRangeKernel24 c p x) := by
  have hf : StronglyMeasurable (fun z : (SphereD 24) × ℝ =>
      z.2^p*sphereGaussianKernel24 (c*z.2) x z.1) := by
    apply Measurable.stronglyMeasurable
    unfold sphereGaussianKernel24
    apply Measurable.mul (measurable_snd.pow_const p)
    apply Real.measurable_exp.comp
    apply Measurable.neg
    apply Measurable.mul (measurable_const.mul measurable_snd)
    exact ((continuous_dist.comp (continuous_const.prodMk continuous_fst)).measurable).pow_const 2
  exact hf.integral_prod_right' (ν := volume.restrict (Ioi (1:ℝ)))

/-- Tonelli bound of a row against the actual uniform probability. -/
theorem shortRangeKernel24_row_lintegral_le {c p : ℝ} (hc : 0 < c) (hp : p < 11) (x : (SphereD 24)) :
    ∫⁻ y, ENNReal.ofReal (shortRangeKernel24 c p x y) ∂(sphereProbabilityD 24) ≤
      ENNReal.ofReal ((316234143225/8192)/c^12/(11-p)) := by
  set F : ℝ → (SphereD 24) → ℝ≥0∞ := fun α y => ENNReal.ofReal (α^p*sphereGaussianKernel24 (c*α) x y)
    with hF
  have hFm : Measurable (Function.uncurry F) := by
    simp only [hF, Function.uncurry_def]
    apply ENNReal.measurable_ofReal.comp
    unfold sphereGaussianKernel24
    apply Measurable.mul (measurable_fst.pow_const p)
    apply Real.measurable_exp.comp
    apply Measurable.neg
    apply Measurable.mul (measurable_const.mul measurable_fst)
    exact ((continuous_dist.comp (continuous_const.prodMk continuous_snd)).measurable).pow_const 2
  have h1 : ∀ y, ENNReal.ofReal (shortRangeKernel24 c p x y) ≤ ∫⁻ α in Ioi 1, F α y := by
    intro y
    apply ofReal_setIntegral_Ioi_le_lintegral24
    intro α hα
    exact mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (le_of_lt hα)) _)
      (sphereGaussianKernel24_nonneg _ _ _)
  have h2 : ∫⁻ y, ∫⁻ α in Ioi 1, F α y ∂volume ∂(sphereProbabilityD 24) =
      ∫⁻ α in Ioi 1, ∫⁻ y, F α y ∂(sphereProbabilityD 24) :=
    lintegral_lintegral_swap ((hFm.comp measurable_swap).aemeasurable)
  have h3 : ∀ α ∈ Ioi (1:ℝ), ∫⁻ y, F α y ∂(sphereProbabilityD 24) =
      ENNReal.ofReal (α^p*sphereGaussianBackground24 (c*α)) := by
    intro α hα
    have hα0 : 0 < α := zero_lt_one.trans hα
    have ht : 0 ≤ c*α := (mul_pos hc hα0).le
    have hi : Integrable (fun y => α^p*sphereGaussianKernel24 (c*α) x y) (sphereProbabilityD 24) :=
      (sphereGaussianKernel24_integrable ht x).const_mul _
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun y =>
      mul_nonneg (Real.rpow_nonneg hα0.le _) (sphereGaussianKernel24_nonneg _ _ _)),
      integral_const_mul, sphereGaussianBackground24_eq_potential ht x]
    rfl
  have h4 : ∀ α ∈ Ioi (1:ℝ), ENNReal.ofReal (α^p*sphereGaussianBackground24 (c*α)) ≤
      ENNReal.ofReal ((316234143225/8192)/c^12*α^(p-12)) := by
    intro α hα
    have hα0 : 0 < α := zero_lt_one.trans hα
    apply ENNReal.ofReal_le_ofReal
    have hB := sphereGaussianBackground24_decay (mul_pos hc hα0)
    have he : (316234143225/8192)/c^12*α^(p-12) = α^p*((316234143225/8192:ℝ)/(c*α)^12) := by
      rw [Real.rpow_sub hα0, show (12:ℝ) = ((12:ℕ):ℝ) by norm_num, Real.rpow_natCast, mul_pow]
      field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hα0.le _)
  have hint : IntegrableOn (fun α : ℝ => (316234143225/8192)/c^12*α^(p-12)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
  have hval : ∫ α in Ioi (1:ℝ), (316234143225/8192)/c^12*α^(p-12) = (316234143225/8192)/c^12/(11-p) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
    have h3p : (11:ℝ)-p ≠ 0 := by linarith
    have hp1 : p-12+1 ≠ 0 := by linarith
    field_simp
    ring
  calc ∫⁻ y, ENNReal.ofReal (shortRangeKernel24 c p x y) ∂(sphereProbabilityD 24)
      ≤ ∫⁻ y, ∫⁻ α in Ioi 1, F α y ∂volume ∂(sphereProbabilityD 24) := lintegral_mono h1
    _ = ∫⁻ α in Ioi 1, ∫⁻ y, F α y ∂(sphereProbabilityD 24) := h2
    _ = ∫⁻ α in Ioi 1, ENNReal.ofReal (α^p*sphereGaussianBackground24 (c*α)) :=
        setLIntegral_congr_fun measurableSet_Ioi h3
    _ ≤ ∫⁻ α in Ioi 1, ENNReal.ofReal ((316234143225/8192)/c^12*α^(p-12)) :=
        setLIntegral_mono (by fun_prop) h4
    _ = ENNReal.ofReal ((316234143225/8192)/c^12/(11-p)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint, hval]
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
        exact mul_nonneg (by positivity) (Real.rpow_nonneg (zero_le_one.trans (le_of_lt hα)) _)

theorem shortRangeKernel24_row_integrable {c p : ℝ} (hc : 0 < c) (hp : p < 11) (x : (SphereD 24)) :
    Integrable (shortRangeKernel24 c p x) (sphereProbabilityD 24) := by
  refine ⟨(shortRangeKernel24_row_measurable c p x).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have he : ∀ y, ‖shortRangeKernel24 c p x y‖ₑ = ENNReal.ofReal (shortRangeKernel24 c p x y) :=
    fun y => Real.enorm_eq_ofReal (shortRangeKernel24_nonneg c p x y)
  simp_rw [he]
  exact (shortRangeKernel24_row_lintegral_le hc hp x).trans_lt ENNReal.ofReal_lt_top

theorem shortRangeKernel24_row_integral_le {c p : ℝ} (hc : 0 < c) (hp : p < 11) (x : (SphereD 24)) :
    ∫ y, shortRangeKernel24 c p x y ∂(sphereProbabilityD 24) ≤ (316234143225/8192)/c^12/(11-p) := by
  have h := shortRangeKernel24_row_lintegral_le hc hp x
  rw [← ofReal_integral_eq_lintegral_ofReal (shortRangeKernel24_row_integrable hc hp x)
    (Eventually.of_forall fun y => shortRangeKernel24_nonneg c p x y)] at h
  have h3 : 0 ≤ (316234143225/8192)/c^12/(11-p) := by
    have : 0 < 11-p := by linarith
    positivity
  exact (ENNReal.ofReal_le_ofReal_iff h3).mp h

theorem shortRangeKernel24_restricted_integrable {c p : ℝ} (hc : 0 < c) (hp : p < 11)
    (A : Set (SphereD 24)) (x : (SphereD 24)) :
    Integrable (shortRangeKernel24 c p x) (sphereRestrictedProbability24 A) := by
  simpa only [sphereRestrictedProbability24, Measure.restrict_apply_univ] using
    (shortRangeKernel24_row_integrable hc hp x).restrict (s := A) |>.to_average

theorem shortRangeKernel24_restricted_row_le {c p : ℝ} (hc : 0 < c) (hp : p < 11)
    (A : Set (SphereD 24)) (x : (SphereD 24)) :
    residualRowPotential (sphereRestrictedProbability24 A) (shortRangeKernel24 c p) x ≤
      (((sphereProbabilityD 24) A)⁻¹).toReal*((316234143225/8192)/c^12/(11-p)) := by
  unfold residualRowPotential sphereRestrictedProbability24
  rw [integral_smul_measure, smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  calc ∫ y in A, shortRangeKernel24 c p x y ∂(sphereProbabilityD 24)
      ≤ ∫ y, shortRangeKernel24 c p x y ∂(sphereProbabilityD 24) :=
        setIntegral_le_integral (shortRangeKernel24_row_integrable hc hp x)
          (Eventually.of_forall fun y => shortRangeKernel24_nonneg c p x y)
    _ ≤ _ := shortRangeKernel24_row_integral_le hc hp x

theorem shortRangeKernel24_restricted_rowPotential_integrable {c p : ℝ} (hc : 0 < c) (hp : p < 11)
    (A : Set (SphereD 24)) (hA : (sphereProbabilityD 24) A ≠ 0) :
    Integrable (residualRowPotential (sphereRestrictedProbability24 A) (shortRangeKernel24 c p))
      (sphereRestrictedProbability24 A) := by
  let := sphereRestrictedProbability24_probability A hA
  have hm : StronglyMeasurable
      (residualRowPotential (sphereRestrictedProbability24 A) (shortRangeKernel24 c p)) :=
    (shortRangeKernel24_measurable c p).integral_prod_right'
      (ν := sphereRestrictedProbability24 A)
  apply Integrable.of_bound hm.aestronglyMeasurable
    ((((sphereProbabilityD 24) A)⁻¹).toReal*((316234143225/8192)/c^12/(11-p)))
  refine Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (residualRowPotential_nonneg _
    (shortRangeKernel24_nonneg c p) x)]
  exact shortRangeKernel24_restricted_row_le hc hp A x

/-- Every short-range tail is dominated by the weighted short-range kernel. -/
theorem tail_le_shortRangeKernel24 {c s γ R : ℝ} (hc : 0 < c) (hs : 0 < s) (hγ : 0 ≤ γ)
    (hR : 1 ≤ R) {x y : (SphereD 24)} (hxy : x ≠ y) :
    ∫ α in Ioi R, α^(s/2-1)*sphereGaussianKernel24 (c*α) x y ≤
      R^(-γ)*shortRangeKernel24 c (s/2-1+γ) x y := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hb : 0 < c*dist x y^2 := by positivity
  have hiγ : IntegrableOn (fun α : ℝ => α^(s/2-1+γ)*sphereGaussianKernel24 (c*α) x y) (Ioi 1) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := s/2-1+γ) (p := 1) (b := c*dist x y^2)
      (by linarith) one_pos hb
    apply (h.mono_set (Ioi_subset_Ioi zero_le_one)).congr_fun _ measurableSet_Ioi
    intro α _
    simp only [sphereGaussianKernel24, Real.rpow_one]
    congr 2
    ring
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hRγ : 0 ≤ R^(-γ) := (Real.rpow_pos_of_pos hR0 _).le
  have hpt : ∀ α ∈ Ioi R, α^(s/2-1)*sphereGaussianKernel24 (c*α) x y ≤
      R^(-γ)*(α^(s/2-1+γ)*sphereGaussianKernel24 (c*α) x y) := by
    intro α hα
    have hα0 : 0 < α := hR0.trans hα
    have hk := sphereGaussianKernel24_nonneg (c*α) x y
    have h1 : 1 ≤ R^(-γ)*α^γ := by
      rw [Real.rpow_neg hR0.le, inv_mul_eq_div, one_le_div (Real.rpow_pos_of_pos hR0 _)]
      exact Real.rpow_le_rpow hR0.le (le_of_lt hα) hγ
    have hpow : α^(s/2-1) ≤ R^(-γ)*α^(s/2-1+γ) := by
      rw [Real.rpow_add hα0]
      calc α^(s/2-1) = α^(s/2-1)*1 := (mul_one _).symm
        _ ≤ α^(s/2-1)*(R^(-γ)*α^γ) := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hα0.le _)
        _ = R^(-γ)*(α^(s/2-1)*α^γ) := by ring
    calc α^(s/2-1)*sphereGaussianKernel24 (c*α) x y
        ≤ R^(-γ)*α^(s/2-1+γ)*sphereGaussianKernel24 (c*α) x y :=
          mul_le_mul_of_nonneg_right hpow hk
      _ = _ := by ring
  have hRi : IntegrableOn (fun α : ℝ => R^(-γ)*(α^(s/2-1+γ)*sphereGaussianKernel24 (c*α) x y))
      (Ioi R) := (hiγ.mono_set (Ioi_subset_Ioi hR)).const_mul _
  have hLi : IntegrableOn (fun α : ℝ => α^(s/2-1)*sphereGaussianKernel24 (c*α) x y) (Ioi R) := by
    apply hRi.mono' (by
      apply Measurable.aestronglyMeasurable
      unfold sphereGaussianKernel24
      fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
    have hα0 : 0 < α := hR0.trans hα
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hα0.le _)
      (sphereGaussianKernel24_nonneg _ _ _))]
    exact hpt α hα
  unfold shortRangeKernel24
  rw [← integral_const_mul]
  calc ∫ α in Ioi R, α^(s/2-1)*sphereGaussianKernel24 (c*α) x y
      ≤ ∫ α in Ioi R, R^(-γ)*(α^(s/2-1+γ)*sphereGaussianKernel24 (c*α) x y) :=
        setIntegral_mono_on hLi hRi measurableSet_Ioi hpt
    _ ≤ ∫ α in Ioi 1, R^(-γ)*(α^(s/2-1+γ)*sphereGaussianKernel24 (c*α) x y) := by
        apply setIntegral_mono_set (hiγ.const_mul _)
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
          exact mul_nonneg hRγ (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (le_of_lt hα)) _)
            (sphereGaussianKernel24_nonneg _ _ _))
        · exact (Ioi_subset_Ioi hR).eventuallyLE

theorem integral_ge_of_eventual_upper_profile24 {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g G : α → ℝ} {f : ℕ → α → ℝ} {C : ℝ}
    (hg : Integrable g μ) (hf : ∀ n, Integrable (f n) μ) (hG : Integrable G μ)
    (hG0 : ∀ᵐ x ∂μ, 0 ≤ G x) (hu : ∀ n, ∀ᵐ x ∂μ, f n x ≤ G x)
    (hp : ∀ᵐ x ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, f n x ≤ g x+ε)
    (hC : ∀ n, C ≤ ∫ x, f n x ∂μ) : C ≤ ∫ x, g x ∂μ := by
  have h := integral_le_of_eventual_lower_profile (μ := μ) (g := fun x => -g x) (M := G)
    (f := fun n x => -f n x) (C := -C) hg.neg (fun n => (hf n).neg) hG hG0
    (fun n => (hu n).mono fun x hx => by linarith)
    (hp.mono fun x hx ε hε => (hx ε hε).mono fun n hn => by linarith)
    (fun n => by rw [integral_neg]; linarith [hC n])
  rw [integral_neg] at h
  linarith

theorem sphereGaussianSequence_energy_upper_of_profile_rpow24 {s : ℝ} (hs : 0 < s) (hs24 : s < 24)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, (ConfigurationD 24) (N k))
    {g G : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0)) (hG : IntegrableOn G (Ioi 0))
    (hG0 : ∀ α : ℝ, 0 < α → 0 ≤ G α)
    (hdom : ∀ k, ∀ α : ℝ, 0 < α → α^(s/2-1)*sphereGaussianCenteredScaled24 α (X k) ≤ G α)
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      α^(s/2-1)*sphereGaussianCenteredScaled24 α (X k) ≤ g α+ε)
    {C : ℝ} (hC : ∀ k, C ≤ normalizedEnergyRpow24 s (X k)) :
    C ≤ (Real.pi^(s/2)*((sphereAreaD 24).real univ)^(-(s/24))/Real.Gamma (s/2))*
      ∫ α : ℝ in Ioi 0, g α := by
  have hA : 0 < (sphereAreaD 24).real univ := sphereAreaD_univ_pos 24
  have hΓ : 0 < Real.Gamma (s/2) := Real.Gamma_pos_of_pos (by positivity)
  set c := Real.pi^(s/2)*((sphereAreaD 24).real univ)^(-(s/24))/Real.Gamma (s/2) with hcdef
  have hc : 0 < c := by
    have h1 : 0 < Real.pi^(s/2) := Real.rpow_pos_of_pos Real.pi_pos _
    have h2 : 0 < ((sphereAreaD 24).real univ)^(-(s/24)) := Real.rpow_pos_of_pos hA _
    positivity
  have hi : ∀ k, C/c ≤ ∫ α : ℝ in Ioi 0, α^(s/2-1)*sphereGaussianCenteredScaled24 α (X k) := by
    intro k
    rw [div_le_iff₀ hc, mul_comm, ← normalizedEnergyRpow24_gaussian_mellin hs hs24 (hN k) (X k)]
    exact hC k
  have h := integral_ge_of_eventual_upper_profile24
    (μ := volume.restrict (Ioi (0:ℝ))) (g := g) (G := G)
    (f := fun k α => α^(s/2-1)*sphereGaussianCenteredScaled24 α (X k)) hg
    (fun k => sphereGaussianCenteredScaled24_weighted_integrable_rpow hs hs24 (hN k) (X k)) hG
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact hG0 α hα)
    (fun k => by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact hdom k α hα)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact hp α hα)
    hi
  have hh := mul_le_mul_of_nonneg_left h hc.le
  rwa [mul_div_cancel₀ C hc.ne'] at hh

/-- Reverse-Fatou upper bound for a sequence: `limsup normalizedEnergyRpow24 s X_k ≤ c_s ∫ g`. -/
theorem normalizedEnergyRpow24_eventually_le_of_profile {s : ℝ} (hs : 0 < s) (hs24 : s < 24)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, (ConfigurationD 24) (N k))
    {g G : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0)) (hG : IntegrableOn G (Ioi 0))
    (hG0 : ∀ α : ℝ, 0 < α → 0 ≤ G α)
    (hdom : ∀ k, ∀ α : ℝ, 0 < α → α^(s/2-1)*sphereGaussianCenteredScaled24 α (X k) ≤ G α)
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      α^(s/2-1)*sphereGaussianCenteredScaled24 α (X k) ≤ g α+ε) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, normalizedEnergyRpow24 s (X k) ≤
      (Real.pi^(s/2)*((sphereAreaD 24).real univ)^(-(s/24))/Real.Gamma (s/2))*
        (∫ α : ℝ in Ioi 0, g α)+η := by
  intro η hη
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hcon
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have h := sphereGaussianSequence_energy_upper_of_profile_rpow24 hs hs24 (fun n => hN (φ n))
    (fun n => X (φ n)) hg hG hG0 (fun n => hdom (φ n))
    (fun α hα ε hε => hφt.eventually (hp α hα ε hε))
    (C := (Real.pi^(s/2)*((sphereAreaD 24).real univ)^(-(s/24))/Real.Gamma (s/2))*
        (∫ α : ℝ in Ioi 0, g α)+η) (fun n => (lt_of_not_ge (hbad n)).le)
  linarith

theorem sphereGaussianCenteredScaled24_weighted_profile_upper_eventually (s : ℝ)
    {N : ℕ → ℕ} (hNt : Tendsto N atTop atTop) (hN : ∀ k, 0 < N k) (X : ∀ k, (ConfigurationD 24) (N k))
    {α : ℝ} (hα : 0 < α)
    (hp : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      sphereGaussianFullScaled24 α (X k) ≤ leechGaussianThetaReal24 α+ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      α^(s/2-1)*sphereGaussianCenteredScaled24 α (X k) ≤ leechGaussianRieszProfileRpow24 s α+ε := by
  intro ε hε
  have hw : 0 < α^(s/2-1) := Real.rpow_pos_of_pos hα _
  set δ := ε/α^(s/2-1)/2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hsc := sphereGaussianScale24_tendsto hNt hα
  have hcorr : ∀ᶠ k in atTop, 33/(α^12*sphereGaussianScale24 (N k) α) ≤ δ := by
    have ht : Tendsto (fun k => 33/(α^12*sphereGaussianScale24 (N k) α)) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds (hsc.const_mul_atTop (by positivity))
    exact ht.eventually (ge_mem_nhds hδ0)
  filter_upwards [hp δ hδ0, hcorr] with k hk hc
  have hb := sphereGaussianCenteredScaled24_le_full (hN k) hα (X k)
  have h2 : δ+δ = ε/α^(s/2-1) := by rw [hδ]; ring
  have hF : sphereGaussianCenteredScaled24 α (X k) ≤
      leechGaussianThetaReal24 α-(α^12)⁻¹-1+ε/α^(s/2-1) := by linarith
  unfold leechGaussianRieszProfileRpow24
  calc α^(s/2-1)*sphereGaussianCenteredScaled24 α (X k)
      ≤ α^(s/2-1)*(leechGaussianThetaReal24 α-(α^12)⁻¹-1+ε/α^(s/2-1)) :=
        mul_le_mul_of_nonneg_left hF hw.le
    _ = α^(s/2-1)*(leechGaussianThetaReal24 α-(α^12)⁻¹-1)+ε := by
      field_simp

/-- All-exponent upper reduction with a supplied majorant: the Leech coefficient is reached from an
upper bound on the full Gaussian sums at every scale. -/
theorem sphere24_riesz_upper_of_full_profile {s : ℝ} (hs : 0 < s) (hs24 : s < 24)
    {N : ℕ → ℕ} (hNt : Tendsto N atTop atTop) (hN : ∀ k, 0 < N k) (X : ∀ k, (ConfigurationD 24) (N k))
    {G : ℝ → ℝ} (hG : IntegrableOn G (Ioi 0)) (hG0 : ∀ α : ℝ, 0 < α → 0 ≤ G α)
    (hdom : ∀ k, ∀ α : ℝ, 0 < α → α^(s/2-1)*sphereGaussianCenteredScaled24 α (X k) ≤ G α)
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      sphereGaussianFullScaled24 α (X k) ≤ leechGaussianThetaReal24 α+ε) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, normalizedEnergyRpow24 s (X k) ≤ sphereRieszCoefficient24 s+η := by
  intro η hη
  have h := normalizedEnergyRpow24_eventually_le_of_profile hs hs24 hN X
    (leechGaussianRieszProfileRpow24_integrable hs hs24) hG hG0 hdom
    (fun α hα => sphereGaussianCenteredScaled24_weighted_profile_upper_eventually s hNt hN X hα
      (hp α hα)) η hη
  unfold sphereRieszCoefficient24
  exact h


/-- Cross-cell potentials are integrable without a separation hypothesis. -/
theorem shortRangeKernel24_cross_rowPotential_integrable {c p : ℝ} (hc : 0 < c) (hp : p < 11)
    (A S : Set (SphereD 24)) (hA : (sphereProbabilityD 24) A ≠ 0) :
    Integrable (residualRowPotential (sphereRestrictedProbability24 S) (shortRangeKernel24 c p))
      (sphereRestrictedProbability24 A) := by
  let := sphereRestrictedProbability24_probability A hA
  have hm : StronglyMeasurable
      (residualRowPotential (sphereRestrictedProbability24 S) (shortRangeKernel24 c p)) :=
    (shortRangeKernel24_measurable c p).integral_prod_right'
      (ν := sphereRestrictedProbability24 S)
  apply Integrable.of_bound hm.aestronglyMeasurable
    ((((sphereProbabilityD 24) S)⁻¹).toReal*((316234143225/8192)/c^12/(11-p)))
  refine Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (residualRowPotential_nonneg _
    (shortRangeKernel24_nonneg c p) x)]
  exact shortRangeKernel24_restricted_row_le hc hp S x

/-- Actual S²⁴ cell selection for the weighted Gaussian kernel and an additional linear cost. -/
theorem exists_shortRange_cell_selection24 {c p : ℝ} (hc : 0 < c) (hp : p < 11)
    (hp0 : -1 ≤ p) (n : ℕ) (C : Fin n → Set (SphereD 24))
    (hCm : ∀ i, MeasurableSet (C i)) (hCp : ∀ i, (sphereProbabilityD 24) (C i) ≠ 0)
    (L : (SphereD 24) → ℝ) (hL : ∀ i, Integrable L (sphereRestrictedProbability24 (C i)))
    (B : Set (SphereD 24)) (hB : (sphereProbabilityD 24) B = 0) :
    ∃ z : Fin n → (SphereD 24), Function.Injective z ∧ (∀ i, z i ∈ C i) ∧
      (∀ i, z i ∉ B) ∧ cellPairSum (shortRangeKernel24 c p) z + ∑ i, L (z i) ≤
        cellBoundK (shortRangeKernel24 c p) n (fun i => sphereRestrictedProbability24 (C i)) +
          ∑ i, ∫ x, L x ∂sphereRestrictedProbability24 (C i) := by
  apply exists_cell_selection (shortRangeKernel24 c p) (shortRangeKernel24_symm c p)
    n (fun i => sphereRestrictedProbability24 (C i)) C L B
  · exact fun i => sphereRestrictedProbability24_probability (C i) (hCp i)
  · exact fun i => inferInstance
  · exact fun i => sphereRestrictedProbability24_compl (C i) (hCm i)
  · intro i
    unfold sphereRestrictedProbability24
    rw [Measure.smul_apply, smul_eq_mul]
    have hrestrict : (sphereProbabilityD 24).restrict (C i) B = 0 :=
      le_antisymm ((Measure.restrict_apply_le _ _).trans_eq hB) zero_le
    rw [hrestrict, mul_zero]
  · exact fun i x => shortRangeKernel24_restricted_integrable hc hp (C i) x
  · exact fun i j => shortRangeKernel24_cross_rowPotential_integrable hc hp (C i) (C j) (hCp i)
  · intro i
    simp only [shortRangeKernel24_self c hp0]
    exact integrable_const 0
  · exact hL

/-- Equal-mass disjoint cells convert a sum of cell rows into one sphere restriction. -/
theorem sphereRestrictedProbability24_sum_integral {n N : ℕ}
    (C : Fin n → Set (SphereD 24)) (hCm : ∀ i, MeasurableSet (C i))
    (hCd : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hCmass : ∀ i, (sphereProbabilityD 24) (C i) = (N : ℝ≥0∞)⁻¹)
    {f : (SphereD 24) → ℝ} (hf : Integrable f (sphereProbabilityD 24)) :
    (∑ i, ∫ x, f x ∂sphereRestrictedProbability24 (C i)) =
      (N:ℝ)*∫ x in ⋃ i, C i, f x ∂(sphereProbabilityD 24) := by
  simp only [sphereRestrictedProbability24, hCmass, inv_inv, integral_smul_measure,
    smul_eq_mul, ENNReal.toReal_natCast]
  rw [← Finset.mul_sum, integral_iUnion hCm hCd hf.integrableOn, tsum_fintype]

/-- The density-scaled short-range row has an N-independent aggregate bound. -/
theorem shortRangeKernel24_cell_rows_le {n N : ℕ} (hN : 0 < N)
    {p : ℝ} (hp : p < 11) (C : Fin n → Set (SphereD 24))
    (hCm : ∀ i, MeasurableSet (C i)) (hCd : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hCmass : ∀ i, (sphereProbabilityD 24) (C i) = (N : ℝ≥0∞)⁻¹)
    (x : (SphereD 24)) :
    ∑ i, ∫ y, shortRangeKernel24 (sphereGaussianScale24 N 1) p x y
      ∂sphereRestrictedProbability24 (C i) ≤ 1/(11-p) := by
  have hc := sphereGaussianScale24_pos hN zero_lt_one
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  rw [sphereRestrictedProbability24_sum_integral C hCm hCd hCmass
    (shortRangeKernel24_row_integrable hc hp x)]
  calc (N:ℝ)*∫ y in ⋃ i, C i, shortRangeKernel24 (sphereGaussianScale24 N 1) p x y
      ∂(sphereProbabilityD 24)
      ≤ (N:ℝ)*∫ y, shortRangeKernel24 (sphereGaussianScale24 N 1) p x y
          ∂(sphereProbabilityD 24) := by
        apply mul_le_mul_of_nonneg_left _ hNR.le
        exact setIntegral_le_integral (shortRangeKernel24_row_integrable hc hp x)
          (.of_forall (shortRangeKernel24_nonneg _ _ x))
    _ ≤ (N:ℝ)*((316234143225/8192)/(sphereGaussianScale24 N 1)^12/(11-p)) :=
      mul_le_mul_of_nonneg_left (shortRangeKernel24_row_integral_le hc hp x) hNR.le
    _ = _ := by
      rw [sphereGaussianScale24_pow_twelve hN, sphereArea24_univ_real]
      have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
      have hNp : (N:ℝ) ≠ 0 := hNR.ne'
      have hden : (11:ℝ)-p ≠ 0 := by linarith
      field_simp [hpi, hNp, hden] <;> norm_num

/-- A conservative recursive expectation bound avoids a separate cross-cell Fubini argument. -/
theorem cellBoundK_le_two_mul_rows24 {E : Type*} [MeasurableSpace E]
    (k : E → E → ℝ) (hk0 : ∀ x y, 0 ≤ k x y) (hdiag : ∀ x, k x x = 0)
    (D : ℝ) :
    ∀ (n : ℕ) (ν : Fin n → Measure E),
      (∀ i, IsProbabilityMeasure (ν i)) →
      (∀ i j, Integrable (fun x => ∫ y, k x y ∂(ν j)) (ν i)) →
      (∀ x, ∑ j, ∫ y, k x y ∂(ν j) ≤ D) →
      cellBoundK k n ν ≤ 2*(n:ℝ)*D := by
  intro n
  induction n with
  | zero => intro ν _ _ _; simp [cellBoundK]
  | succ n ih =>
    intro ν hP hV hrows
    let := hP 0
    have htail : ∀ x, ∑ j : Fin n, ∫ y, k x y ∂(ν j.succ) ≤ D := by
      intro x
      have h := hrows x
      rw [Fin.sum_univ_succ] at h
      have hn : 0 ≤ ∫ y, k x y ∂(ν 0) := integral_nonneg (hk0 x)
      linarith
    have hcross : (∑ j : Fin n, cellCross k (ν 0) (ν j.succ)) ≤ D := by
      unfold cellCross
      rw [← integral_finsetSum Finset.univ (fun (j : Fin n) _ => hV 0 j.succ)]
      calc (∫ x, ∑ j : Fin n, ∫ y, k x y ∂(ν j.succ) ∂(ν 0))
          ≤ ∫ _x, D ∂(ν 0) :=
            integral_mono (integrable_finsetSum Finset.univ (fun j _ => hV 0 j.succ))
              (integrable_const D) htail
        _ = D := by simp
    have hb := ih (fun j => ν j.succ) (fun j => hP j.succ)
      (fun i j => hV i.succ j.succ) htail
    simp only [cellBoundK, hdiag, integral_zero, zero_add, Nat.cast_add, Nat.cast_one]
    linarith

/-- One deterministic injective cell choice has a uniform Gaussian short-range cost. -/
theorem exists_shortRange_cell_bound24 {n N : ℕ} (hN : 0 < N) {p : ℝ}
    (hp : p < 11) (hp0 : -1 ≤ p) (C : Fin n → Set (SphereD 24))
    (hCm : ∀ i, MeasurableSet (C i)) (hCd : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hCmass : ∀ i, (sphereProbabilityD 24) (C i) = (N : ℝ≥0∞)⁻¹)
    (B : Set (SphereD 24)) (hB : (sphereProbabilityD 24) B = 0) :
    ∃ z : Fin n → (SphereD 24), Function.Injective z ∧ (∀ i, z i ∈ C i) ∧
      (∀ i, z i ∉ B) ∧
      cellPairSum (shortRangeKernel24 (sphereGaussianScale24 N 1) p) z ≤
        2*(n:ℝ)/(11-p) := by
  have hc := sphereGaussianScale24_pos hN zero_lt_one
  have hCp : ∀ i, (sphereProbabilityD 24) (C i) ≠ 0 := by
    intro i
    rw [hCmass]
    exact ENNReal.inv_ne_zero.mpr (by simp)
  obtain ⟨z, hz, hCz, hBz, hb⟩ := exists_shortRange_cell_selection24 hc hp hp0 n C hCm hCp
    (fun _ => 0) (fun _ => integrable_const 0) B hB
  have hbound := cellBoundK_le_two_mul_rows24
    (shortRangeKernel24 (sphereGaussianScale24 N 1) p)
    (shortRangeKernel24_nonneg _ _) (shortRangeKernel24_self _ hp0) (1/(11-p))
    n
    (fun i => sphereRestrictedProbability24 (C i))
    (fun i => sphereRestrictedProbability24_probability (C i) (hCp i))
    (fun i j => shortRangeKernel24_cross_rowPotential_integrable hc hp (C i) (C j) (hCp i))
    (shortRangeKernel24_cell_rows_le hN hp C hCm hCd hCmass)
  refine ⟨z, hz, hCz, hBz, ?_⟩
  simp only [Finset.sum_const_zero, integral_zero, add_zero] at hb
  simpa only [div_eq_mul_inv, mul_one, one_mul] using hb.trans hbound

def shortRangeCrossRow24 (c p : ℝ) {M : ℕ} (X : Fin M → (SphereD 24))
    (z : (SphereD 24)) : ℝ := 2*∑ i, shortRangeKernel24 c p (X i) z

theorem shortRangeCrossRow24_integrable {c p : ℝ} (hc : 0 < c) (hp : p < 11) {M : ℕ}
    (X : Fin M → (SphereD 24)) (A : Set (SphereD 24)) :
    Integrable (shortRangeCrossRow24 c p X) (sphereRestrictedProbability24 A) :=
  (integrable_finsetSum _ fun i _ => shortRangeKernel24_restricted_integrable hc hp A (X i)).const_mul 2

theorem shortRangeCrossRow24_cell_integrals_le {n M N : ℕ} (hN : 0 < N) {p : ℝ}
    (hp : p < 11) (X : Fin M → (SphereD 24)) (C : Fin n → Set (SphereD 24))
    (hCm : ∀ i, MeasurableSet (C i)) (hCd : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hCmass : ∀ i, (sphereProbabilityD 24) (C i) = (N : ℝ≥0∞)⁻¹) :
    (∑ i, ∫ x, shortRangeCrossRow24 (sphereGaussianScale24 N 1) p X x
      ∂sphereRestrictedProbability24 (C i)) ≤ 2*(M:ℝ)/(11-p) := by
  have hc := sphereGaussianScale24_pos hN zero_lt_one
  unfold shortRangeCrossRow24
  simp_rw [integral_const_mul, integral_finsetSum _
    (fun j _ => shortRangeKernel24_restricted_integrable hc hp _ (X j))]
  rw [← Finset.mul_sum, Finset.sum_comm]
  calc 2*(∑ j, ∑ i, ∫ x, shortRangeKernel24 (sphereGaussianScale24 N 1) p (X j) x
        ∂sphereRestrictedProbability24 (C i))
      ≤ 2*∑ _j : Fin M, 1/(11-p) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum fun j _ => shortRangeKernel24_cell_rows_le hN hp C hCm hCd hCmass (X j)
    _ = _ := by simp; ring

/-- A single cell choice controls residual pairs and every foreground/residual cross pair. -/
theorem exists_shortRange_cell_cross_bound24 {n M N : ℕ} (hN : 0 < N) {p : ℝ}
    (hp : p < 11) (hp0 : -1 ≤ p) (X : Fin M → (SphereD 24))
    (C : Fin n → Set (SphereD 24)) (hCm : ∀ i, MeasurableSet (C i))
    (hCd : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hCmass : ∀ i, (sphereProbabilityD 24) (C i) = (N : ℝ≥0∞)⁻¹) :
    ∃ z : Fin n → (SphereD 24), Function.Injective z ∧ (∀ i, z i ∈ C i) ∧
      (∀ i, z i ∉ range X) ∧
      cellPairSum (shortRangeKernel24 (sphereGaussianScale24 N 1) p) z +
        ∑ i, shortRangeCrossRow24 (sphereGaussianScale24 N 1) p X (z i) ≤
          2*((n:ℝ)+(M:ℝ))/(11-p) := by
  have hc := sphereGaussianScale24_pos hN zero_lt_one
  have hCp : ∀ i, (sphereProbabilityD 24) (C i) ≠ 0 := by
    intro i
    rw [hCmass]
    exact ENNReal.inv_ne_zero.mpr (by simp)
  obtain ⟨z, hz, hCz, hBz, hb⟩ := exists_shortRange_cell_selection24 hc hp hp0 n C hCm hCp
    (shortRangeCrossRow24 (sphereGaussianScale24 N 1) p X)
    (fun i => shortRangeCrossRow24_integrable hc hp X (C i)) (range X)
    ((finite_range X).measure_zero _)
  have hbound := cellBoundK_le_two_mul_rows24
    (shortRangeKernel24 (sphereGaussianScale24 N 1) p)
    (shortRangeKernel24_nonneg _ _) (shortRangeKernel24_self _ hp0) (1/(11-p))
    n
    (fun i => sphereRestrictedProbability24 (C i))
    (fun i => sphereRestrictedProbability24_probability (C i) (hCp i))
    (fun i j => shortRangeKernel24_cross_rowPotential_integrable hc hp (C i) (C j) (hCp i))
    (shortRangeKernel24_cell_rows_le hN hp C hCm hCd hCmass)
  have hcross := shortRangeCrossRow24_cell_integrals_le hN hp X C hCm hCd hCmass
  refine ⟨z, hz, hCz, hBz, ?_⟩
  calc _ ≤ 2*(n:ℝ)*(1/(11-p)) + 2*(M:ℝ)/(11-p) :=
      hb.trans (add_le_add hbound hcross)
    _ = _ := by ring

/-- Actual Gaussian Mellin tails for residual off-diagonal pairs and ordered cross pairs.
The diagonal is removed before integration. -/
def residualGaussianTail24 (c s R : ℝ) {n M : ℕ}
    (X : Fin M → (SphereD 24)) (z : Fin n → (SphereD 24)) : ℝ :=
  (∑ i, ∑ j ∈ Finset.univ.erase i,
    ∫ α in Ioi R, α^(s/2-1)*sphereGaussianKernel24 (c*α) (z i) (z j)) +
  2*(∑ i, ∑ j,
    ∫ α in Ioi R, α^(s/2-1)*sphereGaussianKernel24 (c*α) (X j) (z i))

theorem residualGaussianTail24_le_kernel_cost {c s γ R : ℝ} (hc : 0 < c)
    (hs : 0 < s) (hγ : 0 ≤ γ) (hR : 1 ≤ R) {n M : ℕ}
    (X : Fin M → (SphereD 24)) (z : Fin n → (SphereD 24))
    (hz : Function.Injective z) (havoid : ∀ i, z i ∉ range X)
    (hp0 : -1 ≤ s/2-1+γ) :
    residualGaussianTail24 c s R X z ≤ R^(-γ)*
      (cellPairSum (shortRangeKernel24 c (s/2-1+γ)) z +
        ∑ i, shortRangeCrossRow24 c (s/2-1+γ) X (z i)) := by
  classical
  have hpair : (∑ i, ∑ j ∈ Finset.univ.erase i,
      ∫ α in Ioi R, α^(s/2-1)*sphereGaussianKernel24 (c*α) (z i) (z j)) ≤
      R^(-γ)*cellPairSum (shortRangeKernel24 c (s/2-1+γ)) z := by
    unfold cellPairSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    have hfull : (∑ j : Fin n, R^(-γ)*shortRangeKernel24 c (s/2-1+γ) (z i) (z j)) =
        ∑ j ∈ Finset.univ.erase i, R^(-γ)*shortRangeKernel24 c (s/2-1+γ) (z i) (z j) := by
      simpa only [shortRangeKernel24_self c hp0, mul_zero, add_zero] using
        (Finset.sum_erase_add Finset.univ
          (fun j => R^(-γ)*shortRangeKernel24 c (s/2-1+γ) (z i) (z j)) (Finset.mem_univ i)).symm
    rw [hfull]
    apply Finset.sum_le_sum
    intro j hj
    exact tail_le_shortRangeKernel24 hc hs hγ hR (hz.ne (Finset.mem_erase.mp hj).1.symm)
  have hcross : 2*(∑ i, ∑ j,
      ∫ α in Ioi R, α^(s/2-1)*sphereGaussianKernel24 (c*α) (X j) (z i)) ≤
      R^(-γ)*(∑ i, shortRangeCrossRow24 c (s/2-1+γ) X (z i)) := by
    unfold shortRangeCrossRow24
    simp only [← Finset.mul_sum]
    rw [show R^(-γ)*(2*∑ i, ∑ j, shortRangeKernel24 c (s/2-1+γ) (X j) (z i)) =
      2*(∑ i, ∑ j, R^(-γ)*shortRangeKernel24 c (s/2-1+γ) (X j) (z i)) by
        simp only [Finset.mul_sum]; ring]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have hne : X j ≠ z i := fun h => havoid i ⟨j, h⟩
    exact tail_le_shortRangeKernel24 hc hs hγ hR hne
  unfold residualGaussianTail24
  rw [mul_add]
  exact add_le_add hpair hcross

/-- All large-scale tails are bounded simultaneously by one Gaussian-only cell selection. -/
theorem exists_residualGaussianTail24_uniform {n M N : ℕ} (hN : 0 < N)
    (hsize : n+M=N) {s : ℝ} (hs : 0 < s) (hs24 : s < 24)
    (X : Fin M → (SphereD 24)) (C : Fin n → Set (SphereD 24))
    (hCm : ∀ i, MeasurableSet (C i)) (hCd : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hCmass : ∀ i, (sphereProbabilityD 24) (C i) = (N : ℝ≥0∞)⁻¹) :
    ∃ z : Fin n → (SphereD 24), Function.Injective z ∧ (∀ i, z i ∈ C i) ∧
      (∀ i, z i ∉ range X) ∧ ∀ R : ℝ, 1 ≤ R →
        residualGaussianTail24 (sphereGaussianScale24 N 1) s R X z/(N:ℝ) ≤
          (8/(24-s))*R^(-(24-s)/4) := by
  set γ : ℝ := (24-s)/4 with hγdef
  have hγ : 0 < γ := by dsimp [γ]; linarith
  have hp : s/2-1+γ < 11 := by dsimp [γ]; linarith
  have hp0 : -1 ≤ s/2-1+γ := by linarith
  obtain ⟨z, hz, hCz, havoid, hb⟩ := exists_shortRange_cell_cross_bound24 hN hp hp0 X C hCm hCd hCmass
  refine ⟨z, hz, hCz, havoid, fun R hR => ?_⟩
  have hc := sphereGaussianScale24_pos hN zero_lt_one
  have htail := residualGaussianTail24_le_kernel_cost hc hs hγ.le hR X z hz havoid hp0
  have hR0 : 0 ≤ R^(-γ) := Real.rpow_nonneg (by linarith) _
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hsz : (n:ℝ)+(M:ℝ) = N := by exact_mod_cast hsize
  calc residualGaussianTail24 (sphereGaussianScale24 N 1) s R X z/(N:ℝ)
      ≤ (R^(-γ)*(2*((n:ℝ)+(M:ℝ))/(11-(s/2-1+γ))))/(N:ℝ) :=
        div_le_div_of_nonneg_right (htail.trans (mul_le_mul_of_nonneg_left hb hR0)) hNR.le
    _ = _ := by
      have hpden : 11-(s/2-1+γ) = (24-s)/4 := by rw [hγdef]; ring
      have hsne : (24:ℝ)-s ≠ 0 := by linarith
      have hfactor : (2*(N:ℝ)/((24-s)/4))/(N:ℝ) = 8/(24-s) := by
        rw [div_div_eq_mul_div]
        field_simp [hNR.ne', hsne] <;> ring
      have hneg : -γ = -(24-s)/4 := by rw [hγdef]; ring
      rw [hpden, hsz, mul_div_assoc, hfactor, hneg, mul_comm]

theorem sphereGaussianPair24_scaled_tail_integrable {c s R : ℝ} (hc : 0 < c)
    (hs : 0 < s) (hR : 0 ≤ R) {x y : (SphereD 24)} (hxy : x ≠ y) :
    IntegrableOn (fun α : ℝ => α^(s/2-1)*sphereGaussianKernel24 (c*α) x y) (Ioi R) := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hb : 0 < c*dist x y^2 := by positivity
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow (s := s/2-1) (p := 1)
    (b := c*dist x y^2) (by linarith) one_pos hb
  apply (hi.mono_set (Ioi_subset_Ioi hR)).congr_fun _ measurableSet_Ioi
  intro α _
  simp only [sphereGaussianKernel24, Real.rpow_one]
  congr 2
  ring

/-- The selected tail cost is the integral of the actual weighted Gaussian pair sums. -/
theorem residualGaussianTail24_eq_integral {c s R : ℝ} (hc : 0 < c)
    (hs : 0 < s) (hR : 0 ≤ R) {n M : ℕ}
    (X : Fin M → (SphereD 24)) (z : Fin n → (SphereD 24))
    (hz : Function.Injective z) (havoid : ∀ i, z i ∉ range X) :
    residualGaussianTail24 c s R X z =
      ∫ α in Ioi R, (∑ i, ∑ j ∈ Finset.univ.erase i,
        α^(s/2-1)*sphereGaussianKernel24 (c*α) (z i) (z j)) +
        2*(∑ i, ∑ j, α^(s/2-1)*sphereGaussianKernel24 (c*α) (X j) (z i)) := by
  classical
  have hres : ∀ i, ∀ j ∈ Finset.univ.erase i, IntegrableOn
      (fun α : ℝ => α^(s/2-1)*sphereGaussianKernel24 (c*α) (z i) (z j)) (Ioi R) :=
    fun i j hj => sphereGaussianPair24_scaled_tail_integrable hc hs hR
      (hz.ne (Finset.mem_erase.mp hj).1.symm)
  have hcross : ∀ i j, IntegrableOn
      (fun α : ℝ => α^(s/2-1)*sphereGaussianKernel24 (c*α) (X j) (z i)) (Ioi R) :=
    fun i j => sphereGaussianPair24_scaled_tail_integrable hc hs hR
      (fun h => havoid i ⟨j, h⟩)
  have hresrow := fun i => integrable_finsetSum _ (hres i)
  have hcrossrow := fun i => integrable_finsetSum Finset.univ (fun j _ => hcross i j)
  rw [integral_add (integrable_finsetSum Finset.univ (fun i _ => hresrow i))
    ((integrable_finsetSum Finset.univ (fun i _ => hcrossrow i)).const_mul 2),
    integral_const_mul, integral_finsetSum _ (fun i _ => hresrow i),
    integral_finsetSum _ (fun i _ => hcrossrow i)]
  simp_rw [integral_finsetSum _ (hres _),
    integral_finsetSum Finset.univ (fun j _ => hcross _ j)]
  rfl

end SphericalRiesz
