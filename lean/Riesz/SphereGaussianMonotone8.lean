import Riesz.SphereGaussianMellinScale8
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Gaussian monotonicity of the neutralized sphere defect and a uniform small-scale bound.

The neutralized Gaussian defect `D(t)` of `Σ δ_{xᵢ} - M σ` is the standard-Gaussian average of
`|φ(√(2t) z)|²`, where `φ` is the Fourier amplitude of the signed measure.  The standard Gaussian
on `ℝ⁹` has the Lebesgue density `(2π)^(-9/2) e^{-|z|²/2}` (uniqueness of characteristic
functions), so the substitution `w = √(2t) z` gives
`√t⁹ D(t) = √2⁻⁹ (2π)^(-9/2) ∫ e^{-|w|²/(4t)} |φ(w)|² dw`,
which is nondecreasing in `t`.  For the density-scaled centered profile `F` this says that
`√α⁹ (F(α)+1)` is nondecreasing.  Averaging over `(α, 2α]` against the `s = 4` Mellin identity
and the common lower `-α·min(1, α⁻⁴)` gives, for every configuration,
`(F(α)+1)·(3/2)α² ≤ √2⁹ ((8/√210)·E₄(X) + 1 + (3/2)α²)`,
where `E₄` is the normalized `s = 4` energy. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace
namespace SphericalRiesz

/-- Lebesgue density of the standard Gaussian on `Ambient9`. -/
def stdGaussianDensity9 (z : Ambient9) : ℝ :=
  ((2*Real.pi)^((9:ℝ)/2))⁻¹*Real.exp (-(1/2)*‖z‖^2)

theorem stdGaussianDensity9_nonneg (z : Ambient9) : 0 ≤ stdGaussianDensity9 z := by
  unfold stdGaussianDensity9
  positivity

theorem stdGaussianDensity9_continuous : Continuous stdGaussianDensity9 := by
  unfold stdGaussianDensity9
  fun_prop

theorem integrable_rexp_neg_mul_sq_norm9 {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : Ambient9 => Real.exp (-b*‖z‖^2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Ambient9)
    (b := (b:ℂ)) (by simpa using hb) 0 0).norm
  refine h.congr (ae_of_all _ fun z => ?_)
  have he : (-(b:ℂ)*((‖z‖:ℝ):ℂ)^2+0*((⟪(0:Ambient9), z⟫:ℝ):ℂ)) = ((-b*‖z‖^2:ℝ):ℂ) := by
    push_cast
    ring
  simp only [he, Complex.norm_exp_ofReal]

/-- The finite measure with the standard Gaussian density. -/
def stdGaussianDensityMeasure9 : Measure Ambient9 :=
  volume.withDensity (fun z => ENNReal.ofReal (stdGaussianDensity9 z))

theorem stdGaussianDensity9_integrable : Integrable stdGaussianDensity9 :=
  (integrable_rexp_neg_mul_sq_norm9 (b := 1/2) (by norm_num)).const_mul _

instance stdGaussianDensityMeasure9_finite : IsFiniteMeasure stdGaussianDensityMeasure9 :=
  isFiniteMeasure_withDensity_ofReal stdGaussianDensity9_integrable.2

theorem integral_stdGaussianDensityMeasure9 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : Ambient9 → F) :
    ∫ z, g z ∂stdGaussianDensityMeasure9 = ∫ z, stdGaussianDensity9 z • g z := by
  rw [stdGaussianDensityMeasure9, integral_withDensity_eq_integral_toReal_smul
    stdGaussianDensity9_continuous.measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (stdGaussianDensity9_nonneg _)]

theorem integral_cexp_gaussian_char9 (t : Ambient9) :
    ∫ x : Ambient9, Complex.exp (-(1/2:ℂ)*‖x‖^2+Complex.I*⟪t, x⟫) =
      (((2*Real.pi)^((9:ℝ)/2):ℝ):ℂ)*Complex.exp (-‖t‖^2/2) := by
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by norm_num) Complex.I t,
    finrank_euclideanSpace_fin, Complex.ofReal_cpow (by positivity)]
  congr 1
  · congr 1
    · push_cast
      ring
    · push_cast
      ring
  · congr 1
    rw [Complex.I_sq]
    ring

theorem charFun_stdGaussianDensityMeasure9 (t : Ambient9) :
    charFun stdGaussianDensityMeasure9 t = Complex.exp (-‖t‖^2/2) := by
  rw [charFun_apply, integral_stdGaussianDensityMeasure9]
  have key : ∀ x : Ambient9, stdGaussianDensity9 x • Complex.exp (⟪x, t⟫*Complex.I) =
      ((((2*Real.pi)^((9:ℝ)/2))⁻¹:ℝ):ℂ)*
        Complex.exp (-(1/2:ℂ)*‖x‖^2+Complex.I*⟪t, x⟫) := by
    intro x
    rw [stdGaussianDensity9, Complex.real_smul, Complex.ofReal_mul, mul_assoc, Complex.ofReal_exp,
      ← Complex.exp_add, real_inner_comm]
    congr 2
    push_cast
    ring
  simp_rw [key]
  rw [integral_const_mul, integral_cexp_gaussian_char9, ← mul_assoc, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (by positivity), Complex.ofReal_one, one_mul]

/-- The standard Gaussian on `Ambient9` has the Lebesgue density `stdGaussianDensity9`. -/
theorem stdGaussian_ambient9_eq : stdGaussian Ambient9 = stdGaussianDensityMeasure9 := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_stdGaussian, charFun_stdGaussianDensityMeasure9]

theorem integral_stdGaussian_ambient9 (g : Ambient9 → ℝ) :
    ∫ z, g z ∂stdGaussian Ambient9 = ∫ z, stdGaussianDensity9 z*g z := by
  rw [stdGaussian_ambient9_eq, integral_stdGaussianDensityMeasure9]
  rfl

/-- Fourier amplitude of the signed measure `Σ δ_{xᵢ} - M σ` at the frequency `w`. -/
def sphereGaussianAmplitude8 {N : ℕ} (M : ℝ) (X : Configuration N) (w : Ambient9) : ℂ :=
  (∑ i, Complex.exp (⟪(X i:Ambient9), w⟫*Complex.I))-(M:ℂ)*charFun ambientSphereProbability8 w

theorem sphereGaussianAmplitude8_continuous {N : ℕ} (M : ℝ) (X : Configuration N) :
    Continuous (sphereGaussianAmplitude8 M X) := by
  have hc : Continuous (charFun ambientSphereProbability8) := continuous_charFun
  unfold sphereGaussianAmplitude8
  fun_prop

theorem sphereGaussianAmplitude8_norm_le {N : ℕ} (M : ℝ) (X : Configuration N) (w : Ambient9) :
    ‖sphereGaussianAmplitude8 M X w‖ ≤ N+|M| := by
  unfold sphereGaussianAmplitude8
  have h1 : ‖∑ i, Complex.exp (⟪(X i:Ambient9), w⟫*Complex.I)‖ ≤ N := by
    calc ‖∑ i, Complex.exp (⟪(X i:Ambient9), w⟫*Complex.I)‖
        ≤ ∑ i, ‖Complex.exp (⟪(X i:Ambient9), w⟫*Complex.I)‖ := norm_sum_le _ _
      _ = N := by simp [Complex.norm_exp_ofReal_mul_I]
  have h2 : ‖(M:ℂ)*charFun ambientSphereProbability8 w‖ ≤ |M| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (norm_charFun_le_one _)
  exact (norm_sub_le _ _).trans (add_le_add h1 h2)

theorem sphereGaussianDefect8_eq_amplitude {N : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (M : ℝ) (X : Configuration N) :
    sphereGaussianDefect8 t M X = ∫ z,
      Complex.normSq (sphereGaussianAmplitude8 M X (Real.sqrt (2*t) • z)) ∂stdGaussian Ambient9 := by
  rw [sphereGaussianDefect8_eq_diffuse ht, diffuseGaussianDefect_eq_normSq ht]
  rfl

/-- Lebesgue form of the neutralized defect: Gaussian weight `e^{-|w|²/(4t)}` on `|φ(w)|²`. -/
theorem sphereGaussianDefect8_eq_lebesgue {N : ℕ} {t : ℝ} (ht : 0 < t)
    (M : ℝ) (X : Configuration N) :
    sphereGaussianDefect8 t M X = (Real.sqrt (2*t)^9)⁻¹*(((2*Real.pi)^((9:ℝ)/2))⁻¹*
      ∫ w, Real.exp (-(4*t)⁻¹*‖w‖^2)*Complex.normSq (sphereGaussianAmplitude8 M X w)) := by
  rw [sphereGaussianDefect8_eq_amplitude ht.le, integral_stdGaussian_ambient9]
  set R := Real.sqrt (2*t) with hRdef
  have hR : 0 < R := Real.sqrt_pos.mpr (by positivity)
  have hR2 : R^2 = 2*t := Real.sq_sqrt (by positivity)
  set G : Ambient9 → ℝ := fun w => ((2*Real.pi)^((9:ℝ)/2))⁻¹*
    (Real.exp (-(4*t)⁻¹*‖w‖^2)*Complex.normSq (sphereGaussianAmplitude8 M X w)) with hG
  have hGz : ∀ z : Ambient9, stdGaussianDensity9 z*
      Complex.normSq (sphereGaussianAmplitude8 M X (R • z)) = G (R • z) := by
    intro z
    simp only [hG, stdGaussianDensity9, norm_smul, Real.norm_eq_abs, abs_of_pos hR, mul_pow, hR2]
    have he : -(4*t)⁻¹*(2*t*‖z‖^2) = -(1/2)*‖z‖^2 := by
      field_simp
      ring
    rw [he]
    ring
  simp_rw [hGz]
  rw [Measure.integral_comp_smul volume G R, finrank_euclideanSpace_fin, smul_eq_mul,
    abs_of_pos (by positivity), hG, integral_const_mul]

theorem sphereGaussianDefect8_sqrt_pow_mul_eq {N : ℕ} {t : ℝ} (ht : 0 < t)
    (M : ℝ) (X : Configuration N) :
    Real.sqrt t^9*sphereGaussianDefect8 t M X = (Real.sqrt 2^9)⁻¹*(((2*Real.pi)^((9:ℝ)/2))⁻¹*
      ∫ w, Real.exp (-(4*t)⁻¹*‖w‖^2)*Complex.normSq (sphereGaussianAmplitude8 M X w)) := by
  rw [sphereGaussianDefect8_eq_lebesgue ht, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), mul_pow]
  have h1 : 0 < Real.sqrt t^9 := pow_pos (Real.sqrt_pos.mpr ht) _
  have h2 : 0 < Real.sqrt 2^9 := pow_pos (Real.sqrt_pos.mpr (by norm_num)) _
  field_simp

theorem sphereGaussianAmplitude8_weighted_integrable {N : ℕ} {t : ℝ} (ht : 0 < t)
    (M : ℝ) (X : Configuration N) :
    Integrable (fun w : Ambient9 =>
      Real.exp (-(4*t)⁻¹*‖w‖^2)*Complex.normSq (sphereGaussianAmplitude8 M X w)) := by
  apply (integrable_rexp_neg_mul_sq_norm9 (b := (4*t)⁻¹) (by positivity)).mul_bdd
    (Complex.continuous_normSq.comp (sphereGaussianAmplitude8_continuous M X)).aestronglyMeasurable
    (c := ((N:ℝ)+|M|)^2)
  refine ae_of_all _ fun w => ?_
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) (sphereGaussianAmplitude8_norm_le M X w) 2

/-- `√t⁹ · D(t)` is nondecreasing in `t > 0`. -/
theorem sphereGaussianDefect8_sqrt_pow_mul_mono {N : ℕ} {t t' : ℝ} (ht : 0 < t) (htt : t ≤ t')
    (M : ℝ) (X : Configuration N) :
    Real.sqrt t^9*sphereGaussianDefect8 t M X ≤ Real.sqrt t'^9*sphereGaussianDefect8 t' M X := by
  have ht' : 0 < t' := ht.trans_le htt
  rw [sphereGaussianDefect8_sqrt_pow_mul_eq ht, sphereGaussianDefect8_sqrt_pow_mul_eq ht']
  have hc : 0 ≤ (Real.sqrt 2^9)⁻¹ := by positivity
  have hc' : 0 ≤ ((2*Real.pi)^((9:ℝ)/2))⁻¹ := by positivity
  apply mul_le_mul_of_nonneg_left _ hc
  apply mul_le_mul_of_nonneg_left _ hc'
  apply integral_mono_of_nonneg
    (ae_of_all _ fun w => mul_nonneg (Real.exp_pos _).le (Complex.normSq_nonneg _))
    (sphereGaussianAmplitude8_weighted_integrable ht' M X)
  refine ae_of_all _ fun w => ?_
  apply mul_le_mul_of_nonneg_right _ (Complex.normSq_nonneg _)
  apply Real.exp_le_exp.mpr
  have hinv : (4*t')⁻¹ ≤ (4*t)⁻¹ := inv_anti₀ (by positivity) (by linarith)
  nlinarith [sq_nonneg ‖w‖]

theorem sphereGaussianCenteredScaled8_add_one {N : ℕ} (hN : 0 < N) {α : ℝ} (hα : 0 ≤ α)
    (X : Configuration N) :
    sphereGaussianCenteredScaled8 α X+1 =
      sphereGaussianDefect8 (sphereGaussianScale8 N α) (N:ℝ) X/(N:ℝ) := by
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hs : 0 ≤ sphereGaussianScale8 N α := by
    rw [sphereGaussianScale8_eq_factor]
    exact mul_nonneg (sphereGaussianDensityFactor8_pos hN).le hα
  rw [sphereGaussianDefect8_charge_N hs, sphereGaussianCenteredScaled8]
  field_simp
  ring

theorem sphereGaussianCenteredScaled8_add_one_nonneg {N : ℕ} (hN : 0 < N) {α : ℝ} (hα : 0 ≤ α)
    (X : Configuration N) : 0 ≤ sphereGaussianCenteredScaled8 α X+1 := by
  have hs : 0 ≤ sphereGaussianScale8 N α := by
    rw [sphereGaussianScale8_eq_factor]
    exact mul_nonneg (sphereGaussianDensityFactor8_pos hN).le hα
  rw [sphereGaussianCenteredScaled8_add_one hN hα]
  exact div_nonneg (sphereGaussianDefect8_nonneg hs _ X) (Nat.cast_nonneg N)

/-- PSD monotonicity of the density-scaled centered profile: `√α⁹ (F(α)+1)` is nondecreasing. -/
theorem sphereGaussianCenteredScaled8_sqrt_pow_mono {N : ℕ} (hN : 0 < N) (X : Configuration N)
    {α α' : ℝ} (hα : 0 < α) (hαα : α ≤ α') :
    Real.sqrt α^9*(sphereGaussianCenteredScaled8 α X+1) ≤
      Real.sqrt α'^9*(sphereGaussianCenteredScaled8 α' X+1) := by
  have hα' : 0 < α' := hα.trans_le hαα
  set c := sphereGaussianDensityFactor8 N with hcdef
  have hc : 0 < c := sphereGaussianDensityFactor8_pos hN
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  rw [sphereGaussianCenteredScaled8_add_one hN hα.le, sphereGaussianCenteredScaled8_add_one hN hα'.le,
    sphereGaussianScale8_eq_factor, sphereGaussianScale8_eq_factor]
  have hm := sphereGaussianDefect8_sqrt_pow_mul_mono (mul_pos hc hα)
    (mul_le_mul_of_nonneg_left hαα hc.le) (N:ℝ) X
  rw [Real.sqrt_mul hc.le, Real.sqrt_mul hc.le, mul_pow, mul_pow] at hm
  have hc9 : 0 < Real.sqrt c^9 := pow_pos (Real.sqrt_pos.mpr hc) _
  rw [← hcdef]
  have key : ∀ a : ℝ, Real.sqrt a^9*(sphereGaussianDefect8 (c*a) (N:ℝ) X/(N:ℝ)) =
      (Real.sqrt c^9*(N:ℝ))⁻¹*(Real.sqrt c^9*Real.sqrt a^9*sphereGaussianDefect8 (c*a) (N:ℝ) X) := by
    intro a
    field_simp
  rw [key, key]
  exact mul_le_mul_of_nonneg_left hm (by positivity)

/-- Doubling form of the monotonicity: `F(α)+1 ≤ √2⁹ (F(β)+1)` for `α ≤ β ≤ 2α`. -/
theorem sphereGaussianCenteredScaled8_doubling {N : ℕ} (hN : 0 < N) (X : Configuration N)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 2*α) :
    sphereGaussianCenteredScaled8 α X+1 ≤ Real.sqrt 2^9*(sphereGaussianCenteredScaled8 β X+1) := by
  have hm := sphereGaussianCenteredScaled8_sqrt_pow_mono hN X hα hαβ
  have hβ0 : 0 ≤ sphereGaussianCenteredScaled8 β X+1 :=
    sphereGaussianCenteredScaled8_add_one_nonneg hN (hα.le.trans hαβ) X
  have hsq : Real.sqrt β ≤ Real.sqrt 2*Real.sqrt α := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hβ
  have hpow : Real.sqrt β^9 ≤ Real.sqrt 2^9*Real.sqrt α^9 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 9
  have hα9 : 0 < Real.sqrt α^9 := pow_pos (Real.sqrt_pos.mpr hα) _
  have h2 : Real.sqrt α^9*(sphereGaussianCenteredScaled8 α X+1) ≤
      Real.sqrt α^9*(Real.sqrt 2^9*(sphereGaussianCenteredScaled8 β X+1)) := by
    calc _ ≤ Real.sqrt β^9*(sphereGaussianCenteredScaled8 β X+1) := hm
      _ ≤ (Real.sqrt 2^9*Real.sqrt α^9)*(sphereGaussianCenteredScaled8 β X+1) :=
        mul_le_mul_of_nonneg_right hpow hβ0
      _ = _ := by ring
  exact le_of_mul_le_mul_left h2 hα9

/-- Averaging a doubling inequality against a weighted integral with an integrable lower. -/
theorem doubling_average_bound {F m : ℝ → ℝ} {α κ : ℝ} (hα : 0 < α) (hκ : 0 < κ)
    (hdbl : ∀ β ∈ Ioc α (2*α), F α+1 ≤ κ*(F β+1))
    (hlow : ∀ β, 0 < β → -m β ≤ β*F β)
    (hm0 : ∀ β, 0 < β → 0 ≤ m β)
    (hFi : IntegrableOn (fun β => β*F β) (Ioi 0))
    (hmi : IntegrableOn m (Ioi 0)) :
    (F α+1)*(3/2*α^2) ≤ κ*((∫ β in Ioi 0, β*F β)+(∫ β in Ioi 0, m β)+3/2*α^2) := by
  have hSsub : Ioc α (2*α) ⊆ Ioi 0 := fun β hβ => hα.trans hβ.1
  have hsplit := integral_inter_add_sdiff (μ := volume) (measurableSet_Ioc (a := α) (b := 2*α)) hFi
  rw [inter_eq_right.mpr hSsub] at hsplit
  have hcomp : -(∫ β in Ioi 0, m β) ≤ ∫ β in Ioi 0 \ Ioc α (2*α), β*F β := by
    have h1 : ∫ β in Ioi 0 \ Ioc α (2*α), -m β ≤ ∫ β in Ioi 0 \ Ioc α (2*α), β*F β :=
      setIntegral_mono_on (hmi.mono_set sdiff_subset).neg (hFi.mono_set sdiff_subset)
        (measurableSet_Ioi.diff measurableSet_Ioc) (fun β hβ => hlow β hβ.1)
    have h2 : ∫ β in Ioi 0 \ Ioc α (2*α), m β ≤ ∫ β in Ioi 0, m β := by
      apply setIntegral_mono_set hmi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with β hβ
        exact hm0 β hβ
      · exact (sdiff_subset (s := Ioi (0:ℝ)) (t := Ioc α (2*α))).eventuallyLE
    rw [integral_neg] at h1
    linarith
  have hid : ∫ β in Ioc α (2*α), β*((F α+1)/κ-1) = ((F α+1)/κ-1)*(3/2*α^2) := by
    rw [integral_mul_const, ← intervalIntegral.integral_of_le (by linarith), integral_id]
    ring
  have hS_low : ((F α+1)/κ-1)*(3/2*α^2) ≤ ∫ β in Ioc α (2*α), β*F β := by
    rw [← hid]
    have hci : IntegrableOn (fun β : ℝ => β*((F α+1)/κ-1)) (Ioc α (2*α)) :=
      (continuous_id.mul continuous_const).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    apply setIntegral_mono_on hci (hFi.mono_set hSsub) measurableSet_Ioc
    intro β hβ
    have hβ0 : 0 < β := hα.trans hβ.1
    have hd := hdbl β hβ
    apply mul_le_mul_of_nonneg_left _ hβ0.le
    rw [div_sub_one hκ.ne', div_le_iff₀ hκ]
    linarith
  have hfinal : ((F α+1)/κ-1)*(3/2*α^2) ≤ (∫ β in Ioi 0, β*F β)+(∫ β in Ioi 0, m β) := by
    linarith
  have he : (F α+1)*(3/2*α^2) = κ*(((F α+1)/κ-1)*(3/2*α^2))+κ*(3/2*α^2) := by
    field_simp
    ring
  rw [he]
  nlinarith

/-- Uniform small-scale bound from the `s = 4` energy: for every configuration and `α > 0`,
`(F(α)+1)·(3/2)α² ≤ √2⁹ ((8/√210)·E₄(X) + 1 + (3/2)α²)`. -/
theorem sphereGaussianCenteredScaled8_small_scale_bound {N : ℕ} (hN : 0 < N)
    (X : Configuration N) {α : ℝ} (hα : 0 < α) :
    (sphereGaussianCenteredScaled8 α X+1)*(3/2*α^2) ≤
      Real.sqrt 2^9*((8/Real.sqrt 210)*normalizedEnergy X+1+3/2*α^2) := by
  have h := doubling_average_bound (F := fun β => sphereGaussianCenteredScaled8 β X)
    (m := sphereGaussianMajorant8 4) hα (by positivity)
    (fun β hβ => sphereGaussianCenteredScaled8_doubling hN X hα hβ.1.le hβ.2)
    (fun β hβ => sphereGaussianCenteredScaled8_weighted_lower hN hβ X)
    (fun β hβ => sphereGaussianMajorant8_nonneg 4 hβ)
    (sphereGaussianCenteredScaled8_weighted_integrable hN X)
    (sphereGaussianMajorant8_integrable (by norm_num) (by norm_num))
  rw [sphereGaussianMajorant8_four_integral] at h
  have hE : (∫ β in Ioi 0, β*sphereGaussianCenteredScaled8 β X) =
      (8/Real.sqrt 210)*normalizedEnergy X := by
    rw [normalizedEnergy_gaussian_mellin_four hN X, sphereGaussianArea8_coarse_coefficient]
    have : (0:ℝ) < Real.sqrt 210 := by positivity
    field_simp
  rw [hE] at h
  exact h

/-- The `α⁻²` majorant: `F(α)+1 ≤ √2⁹ (1 + (2/3)((8/√210)·E₄(X)+1)/α²)`. -/
theorem sphereGaussianCenteredScaled8_le_inv_sq {N : ℕ} (hN : 0 < N) (X : Configuration N)
    {α : ℝ} (hα : 0 < α) :
    sphereGaussianCenteredScaled8 α X+1 ≤
      Real.sqrt 2^9*(1+(2/3)*((8/Real.sqrt 210)*normalizedEnergy X+1)/α^2) := by
  have h := sphereGaussianCenteredScaled8_small_scale_bound hN X hα
  have hα2 : 0 < 3/2*α^2 := by positivity
  rw [← le_div_iff₀ hα2] at h
  calc _ ≤ _ := h
    _ = _ := by
      field_simp
      ring

end SphericalRiesz
