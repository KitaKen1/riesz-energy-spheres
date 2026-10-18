import Riesz.SphereGaussianUpper24
import Riesz.NodeSeparation
import Riesz.EqualAreaFinitePatchGeometry24
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Actual Gaussian end controls on S²⁴ and its Leech charts. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
namespace SphericalRiesz
open Boundary

/-- Lebesgue density of the standard Gaussian on `(AmbientD 24)`. -/
def stdGaussianDensity25 (z : (AmbientD 24)) : ℝ :=
  ((2*Real.pi)^((25:ℝ)/2))⁻¹*Real.exp (-(1/2)*‖z‖^2)

theorem stdGaussianDensity25_nonneg (z : (AmbientD 24)) : 0 ≤ stdGaussianDensity25 z := by
  unfold stdGaussianDensity25
  positivity

theorem stdGaussianDensity25_continuous : Continuous stdGaussianDensity25 := by
  unfold stdGaussianDensity25
  fun_prop

theorem integrable_rexp_neg_mul_sq_norm25 {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : (AmbientD 24) => Real.exp (-b*‖z‖^2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := (AmbientD 24))
    (b := (b:ℂ)) (by simpa using hb) 0 0).norm
  refine h.congr (ae_of_all _ fun z => ?_)
  have he : (-(b:ℂ)*((‖z‖:ℝ):ℂ)^2+0*((⟪(0:(AmbientD 24)), z⟫:ℝ):ℂ)) = ((-b*‖z‖^2:ℝ):ℂ) := by
    push_cast
    ring
  simp only [he, Complex.norm_exp_ofReal]

/-- The finite measure with the standard Gaussian density. -/
def stdGaussianDensityMeasure25 : Measure (AmbientD 24) :=
  volume.withDensity (fun z => ENNReal.ofReal (stdGaussianDensity25 z))

theorem stdGaussianDensity25_integrable : Integrable stdGaussianDensity25 :=
  (integrable_rexp_neg_mul_sq_norm25 (b := 1/2) (by norm_num)).const_mul _

instance stdGaussianDensityMeasure25_finite : IsFiniteMeasure stdGaussianDensityMeasure25 :=
  isFiniteMeasure_withDensity_ofReal stdGaussianDensity25_integrable.2

theorem integral_stdGaussianDensityMeasure25 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : (AmbientD 24) → F) :
    ∫ z, g z ∂stdGaussianDensityMeasure25 = ∫ z, stdGaussianDensity25 z • g z := by
  rw [stdGaussianDensityMeasure25, integral_withDensity_eq_integral_toReal_smul
    stdGaussianDensity25_continuous.measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (stdGaussianDensity25_nonneg _)]

theorem integral_cexp_gaussian_char25 (t : (AmbientD 24)) :
    ∫ x : (AmbientD 24), Complex.exp (-(1/2:ℂ)*‖x‖^2+Complex.I*⟪t, x⟫) =
      (((2*Real.pi)^((25:ℝ)/2):ℝ):ℂ)*Complex.exp (-‖t‖^2/2) := by
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

theorem charFun_stdGaussianDensityMeasure25 (t : (AmbientD 24)) :
    charFun stdGaussianDensityMeasure25 t = Complex.exp (-‖t‖^2/2) := by
  rw [charFun_apply, integral_stdGaussianDensityMeasure25]
  have key : ∀ x : (AmbientD 24), stdGaussianDensity25 x • Complex.exp (⟪x, t⟫*Complex.I) =
      ((((2*Real.pi)^((25:ℝ)/2))⁻¹:ℝ):ℂ)*
        Complex.exp (-(1/2:ℂ)*‖x‖^2+Complex.I*⟪t, x⟫) := by
    intro x
    rw [stdGaussianDensity25, Complex.real_smul, Complex.ofReal_mul, mul_assoc, Complex.ofReal_exp,
      ← Complex.exp_add, real_inner_comm]
    congr 2
    push_cast
    ring
  simp_rw [key]
  rw [integral_const_mul, integral_cexp_gaussian_char25, ← mul_assoc, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (by positivity), Complex.ofReal_one, one_mul]

/-- The standard Gaussian on `(AmbientD 24)` has the Lebesgue density `stdGaussianDensity25`. -/
theorem stdGaussian_ambient25_eq : stdGaussian (AmbientD 24) = stdGaussianDensityMeasure25 := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_stdGaussian, charFun_stdGaussianDensityMeasure25]

theorem integral_stdGaussian_ambient25 (g : (AmbientD 24) → ℝ) :
    ∫ z, g z ∂stdGaussian (AmbientD 24) = ∫ z, stdGaussianDensity25 z*g z := by
  rw [stdGaussian_ambient25_eq, integral_stdGaussianDensityMeasure25]
  rfl

/-- Fourier amplitude of the signed measure `Σ δ_{xᵢ} - M σ` at the frequency `w`. -/
def sphereGaussianAmplitude24 {N : ℕ} (M : ℝ) (X : (ConfigurationD 24) N) (w : (AmbientD 24)) : ℂ :=
  (∑ i, Complex.exp (⟪(X i:(AmbientD 24)), w⟫*Complex.I))-(M:ℂ)*charFun ambientSphereProbability24 w

theorem sphereGaussianAmplitude24_continuous {N : ℕ} (M : ℝ) (X : (ConfigurationD 24) N) :
    Continuous (sphereGaussianAmplitude24 M X) := by
  have hc : Continuous (charFun ambientSphereProbability24) := continuous_charFun
  unfold sphereGaussianAmplitude24
  fun_prop

theorem sphereGaussianAmplitude24_norm_le {N : ℕ} (M : ℝ) (X : (ConfigurationD 24) N) (w : (AmbientD 24)) :
    ‖sphereGaussianAmplitude24 M X w‖ ≤ N+|M| := by
  unfold sphereGaussianAmplitude24
  have h1 : ‖∑ i, Complex.exp (⟪(X i:(AmbientD 24)), w⟫*Complex.I)‖ ≤ N := by
    calc ‖∑ i, Complex.exp (⟪(X i:(AmbientD 24)), w⟫*Complex.I)‖
        ≤ ∑ i, ‖Complex.exp (⟪(X i:(AmbientD 24)), w⟫*Complex.I)‖ := norm_sum_le _ _
      _ = N := by simp [Complex.norm_exp_ofReal_mul_I]
  have h2 : ‖(M:ℂ)*charFun ambientSphereProbability24 w‖ ≤ |M| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (norm_charFun_le_one _)
  exact (norm_sub_le _ _).trans (add_le_add h1 h2)

theorem sphereGaussianDefect24_eq_amplitude {N : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (M : ℝ) (X : (ConfigurationD 24) N) :
    sphereGaussianDefect24 t M X = ∫ z,
      Complex.normSq (sphereGaussianAmplitude24 M X (Real.sqrt (2*t) • z)) ∂stdGaussian (AmbientD 24) := by
  rw [sphereGaussianDefect24_eq_diffuse ht, diffuseGaussianDefect_eq_normSq ht]
  rfl

/-- Lebesgue form of the neutralized defect: Gaussian weight `e^{-|w|²/(4t)}` on `|φ(w)|²`. -/
theorem sphereGaussianDefect24_eq_lebesgue {N : ℕ} {t : ℝ} (ht : 0 < t)
    (M : ℝ) (X : (ConfigurationD 24) N) :
    sphereGaussianDefect24 t M X = (Real.sqrt (2*t)^25)⁻¹*(((2*Real.pi)^((25:ℝ)/2))⁻¹*
      ∫ w, Real.exp (-(4*t)⁻¹*‖w‖^2)*Complex.normSq (sphereGaussianAmplitude24 M X w)) := by
  rw [sphereGaussianDefect24_eq_amplitude ht.le, integral_stdGaussian_ambient25]
  set R := Real.sqrt (2*t) with hRdef
  have hR : 0 < R := Real.sqrt_pos.mpr (by positivity)
  have hR2 : R^2 = 2*t := Real.sq_sqrt (by positivity)
  set G : (AmbientD 24) → ℝ := fun w => ((2*Real.pi)^((25:ℝ)/2))⁻¹*
    (Real.exp (-(4*t)⁻¹*‖w‖^2)*Complex.normSq (sphereGaussianAmplitude24 M X w)) with hG
  have hGz : ∀ z : (AmbientD 24), stdGaussianDensity25 z*
      Complex.normSq (sphereGaussianAmplitude24 M X (R • z)) = G (R • z) := by
    intro z
    simp only [hG, stdGaussianDensity25, norm_smul, Real.norm_eq_abs, abs_of_pos hR, mul_pow, hR2]
    have he : -(4*t)⁻¹*(2*t*‖z‖^2) = -(1/2)*‖z‖^2 := by
      field_simp
      ring
    rw [he]
    ring
  simp_rw [hGz]
  rw [Measure.integral_comp_smul volume G R, finrank_euclideanSpace_fin, smul_eq_mul,
    abs_of_pos (by positivity), hG, integral_const_mul]

theorem sphereGaussianDefect24_sqrt_pow_mul_eq {N : ℕ} {t : ℝ} (ht : 0 < t)
    (M : ℝ) (X : (ConfigurationD 24) N) :
    Real.sqrt t^25*sphereGaussianDefect24 t M X = (Real.sqrt 2^25)⁻¹*(((2*Real.pi)^((25:ℝ)/2))⁻¹*
      ∫ w, Real.exp (-(4*t)⁻¹*‖w‖^2)*Complex.normSq (sphereGaussianAmplitude24 M X w)) := by
  rw [sphereGaussianDefect24_eq_lebesgue ht, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), mul_pow]
  have h1 : 0 < Real.sqrt t^25 := pow_pos (Real.sqrt_pos.mpr ht) _
  have h2 : 0 < Real.sqrt 2^25 := pow_pos (Real.sqrt_pos.mpr (by norm_num)) _
  field_simp

theorem sphereGaussianAmplitude24_weighted_integrable {N : ℕ} {t : ℝ} (ht : 0 < t)
    (M : ℝ) (X : (ConfigurationD 24) N) :
    Integrable (fun w : (AmbientD 24) =>
      Real.exp (-(4*t)⁻¹*‖w‖^2)*Complex.normSq (sphereGaussianAmplitude24 M X w)) := by
  apply (integrable_rexp_neg_mul_sq_norm25 (b := (4*t)⁻¹) (by positivity)).mul_bdd
    (Complex.continuous_normSq.comp (sphereGaussianAmplitude24_continuous M X)).aestronglyMeasurable
    (c := ((N:ℝ)+|M|)^2)
  refine ae_of_all _ fun w => ?_
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) (sphereGaussianAmplitude24_norm_le M X w) 2

/-- `√t²⁵ · D(t)` is nondecreasing in `t > 0`. -/
theorem sphereGaussianDefect24_sqrt_pow_mul_mono {N : ℕ} {t t' : ℝ} (ht : 0 < t) (htt : t ≤ t')
    (M : ℝ) (X : (ConfigurationD 24) N) :
    Real.sqrt t^25*sphereGaussianDefect24 t M X ≤ Real.sqrt t'^25*sphereGaussianDefect24 t' M X := by
  have ht' : 0 < t' := ht.trans_le htt
  rw [sphereGaussianDefect24_sqrt_pow_mul_eq ht, sphereGaussianDefect24_sqrt_pow_mul_eq ht']
  have hc : 0 ≤ (Real.sqrt 2^25)⁻¹ := by positivity
  have hc' : 0 ≤ ((2*Real.pi)^((25:ℝ)/2))⁻¹ := by positivity
  apply mul_le_mul_of_nonneg_left _ hc
  apply mul_le_mul_of_nonneg_left _ hc'
  apply integral_mono_of_nonneg
    (ae_of_all _ fun w => mul_nonneg (Real.exp_pos _).le (Complex.normSq_nonneg _))
    (sphereGaussianAmplitude24_weighted_integrable ht' M X)
  refine ae_of_all _ fun w => ?_
  apply mul_le_mul_of_nonneg_right _ (Complex.normSq_nonneg _)
  apply Real.exp_le_exp.mpr
  have hinv : (4*t')⁻¹ ≤ (4*t)⁻¹ := inv_anti₀ (by positivity) (by linarith)
  nlinarith [sq_nonneg ‖w‖]

theorem sphereGaussianCenteredScaled24_add_one {N : ℕ} (hN : 0 < N) {α : ℝ} (hα : 0 ≤ α)
    (X : (ConfigurationD 24) N) :
    sphereGaussianCenteredScaled24 α X+1 =
      sphereGaussianDefect24 (sphereGaussianScale24 N α) (N:ℝ) X/(N:ℝ) := by
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hs : 0 ≤ sphereGaussianScale24 N α := by
    rw [sphereGaussianScale24_eq_factor]
    exact mul_nonneg (sphereGaussianDensityFactor24_pos hN).le hα
  rw [sphereGaussianDefect24_charge_N hs, sphereGaussianCenteredScaled24]
  field_simp
  ring

theorem sphereGaussianCenteredScaled24_add_one_nonneg {N : ℕ} (hN : 0 < N) {α : ℝ} (hα : 0 ≤ α)
    (X : (ConfigurationD 24) N) : 0 ≤ sphereGaussianCenteredScaled24 α X+1 := by
  have hs : 0 ≤ sphereGaussianScale24 N α := by
    rw [sphereGaussianScale24_eq_factor]
    exact mul_nonneg (sphereGaussianDensityFactor24_pos hN).le hα
  rw [sphereGaussianCenteredScaled24_add_one hN hα]
  exact div_nonneg (sphereGaussianDefect24_nonneg hs _ X) (Nat.cast_nonneg N)

/-- PSD monotonicity of the density-scaled centered profile: `√α²⁵ (F(α)+1)` is nondecreasing. -/
theorem sphereGaussianCenteredScaled24_sqrt_pow_mono {N : ℕ} (hN : 0 < N) (X : (ConfigurationD 24) N)
    {α α' : ℝ} (hα : 0 < α) (hαα : α ≤ α') :
    Real.sqrt α^25*(sphereGaussianCenteredScaled24 α X+1) ≤
      Real.sqrt α'^25*(sphereGaussianCenteredScaled24 α' X+1) := by
  have hα' : 0 < α' := hα.trans_le hαα
  set c := sphereGaussianDensityFactor24 N with hcdef
  have hc : 0 < c := sphereGaussianDensityFactor24_pos hN
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  rw [sphereGaussianCenteredScaled24_add_one hN hα.le, sphereGaussianCenteredScaled24_add_one hN hα'.le,
    sphereGaussianScale24_eq_factor, sphereGaussianScale24_eq_factor]
  have hm := sphereGaussianDefect24_sqrt_pow_mul_mono (mul_pos hc hα)
    (mul_le_mul_of_nonneg_left hαα hc.le) (N:ℝ) X
  rw [Real.sqrt_mul hc.le, Real.sqrt_mul hc.le, mul_pow, mul_pow] at hm
  have hc9 : 0 < Real.sqrt c^25 := pow_pos (Real.sqrt_pos.mpr hc) _
  rw [← hcdef]
  have key : ∀ a : ℝ, Real.sqrt a^25*(sphereGaussianDefect24 (c*a) (N:ℝ) X/(N:ℝ)) =
      (Real.sqrt c^25*(N:ℝ))⁻¹*(Real.sqrt c^25*Real.sqrt a^25*sphereGaussianDefect24 (c*a) (N:ℝ) X) := by
    intro a
    field_simp
  rw [key, key]
  exact mul_le_mul_of_nonneg_left hm (by positivity)

/-- Doubling form of the monotonicity: `F(α)+1 ≤ √2²⁵ (F(β)+1)` for `α ≤ β ≤ 2α`. -/
theorem sphereGaussianCenteredScaled24_doubling {N : ℕ} (hN : 0 < N) (X : (ConfigurationD 24) N)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 2*α) :
    sphereGaussianCenteredScaled24 α X+1 ≤ Real.sqrt 2^25*(sphereGaussianCenteredScaled24 β X+1) := by
  have hm := sphereGaussianCenteredScaled24_sqrt_pow_mono hN X hα hαβ
  have hβ0 : 0 ≤ sphereGaussianCenteredScaled24 β X+1 :=
    sphereGaussianCenteredScaled24_add_one_nonneg hN (hα.le.trans hαβ) X
  have hsq : Real.sqrt β ≤ Real.sqrt 2*Real.sqrt α := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hβ
  have hpow : Real.sqrt β^25 ≤ Real.sqrt 2^25*Real.sqrt α^25 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 25
  have hα9 : 0 < Real.sqrt α^25 := pow_pos (Real.sqrt_pos.mpr hα) _
  have h2 : Real.sqrt α^25*(sphereGaussianCenteredScaled24 α X+1) ≤
      Real.sqrt α^25*(Real.sqrt 2^25*(sphereGaussianCenteredScaled24 β X+1)) := by
    calc
      _ ≤ Real.sqrt β^25*(sphereGaussianCenteredScaled24 β X+1) := hm
      _ ≤ (Real.sqrt 2^25*Real.sqrt α^25)*(sphereGaussianCenteredScaled24 β X+1) :=
        mul_le_mul_of_nonneg_right hpow hβ0
      _ = _ := by ring
  exact le_of_mul_le_mul_left h2 hα9


/-- An actual Gaussian PSD budget on the macroscopic interval. -/
def sphereGaussianSmallBudget24 {N : ℕ} (q : ℝ) (X : (ConfigurationD 24) N) : ℝ :=
  ∫ α in Ioc (0:ℝ) 4, α^(q-1)*(sphereGaussianCenteredScaled24 α X+1)

theorem sphereGaussianSmallBudget24_integrable {N : ℕ} (hN : 0 < N)
    {q : ℝ} (hq : 0 < q) (hq12 : q < 12) (X : (ConfigurationD 24) N) :
    IntegrableOn (fun α : ℝ => α^(q-1)*(sphereGaussianCenteredScaled24 α X+1)) (Ioc 0 4) := by
  have hf := (sphereGaussianCenteredScaled24_weighted_integrable_rpow
    (s := 2*q) (by linarith) (by linarith) hN X).mono_set (s := Ioc (0:ℝ) 4) Ioc_subset_Ioi_self
  have hw : IntegrableOn (fun α : ℝ => α^(q-1)) (Ioc 0 4) := by
    exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < q-1) (a := 0) (b := 4)).1
  have he : (fun α : ℝ => α^(q-1)*(sphereGaussianCenteredScaled24 α X+1)) =
      (fun α => α^(q-1)*sphereGaussianCenteredScaled24 α X) + (fun α => α^(q-1)) := by
    funext α; simp only [Pi.add_apply]; ring
  rw [he]
  have hqeq : 2*q/2-1 = q-1 := by ring
  rw [hqeq] at hf
  exact hf.add hw

theorem sphereGaussianSmallBudget24_nonneg {N : ℕ} (hN : 0 < N)
    (q : ℝ) (X : (ConfigurationD 24) N) : 0 ≤ sphereGaussianSmallBudget24 q X := by
  apply setIntegral_nonneg measurableSet_Ioc
  intro α hα
  exact mul_nonneg (Real.rpow_nonneg hα.1.le _)
    (sphereGaussianCenteredScaled24_add_one_nonneg hN hα.1.le X)

/-- PSD doubling turns a Gaussian integral budget into a pointwise small-scale bound. -/
theorem sphereGaussianCenteredScaled24_small_budget_bound {N : ℕ} (hN : 0 < N)
    {q : ℝ} (hq : 0 < q) (hq12 : q < 12) (X : (ConfigurationD 24) N)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 2) :
    (sphereGaussianCenteredScaled24 α X+1)*α^q ≤
      (Real.sqrt 2^25*q/(2^q-1))*sphereGaussianSmallBudget24 q X := by
  let F := fun β => sphereGaussianCenteredScaled24 β X+1
  let κ : ℝ := Real.sqrt 2^25
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hi := sphereGaussianSmallBudget24_integrable hN hq hq12 X
  have hsub : Ioc α (2*α) ⊆ Ioc (0:ℝ) 4 := fun β hβ => ⟨hα.trans hβ.1,by linarith [hβ.2]⟩
  have hw : IntegrableOn (fun β : ℝ => β^(q-1)) (Ioc α (2*α)) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < q-1)).1
  have hid : (∫ β in Ioc α (2*α), β^(q-1)) = α^q*(2^q-1)/q := by
    rw [← intervalIntegral.integral_of_le (by linarith), integral_rpow (Or.inl (by linarith)),
      show q-1+1=q by ring, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hα.le]
    ring
  have hl : F α/κ*(α^q*(2^q-1)/q) ≤ sphereGaussianSmallBudget24 q X := by
    calc
      _ = ∫ β in Ioc α (2*α), (F α/κ)*β^(q-1) := by rw [integral_const_mul,hid]
      _ ≤ ∫ β in Ioc α (2*α), β^(q-1)*F β := by
        apply setIntegral_mono_on (hw.const_mul _) (hi.mono_set hsub) measurableSet_Ioc
        intro β hβ
        have hd := sphereGaussianCenteredScaled24_doubling hN X hα hβ.1.le hβ.2
        have hd' : F α/κ ≤ F β := (div_le_iff₀ hκ).mpr (by simpa [F,κ,mul_comm] using hd)
        exact (mul_le_mul_of_nonneg_right hd' (Real.rpow_nonneg (hα.le.trans hβ.1.le) _)).trans_eq (mul_comm _ _)
      _ ≤ sphereGaussianSmallBudget24 q X := by
        apply setIntegral_mono_set hi
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with β hβ
          exact mul_nonneg (Real.rpow_nonneg hβ.1.le _)
            (sphereGaussianCenteredScaled24_add_one_nonneg hN hβ.1.le X)
        · exact hsub.eventuallyLE
  have h2 : 0 < (2:ℝ)^q-1 := by
    have := Real.one_lt_rpow (by norm_num : (1:ℝ) < 2) hq
    linarith
  have he : (F α/κ*(α^q*(2^q-1)/q))*(κ*q/(2^q-1)) = F α*α^q := by
    field_simp <;> ring
  have hb := mul_le_mul_of_nonneg_right hl (by positivity : 0 ≤ κ*q/(2^q-1))
  rw [he] at hb
  exact hb.trans_eq (mul_comm _ _)

/-- The uniform budget at q=s/4 gives an integrable small-alpha upper power. -/
theorem sphereGaussianCenteredScaled24_small_weighted_bound {N : ℕ} (hN : 0 < N)
    {s B : ℝ} (hs : 0 < s) (hs24 : s < 24) (X : (ConfigurationD 24) N)
    (hB : sphereGaussianSmallBudget24 (s/4) X ≤ B)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 2) :
    α^(s/2-1)*sphereGaussianCenteredScaled24 α X ≤
      (Real.sqrt 2^25*(s/4)/(2^(s/4)-1))*B*α^(s/4-1) := by
  have h := sphereGaussianCenteredScaled24_small_budget_bound hN
    (q := s/4) (by linarith) (by linarith) X hα hα1
  have hconst : 0 ≤ Real.sqrt 2^25*(s/4)/(2^(s/4)-1) := by
    have := Real.one_lt_rpow (by norm_num : (1:ℝ) < 2) (by linarith : 0 < s/4)
    positivity
  have hb := h.trans (mul_le_mul_of_nonneg_left hB hconst)
  have hq : 0 < α^(s/4) := Real.rpow_pos_of_pos hα _
  have hf : sphereGaussianCenteredScaled24 α X ≤
      (Real.sqrt 2^25*(s/4)/(2^(s/4)-1))*B/α^(s/4) := by
    apply (le_div_iff₀ hq).mpr
    nlinarith
  calc
    _ ≤ α^(s/2-1)*((Real.sqrt 2^25*(s/4)/(2^(s/4)-1))*B/α^(s/4)) :=
      mul_le_mul_of_nonneg_left hf (Real.rpow_nonneg hα.le _)
    _ = _ := by
      have hp : α^(s/2-1)/α^(s/4) = α^(s/4-1) := by
        rw [← Real.rpow_sub hα]
        congr 1
        ring
      calc
        _ = ((Real.sqrt 2^25*(s/4)/(2^(s/4)-1))*B)*(α^(s/2-1)/α^(s/4)) := by ring
        _ = _ := by rw [hp]

/-- Every finite subset of the actual Leech lattice is bounded by its theta tail. -/
theorem finiteLeechGaussian_row_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : ι ↪ leechLattice) (i : ι) {β : ℝ} (hβ : 0 < β) :
    (∑ j ∈ Finset.univ.erase i, Real.exp (-(Real.pi*β*‖((U j-U i : leechLattice) : LeechAmbient)‖^2))) ≤
      leechGaussianThetaReal24 β-1 := by
  classical
  let f : leechLattice → ℝ := fun u => Real.exp (-(Real.pi*β*‖(u : LeechAmbient)‖^2))
  have hf : HasSum f (leechGaussianThetaReal24 β) :=
    Complex.hasSum_ofReal.mp (leechLatticeGaussian_hasSum hβ)
  have hf0 : f 0 = 1 := by simp [f]
  have hup := hf.update (0 : leechLattice) 0
  rw [hf0] at hup
  let V : ι → leechLattice := fun j => U j-U i
  have hV : Function.Injective V := fun j k h => U.injective (sub_left_injective h)
  have hsum : (∑ j ∈ Finset.univ.erase i, f (V j)) =
      ∑ u ∈ (Finset.univ.erase i).image V, Function.update f 0 0 u := by
    rw [Finset.sum_image (fun j _ k _ h => hV h)]
    apply Finset.sum_congr rfl
    intro j hj
    have hj0 : V j ≠ 0 := fun h => (Finset.mem_erase.mp hj).1 (U.injective (sub_eq_zero.mp h))
    exact (Function.update_of_ne hj0 _ _).symm
  change (∑ j ∈ Finset.univ.erase i, f (V j)) ≤ _
  rw [hsum]
  have hnonneg : ∀ u, 0 ≤ Function.update f 0 0 u := by
    intro u; by_cases hu : u=0
    · simp [hu]
    · rw [Function.update_of_ne hu]; exact (Real.exp_pos _).le
  have hle := hup.summable.sum_le_tsum ((Finset.univ.erase i).image V) (fun u _ => hnonneg u)
  rw [hup.tsum_eq] at hle
  linarith

/-- A lower distance estimate for a physical Leech patch controls its full Gaussian row. -/
theorem leechPatchGaussian_row_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : ι ↪ leechLattice) (Y : ι → (SphereD 24)) {ell t : ℝ} (hell : 0 < ell) (ht : 0 < t)
    (hd : ∀ i j, ell*‖((U j-U i : leechLattice) : LeechAmbient)‖ ≤ dist (Y i) (Y j)) (i : ι) :
    (∑ j ∈ Finset.univ.erase i, sphereGaussianKernel24 t (Y i) (Y j)) ≤
      leechGaussianThetaReal24 (t*ell^2/Real.pi)-1 := by
  have hβ : 0 < t*ell^2/Real.pi := by positivity
  apply le_trans _ (finiteLeechGaussian_row_le U i hβ)
  apply Finset.sum_le_sum
  intro j _
  unfold sphereGaussianKernel24
  apply Real.exp_le_exp.mpr
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ ell*‖((U j-U i : leechLattice) : LeechAmbient)‖) (hd i j) 2
  have he : Real.pi*(t*ell^2/Real.pi) = t*ell^2 := by field_simp
  rw [he,mul_pow] at *
  nlinarith

theorem leechPatchGaussian_row_exp_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : ι ↪ leechLattice) (Y : ι → (SphereD 24)) {ell t : ℝ} (hell : 0 < ell) (ht : 0 < t)
    (hd : ∀ i j, ell*‖((U j-U i : leechLattice) : LeechAmbient)‖ ≤ dist (Y i) (Y j))
    (hscale : 1 ≤ t*ell^2/Real.pi) (i : ι) :
    (∑ j ∈ Finset.univ.erase i, sphereGaussianKernel24 t (Y i) (Y j)) ≤
      Real.exp (-(2*Real.pi)*(t*ell^2/Real.pi-1))*(leechGaussianThetaReal24 1-1) :=
  (leechPatchGaussian_row_le U Y hell ht hd i).trans (leechGaussianThetaReal24_tail_le hscale)


theorem equalAreaLeechPatch_dist_eq (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (v c x y : Fin 24 → ℝ) {ε : ℝ} (hε : 0 < ε) :
    dist (equalAreaLeechPatch g v c ε x) (equalAreaLeechPatch g v c ε y) =
      ε*dist (equalAreaNormalizedLeechPatch g v c ε x) (equalAreaNormalizedLeechPatch g v c ε y) := by
  rw [equalAreaNormalizedLeechPatch_eq,equalAreaNormalizedLeechPatch_eq,dist_eq_norm,dist_eq_norm,
    ← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hε)]
  have he : (equalAreaLeechPatch g v c ε x-equalAreaLeechPatch g v c ε c)-
      (equalAreaLeechPatch g v c ε y-equalAreaLeechPatch g v c ε c) =
      equalAreaLeechPatch g v c ε x-equalAreaLeechPatch g v c ε y := by abel
  rw [he,← mul_assoc,mul_inv_cancel₀ hε.ne',one_mul]

/-- The theta row estimate applies to the actual near-flat sphere charts. -/
theorem equalAreaLeechPatch_gaussian_row_uniform {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
      (v c : Fin 24 → ℝ), ‖v‖ ≤ ρ → ∀ (hc : c ∈ UnitCube 24)
      (ε : ℝ) (hε : 0 < ε), ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8),
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (U : ι ↪ leechLattice) (x : ι → UnitCube 24)
      (a : ℝ), 0 < a →
      (∀ i j, dist (WithLp.toLp 2 (leechMap (x i)) : LeechAmbient)
        (WithLp.toLp 2 (leechMap (x j))) = a*‖((U j-U i : leechLattice) : LeechAmbient)‖) →
      ∀ t : ℝ, 0 < t → ∀ i : ι,
      (∑ j ∈ Finset.univ.erase i, sphereGaussianKernel24 t
        (equalAreaLeechCubeEmbedding24 g v c ε hε hc hsmall (x i))
        (equalAreaLeechCubeEmbedding24 g v c ε hε hc hsmall (x j))) ≤
      leechGaussianThetaReal24 (t*((1-η)*ε*a)^2/Real.pi)-1 := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := equalAreaNormalizedLeechPatch_relative_distance_uniform η hη
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro g v c hv hc ε hε hs hsmall ι _ _ U x a ha hflat t ht i
  have hη0 : 0 < 1-η := by linarith
  apply leechPatchGaussian_row_le U _ (by positivity : 0 < (1-η)*ε*a) ht _ i
  intro j k
  change _ ≤ dist (equalAreaLeechPatch g v c ε (x j)) (equalAreaLeechPatch g v c ε (x k))
  rw [equalAreaLeechPatch_dist_eq g v c _ _ hε]
  have hd := (abs_le.mp (hb v hv ε hε hs g c hc (x j) (x j).property (x k) (x k).property)).1
  rw [hflat] at hd
  nlinarith

/-- Cross pairs between separated physical patches have an exponential Gaussian bound. -/
theorem separatedGaussian_cross_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : ι → (SphereD 24)) (Y : κ → (SphereD 24)) {δ t : ℝ} (hδ : 0 ≤ δ) (ht : 0 ≤ t)
    (hd : ∀ i j, δ ≤ dist (X i) (Y j)) :
    (∑ i, ∑ j, sphereGaussianKernel24 t (X i) (Y j)) ≤
      (Fintype.card ι:ℝ)*(Fintype.card κ:ℝ)*Real.exp (-(t*δ^2)) := by
  calc
    _ ≤ (∑ _ : ι, ∑ _ : κ, Real.exp (-(t*δ^2))) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      unfold sphereGaussianKernel24
      apply Real.exp_le_exp.mpr
      have hsq := pow_le_pow_left₀ hδ (hd i j) 2
      nlinarith
    _ = _ := by simp; ring

/-- At the actual density scale even N times a separated Gaussian cross row vanishes. -/
theorem sphereGaussianScale24_separated_tendsto {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (hNp : ∀ k, 0 < N k) {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) :
    Tendsto (fun k => (N k:ℝ)*Real.exp (-(sphereGaussianScale24 (N k) α*δ^2))) atTop (𝓝 0) := by
  have hc := sphereGaussianScale24_tendsto hN hα
  have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 12).comp
    (hc.atTop_mul_const (by positivity : 0 < δ^2))
  have hA : 0 < (sphereAreaD 24).real univ := sphereAreaD_univ_pos 24
  have he : ∀ k, (N k:ℝ)*Real.exp (-(sphereGaussianScale24 (N k) α*δ^2)) =
      ((sphereAreaD 24).real univ/(Real.pi^12*α^12*(δ^2)^12))*
      ((sphereGaussianScale24 (N k) α*δ^2)^12*Real.exp (-(sphereGaussianScale24 (N k) α*δ^2))) := by
    intro k
    rw [mul_pow,sphereGaussianScale24_pow_twelve (hNp k) α]
    field_simp <;> ring
  simpa only [mul_zero] using (ht.const_mul _).congr (fun k => (he k).symm)


/-- A stronger Mellin tail kernel also gives pointwise Gaussian domination. -/
theorem gaussian24_le_shortRange_pointwise {c p α : ℝ} (hc : 0 < c) (hp : 0 ≤ p)
    (hα : 2 ≤ α) {x y : (SphereD 24)} (hxy : x ≠ y) :
    sphereGaussianKernel24 (c*α) x y ≤
      2^(p+1)*α^(-(p+1))*shortRangeKernel24 c p x y := by
  have hα0 : 0 < α := by linarith
  have hi := sphereGaussianPair24_scaled_tail_integrable (c := c) (s := 2*(p+1)) hc
    (by linarith) zero_le_one hxy
  have hpe : 2*(p+1)/2-1 = p := by ring
  rw [hpe] at hi
  have hsub : Ioc (α/2) α ⊆ Ioi (1:ℝ) := fun β hβ => by
    have hb : α/2 < β := hβ.1
    change 1 < β
    linarith
  have hlow : (α/2)^(p+1)*sphereGaussianKernel24 (c*α) x y ≤ shortRangeKernel24 c p x y := by
    calc
      _ = (∫ β in Ioc (α/2) α, (α/2)^p*sphereGaussianKernel24 (c*α) x y) := by
        rw [setIntegral_const,Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal (by linarith)]
        simp only [smul_eq_mul]
        rw [show α-α/2=α/2 by ring,Real.rpow_add_one (by linarith : α/2 ≠ 0)]
        ring
      _ ≤ (∫ β in Ioc (α/2) α, β^p*sphereGaussianKernel24 (c*β) x y) := by
        apply setIntegral_mono_on (integrable_const _) (hi.mono_set hsub) measurableSet_Ioc
        intro β hβ
        have hg : sphereGaussianKernel24 (c*α) x y ≤ sphereGaussianKernel24 (c*β) x y := by
          unfold sphereGaussianKernel24
          apply Real.exp_le_exp.mpr
          have hmul := mul_le_mul_of_nonneg_left hβ.2
            (mul_nonneg hc.le (sq_nonneg (dist x y)))
          nlinarith
        exact mul_le_mul (Real.rpow_le_rpow (by linarith) hβ.1.le hp) hg
          (sphereGaussianKernel24_nonneg _ _ _) (Real.rpow_nonneg (by linarith [hβ.1]) _)
      _ ≤ shortRangeKernel24 c p x y := by
        apply setIntegral_mono_set hi
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with β hβ
          exact mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hβ.le) _) (sphereGaussianKernel24_nonneg _ _ _)
        · exact hsub.eventuallyLE
  have hpow : 0 < (α/2)^(p+1) := Real.rpow_pos_of_pos (by linarith) _
  have hinv : ((α/2)^(p+1))⁻¹ = 2^(p+1)*α^(-(p+1)) := by
    rw [Real.div_rpow hα0.le (by norm_num : (0:ℝ) ≤ 2), inv_div, Real.rpow_neg hα0.le]
    ring
  calc
    _ ≤ ((α/2)^(p+1))⁻¹*shortRangeKernel24 c p x y := by
      rw [← div_eq_inv_mul,le_div_iff₀ hpow]
      simpa only [mul_comm] using hlow
    _ = _ := by rw [hinv]

/-- A uniform actual tail-kernel budget controls the weighted centered profile at infinity. -/
theorem sphereGaussianCenteredScaled24_large_budget_bound {N : ℕ} (hN : 0 < N)
    {s D : ℝ} (hs : 0 < s) (X : (ConfigurationD 24) N)
    (hD : cellPairSum (shortRangeKernel24 (sphereGaussianDensityFactor24 N) (s/4+5)) X/(N:ℝ) ≤ D)
    {α : ℝ} (hα : 2 ≤ α) :
    α^(s/2-1)*sphereGaussianCenteredScaled24 α X ≤
      2^(s/4+6)*D*α^(s/4-7) := by
  classical
  have hα0 : 0 < α := by linarith
  let A : ℝ := 2^(s/4+6)*α^(-(s/4+6))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hNR : 0 < (N:ℝ) := by exact_mod_cast hN
  have hrow : (∑ i, ∑ j ∈ Finset.univ.erase i,
      sphereGaussianKernel24 (sphereGaussianScale24 N α) (X i) (X j)) ≤
      A*cellPairSum (shortRangeKernel24 (sphereGaussianDensityFactor24 N) (s/4+5)) X := by
    unfold cellPairSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    calc
      _ ≤ (∑ j ∈ Finset.univ.erase i, A*shortRangeKernel24
        (sphereGaussianDensityFactor24 N) (s/4+5) (X i) (X j)) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [sphereGaussianScale24_eq_factor]
        simpa only [A,show s/4+5+1=s/4+6 by ring] using
          gaussian24_le_shortRange_pointwise (sphereGaussianDensityFactor24_pos hN)
            (by linarith : 0 ≤ s/4+5) hα (X.injective.ne (Finset.mem_erase.mp hj).1.symm)
      _ ≤ (∑ j : Fin N, A*shortRangeKernel24
          (sphereGaussianDensityFactor24 N) (s/4+5) (X i) (X j)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ =>
          mul_nonneg hA (shortRangeKernel24_nonneg _ _ _ _))
  have hcenter : sphereGaussianCenteredScaled24 α X ≤
      A*(cellPairSum (shortRangeKernel24 (sphereGaussianDensityFactor24 N) (s/4+5)) X/(N:ℝ)) := by
    have hoff := sphereGaussianOffDiagonal24_eq_full_sub (sphereGaussianScale24 N α) X
    have hbg := sphereGaussianBackground24_nonneg (sphereGaussianScale24 N α)
    have he : sphereGaussianOffDiagonal24 (sphereGaussianScale24 N α) X/(N:ℝ) =
        (∑ i, ∑ j, sphereGaussianKernel24 (sphereGaussianScale24 N α) (X i) (X j))/(N:ℝ)-1 := by
      rw [hoff,sub_div,div_self hNR.ne']
    calc
      _ ≤ sphereGaussianOffDiagonal24 (sphereGaussianScale24 N α) X/(N:ℝ) := by
        rw [he]
        unfold sphereGaussianCenteredScaled24
        nlinarith [mul_nonneg hNR.le hbg]
      _ ≤ (A*cellPairSum (shortRangeKernel24 (sphereGaussianDensityFactor24 N) (s/4+5)) X)/(N:ℝ) :=
        div_le_div_of_nonneg_right hrow hNR.le
      _ = _ := by ring
  have hb := hcenter.trans (mul_le_mul_of_nonneg_left hD hA)
  calc
    _ ≤ α^(s/2-1)*(A*D) := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hα0.le _)
    _ = _ := by
      dsimp [A]
      rw [show α^(s/2-1)*(2^(s/4+6)*α^(-(s/4+6))*D) =
        (2^(s/4+6)*D)*(α^(s/2-1)*α^(-(s/4+6))) by ring,
        ← Real.rpow_add hα0,show s/2-1+ -(s/4+6)=s/4-7 by ring]

/-- An explicit majorant, with actual Gaussian budgets as its constants. -/
def sphereGaussianUpperMajorant24 (s B D α : ℝ) : ℝ :=
  if α ≤ 2 then (Real.sqrt 2^25*(s/4)/(2^(s/4)-1))*|B| *α^(s/4-1)
  else 2^(s/4+6)*|D| *α^(s/4-7)

theorem sphereGaussianUpperMajorant24_nonneg {s : ℝ} (hs : 0 < s) (B D : ℝ)
    {α : ℝ} (hα : 0 < α) : 0 ≤ sphereGaussianUpperMajorant24 s B D α := by
  have h2 : 0 < (2:ℝ)^(s/4)-1 := by
    have := Real.one_lt_rpow (by norm_num : (1:ℝ) < 2) (by linarith : 0 < s/4)
    linarith
  unfold sphereGaussianUpperMajorant24
  split_ifs <;> positivity

theorem sphereGaussianUpperMajorant24_integrable {s : ℝ} (hs : 0 < s) (hs24 : s < 24) (B D : ℝ) :
    IntegrableOn (sphereGaussianUpperMajorant24 s B D) (Ioi 0) := by
  have hi0 : IntegrableOn (fun α : ℝ => α^(s/4-1)) (Ioo 0 2) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0:ℝ) < 2)).mpr (by linarith)
  have hj0 : IntegrableOn (fun α : ℝ => α^(s/4-7)) (Ioi 2) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hi1 : IntegrableOn (fun α : ℝ => (Real.sqrt 2^25*(s/4)/(2^(s/4)-1))*|B| *α^(s/4-1)) (Ioo 0 2) := hi0.const_mul _
  have hj1 : IntegrableOn (fun α : ℝ => 2^(s/4+6)*|D| *α^(s/4-7)) (Ioi 2) := hj0.const_mul _
  have hi := hi1.integrable_indicator measurableSet_Ioo
  have hj := hj1.integrable_indicator measurableSet_Ioi
  apply (hi.add hj).integrableOn.congr
  have hne : ∀ᵐ α : ℝ ∂volume.restrict (Ioi 0), α ≠ 2 := by
    have hm : ({2}:Set ℝ)ᶜ ∈ ae (volume.restrict (Ioi 0)) :=
      compl_mem_ae_iff.mpr (measure_singleton (2:ℝ))
    filter_upwards [hm] with α hα
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hα
  filter_upwards [ae_restrict_mem measurableSet_Ioi,hne] with α hα hne
  dsimp only [sphereGaussianUpperMajorant24,Pi.add_apply]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [if_pos hlt.le,indicator_of_mem (show α ∈ Ioo 0 2 from ⟨hα,hlt⟩),
      indicator_of_notMem (show α ∉ Ioi 2 by simpa using hlt.le),add_zero]
  · rw [if_neg (not_le.mpr hgt),indicator_of_notMem (notMem_Ioo_of_ge hgt.le),
      indicator_of_mem (show α ∈ Ioi 2 from hgt),zero_add]

/-- The explicit Gaussian budgets discharge the integrable-majorant premise of the upper bridge. -/
theorem sphere24_riesz_upper_of_gaussian_budgets {s : ℝ} (hs : 0 < s) (hs24 : s < 24)
    {N : ℕ → ℕ} (hNt : Tendsto N atTop atTop) (hN : ∀ k, 0 < N k)
    (X : ∀ k, (ConfigurationD 24) (N k)) (B D : ℝ)
    (hB : ∀ k, sphereGaussianSmallBudget24 (s/4) (X k) ≤ B)
    (hD : ∀ k, cellPairSum (shortRangeKernel24 (sphereGaussianDensityFactor24 (N k)) (s/4+5))
      (X k)/(N k:ℝ) ≤ D)
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      sphereGaussianFullScaled24 α (X k) ≤ leechGaussianThetaReal24 α+ε) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
      normalizedEnergyRpow24 s (X k) ≤ sphereRieszCoefficient24 s+η := by
  apply sphere24_riesz_upper_of_full_profile hs hs24 hNt hN X
    (sphereGaussianUpperMajorant24_integrable hs hs24 B D)
    (fun α hα => sphereGaussianUpperMajorant24_nonneg hs B D hα) _ hp
  intro k α hα
  unfold sphereGaussianUpperMajorant24
  split_ifs with hsmall
  · exact sphereGaussianCenteredScaled24_small_weighted_bound (hN k) hs hs24 (X k)
      ((hB k).trans (le_abs_self B)) hα hsmall
  · exact sphereGaussianCenteredScaled24_large_budget_bound (hN k) hs (X k)
      ((hD k).trans (le_abs_self D)) (le_of_not_ge hsmall)


/-- Concrete n^24 midpoint coordinates for a finite Leech lattice patch. -/
def leechMidpointGrid24 (n : ℕ) (hn : 0 < n) (u : Fin 24 → Fin n) : UnitCube 24 :=
  ⟨fun i => ((u i:ℝ)+1/2)/(n:ℝ), by
    intro i
    have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
    have hu : (u i:ℝ)+1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt (u i).isLt
    exact ⟨by positivity, (div_le_one hnR).mpr (by linarith)⟩⟩

def leechGridLattice24 (n : ℕ) : (Fin 24 → Fin n) ↪ leechLattice where
  toFun u := ⟨leechIntegerPoint (fun i => (u i:ℤ)), (leechLattice_mem_iff _).mpr ⟨_,rfl⟩⟩
  inj' := by
    intro u w h
    have h' := congrArg (fun z : leechLattice => WithLp.ofLp (z : LeechAmbient)) h
    have hc := leechMap_injective h'
    funext i
    apply Fin.ext
    have hi : ((u i).val : ℝ) = ((w i).val : ℝ) := by simpa using congrFun hc i
    exact_mod_cast hi

theorem leechMidpointGrid24_card (n : ℕ) : Fintype.card (Fin 24 → Fin n) = n^24 := by
  simp

theorem leechMidpointGrid24_flat_distance (n : ℕ) (hn : 0 < n) (u w : Fin 24 → Fin n) :
    dist (WithLp.toLp 2 (leechMap (leechMidpointGrid24 n hn u)) : LeechAmbient)
      (WithLp.toLp 2 (leechMap (leechMidpointGrid24 n hn w))) =
      (n:ℝ)⁻¹*‖((leechGridLattice24 n w-leechGridLattice24 n u : leechLattice) : LeechAmbient)‖ := by
  have he : (leechMidpointGrid24 n hn u : Fin 24 → ℝ)-leechMidpointGrid24 n hn w =
      (n:ℝ)⁻¹ • (fun i => (u i:ℝ)-(w i:ℝ)) := by
    funext i
    simp only [leechMidpointGrid24,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv]
    ring
  rw [dist_eq_norm,← WithLp.toLp_sub,← map_sub,he,map_smul,WithLp.toLp_smul,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)⁻¹)]
  congr 1
  change ‖WithLp.toLp 2 (leechMap (fun i => (u i:ℝ)-(w i:ℝ)))‖ =
    ‖leechIntegerPoint (fun i => (w i:ℤ))-leechIntegerPoint (fun i => (u i:ℤ))‖
  rw [norm_sub_rev]
  rw [leechIntegerPoint,leechIntegerPoint,← WithLp.toLp_sub,← map_sub]
  simp only [Int.cast_natCast]
  rfl

/-- Actual sphere midpoint patches have a theta row bound uniform in the refinement n. -/
theorem equalAreaLeechMidpoint24_gaussian_rows {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
      (v c : Fin 24 → ℝ), ‖v‖ ≤ ρ → ∀ (hc : c ∈ UnitCube 24)
      (ε : ℝ) (hε : 0 < ε), ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) (n : ℕ) (hn : 0 < n)
      (t : ℝ), 0 < t → ∀ u : Fin 24 → Fin n,
      (∑ w ∈ Finset.univ.erase u, sphereGaussianKernel24 t
        (equalAreaLeechCubeEmbedding24 g v c ε hε hc hsmall (leechMidpointGrid24 n hn u))
        (equalAreaLeechCubeEmbedding24 g v c ε hε hc hsmall (leechMidpointGrid24 n hn w))) ≤
      leechGaussianThetaReal24 (t*((1-η)*ε/(n:ℝ))^2/Real.pi)-1 := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := equalAreaLeechPatch_gaussian_row_uniform hη hη1
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro g v c hv hc ε hε hs hsmall n hn t ht u
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  simpa only [div_eq_mul_inv] using hb g v c hv hc ε hε hs hsmall (leechGridLattice24 n)
    (leechMidpointGrid24 n hn) (n:ℝ)⁻¹ (inv_pos.mpr hnR)
    (leechMidpointGrid24_flat_distance n hn) t ht u


/-- The actual flat derivative has a positive norm, with no additional hypothesis. -/
theorem equalAreaFlatDerivative24_norm_pos : 0 < ‖equalAreaFlatDerivative24‖ := by
  by_contra h
  have hz : equalAreaFlatDerivative24 = 0 := norm_eq_zero.mp
    (le_antisymm (le_of_not_gt h) (norm_nonneg _))
  have hc := equalAreaLeech_distance_controls_coordinates (fun _ : Fin 24 => (1 : ℝ)) 0
  rw [← equalAreaFlatDerivative24_dist, hz] at hc
  norm_num at hc

/-- Boundary corrections retain control by their distinct integer labels. -/
theorem correctedRule_label_sub_le {n : ℕ} (hn : 8 ≤ n) (u w : NodeIndex n) :
    |(midpointLabel n u:ℝ)-(midpointLabel n w:ℝ)| ≤
      2*|unscaledRuleNode n u-unscaledRuleNode n w| := by
  have haux : ∀ i j : NodeIndex n, midpointLabel n i < midpointLabel n j →
      |(midpointLabel n i:ℝ)-(midpointLabel n j:ℝ)| ≤
        2*|unscaledRuleNode n i-unscaledRuleNode n j| := by
    intro i j hij
    have hg : (midpointLabel n i:ℝ)+1 ≤ midpointLabel n j := by
      exact_mod_cast Nat.succ_le_of_lt hij
    have hi := abs_lt.mp (unscaledRuleNode_close_to_label hn i)
    have hj := abs_lt.mp (unscaledRuleNode_close_to_label hn j)
    rw [abs_of_nonpos (by linarith : (midpointLabel n i:ℝ)-(midpointLabel n j:ℝ) ≤ 0)]
    have hdiff : -(midpointLabel n i:ℝ)+(midpointLabel n j:ℝ) ≤
        2*(unscaledRuleNode n j-unscaledRuleNode n i) := by linarith
    calc
      _ ≤ 2*(unscaledRuleNode n j-unscaledRuleNode n i) := by linarith
      _ ≤ 2*|unscaledRuleNode n j-unscaledRuleNode n i| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
      _ = _ := by rw [abs_sub_comm]
  rcases lt_trichotomy (midpointLabel n u) (midpointLabel n w) with h | h | h
  · exact haux u w h
  · simp [h]
  · simpa only [abs_sub_comm] using haux w u h

def leechCorrectedLabel24 (n : ℕ) (hn : 8 ≤ n) :
    (Fin 24 → NodeIndex n) ↪ leechLattice where
  toFun u := ⟨leechIntegerPoint (fun i => (midpointLabel n (u i):ℤ)),
    (leechLattice_mem_iff _).mpr ⟨_,rfl⟩⟩
  inj' := by
    intro u w h
    have hc := leechMap_injective (congrArg (fun z : leechLattice => WithLp.ofLp (z : LeechAmbient)) h)
    funext i
    apply midpointLabel_injective hn
    have hi : (midpointLabel n (u i):ℝ) = (midpointLabel n (w i):ℝ) := by
      simpa using congrFun hc i
    exact_mod_cast hi

/-- All boundary-corrected nodes admit one lattice-label distance bound. -/
theorem leechCorrectedLabel24_norm_le {n : ℕ} (hn : 8 ≤ n)
    (u w : Fin 24 → NodeIndex n) :
    ‖((leechCorrectedLabel24 n hn w-leechCorrectedLabel24 n hn u : leechLattice) : LeechAmbient)‖ ≤
      (2*(n:ℝ)*‖equalAreaFlatDerivative24‖)*‖cubeNode 24 n u-cubeNode 24 n w‖ := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  let z : Fin 24 → ℝ := fun i => (midpointLabel n (u i):ℝ)-(midpointLabel n (w i):ℝ)
  have hz : ‖z‖ ≤ (2*(n:ℝ))*‖cubeNode 24 n u-cubeNode 24 n w‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    have h := correctedRule_label_sub_le hn (u i) (w i)
    have he : |unscaledRuleNode n (u i)-unscaledRuleNode n (w i)| =
        (n:ℝ)*|cubeNode 24 n u i-cubeNode 24 n w i| := by
      simp only [cubeNode,ruleNode,← sub_div,abs_div,abs_of_pos hnR]
      field_simp
    rw [he] at h
    calc ‖z i‖ ≤ 2*((n:ℝ)*|cubeNode 24 n u i-cubeNode 24 n w i|) := h
      _ ≤ (2*(n:ℝ))*‖cubeNode 24 n u-cubeNode 24 n w‖ := by
        have hi := norm_le_pi_norm (cubeNode 24 n u-cubeNode 24 n w) i
        simp only [Pi.sub_apply,Real.norm_eq_abs] at hi
        nlinarith
  have he : ‖((leechCorrectedLabel24 n hn w-leechCorrectedLabel24 n hn u : leechLattice) : LeechAmbient)‖ =
      ‖equalAreaFlatDerivative24 z‖ := by
    conv_rhs =>
      rw [← dist_zero_right, ← map_zero equalAreaFlatDerivative24,
        equalAreaFlatDerivative24_dist, map_zero, WithLp.toLp_zero, dist_zero_right]
    change ‖leechIntegerPoint (fun i => (midpointLabel n (w i):ℤ))-
      leechIntegerPoint (fun i => (midpointLabel n (u i):ℤ))‖ = ‖WithLp.toLp 2 (leechMap z)‖
    rw [norm_sub_rev,leechIntegerPoint,leechIntegerPoint,← WithLp.toLp_sub,← map_sub]
    rfl
  rw [he]
  calc
    _ ≤ ‖equalAreaFlatDerivative24‖*‖z‖ := equalAreaFlatDerivative24.le_opNorm z
    _ ≤ ‖equalAreaFlatDerivative24‖*((2*(n:ℝ))*‖cubeNode 24 n u-cubeNode 24 n w‖) :=
      mul_le_mul_of_nonneg_left hz (norm_nonneg _)
    _ = _ := by ring

/-- The actual boundary-corrected foreground rows have a uniform Gaussian theta bound. -/
theorem equalAreaLeechCorrected24_gaussian_row {n : ℕ} (hn : 8 ≤ n)
    (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (v c : Fin 24 → ℝ)
    (hc : c ∈ UnitCube 24) {ε : ℝ} (hε : 0 < ε)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) {L t : ℝ} (hL : 0 < L) (ht : 0 < t)
    (hlower : ∀ x ∈ UnitCube 24, ∀ y ∈ UnitCube 24,
      L*‖x-y‖ ≤ dist (equalAreaNormalizedLeechPatch g v c ε x) (equalAreaNormalizedLeechPatch g v c ε y))
    (u : Fin 24 → NodeIndex n) :
    (∑ w ∈ Finset.univ.erase u, sphereGaussianKernel24 t
      (equalAreaLeechCubeEmbedding24 g v c ε hε hc hsmall
        ⟨cubeNode 24 n u,fun i => ⟨(cubeNode_mem_open 24 n hn u i).1.le,(cubeNode_mem_open 24 n hn u i).2.le⟩⟩)
      (equalAreaLeechCubeEmbedding24 g v c ε hε hc hsmall
        ⟨cubeNode 24 n w,fun i => ⟨(cubeNode_mem_open 24 n hn w i).1.le,(cubeNode_mem_open 24 n hn w i).2.le⟩⟩)) ≤
    leechGaussianThetaReal24 (t*(ε*L/(2*(n:ℝ)*‖equalAreaFlatDerivative24‖))^2/Real.pi)-1 := by
  have hflat := equalAreaFlatDerivative24_norm_pos
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  apply leechPatchGaussian_row_le (leechCorrectedLabel24 n hn) _ (by positivity) ht _ u
  intro i j
  change _ ≤ dist (equalAreaLeechPatch g v c ε (cubeNode 24 n i))
    (equalAreaLeechPatch g v c ε (cubeNode 24 n j))
  rw [equalAreaLeechPatch_dist_eq g v c _ _ hε]
  have hi : cubeNode 24 n i ∈ UnitCube 24 := fun k => ⟨(cubeNode_mem_open 24 n hn i k).1.le,(cubeNode_mem_open 24 n hn i k).2.le⟩
  have hj : cubeNode 24 n j ∈ UnitCube 24 := fun k => ⟨(cubeNode_mem_open 24 n hn j k).1.le,(cubeNode_mem_open 24 n hn j k).2.le⟩
  have hgeom := hlower _ hi _ hj
  have hlabel := leechCorrectedLabel24_norm_le hn i j
  have hden : 0 < 2*(n:ℝ)*‖equalAreaFlatDerivative24‖ := by positivity
  have hdiv : ‖((leechCorrectedLabel24 n hn j-leechCorrectedLabel24 n hn i : leechLattice) :
      LeechAmbient)‖/(2*(n:ℝ)*‖equalAreaFlatDerivative24‖) ≤ ‖cubeNode 24 n i-cubeNode 24 n j‖ :=
    (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hlabel)
  calc
    _ = ε*L*(‖((leechCorrectedLabel24 n hn j-leechCorrectedLabel24 n hn i : leechLattice) : LeechAmbient)‖ /
      (2*(n:ℝ)*‖equalAreaFlatDerivative24‖)) := by ring
    _ ≤ ε*L*‖cubeNode 24 n i-cubeNode 24 n j‖ := mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ ≤ _ := by nlinarith


end SphericalRiesz
