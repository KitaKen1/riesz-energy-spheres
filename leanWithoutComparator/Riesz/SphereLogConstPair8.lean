import Riesz.SphereLogCoefficient8
import Riesz.SphereRieszConstPair8

/-! The logarithmic constant is the actual double integral (stage LOG).

On the unit sphere `d = |x - y| ≤ 2`, so `log (2/d) = ½ ∫ t⁻¹ (e^(-t d²) - e^(-4t)) dt` has a
nonnegative integrand (Frullani with `a = d²`, `b = 4`). Tonelli in `[0,∞]` off the null diagonal
gives `∫∫ log (2/|x-y|) = ½ ∫ t⁻¹ (B(t) - e^(-4t)) dt < ∞`, and `-log d = log (2/d) - log 2`
together with `½ ∫ t⁻¹ (e^(-4t) - e^(-t)) dt = -log 2` identifies
`W_log = ½ ∫ t⁻¹ (B(t) - e^(-t)) dt` with `∫∫ -log |x - y| dσ dσ`. Hence the logarithmic lower
bound holds in the form of the conjecture. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace SphericalRiesz

theorem frullani_exp_pair {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t⁻¹*(Real.exp (-(a*t))-Real.exp (-(b*t)))) (Ioi 0) ∧
    (∫ t in Ioi 0, t⁻¹*(Real.exp (-(a*t))-Real.exp (-(b*t)))) = Real.log b-Real.log a := by
  obtain ⟨h1, h2⟩ := frullani_exp ha
  obtain ⟨h3, h4⟩ := frullani_exp hb
  have he : (fun t : ℝ => t⁻¹*(Real.exp (-(a*t))-Real.exp (-(b*t)))) =
      fun t => t⁻¹*(Real.exp (-(a*t))-Real.exp (-t))-t⁻¹*(Real.exp (-(b*t))-Real.exp (-t)) := by
    funext t; ring
  rw [he]
  refine ⟨h1.sub h3, ?_⟩
  rw [integral_sub h1 h3, h2, h4]
  ring

theorem sphereLogPair8_ofReal_mellin {x y : Sphere8} (hxy : x ≠ y) :
    ENNReal.ofReal (Real.log (2/dist x y)) = ENNReal.ofReal (1/2) *
      ∫⁻ t in Ioi 0, ENNReal.ofReal (t⁻¹*(sphereGaussianKernel8 t x y-Real.exp (-(4*t)))) := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hd2 := sphere8_dist_le_two x y
  have hpos : ∀ t ∈ Ioi (0:ℝ), 0 ≤ t⁻¹*(sphereGaussianKernel8 t x y-Real.exp (-(4*t))) := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    apply mul_nonneg (inv_nonneg.mpr ht0.le)
    have hdd : (dist x y)^2 ≤ 4 := by nlinarith [hd.le]
    have : t*(dist x y)^2 ≤ 4*t := by nlinarith [mul_le_mul_of_nonneg_left hdd ht0.le]
    simp only [sphereGaussianKernel8]
    linarith [Real.exp_le_exp.mpr (neg_le_neg this)]
  obtain ⟨hint, hval⟩ := frullani_exp_pair (a := (dist x y)^2) (b := 4) (by positivity)
    (by norm_num)
  have hint' : IntegrableOn (fun t : ℝ => t⁻¹*(sphereGaussianKernel8 t x y-Real.exp (-(4*t))))
      (Ioi 0) := by
    refine hint.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [sphereGaussianKernel8, mul_comm t]
  have hval' : (∫ t in Ioi 0, t⁻¹*(sphereGaussianKernel8 t x y-Real.exp (-(4*t)))) =
      2*Real.log (2/dist x y) := by
    rw [← setIntegral_congr_fun measurableSet_Ioi (fun t _ => by
      simp only [sphereGaussianKernel8, mul_comm t] :
        ∀ t ∈ Ioi (0:ℝ), t⁻¹*(Real.exp (-((dist x y)^2*t))-Real.exp (-(4*t))) =
          t⁻¹*(sphereGaussianKernel8 t x y-Real.exp (-(4*t)))), hval,
      Real.log_div (by norm_num) hd.ne', Real.log_pow, show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [← ofReal_integral_eq_lintegral_ofReal hint'
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hpos t ht), hval', ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

theorem sphereGaussianBackground8_ge_exp {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-(4*t)) ≤ sphereGaussianBackground8 t := by
  have hle : ∀ p : Sphere8 × Sphere8, Real.exp (-(4*t)) ≤ sphereGaussianKernel8 t p.1 p.2 := by
    intro p
    have hd2 := sphere8_dist_le_two p.1 p.2
    have hd0 : 0 ≤ dist p.1 p.2 := dist_nonneg
    have hdd : (dist p.1 p.2)^2 ≤ 4 := by nlinarith
    have : t*(dist p.1 p.2)^2 ≤ 4*t := by nlinarith [mul_le_mul_of_nonneg_left hdd ht]
    simp only [sphereGaussianKernel8]
    exact Real.exp_le_exp.mpr (neg_le_neg this)
  have h := integral_mono
    (integrable_const (Real.exp (-(4*t))) (μ := sphereProbability8.prod sphereProbability8))
    (sphereGaussianKernel8_pair_integrable ht) hle
  unfold sphereGaussianBackground8
  simpa using h

theorem sphereGaussianBackground8_log4_integrable :
    IntegrableOn (fun t : ℝ => t⁻¹*(sphereGaussianBackground8 t-Real.exp (-(4*t)))) (Ioi 0) := by
  have h1 := sphereGaussianBackground8_log_integrable
  have h2 := (frullani_exp (a := 4) (by norm_num)).1
  have he : (fun t : ℝ => t⁻¹*(sphereGaussianBackground8 t-Real.exp (-(4*t)))) =
      fun t => t⁻¹*(sphereGaussianBackground8 t-Real.exp (-t))-
        t⁻¹*(Real.exp (-(4*t))-Real.exp (-t)) := by
    funext t; ring
  rw [he]
  exact h1.sub h2

theorem sphereLogPair8_lintegral :
    ∫⁻ p : Sphere8 × Sphere8, ENNReal.ofReal (Real.log (2/dist p.1 p.2))
        ∂(sphereProbability8.prod sphereProbability8) =
      ENNReal.ofReal ((1/2)*∫ t in Ioi 0, t⁻¹*(sphereGaussianBackground8 t-Real.exp (-(4*t)))) := by
  set μ := sphereProbability8.prod sphereProbability8 with hμ
  set F : ℝ → Sphere8 × Sphere8 → ℝ≥0∞ :=
    fun t p => ENNReal.ofReal (t⁻¹*(sphereGaussianKernel8 t p.1 p.2-Real.exp (-(4*t)))) with hF
  have hFm : Measurable (Function.uncurry F) := by
    simp only [hF, Function.uncurry_def, sphereGaussianKernel8]
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.mul
    · exact measurable_fst.inv
    · apply Measurable.sub
      · apply Real.measurable_exp.comp
        apply Measurable.neg
        apply measurable_fst.mul
        exact (continuous_dist.comp (continuous_fst.prodMk continuous_snd)).measurable.comp
          measurable_snd |>.pow_const 2
      · exact Real.measurable_exp.comp ((measurable_const.mul measurable_fst).neg)
  have hae : (fun p : Sphere8 × Sphere8 => ENNReal.ofReal (Real.log (2/dist p.1 p.2))) =ᵐ[μ]
      (fun p => ENNReal.ofReal (1/2) * ∫⁻ t in Ioi 0, F t p) := by
    have hnull : μ {p : Sphere8 × Sphere8 | p.1 = p.2} = 0 := sphereProbability8_prod_diagonal_null
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with p hp
    exact sphereLogPair8_ofReal_mellin hp
  have hmeas : Measurable (fun p : Sphere8 × Sphere8 => ∫⁻ t in Ioi 0, F t p) :=
    Measurable.lintegral_prod_left' (μ := volume.restrict (Ioi (0:ℝ))) hFm
  rw [lintegral_congr_ae hae, lintegral_const_mul _ hmeas,
    lintegral_lintegral_swap (f := fun (p : Sphere8 × Sphere8) (t : ℝ) => F t p)
      ((hFm.comp measurable_swap).aemeasurable)]
  have hin : ∀ t ∈ Ioi (0:ℝ), ∫⁻ p, F t p ∂μ =
      ENNReal.ofReal (t⁻¹*(sphereGaussianBackground8 t-Real.exp (-(4*t)))) := by
    intro t ht
    have ht0 : 0 ≤ t := (show (0:ℝ) < t from ht).le
    have hi : Integrable (fun p : Sphere8 × Sphere8 =>
        t⁻¹*(sphereGaussianKernel8 t p.1 p.2-Real.exp (-(4*t)))) μ :=
      ((sphereGaussianKernel8_pair_integrable ht0).sub (integrable_const _)).const_mul _
    have hnn : ∀ p : Sphere8 × Sphere8,
        0 ≤ t⁻¹*(sphereGaussianKernel8 t p.1 p.2-Real.exp (-(4*t))) := by
      intro p
      apply mul_nonneg (inv_nonneg.mpr ht0)
      have hd2 := sphere8_dist_le_two p.1 p.2
      have hd0 : 0 ≤ dist p.1 p.2 := dist_nonneg
      have hdd : (dist p.1 p.2)^2 ≤ 4 := by nlinarith
      have : t*(dist p.1 p.2)^2 ≤ 4*t := by nlinarith [mul_le_mul_of_nonneg_left hdd ht0]
      simp only [sphereGaussianKernel8]
      linarith [Real.exp_le_exp.mpr (neg_le_neg this)]
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnn),
      integral_const_mul, integral_sub (sphereGaussianKernel8_pair_integrable ht0)
        (integrable_const _)]
    simp [sphereGaussianBackground8, hμ]
  rw [setLIntegral_congr_fun measurableSet_Ioi hin,
    ← ofReal_integral_eq_lintegral_ofReal sphereGaussianBackground8_log4_integrable
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : (0:ℝ) < t := ht
        apply mul_nonneg (inv_nonneg.mpr ht0.le)
        linarith [sphereGaussianBackground8_ge_exp ht0.le]),
    ← ENNReal.ofReal_mul (by norm_num)]

theorem sphereLogPair8_nonneg (p : Sphere8 × Sphere8) : 0 ≤ Real.log (2/dist p.1 p.2) := by
  rcases eq_or_lt_of_le (dist_nonneg : 0 ≤ dist p.1 p.2) with h | h
  · rw [← h, div_zero, Real.log_zero]
  · apply Real.log_nonneg
    rw [le_div_iff₀ h]
    linarith [sphere8_dist_le_two p.1 p.2]

theorem sphereLogPair8_integrable :
    Integrable (fun p : Sphere8 × Sphere8 => Real.log (2/dist p.1 p.2))
      (sphereProbability8.prod sphereProbability8) := by
  have hm : Measurable (fun p : Sphere8 × Sphere8 => Real.log (2/dist p.1 p.2)) :=
    Real.measurable_log.comp (measurable_const.div
      (continuous_dist.comp (continuous_fst.prodMk continuous_snd)).measurable)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall sphereLogPair8_nonneg),
    sphereLogPair8_lintegral]
  exact ENNReal.ofReal_lt_top

/-- `W_log` is the actual double integral of `-log |x - y|`. -/
theorem sphereLogConst8_eq_pair_integral :
    sphereLogConst8 = ∫ p : Sphere8 × Sphere8, -Real.log (dist p.1 p.2)
      ∂(sphereProbability8.prod sphereProbability8) := by
  set μ := sphereProbability8.prod sphereProbability8 with hμ
  have hI4 := sphereGaussianBackground8_log4_integrable
  have hnnI : 0 ≤ (1/2)*∫ t in Ioi 0, t⁻¹*(sphereGaussianBackground8 t-Real.exp (-(4*t))) := by
    apply mul_nonneg (by norm_num)
    apply setIntegral_nonneg measurableSet_Ioi
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    apply mul_nonneg (inv_nonneg.mpr ht0.le)
    linarith [sphereGaussianBackground8_ge_exp ht0.le]
  have hlog2 : (∫ p, Real.log (2/dist p.1 p.2) ∂μ) =
      (1/2)*∫ t in Ioi 0, t⁻¹*(sphereGaussianBackground8 t-Real.exp (-(4*t))) := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall sphereLogPair8_nonneg)
        sphereLogPair8_integrable.aestronglyMeasurable, sphereLogPair8_lintegral,
      ENNReal.toReal_ofReal hnnI]
  have hae : (fun p : Sphere8 × Sphere8 => -Real.log (dist p.1 p.2)) =ᵐ[μ]
      (fun p => Real.log (2/dist p.1 p.2)-Real.log 2) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp sphereProbability8_prod_diagonal_null]
      with p hp
    have hd : 0 < dist p.1 p.2 := dist_pos.mpr hp
    rw [Real.log_div (by norm_num) hd.ne']
    ring
  have hc : (∫ _p : Sphere8 × Sphere8, Real.log 2 ∂μ) = Real.log 2 := by
    simp [hμ]
  rw [integral_congr_ae hae, integral_sub sphereLogPair8_integrable (integrable_const _), hlog2, hc]
  obtain ⟨h4i, h4v⟩ := frullani_exp (a := 4) (by norm_num)
  have hsplit : (∫ t in Ioi 0, t⁻¹*(sphereGaussianBackground8 t-Real.exp (-t))) =
      (∫ t in Ioi 0, t⁻¹*(sphereGaussianBackground8 t-Real.exp (-(4*t))))+
        ∫ t in Ioi 0, t⁻¹*(Real.exp (-(4*t))-Real.exp (-t)) := by
    rw [← integral_add hI4 h4i]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    ring
  unfold sphereLogConst8
  rw [hsplit, h4v, show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
  push_cast
  ring

/-- The universal sharp lower bound for the logarithmic energy on S⁸ in the form of the
conjecture: actual double integral of `-log |x - y|`, the `-(N/8) log N` term and the coefficient
`-60 Re ζ'(-3) + ⅝ log 2 - ⅛ log 105`, under the CKMRV Laplace–sine contract. -/
theorem sphere8_log_lower_conjecture_form (D : E8LaplaceSineData8) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Configuration N,
      -60*(deriv riemannZeta (-3)).re+(5/8)*Real.log 2-(1/8)*Real.log 105-η ≤
        (energyLog X-(∫ p : Sphere8 × Sphere8, -Real.log (dist p.1 p.2)
          ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2+(N:ℝ)/8*Real.log N)/(N:ℝ) := by
  rw [← sphereLogConst8_eq_pair_integral]
  exact sphere8_log_lower_explicit D

#print axioms frullani_exp_pair
#print axioms sphereLogPair8_ofReal_mellin
#print axioms sphereGaussianBackground8_ge_exp
#print axioms sphereGaussianBackground8_log4_integrable
#print axioms sphereLogPair8_lintegral
#print axioms sphereLogPair8_nonneg
#print axioms sphereLogPair8_integrable
#print axioms sphereLogConst8_eq_pair_integral
#print axioms sphere8_log_lower_conjecture_form

end SphericalRiesz
