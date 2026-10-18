import Riesz.E8EpsteinStrip8
import Riesz.SphereAtomless8

/-! The Mellin-defined constant `I_s` is the continuous Riesz `s`-energy of the actual uniform
probability on S⁸: for `0 < s < 8`, the chordal kernel `dist^(-s)` is integrable on
`S⁸ × S⁸` and `∫∫ dist(x,y)^(-s) dσ dσ = sphereRieszConst8 s`.

Proof by Tonelli in `ℝ≥0∞`: off the (null) diagonal each pair has the Gaussian Mellin
representation, the lintegrals are swapped, and the Gaussian background integral is finite. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SphericalRiesz

theorem sphereProbability8_prod_diagonal_null :
    (sphereProbability8.prod sphereProbability8) {p : Sphere8 × Sphere8 | p.1 = p.2} = 0 := by
  have hm : MeasurableSet {p : Sphere8 × Sphere8 | p.1 = p.2} :=
    (isClosed_diagonal (X := Sphere8)).measurableSet
  rw [Measure.measure_prod_null hm]
  refine Filter.Eventually.of_forall (fun x => ?_)
  have hs : (Prod.mk x ⁻¹' {p : Sphere8 × Sphere8 | p.1 = p.2}) = {x} := by
    ext y
    simp [eq_comm]
  simp only [Pi.zero_apply]
  rw [hs]
  exact measure_singleton x

theorem sphereRieszPair8_ofReal_mellin {s : ℝ} (hs : 0 < s) {x y : Sphere8} (hxy : x ≠ y) :
    ENNReal.ofReal ((dist x y)^(-s)) = ENNReal.ofReal (Real.Gamma (s/2))⁻¹ *
      ∫⁻ t in Ioi 0, ENNReal.ofReal (t^(s/2-1)*Real.exp (-(t*(dist x y)^2))) := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hΓ : 0 < Real.Gamma (s/2) := Real.Gamma_pos_of_pos (by positivity)
  have hint : IntegrableOn (fun t : ℝ => t^(s/2-1)*Real.exp (-(t*(dist x y)^2))) (Ioi 0) := by
    have h := gaussianPair_mellin_rpow_integrable hs hd
    apply h.congr_fun _ measurableSet_Ioi
    intro t _
    simp only [mul_comm t]
  have hval : (∫ t : ℝ in Ioi 0, t^(s/2-1)*Real.exp (-(t*(dist x y)^2))) =
      Real.Gamma (s/2)*(dist x y)^(-s) := by
    rw [← gaussianPair_mellin_rpow hs hd]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [mul_comm t]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le), hval,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hΓ.le), ← mul_assoc, inv_mul_cancel₀ hΓ.ne', one_mul]

theorem sphereRieszPair8_lintegral {s : ℝ} (hs : 0 < s) (hs8 : s < 8) :
    ∫⁻ p : Sphere8 × Sphere8, ENNReal.ofReal ((dist p.1 p.2)^(-s))
        ∂(sphereProbability8.prod sphereProbability8) =
      ENNReal.ofReal (sphereRieszConst8 s) := by
  set μ := sphereProbability8.prod sphereProbability8 with hμ
  have hΓ : 0 < Real.Gamma (s/2) := Real.Gamma_pos_of_pos (by positivity)
  set F : ℝ → Sphere8 × Sphere8 → ℝ≥0∞ :=
    fun t p => ENNReal.ofReal (t^(s/2-1)*Real.exp (-(t*(dist p.1 p.2)^2))) with hF
  have hFm : Measurable (Function.uncurry F) := by
    simp only [hF, Function.uncurry_def]
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.mul
    · exact measurable_fst.pow_const _
    · apply Real.measurable_exp.comp
      apply Measurable.neg
      apply measurable_fst.mul
      exact (continuous_dist.comp (continuous_fst.prodMk continuous_snd)).measurable.comp
        measurable_snd |>.pow_const 2
  have hae : (fun p : Sphere8 × Sphere8 => ENNReal.ofReal ((dist p.1 p.2)^(-s))) =ᵐ[μ]
      (fun p => ENNReal.ofReal (Real.Gamma (s/2))⁻¹ * ∫⁻ t in Ioi 0, F t p) := by
    have hnull : μ {p : Sphere8 × Sphere8 | p.1 = p.2} = 0 := sphereProbability8_prod_diagonal_null
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with p hp
    exact sphereRieszPair8_ofReal_mellin hs hp
  have hmeas : Measurable (fun p : Sphere8 × Sphere8 => ∫⁻ t in Ioi 0, F t p) :=
    Measurable.lintegral_prod_left' (μ := volume.restrict (Ioi (0:ℝ))) hFm
  rw [lintegral_congr_ae hae, lintegral_const_mul _ hmeas,
    lintegral_lintegral_swap (f := fun (p : Sphere8 × Sphere8) (t : ℝ) => F t p)
      ((hFm.comp measurable_swap).aemeasurable)]
  have hin : ∀ t ∈ Ioi (0:ℝ), ∫⁻ p, F t p ∂μ =
      ENNReal.ofReal (t^(s/2-1)*sphereGaussianBackground8 t) := by
    intro t ht
    have ht0 : 0 ≤ t := (show (0:ℝ) < t from ht).le
    have hi : Integrable (fun p : Sphere8 × Sphere8 =>
        t^(s/2-1)*Real.exp (-(t*(dist p.1 p.2)^2))) μ :=
      (sphereGaussianKernel8_pair_integrable ht0).const_mul _
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun p =>
        mul_nonneg (Real.rpow_nonneg ht0 _) (Real.exp_pos _).le)), integral_const_mul]
    rfl
  rw [setLIntegral_congr_fun measurableSet_Ioi hin,
    ← ofReal_integral_eq_lintegral_ofReal
      (sphereGaussianBackground8_weighted_integrable_rpow hs hs8)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _)
          (sphereGaussianBackground8_nonneg t)),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hΓ.le)]
  rfl

theorem sphereRieszPair8_integrable {s : ℝ} (hs : 0 < s) (hs8 : s < 8) :
    Integrable (fun p : Sphere8 × Sphere8 => (dist p.1 p.2)^(-s))
      (sphereProbability8.prod sphereProbability8) := by
  have hm : Measurable (fun p : Sphere8 × Sphere8 => (dist p.1 p.2)^(-s)) :=
    (continuous_dist.comp (continuous_fst.prodMk continuous_snd)).measurable.pow_const _
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun p =>
      Real.rpow_nonneg dist_nonneg _)),
    sphereRieszPair8_lintegral hs hs8]
  exact ENNReal.ofReal_lt_top

/-- `I_s` is the actual continuous Riesz `s`-energy of the uniform probability on S⁸. -/
theorem sphereRieszConst8_eq_pair_integral {s : ℝ} (hs : 0 < s) (hs8 : s < 8) :
    sphereRieszConst8 s = ∫ p : Sphere8 × Sphere8, (dist p.1 p.2)^(-s)
      ∂(sphereProbability8.prod sphereProbability8) := by
  have hnn : 0 ≤ sphereRieszConst8 s := by
    unfold sphereRieszConst8
    apply mul_nonneg (inv_nonneg.mpr (Real.Gamma_pos_of_pos (by positivity)).le)
    apply setIntegral_nonneg measurableSet_Ioi
    intro t ht
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (sphereGaussianBackground8_nonneg t)
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun p =>
      Real.rpow_nonneg dist_nonneg _))
      (sphereRieszPair8_integrable hs hs8).aestronglyMeasurable,
    sphereRieszPair8_lintegral hs hs8, ENNReal.toReal_ofReal hnn]

/-- The all-exponent sharp lower bound in the form of the conjecture: the continuous constant is the
actual double integral `∫∫ |x-y|^(-s) dσ dσ` and the coefficient is the E8 Epstein value
(`0 < s < 8`, `s ≠ 2`), under the CKMRV Laplace–sine contract. -/
theorem sphere8_riesz_sharp_lower_conjecture_form (D : E8LaplaceSineData8)
    {s : ℝ} (hs : 0 < s) (hs8 : s < 8) (hs2 : s ≠ 2) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Configuration N,
      (sphereArea8.real univ)^(-(s/8)) * (e8EpsteinCandidate ((s/2:ℝ):ℂ)).re-η ≤
        (energyRpow s X-(∫ p : Sphere8 × Sphere8, (dist p.1 p.2)^(-s)
          ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2)/(N:ℝ)^(1+s/8) := by
  intro η hη
  obtain ⟨N₀, h⟩ := sphere8_riesz_sharp_lower_epstein_of_laplaceSineData D hs hs8 hs2 η hη
  refine ⟨N₀, fun N hN X => ?_⟩
  have := h N hN X
  rwa [normalizedEnergyRpow, sphereRieszConst8_eq_pair_integral hs hs8] at this

#print axioms sphere8_riesz_sharp_lower_conjecture_form
#print axioms sphereProbability8_prod_diagonal_null
#print axioms sphereRieszPair8_ofReal_mellin
#print axioms sphereRieszPair8_lintegral
#print axioms sphereRieszPair8_integrable
#print axioms sphereRieszConst8_eq_pair_integral

end SphericalRiesz
