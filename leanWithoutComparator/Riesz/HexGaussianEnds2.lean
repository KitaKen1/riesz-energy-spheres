import Riesz.SphereRieszLower2
import Riesz.CellFirstMoment
import Riesz.ResidualJointSelection
import Riesz.NodeSeparation
import Riesz.EqualAreaHex2
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Gaussian upper tools and Gaussian ends on S² (stage S2-3).

Dimension-2 port of `SphereGaussianUpper24` and `LeechGaussianEnds24`, for the unit sphere
S² ⊂ ℝ³ and the triangular lattice of covolume one.

* Background of the Gaussian kernel on S²: `B(t) ≥ 1/(4t) - 1/(16t²)`, so at the density scale
  `sphereGaussianScale2 N α = α N/4` the centred profile is at most the full profile minus
  `α⁻¹ + 1`, up to an error that tends to zero.
* Restricted probabilities of regions of S² and the short-range kernel
  `T_{c,p}(x, y) = ∫_1^∞ α^p K_{cα}(x, y) dα`; its rows are integrable for `p < 0`, with the bound
  `(1/4)/c/(-p)`.  The admissible range is `-1 ≤ p < 0` (in dimension 24 it is `-1 ≤ p < 11`).
* Reverse Fatou for weighted centred profiles, selection of points in cells with small
  short-range cost (single cells, cross terms, joint bounds).
* Gaussian ends: bump fields in ℝ³, the small end, the theta tail of the triangular lattice with
  rate `2π/√3`, separated cross rows, pointwise domination of the Gaussian by the short-range
  kernel for `-1 < p ≤ 0` (constant 2), the large-scale bound with exponent `s/4 - 3/2`, and the
  integrable majorant used by the bridge from the Gaussian window to the Riesz energy.

The parts are kept in their own sections. -/

section

/-! # Gaussian upper tools on `S²`: background, short-range kernel, reverse Fatou (stage S2-3)

Dimension-2 port of `SphereGaussianUpper24`: the unit sphere `S² ⊂ ℝ³` with its uniform probability
measure `σ`, the Gaussian kernel `K_t(x, y) = exp(-t |x - y|²)` and the triangular lattice of
covolume one in place of the Leech lattice.

* Background.  On `S²` the background is `B(t) = (1/2) ∫_0^2 exp(-2tv) dv`.  The minorant
  `(1 - v/2) exp(-2tv)` of the integrand gives `B(t) ≥ 1/(4t) - 1/(16 t²)`; at the density scale
  `sphereGaussianScale2 N α = α N/4` this is `N B ≥ α⁻¹ - (1/4)/(α · scale)`, so the centred
  Gaussian profile is at most the full profile minus `α⁻¹ + 1`, up to an error that tends to `0`.
* Restricted probabilities `σ(A)⁻¹ σ|_A` of regions of `S²`.
* Short-range kernel `T_{c,p}(x, y) = ∫_1^∞ α^p K_{cα}(x, y) dα`, with `T_{c,p}(x, x) = 0` for
  `-1 ≤ p`.  Its rows against `σ` are integrable for `p < 0` (the exponent `d/2 - 1` of the general
  dimension is `0`), with `∫ T_{c,p}(x, y) dσ(y) ≤ (1/4)/c/(-p)`, because `B(t) ≤ 1/(4t)`.  The
  admissible range is `-1 ≤ p < 0`.
* Reverse Fatou.  An integrable majorant of the weighted centred profiles and an upper bound of the
  full Gaussian sums by the theta function `Θ` of the triangular lattice at every scale give
  `limsup (E_s - I_s N²)/N^(1+s/2) ≤ C_s`, `C_s = sphereRieszCoefficient2 s`, for `0 < s < 2`.
* Cell selections.  One point in each cell of an equal-mass family, avoiding a null set, with the
  short-range pair cost and the cross cost against given points bounded by their means; the tails
  `∫_R^∞ α^(s/2-1) K` of all residual pairs are bounded by `(8/(2-s)) R^(-(2-s)/4)` per point. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace SphericalRiesz

/-! ## The lower bound of the Gaussian background

In dimension `d` the height integrand carries the factor `(2-v)^(d/2-1)`, bounded below by
Bernoulli's inequality; the resulting minorant is nonpositive for `v ≥ 2`.  For `d = 2` the factor
is `1` and that minorant is the positive function `exp(-2tv)`, so the minorant
`(1 - v/2) exp(-2tv)` is used instead: it is below the integrand on `[0, 2]` and nonpositive
beyond.  Hence `B(t) ≥ (1/2) ∫_0^∞ (1 - v/2) exp(-2tv) dv = 1/(4t) - 1/(16 t²)`. -/

/-- On `[0, 2]` the height integrand `exp(-2tv)` dominates `(1 - v/2) exp(-2tv)`. -/
theorem polePolynomialGaussian2_ge_first (t : ℝ) {v : ℝ} (hv : v ∈ Icc (0:ℝ) 2) :
    Real.exp (-(2*t*v))-(1/2)*(v*Real.exp (-(2*t*v))) ≤ polePolynomialGaussian2 t v := by
  have hw : 0 ≤ v*Real.exp (-(2*t*v)) := mul_nonneg hv.1 (Real.exp_pos _).le
  unfold polePolynomialGaussian2
  linarith

/-- `∫_0^∞ v exp(-2tv) dv = 1/(4t²)`: the Gamma moment of order `d/2 = 1`. -/
theorem firstGaussian2_integral {t : ℝ} (ht : 0 < t) :
    (∫ v : ℝ in Ioi 0, v*Real.exp (-(2*t*v))) = 1/(4*t^2) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 2) (r := 2*t) (by norm_num) (by positivity)
  have h' : (∫ v : ℝ in Ioi 0, v*Real.exp (-(2*t*v))) = (1/(2*t))^2 := by
    simpa only [show (2:ℝ)-1 = 1 by norm_num, Real.rpow_one, Real.rpow_ofNat, Real.Gamma_two,
      mul_one] using h
  rw [h']
  ring

theorem firstGaussian2_integrable {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun v : ℝ => v*Real.exp (-(2*t*v))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [firstGaussian2_integral ht]
  exact (by positivity : (0:ℝ) < 1/(4*t^2)).ne'

/-- Lower asymptotic of the Gaussian background of `S²`: `B(t) ≥ 1/(4t) - 1/(16 t²)`. -/
theorem sphereGaussianBackground2_lower {t : ℝ} (ht : 0 < t) :
    (1/4:ℝ)/t-(1/16:ℝ)/t^2 ≤ sphereGaussianBackground2 t := by
  set h : ℝ → ℝ := fun v =>
    Real.exp (-(2*t*v))-(1/2)*(v*Real.exp (-(2*t*v))) with hh
  have hi : IntegrableOn h (Ioi 0) :=
    (zerothGaussian2_integrable ht).sub ((firstGaussian2_integrable ht).const_mul (1/2))
  have hint : (∫ v in Ioi (0:ℝ), h v) = 1/(2*t)-1/(8*t^2) := by
    rw [hh, integral_sub (zerothGaussian2_integrable ht)
      ((firstGaussian2_integrable ht).const_mul (1/2)), integral_const_mul,
      zerothGaussian2_integral ht, firstGaussian2_integral ht]
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
    simp only [hh]
    have he : Real.exp (-(2*t*v))-(1/2)*(v*Real.exp (-(2*t*v))) =
        -((1/2)*(v-2)*Real.exp (-(2*t*v))) := by ring
    rw [he, neg_nonpos]
    have hvlin : 0 ≤ v-2 := by linarith
    positivity
  have hlow : 1/(2*t)-1/(8*t^2) ≤ ∫ v in Ioo (0:ℝ) 2, h v := by linarith
  have hg : IntegrableOn (polePolynomialGaussian2 t) (Ioo (0:ℝ) 2) :=
    (polePolynomialGaussian2_continuous t).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hcmp : (∫ v in Ioo (0:ℝ) 2, h v) ≤
      ∫ v in Ioo (0:ℝ) 2, polePolynomialGaussian2 t v :=
    setIntegral_mono_on (hi.mono_set Ioo_subset_Ioi_self) hg measurableSet_Ioo
      (fun v hv => polePolynomialGaussian2_ge_first t ⟨hv.1.le, hv.2.le⟩)
  rw [sphereGaussianBackground2_polynomial_set ht.le]
  have hfin : (1/4:ℝ)/t-(1/16:ℝ)/t^2 = (1/2:ℝ)*(1/(2*t)-1/(8*t^2)) := by ring
  rw [hfin]
  exact mul_le_mul_of_nonneg_left (hlow.trans hcmp) (by norm_num)

/-- In dimension two the Gaussian scale is `α N/4`: it is `π α N/A` with the area `A = 4π` of
`S²` (the dimension-24 chain uses the twelfth power of the scale here). -/
theorem sphereGaussianScale2_eq_quarter (N : ℕ) (α : ℝ) :
    sphereGaussianScale2 N α = α*(N:ℝ)/4 := by
  have hpi : Real.pi*Real.pi⁻¹ = 1 := mul_inv_cancel₀ Real.pi_pos.ne'
  rw [sphereGaussianScale2_eq, sphereArea2_univ_real]
  linear_combination (α*(N:ℝ)/4)*hpi

/-- Density-scaled form: `N·B(cα) ≥ α⁻¹ - (1/4)/(α cα)`. -/
theorem sphereGaussianBackground2_scaled_lower {N : ℕ} (hN : 0 < N) {α : ℝ} (hα : 0 < α) :
    α⁻¹-(1/4)/(α*sphereGaussianScale2 N α) ≤
      (N:ℝ)*sphereGaussianBackground2 (sphereGaussianScale2 N α) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hs := sphereGaussianScale2_pos hN hα
  have hb := mul_le_mul_of_nonneg_left (sphereGaussianBackground2_lower hs) hNR.le
  have hN1 : (N:ℝ)*(N:ℝ)⁻¹ = 1 := mul_inv_cancel₀ hNR.ne'
  have he : (N:ℝ)*((1/4:ℝ)/sphereGaussianScale2 N α-(1/16:ℝ)/(sphereGaussianScale2 N α)^2) =
      α⁻¹-(1/4)/(α*sphereGaussianScale2 N α) := by
    rw [sphereGaussianScale2_eq_quarter]
    linear_combination (α⁻¹-α⁻¹^2*(N:ℝ)⁻¹)*hN1
  linarith

theorem sphereGaussianCenteredScaled2_le_full {N : ℕ} (hN : 0 < N) {α : ℝ} (hα : 0 < α)
    (X : (ConfigurationD 2) N) :
    sphereGaussianCenteredScaled2 α X ≤
      sphereGaussianFullScaled2 α X-α⁻¹-1+(1/4)/(α*sphereGaussianScale2 N α) := by
  have h := sphereGaussianBackground2_scaled_lower hN hα
  unfold sphereGaussianCenteredScaled2 sphereGaussianFullScaled2
  linarith

theorem sphereGaussianScale2_tendsto {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) {α : ℝ}
    (hα : 0 < α) : Tendsto (fun k => sphereGaussianScale2 (N k) α) atTop atTop := by
  have hA : 0 < (sphereAreaD 2).real univ := sphereAreaD_univ_pos 2
  have h1 : Tendsto (fun k => ((N k:ℕ):ℝ)/(sphereAreaD 2).real univ) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp hN).atTop_div_const hA
  have h2 := (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1)).comp h1
  unfold sphereGaussianScale2
  exact h2.const_mul_atTop (by positivity)

/-! ## The restricted probability of a region -/

/-- The uniform probability of `S²` conditioned on the region `A`. -/
def sphereRestrictedProbability2 (A : Set (SphereD 2)) : Measure (SphereD 2) :=
  ((sphereProbabilityD 2) A)⁻¹ • (sphereProbabilityD 2).restrict A

theorem sphereRestrictedProbability2_probability (A : Set (SphereD 2))
    (hA : (sphereProbabilityD 2) A ≠ 0) :
    IsProbabilityMeasure (sphereRestrictedProbability2 A) := by
  refine ⟨?_⟩
  simp only [sphereRestrictedProbability2,Measure.smul_apply,smul_eq_mul,
    Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hA (measure_ne_top _ _)

instance sphereRestrictedProbability2_finite (A : Set (SphereD 2)) :
    IsFiniteMeasure (sphereRestrictedProbability2 A) := by
  by_cases hA : (sphereProbabilityD 2) A = 0
  · refine ⟨?_⟩
    simp [sphereRestrictedProbability2, Measure.smul_apply, hA]
  · let := sphereRestrictedProbability2_probability A hA
    infer_instance

instance sphereRestrictedProbability2_nullSingleton (A : Set (SphereD 2)) :
    NullSingletonClass (sphereRestrictedProbability2 A) := by
  refine ⟨fun p => ?_⟩
  simp [sphereRestrictedProbability2,Measure.smul_apply]

theorem sphereRestrictedProbability2_compl (A : Set (SphereD 2)) (hA : MeasurableSet A) :
    sphereRestrictedProbability2 A Aᶜ = 0 := by
  simp [sphereRestrictedProbability2,Measure.smul_apply,Measure.restrict_apply hA.compl]

/-! ## The short-range kernel and its rows -/

/-- The weighted short-range kernel `∫_1^∞ α^p exp(-c α |x - y|²) dα`. -/
def shortRangeKernel2 (c p : ℝ) (x y : (SphereD 2)) : ℝ :=
  ∫ α in Ioi (1:ℝ), α^p*sphereGaussianKernel2 (c*α) x y

theorem shortRangeKernel2_symm (c p : ℝ) (x y : (SphereD 2)) :
    shortRangeKernel2 c p x y = shortRangeKernel2 c p y x := by
  unfold shortRangeKernel2 sphereGaussianKernel2
  simp_rw [dist_comm x y]

theorem shortRangeKernel2_nonneg (c p : ℝ) (x y : (SphereD 2)) : 0 ≤ shortRangeKernel2 c p x y :=
  setIntegral_nonneg measurableSet_Ioi fun _α hα =>
    mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (le_of_lt hα)) _)
      (sphereGaussianKernel2_nonneg _ _ _)

theorem shortRangeKernel2_self (c : ℝ) {p : ℝ} (hp : -1 ≤ p) (x : (SphereD 2)) :
    shortRangeKernel2 c p x x = 0 := by
  unfold shortRangeKernel2
  simp only [sphereGaussianKernel2_self, mul_one]
  apply integral_undef
  intro h
  have := (integrableOn_Ioi_rpow_iff (s := p) zero_lt_one).mp h
  linarith

theorem ofReal_setIntegral_Ioi_le_lintegral2 {f : ℝ → ℝ} {a : ℝ} (hf : ∀ α ∈ Ioi a, 0 ≤ f α) :
    ENNReal.ofReal (∫ α in Ioi a, f α) ≤ ∫⁻ α in Ioi a, ENNReal.ofReal (f α) := by
  by_cases hi : IntegrableOn f (Ioi a)
  · rw [ofReal_integral_eq_lintegral_ofReal hi]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
    exact hf α hα
  · rw [integral_undef hi, ENNReal.ofReal_zero]
    exact zero_le

theorem shortRangeKernel2_measurable (c p : ℝ) :
    StronglyMeasurable (fun q : (SphereD 2) × (SphereD 2) => shortRangeKernel2 c p q.1 q.2) := by
  have hf : StronglyMeasurable (fun z : ((SphereD 2) × (SphereD 2)) × ℝ =>
      z.2^p*sphereGaussianKernel2 (c*z.2) z.1.1 z.1.2) := by
    apply Measurable.stronglyMeasurable
    unfold sphereGaussianKernel2
    apply Measurable.mul (measurable_snd.pow_const p)
    apply Real.measurable_exp.comp
    apply Measurable.neg
    apply Measurable.mul (measurable_const.mul measurable_snd)
    exact ((continuous_dist.comp (continuous_fst.comp continuous_fst |>.prodMk
      (continuous_snd.comp continuous_fst))).measurable).pow_const 2
  exact hf.integral_prod_right' (ν := volume.restrict (Ioi (1:ℝ)))

theorem shortRangeKernel2_row_measurable (c p : ℝ) (x : (SphereD 2)) :
    StronglyMeasurable (shortRangeKernel2 c p x) := by
  have hf : StronglyMeasurable (fun z : (SphereD 2) × ℝ =>
      z.2^p*sphereGaussianKernel2 (c*z.2) x z.1) := by
    apply Measurable.stronglyMeasurable
    unfold sphereGaussianKernel2
    apply Measurable.mul (measurable_snd.pow_const p)
    apply Real.measurable_exp.comp
    apply Measurable.neg
    apply Measurable.mul (measurable_const.mul measurable_snd)
    exact ((continuous_dist.comp (continuous_const.prodMk continuous_fst)).measurable).pow_const 2
  exact hf.integral_prod_right' (ν := volume.restrict (Ioi (1:ℝ)))

/-- Tonelli bound of a row against the actual uniform probability. -/
theorem shortRangeKernel2_row_lintegral_le {c p : ℝ} (hc : 0 < c) (hp : p < 0) (x : (SphereD 2)) :
    ∫⁻ y, ENNReal.ofReal (shortRangeKernel2 c p x y) ∂(sphereProbabilityD 2) ≤
      ENNReal.ofReal ((1/4)/c/(-p)) := by
  set F : ℝ → (SphereD 2) → ℝ≥0∞ := fun α y => ENNReal.ofReal (α^p*sphereGaussianKernel2 (c*α) x y)
    with hF
  have hFm : Measurable (Function.uncurry F) := by
    simp only [hF, Function.uncurry_def]
    apply ENNReal.measurable_ofReal.comp
    unfold sphereGaussianKernel2
    apply Measurable.mul (measurable_fst.pow_const p)
    apply Real.measurable_exp.comp
    apply Measurable.neg
    apply Measurable.mul (measurable_const.mul measurable_fst)
    exact ((continuous_dist.comp (continuous_const.prodMk continuous_snd)).measurable).pow_const 2
  have h1 : ∀ y, ENNReal.ofReal (shortRangeKernel2 c p x y) ≤ ∫⁻ α in Ioi 1, F α y := by
    intro y
    apply ofReal_setIntegral_Ioi_le_lintegral2
    intro α hα
    exact mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (le_of_lt hα)) _)
      (sphereGaussianKernel2_nonneg _ _ _)
  have h2 : ∫⁻ y, ∫⁻ α in Ioi 1, F α y ∂volume ∂(sphereProbabilityD 2) =
      ∫⁻ α in Ioi 1, ∫⁻ y, F α y ∂(sphereProbabilityD 2) :=
    lintegral_lintegral_swap ((hFm.comp measurable_swap).aemeasurable)
  have h3 : ∀ α ∈ Ioi (1:ℝ), ∫⁻ y, F α y ∂(sphereProbabilityD 2) =
      ENNReal.ofReal (α^p*sphereGaussianBackground2 (c*α)) := by
    intro α hα
    have hα0 : 0 < α := zero_lt_one.trans hα
    have ht : 0 ≤ c*α := (mul_pos hc hα0).le
    have hi : Integrable (fun y => α^p*sphereGaussianKernel2 (c*α) x y) (sphereProbabilityD 2) :=
      (sphereGaussianKernel2_integrable ht x).const_mul _
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun y =>
      mul_nonneg (Real.rpow_nonneg hα0.le _) (sphereGaussianKernel2_nonneg _ _ _)),
      integral_const_mul, sphereGaussianBackground2_eq_potential ht x]
    rfl
  have h4 : ∀ α ∈ Ioi (1:ℝ), ENNReal.ofReal (α^p*sphereGaussianBackground2 (c*α)) ≤
      ENNReal.ofReal ((1/4)/c*α^(p-1)) := by
    intro α hα
    have hα0 : 0 < α := zero_lt_one.trans hα
    apply ENNReal.ofReal_le_ofReal
    have hB := sphereGaussianBackground2_decay (mul_pos hc hα0)
    have he : (1/4)/c*α^(p-1) = α^p*((1/4:ℝ)/(c*α)) := by
      rw [Real.rpow_sub_one hα0.ne']
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hB (Real.rpow_nonneg hα0.le _)
  have hint : IntegrableOn (fun α : ℝ => (1/4)/c*α^(p-1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
  have hval : ∫ α in Ioi (1:ℝ), (1/4)/c*α^(p-1) = (1/4)/c/(-p) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow,
      show p-1+1 = p by ring]
    ring
  calc ∫⁻ y, ENNReal.ofReal (shortRangeKernel2 c p x y) ∂(sphereProbabilityD 2)
      ≤ ∫⁻ y, ∫⁻ α in Ioi 1, F α y ∂volume ∂(sphereProbabilityD 2) := lintegral_mono h1
    _ = ∫⁻ α in Ioi 1, ∫⁻ y, F α y ∂(sphereProbabilityD 2) := h2
    _ = ∫⁻ α in Ioi 1, ENNReal.ofReal (α^p*sphereGaussianBackground2 (c*α)) :=
        setLIntegral_congr_fun measurableSet_Ioi h3
    _ ≤ ∫⁻ α in Ioi 1, ENNReal.ofReal ((1/4)/c*α^(p-1)) :=
        setLIntegral_mono (by fun_prop) h4
    _ = ENNReal.ofReal ((1/4)/c/(-p)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint, hval]
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
        exact mul_nonneg (by positivity) (Real.rpow_nonneg (zero_le_one.trans (le_of_lt hα)) _)

theorem shortRangeKernel2_row_integrable {c p : ℝ} (hc : 0 < c) (hp : p < 0) (x : (SphereD 2)) :
    Integrable (shortRangeKernel2 c p x) (sphereProbabilityD 2) := by
  refine ⟨(shortRangeKernel2_row_measurable c p x).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have he : ∀ y, ‖shortRangeKernel2 c p x y‖ₑ = ENNReal.ofReal (shortRangeKernel2 c p x y) :=
    fun y => Real.enorm_eq_ofReal (shortRangeKernel2_nonneg c p x y)
  simp_rw [he]
  exact (shortRangeKernel2_row_lintegral_le hc hp x).trans_lt ENNReal.ofReal_lt_top

theorem shortRangeKernel2_row_integral_le {c p : ℝ} (hc : 0 < c) (hp : p < 0) (x : (SphereD 2)) :
    ∫ y, shortRangeKernel2 c p x y ∂(sphereProbabilityD 2) ≤ (1/4)/c/(-p) := by
  have h := shortRangeKernel2_row_lintegral_le hc hp x
  rw [← ofReal_integral_eq_lintegral_ofReal (shortRangeKernel2_row_integrable hc hp x)
    (Eventually.of_forall fun y => shortRangeKernel2_nonneg c p x y)] at h
  have h3 : 0 ≤ (1/4)/c/(-p) := by
    have : 0 < -p := by linarith
    positivity
  exact (ENNReal.ofReal_le_ofReal_iff h3).mp h

theorem shortRangeKernel2_restricted_integrable {c p : ℝ} (hc : 0 < c) (hp : p < 0)
    (A : Set (SphereD 2)) (x : (SphereD 2)) :
    Integrable (shortRangeKernel2 c p x) (sphereRestrictedProbability2 A) := by
  simpa only [sphereRestrictedProbability2, Measure.restrict_apply_univ] using
    (shortRangeKernel2_row_integrable hc hp x).restrict (s := A) |>.to_average

theorem shortRangeKernel2_restricted_row_le {c p : ℝ} (hc : 0 < c) (hp : p < 0)
    (A : Set (SphereD 2)) (x : (SphereD 2)) :
    residualRowPotential (sphereRestrictedProbability2 A) (shortRangeKernel2 c p) x ≤
      (((sphereProbabilityD 2) A)⁻¹).toReal*((1/4)/c/(-p)) := by
  unfold residualRowPotential sphereRestrictedProbability2
  rw [integral_smul_measure, smul_eq_mul]
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  calc ∫ y in A, shortRangeKernel2 c p x y ∂(sphereProbabilityD 2)
      ≤ ∫ y, shortRangeKernel2 c p x y ∂(sphereProbabilityD 2) :=
        setIntegral_le_integral (shortRangeKernel2_row_integrable hc hp x)
          (Eventually.of_forall fun y => shortRangeKernel2_nonneg c p x y)
    _ ≤ _ := shortRangeKernel2_row_integral_le hc hp x

theorem shortRangeKernel2_restricted_rowPotential_integrable {c p : ℝ} (hc : 0 < c) (hp : p < 0)
    (A : Set (SphereD 2)) (hA : (sphereProbabilityD 2) A ≠ 0) :
    Integrable (residualRowPotential (sphereRestrictedProbability2 A) (shortRangeKernel2 c p))
      (sphereRestrictedProbability2 A) := by
  let := sphereRestrictedProbability2_probability A hA
  have hm : StronglyMeasurable
      (residualRowPotential (sphereRestrictedProbability2 A) (shortRangeKernel2 c p)) :=
    (shortRangeKernel2_measurable c p).integral_prod_right'
      (ν := sphereRestrictedProbability2 A)
  apply Integrable.of_bound hm.aestronglyMeasurable
    ((((sphereProbabilityD 2) A)⁻¹).toReal*((1/4)/c/(-p)))
  refine Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (residualRowPotential_nonneg _
    (shortRangeKernel2_nonneg c p) x)]
  exact shortRangeKernel2_restricted_row_le hc hp A x

/-- Every short-range tail is dominated by the weighted short-range kernel. -/
theorem tail_le_shortRangeKernel2 {c s γ R : ℝ} (hc : 0 < c) (hs : 0 < s) (hγ : 0 ≤ γ)
    (hR : 1 ≤ R) {x y : (SphereD 2)} (hxy : x ≠ y) :
    ∫ α in Ioi R, α^(s/2-1)*sphereGaussianKernel2 (c*α) x y ≤
      R^(-γ)*shortRangeKernel2 c (s/2-1+γ) x y := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hb : 0 < c*dist x y^2 := by positivity
  have hiγ : IntegrableOn (fun α : ℝ => α^(s/2-1+γ)*sphereGaussianKernel2 (c*α) x y) (Ioi 1) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := s/2-1+γ) (p := 1) (b := c*dist x y^2)
      (by linarith) one_pos hb
    apply (h.mono_set (Ioi_subset_Ioi zero_le_one)).congr_fun _ measurableSet_Ioi
    intro α _
    simp only [sphereGaussianKernel2, Real.rpow_one]
    congr 2
    ring
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hRγ : 0 ≤ R^(-γ) := (Real.rpow_pos_of_pos hR0 _).le
  have hpt : ∀ α ∈ Ioi R, α^(s/2-1)*sphereGaussianKernel2 (c*α) x y ≤
      R^(-γ)*(α^(s/2-1+γ)*sphereGaussianKernel2 (c*α) x y) := by
    intro α hα
    have hα0 : 0 < α := hR0.trans hα
    have hk := sphereGaussianKernel2_nonneg (c*α) x y
    have h1 : 1 ≤ R^(-γ)*α^γ := by
      rw [Real.rpow_neg hR0.le, inv_mul_eq_div, one_le_div (Real.rpow_pos_of_pos hR0 _)]
      exact Real.rpow_le_rpow hR0.le (le_of_lt hα) hγ
    have hpow : α^(s/2-1) ≤ R^(-γ)*α^(s/2-1+γ) := by
      rw [Real.rpow_add hα0]
      calc α^(s/2-1) = α^(s/2-1)*1 := (mul_one _).symm
        _ ≤ α^(s/2-1)*(R^(-γ)*α^γ) := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hα0.le _)
        _ = R^(-γ)*(α^(s/2-1)*α^γ) := by ring
    calc α^(s/2-1)*sphereGaussianKernel2 (c*α) x y
        ≤ R^(-γ)*α^(s/2-1+γ)*sphereGaussianKernel2 (c*α) x y :=
          mul_le_mul_of_nonneg_right hpow hk
      _ = _ := by ring
  have hRi : IntegrableOn (fun α : ℝ => R^(-γ)*(α^(s/2-1+γ)*sphereGaussianKernel2 (c*α) x y))
      (Ioi R) := (hiγ.mono_set (Ioi_subset_Ioi hR)).const_mul _
  have hLi : IntegrableOn (fun α : ℝ => α^(s/2-1)*sphereGaussianKernel2 (c*α) x y) (Ioi R) := by
    apply hRi.mono' (by
      apply Measurable.aestronglyMeasurable
      unfold sphereGaussianKernel2
      fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
    have hα0 : 0 < α := hR0.trans hα
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hα0.le _)
      (sphereGaussianKernel2_nonneg _ _ _))]
    exact hpt α hα
  unfold shortRangeKernel2
  rw [← integral_const_mul]
  calc ∫ α in Ioi R, α^(s/2-1)*sphereGaussianKernel2 (c*α) x y
      ≤ ∫ α in Ioi R, R^(-γ)*(α^(s/2-1+γ)*sphereGaussianKernel2 (c*α) x y) :=
        setIntegral_mono_on hLi hRi measurableSet_Ioi hpt
    _ ≤ ∫ α in Ioi 1, R^(-γ)*(α^(s/2-1+γ)*sphereGaussianKernel2 (c*α) x y) := by
        apply setIntegral_mono_set (hiγ.const_mul _)
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
          exact mul_nonneg hRγ (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (le_of_lt hα)) _)
            (sphereGaussianKernel2_nonneg _ _ _))
        · exact (Ioi_subset_Ioi hR).eventuallyLE

/-! ## The reverse-Fatou transfer, for `0 < s < 2` -/

theorem integral_ge_of_eventual_upper_profile2 {α : Type*} [MeasurableSpace α]
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

theorem sphereGaussianSequence_energy_upper_of_profile_rpow2 {s : ℝ} (hs : 0 < s) (hs2 : s < 2)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, (ConfigurationD 2) (N k))
    {g G : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0)) (hG : IntegrableOn G (Ioi 0))
    (hG0 : ∀ α : ℝ, 0 < α → 0 ≤ G α)
    (hdom : ∀ k, ∀ α : ℝ, 0 < α → α^(s/2-1)*sphereGaussianCenteredScaled2 α (X k) ≤ G α)
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      α^(s/2-1)*sphereGaussianCenteredScaled2 α (X k) ≤ g α+ε)
    {C : ℝ} (hC : ∀ k, C ≤ normalizedEnergyRpow2 s (X k)) :
    C ≤ (Real.pi^(s/2)*((sphereAreaD 2).real univ)^(-(s/2))/Real.Gamma (s/2))*
      ∫ α : ℝ in Ioi 0, g α := by
  have hA : 0 < (sphereAreaD 2).real univ := sphereAreaD_univ_pos 2
  have hΓ : 0 < Real.Gamma (s/2) := Real.Gamma_pos_of_pos (by positivity)
  set c := Real.pi^(s/2)*((sphereAreaD 2).real univ)^(-(s/2))/Real.Gamma (s/2) with hcdef
  have hc : 0 < c := by
    have h1 : 0 < Real.pi^(s/2) := Real.rpow_pos_of_pos Real.pi_pos _
    have h2 : 0 < ((sphereAreaD 2).real univ)^(-(s/2)) := Real.rpow_pos_of_pos hA _
    positivity
  have hi : ∀ k, C/c ≤ ∫ α : ℝ in Ioi 0, α^(s/2-1)*sphereGaussianCenteredScaled2 α (X k) := by
    intro k
    rw [div_le_iff₀ hc, mul_comm, ← normalizedEnergyRpow2_gaussian_mellin hs hs2 (hN k) (X k)]
    exact hC k
  have h := integral_ge_of_eventual_upper_profile2
    (μ := volume.restrict (Ioi (0:ℝ))) (g := g) (G := G)
    (f := fun k α => α^(s/2-1)*sphereGaussianCenteredScaled2 α (X k)) hg
    (fun k => sphereGaussianCenteredScaled2_weighted_integrable_rpow hs hs2 (hN k) (X k)) hG
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

/-- Reverse-Fatou upper bound for a sequence: `limsup normalizedEnergyRpow2 s X_k ≤ c_s ∫ g`. -/
theorem normalizedEnergyRpow2_eventually_le_of_profile {s : ℝ} (hs : 0 < s) (hs2 : s < 2)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, (ConfigurationD 2) (N k))
    {g G : ℝ → ℝ} (hg : IntegrableOn g (Ioi 0)) (hG : IntegrableOn G (Ioi 0))
    (hG0 : ∀ α : ℝ, 0 < α → 0 ≤ G α)
    (hdom : ∀ k, ∀ α : ℝ, 0 < α → α^(s/2-1)*sphereGaussianCenteredScaled2 α (X k) ≤ G α)
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      α^(s/2-1)*sphereGaussianCenteredScaled2 α (X k) ≤ g α+ε) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, normalizedEnergyRpow2 s (X k) ≤
      (Real.pi^(s/2)*((sphereAreaD 2).real univ)^(-(s/2))/Real.Gamma (s/2))*
        (∫ α : ℝ in Ioi 0, g α)+η := by
  intro η hη
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hcon
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have h := sphereGaussianSequence_energy_upper_of_profile_rpow2 hs hs2 (fun n => hN (φ n))
    (fun n => X (φ n)) hg hG hG0 (fun n => hdom (φ n))
    (fun α hα ε hε => hφt.eventually (hp α hα ε hε))
    (C := (Real.pi^(s/2)*((sphereAreaD 2).real univ)^(-(s/2))/Real.Gamma (s/2))*
        (∫ α : ℝ in Ioi 0, g α)+η) (fun n => (lt_of_not_ge (hbad n)).le)
  linarith

theorem sphereGaussianCenteredScaled2_weighted_profile_upper_eventually (s : ℝ)
    {N : ℕ → ℕ} (hNt : Tendsto N atTop atTop) (hN : ∀ k, 0 < N k) (X : ∀ k, (ConfigurationD 2) (N k))
    {α : ℝ} (hα : 0 < α)
    (hp : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      sphereGaussianFullScaled2 α (X k) ≤ hexGaussianThetaReal2 α+ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      α^(s/2-1)*sphereGaussianCenteredScaled2 α (X k) ≤ hexGaussianRieszProfileRpow2 s α+ε := by
  intro ε hε
  have hw : 0 < α^(s/2-1) := Real.rpow_pos_of_pos hα _
  set δ := ε/α^(s/2-1)/2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hsc := sphereGaussianScale2_tendsto hNt hα
  have hcorr : ∀ᶠ k in atTop, (1/4)/(α*sphereGaussianScale2 (N k) α) ≤ δ := by
    have ht : Tendsto (fun k => (1/4)/(α*sphereGaussianScale2 (N k) α)) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds (hsc.const_mul_atTop hα)
    exact ht.eventually (ge_mem_nhds hδ0)
  filter_upwards [hp δ hδ0, hcorr] with k hk hc
  have hb := sphereGaussianCenteredScaled2_le_full (hN k) hα (X k)
  have h2 : δ+δ = ε/α^(s/2-1) := by rw [hδ]; ring
  have hF : sphereGaussianCenteredScaled2 α (X k) ≤
      hexGaussianThetaReal2 α-α⁻¹-1+ε/α^(s/2-1) := by linarith
  unfold hexGaussianRieszProfileRpow2
  calc α^(s/2-1)*sphereGaussianCenteredScaled2 α (X k)
      ≤ α^(s/2-1)*(hexGaussianThetaReal2 α-α⁻¹-1+ε/α^(s/2-1)) :=
        mul_le_mul_of_nonneg_left hF hw.le
    _ = α^(s/2-1)*(hexGaussianThetaReal2 α-α⁻¹-1)+ε := by
      have he : α^(s/2-1)*(ε/α^(s/2-1)) = ε := mul_div_cancel₀ ε hw.ne'
      linear_combination he

/-- Upper reduction for every exponent `0 < s < 2` with a supplied majorant: the coefficient of
the triangular lattice is reached from an upper bound on the full Gaussian sums at every scale. -/
theorem sphere2_riesz_upper_of_full_profile {s : ℝ} (hs : 0 < s) (hs2 : s < 2)
    {N : ℕ → ℕ} (hNt : Tendsto N atTop atTop) (hN : ∀ k, 0 < N k) (X : ∀ k, (ConfigurationD 2) (N k))
    {G : ℝ → ℝ} (hG : IntegrableOn G (Ioi 0)) (hG0 : ∀ α : ℝ, 0 < α → 0 ≤ G α)
    (hdom : ∀ k, ∀ α : ℝ, 0 < α → α^(s/2-1)*sphereGaussianCenteredScaled2 α (X k) ≤ G α)
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      sphereGaussianFullScaled2 α (X k) ≤ hexGaussianThetaReal2 α+ε) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, normalizedEnergyRpow2 s (X k) ≤ sphereRieszCoefficient2 s+η := by
  intro η hη
  have h := normalizedEnergyRpow2_eventually_le_of_profile hs hs2 hN X
    (hexGaussianRieszProfileRpow2_integrable hs hs2) hG hG0 hdom
    (fun α hα => sphereGaussianCenteredScaled2_weighted_profile_upper_eventually s hNt hN X hα
      (hp α hα)) η hη
  unfold sphereRieszCoefficient2
  exact h

/-! ## Cell selections for the short-range kernel -/

/-- Cross-cell potentials are integrable without a separation hypothesis. -/
theorem shortRangeKernel2_cross_rowPotential_integrable {c p : ℝ} (hc : 0 < c) (hp : p < 0)
    (A S : Set (SphereD 2)) (hA : (sphereProbabilityD 2) A ≠ 0) :
    Integrable (residualRowPotential (sphereRestrictedProbability2 S) (shortRangeKernel2 c p))
      (sphereRestrictedProbability2 A) := by
  let := sphereRestrictedProbability2_probability A hA
  have hm : StronglyMeasurable
      (residualRowPotential (sphereRestrictedProbability2 S) (shortRangeKernel2 c p)) :=
    (shortRangeKernel2_measurable c p).integral_prod_right'
      (ν := sphereRestrictedProbability2 S)
  apply Integrable.of_bound hm.aestronglyMeasurable
    ((((sphereProbabilityD 2) S)⁻¹).toReal*((1/4)/c/(-p)))
  refine Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (residualRowPotential_nonneg _
    (shortRangeKernel2_nonneg c p) x)]
  exact shortRangeKernel2_restricted_row_le hc hp S x

/-- Cell selection on `S²` for the weighted Gaussian kernel and an additional linear cost. -/
theorem exists_shortRange_cell_selection2 {c p : ℝ} (hc : 0 < c) (hp : p < 0)
    (hp0 : -1 ≤ p) (n : ℕ) (C : Fin n → Set (SphereD 2))
    (hCm : ∀ i, MeasurableSet (C i)) (hCp : ∀ i, (sphereProbabilityD 2) (C i) ≠ 0)
    (L : (SphereD 2) → ℝ) (hL : ∀ i, Integrable L (sphereRestrictedProbability2 (C i)))
    (B : Set (SphereD 2)) (hB : (sphereProbabilityD 2) B = 0) :
    ∃ z : Fin n → (SphereD 2), Function.Injective z ∧ (∀ i, z i ∈ C i) ∧
      (∀ i, z i ∉ B) ∧ cellPairSum (shortRangeKernel2 c p) z + ∑ i, L (z i) ≤
        cellBoundK (shortRangeKernel2 c p) n (fun i => sphereRestrictedProbability2 (C i)) +
          ∑ i, ∫ x, L x ∂sphereRestrictedProbability2 (C i) := by
  apply exists_cell_selection (shortRangeKernel2 c p) (shortRangeKernel2_symm c p)
    n (fun i => sphereRestrictedProbability2 (C i)) C L B
  · exact fun i => sphereRestrictedProbability2_probability (C i) (hCp i)
  · exact fun i => inferInstance
  · exact fun i => sphereRestrictedProbability2_compl (C i) (hCm i)
  · intro i
    unfold sphereRestrictedProbability2
    rw [Measure.smul_apply, smul_eq_mul]
    have hrestrict : (sphereProbabilityD 2).restrict (C i) B = 0 :=
      le_antisymm ((Measure.restrict_apply_le _ _).trans_eq hB) zero_le
    rw [hrestrict, mul_zero]
  · exact fun i x => shortRangeKernel2_restricted_integrable hc hp (C i) x
  · exact fun i j => shortRangeKernel2_cross_rowPotential_integrable hc hp (C i) (C j) (hCp i)
  · intro i
    simp only [shortRangeKernel2_self c hp0]
    exact integrable_const 0
  · exact hL

/-- Equal-mass disjoint cells convert a sum of cell rows into one sphere restriction. -/
theorem sphereRestrictedProbability2_sum_integral {n N : ℕ}
    (C : Fin n → Set (SphereD 2)) (hCm : ∀ i, MeasurableSet (C i))
    (hCd : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hCmass : ∀ i, (sphereProbabilityD 2) (C i) = (N : ℝ≥0∞)⁻¹)
    {f : (SphereD 2) → ℝ} (hf : Integrable f (sphereProbabilityD 2)) :
    (∑ i, ∫ x, f x ∂sphereRestrictedProbability2 (C i)) =
      (N:ℝ)*∫ x in ⋃ i, C i, f x ∂(sphereProbabilityD 2) := by
  simp only [sphereRestrictedProbability2, hCmass, inv_inv, integral_smul_measure,
    smul_eq_mul, ENNReal.toReal_natCast]
  rw [← Finset.mul_sum, integral_iUnion hCm hCd hf.integrableOn, tsum_fintype]

/-- The density-scaled short-range row has an N-independent aggregate bound. -/
theorem shortRangeKernel2_cell_rows_le {n N : ℕ} (hN : 0 < N)
    {p : ℝ} (hp : p < 0) (C : Fin n → Set (SphereD 2))
    (hCm : ∀ i, MeasurableSet (C i)) (hCd : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hCmass : ∀ i, (sphereProbabilityD 2) (C i) = (N : ℝ≥0∞)⁻¹)
    (x : (SphereD 2)) :
    ∑ i, ∫ y, shortRangeKernel2 (sphereGaussianScale2 N 1) p x y
      ∂sphereRestrictedProbability2 (C i) ≤ 1/(-p) := by
  have hc := sphereGaussianScale2_pos hN zero_lt_one
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  rw [sphereRestrictedProbability2_sum_integral C hCm hCd hCmass
    (shortRangeKernel2_row_integrable hc hp x)]
  calc (N:ℝ)*∫ y in ⋃ i, C i, shortRangeKernel2 (sphereGaussianScale2 N 1) p x y
      ∂(sphereProbabilityD 2)
      ≤ (N:ℝ)*∫ y, shortRangeKernel2 (sphereGaussianScale2 N 1) p x y
          ∂(sphereProbabilityD 2) := by
        apply mul_le_mul_of_nonneg_left _ hNR.le
        exact setIntegral_le_integral (shortRangeKernel2_row_integrable hc hp x)
          (.of_forall (shortRangeKernel2_nonneg _ _ x))
    _ ≤ (N:ℝ)*((1/4)/(sphereGaussianScale2 N 1)/(-p)) :=
      mul_le_mul_of_nonneg_left (shortRangeKernel2_row_integral_le hc hp x) hNR.le
    _ = _ := by
      have hN1 : (N:ℝ)*(N:ℝ)⁻¹ = 1 := mul_inv_cancel₀ hNR.ne'
      rw [sphereGaussianScale2_eq_quarter]
      linear_combination (1/(-p))*hN1

/-- A conservative recursive expectation bound avoids a separate cross-cell Fubini argument. -/
theorem cellBoundK_le_two_mul_rows2 {E : Type*} [MeasurableSpace E]
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
theorem exists_shortRange_cell_bound2 {n N : ℕ} (hN : 0 < N) {p : ℝ}
    (hp : p < 0) (hp0 : -1 ≤ p) (C : Fin n → Set (SphereD 2))
    (hCm : ∀ i, MeasurableSet (C i)) (hCd : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hCmass : ∀ i, (sphereProbabilityD 2) (C i) = (N : ℝ≥0∞)⁻¹)
    (B : Set (SphereD 2)) (hB : (sphereProbabilityD 2) B = 0) :
    ∃ z : Fin n → (SphereD 2), Function.Injective z ∧ (∀ i, z i ∈ C i) ∧
      (∀ i, z i ∉ B) ∧
      cellPairSum (shortRangeKernel2 (sphereGaussianScale2 N 1) p) z ≤
        2*(n:ℝ)/(-p) := by
  have hc := sphereGaussianScale2_pos hN zero_lt_one
  have hCp : ∀ i, (sphereProbabilityD 2) (C i) ≠ 0 := by
    intro i
    rw [hCmass]
    exact ENNReal.inv_ne_zero.mpr (by simp)
  obtain ⟨z, hz, hCz, hBz, hb⟩ := exists_shortRange_cell_selection2 hc hp hp0 n C hCm hCp
    (fun _ => 0) (fun _ => integrable_const 0) B hB
  have hbound := cellBoundK_le_two_mul_rows2
    (shortRangeKernel2 (sphereGaussianScale2 N 1) p)
    (shortRangeKernel2_nonneg _ _) (shortRangeKernel2_self _ hp0) (1/(-p))
    n
    (fun i => sphereRestrictedProbability2 (C i))
    (fun i => sphereRestrictedProbability2_probability (C i) (hCp i))
    (fun i j => shortRangeKernel2_cross_rowPotential_integrable hc hp (C i) (C j) (hCp i))
    (shortRangeKernel2_cell_rows_le hN hp C hCm hCd hCmass)
  refine ⟨z, hz, hCz, hBz, ?_⟩
  simp only [Finset.sum_const_zero, integral_zero, add_zero] at hb
  calc cellPairSum (shortRangeKernel2 (sphereGaussianScale2 N 1) p) z
      ≤ 2*(n:ℝ)*(1/(-p)) := hb.trans hbound
    _ = 2*(n:ℝ)/(-p) := by ring

/-- Twice the short-range row of a point `z` against given points `X` (ordered cross pairs). -/
def shortRangeCrossRow2 (c p : ℝ) {M : ℕ} (X : Fin M → (SphereD 2))
    (z : (SphereD 2)) : ℝ := 2*∑ i, shortRangeKernel2 c p (X i) z

theorem shortRangeCrossRow2_integrable {c p : ℝ} (hc : 0 < c) (hp : p < 0) {M : ℕ}
    (X : Fin M → (SphereD 2)) (A : Set (SphereD 2)) :
    Integrable (shortRangeCrossRow2 c p X) (sphereRestrictedProbability2 A) :=
  (integrable_finsetSum _ fun i _ => shortRangeKernel2_restricted_integrable hc hp A (X i)).const_mul 2

theorem shortRangeCrossRow2_cell_integrals_le {n M N : ℕ} (hN : 0 < N) {p : ℝ}
    (hp : p < 0) (X : Fin M → (SphereD 2)) (C : Fin n → Set (SphereD 2))
    (hCm : ∀ i, MeasurableSet (C i)) (hCd : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hCmass : ∀ i, (sphereProbabilityD 2) (C i) = (N : ℝ≥0∞)⁻¹) :
    (∑ i, ∫ x, shortRangeCrossRow2 (sphereGaussianScale2 N 1) p X x
      ∂sphereRestrictedProbability2 (C i)) ≤ 2*(M:ℝ)/(-p) := by
  have hc := sphereGaussianScale2_pos hN zero_lt_one
  unfold shortRangeCrossRow2
  simp_rw [integral_const_mul, integral_finsetSum _
    (fun j _ => shortRangeKernel2_restricted_integrable hc hp _ (X j))]
  rw [← Finset.mul_sum, Finset.sum_comm]
  calc 2*(∑ j, ∑ i, ∫ x, shortRangeKernel2 (sphereGaussianScale2 N 1) p (X j) x
        ∂sphereRestrictedProbability2 (C i))
      ≤ 2*∑ _j : Fin M, 1/(-p) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum fun j _ => shortRangeKernel2_cell_rows_le hN hp C hCm hCd hCmass (X j)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- A single cell choice controls residual pairs and every foreground/residual cross pair. -/
theorem exists_shortRange_cell_cross_bound2 {n M N : ℕ} (hN : 0 < N) {p : ℝ}
    (hp : p < 0) (hp0 : -1 ≤ p) (X : Fin M → (SphereD 2))
    (C : Fin n → Set (SphereD 2)) (hCm : ∀ i, MeasurableSet (C i))
    (hCd : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hCmass : ∀ i, (sphereProbabilityD 2) (C i) = (N : ℝ≥0∞)⁻¹) :
    ∃ z : Fin n → (SphereD 2), Function.Injective z ∧ (∀ i, z i ∈ C i) ∧
      (∀ i, z i ∉ range X) ∧
      cellPairSum (shortRangeKernel2 (sphereGaussianScale2 N 1) p) z +
        ∑ i, shortRangeCrossRow2 (sphereGaussianScale2 N 1) p X (z i) ≤
          2*((n:ℝ)+(M:ℝ))/(-p) := by
  have hc := sphereGaussianScale2_pos hN zero_lt_one
  have hCp : ∀ i, (sphereProbabilityD 2) (C i) ≠ 0 := by
    intro i
    rw [hCmass]
    exact ENNReal.inv_ne_zero.mpr (by simp)
  obtain ⟨z, hz, hCz, hBz, hb⟩ := exists_shortRange_cell_selection2 hc hp hp0 n C hCm hCp
    (shortRangeCrossRow2 (sphereGaussianScale2 N 1) p X)
    (fun i => shortRangeCrossRow2_integrable hc hp X (C i)) (range X)
    ((finite_range X).measure_zero _)
  have hbound := cellBoundK_le_two_mul_rows2
    (shortRangeKernel2 (sphereGaussianScale2 N 1) p)
    (shortRangeKernel2_nonneg _ _) (shortRangeKernel2_self _ hp0) (1/(-p))
    n
    (fun i => sphereRestrictedProbability2 (C i))
    (fun i => sphereRestrictedProbability2_probability (C i) (hCp i))
    (fun i j => shortRangeKernel2_cross_rowPotential_integrable hc hp (C i) (C j) (hCp i))
    (shortRangeKernel2_cell_rows_le hN hp C hCm hCd hCmass)
  have hcross := shortRangeCrossRow2_cell_integrals_le hN hp X C hCm hCd hCmass
  refine ⟨z, hz, hCz, hBz, ?_⟩
  calc _ ≤ 2*(n:ℝ)*(1/(-p)) + 2*(M:ℝ)/(-p) :=
      hb.trans (add_le_add hbound hcross)
    _ = _ := by ring

/-- Actual Gaussian Mellin tails for residual off-diagonal pairs and ordered cross pairs.
The diagonal is removed before integration. -/
def residualGaussianTail2 (c s R : ℝ) {n M : ℕ}
    (X : Fin M → (SphereD 2)) (z : Fin n → (SphereD 2)) : ℝ :=
  (∑ i, ∑ j ∈ Finset.univ.erase i,
    ∫ α in Ioi R, α^(s/2-1)*sphereGaussianKernel2 (c*α) (z i) (z j)) +
  2*(∑ i, ∑ j,
    ∫ α in Ioi R, α^(s/2-1)*sphereGaussianKernel2 (c*α) (X j) (z i))

theorem residualGaussianTail2_le_kernel_cost {c s γ R : ℝ} (hc : 0 < c)
    (hs : 0 < s) (hγ : 0 ≤ γ) (hR : 1 ≤ R) {n M : ℕ}
    (X : Fin M → (SphereD 2)) (z : Fin n → (SphereD 2))
    (hz : Function.Injective z) (havoid : ∀ i, z i ∉ range X)
    (hp0 : -1 ≤ s/2-1+γ) :
    residualGaussianTail2 c s R X z ≤ R^(-γ)*
      (cellPairSum (shortRangeKernel2 c (s/2-1+γ)) z +
        ∑ i, shortRangeCrossRow2 c (s/2-1+γ) X (z i)) := by
  classical
  have hpair : (∑ i, ∑ j ∈ Finset.univ.erase i,
      ∫ α in Ioi R, α^(s/2-1)*sphereGaussianKernel2 (c*α) (z i) (z j)) ≤
      R^(-γ)*cellPairSum (shortRangeKernel2 c (s/2-1+γ)) z := by
    unfold cellPairSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    have hfull : (∑ j : Fin n, R^(-γ)*shortRangeKernel2 c (s/2-1+γ) (z i) (z j)) =
        ∑ j ∈ Finset.univ.erase i, R^(-γ)*shortRangeKernel2 c (s/2-1+γ) (z i) (z j) := by
      simpa only [shortRangeKernel2_self c hp0, mul_zero, add_zero] using
        (Finset.sum_erase_add Finset.univ
          (fun j => R^(-γ)*shortRangeKernel2 c (s/2-1+γ) (z i) (z j)) (Finset.mem_univ i)).symm
    rw [hfull]
    apply Finset.sum_le_sum
    intro j hj
    exact tail_le_shortRangeKernel2 hc hs hγ hR (hz.ne (Finset.mem_erase.mp hj).1.symm)
  have hcross : 2*(∑ i, ∑ j,
      ∫ α in Ioi R, α^(s/2-1)*sphereGaussianKernel2 (c*α) (X j) (z i)) ≤
      R^(-γ)*(∑ i, shortRangeCrossRow2 c (s/2-1+γ) X (z i)) := by
    unfold shortRangeCrossRow2
    simp only [← Finset.mul_sum]
    rw [show R^(-γ)*(2*∑ i, ∑ j, shortRangeKernel2 c (s/2-1+γ) (X j) (z i)) =
      2*(∑ i, ∑ j, R^(-γ)*shortRangeKernel2 c (s/2-1+γ) (X j) (z i)) by
        simp only [Finset.mul_sum]; ring_nf]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have hne : X j ≠ z i := fun h => havoid i ⟨j, h⟩
    exact tail_le_shortRangeKernel2 hc hs hγ hR hne
  unfold residualGaussianTail2
  rw [mul_add]
  exact add_le_add hpair hcross

/-- All large-scale tails are bounded simultaneously by one Gaussian-only cell selection. -/
theorem exists_residualGaussianTail2_uniform {n M N : ℕ} (hN : 0 < N)
    (hsize : n+M=N) {s : ℝ} (hs : 0 < s) (hs2 : s < 2)
    (X : Fin M → (SphereD 2)) (C : Fin n → Set (SphereD 2))
    (hCm : ∀ i, MeasurableSet (C i)) (hCd : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hCmass : ∀ i, (sphereProbabilityD 2) (C i) = (N : ℝ≥0∞)⁻¹) :
    ∃ z : Fin n → (SphereD 2), Function.Injective z ∧ (∀ i, z i ∈ C i) ∧
      (∀ i, z i ∉ range X) ∧ ∀ R : ℝ, 1 ≤ R →
        residualGaussianTail2 (sphereGaussianScale2 N 1) s R X z/(N:ℝ) ≤
          (8/(2-s))*R^(-(2-s)/4) := by
  set γ : ℝ := (2-s)/4 with hγdef
  have hγ : 0 < γ := by dsimp [γ]; linarith
  have hp : s/2-1+γ < 0 := by dsimp [γ]; linarith
  have hp0 : -1 ≤ s/2-1+γ := by linarith
  obtain ⟨z, hz, hCz, havoid, hb⟩ := exists_shortRange_cell_cross_bound2 hN hp hp0 X C hCm hCd hCmass
  refine ⟨z, hz, hCz, havoid, fun R hR => ?_⟩
  have hc := sphereGaussianScale2_pos hN zero_lt_one
  have htail := residualGaussianTail2_le_kernel_cost hc hs hγ.le hR X z hz havoid hp0
  have hR0 : 0 ≤ R^(-γ) := Real.rpow_nonneg (by linarith) _
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hsz : (n:ℝ)+(M:ℝ) = N := by exact_mod_cast hsize
  calc residualGaussianTail2 (sphereGaussianScale2 N 1) s R X z/(N:ℝ)
      ≤ (R^(-γ)*(2*((n:ℝ)+(M:ℝ))/(-(s/2-1+γ))))/(N:ℝ) :=
        div_le_div_of_nonneg_right (htail.trans (mul_le_mul_of_nonneg_left hb hR0)) hNR.le
    _ = _ := by
      have hpden : -(s/2-1+γ) = (2-s)/4 := by rw [hγdef]; ring
      have hN1 : (N:ℝ)*(N:ℝ)⁻¹ = 1 := mul_inv_cancel₀ hNR.ne'
      have hfactor : (2*(N:ℝ)/((2-s)/4))/(N:ℝ) = 8/(2-s) := by
        rw [div_div_eq_mul_div]
        linear_combination (8/(2-s))*hN1
      have hneg : -γ = -(2-s)/4 := by rw [hγdef]; ring
      rw [hpden, hsz, mul_div_assoc, hfactor, hneg, mul_comm]

theorem sphereGaussianPair2_scaled_tail_integrable {c s R : ℝ} (hc : 0 < c)
    (hs : 0 < s) (hR : 0 ≤ R) {x y : (SphereD 2)} (hxy : x ≠ y) :
    IntegrableOn (fun α : ℝ => α^(s/2-1)*sphereGaussianKernel2 (c*α) x y) (Ioi R) := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hb : 0 < c*dist x y^2 := by positivity
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow (s := s/2-1) (p := 1)
    (b := c*dist x y^2) (by linarith) one_pos hb
  apply (hi.mono_set (Ioi_subset_Ioi hR)).congr_fun _ measurableSet_Ioi
  intro α _
  simp only [sphereGaussianKernel2, Real.rpow_one]
  congr 2
  ring

/-- The selected tail cost is the integral of the actual weighted Gaussian pair sums. -/
theorem residualGaussianTail2_eq_integral {c s R : ℝ} (hc : 0 < c)
    (hs : 0 < s) (hR : 0 ≤ R) {n M : ℕ}
    (X : Fin M → (SphereD 2)) (z : Fin n → (SphereD 2))
    (hz : Function.Injective z) (havoid : ∀ i, z i ∉ range X) :
    residualGaussianTail2 c s R X z =
      ∫ α in Ioi R, (∑ i, ∑ j ∈ Finset.univ.erase i,
        α^(s/2-1)*sphereGaussianKernel2 (c*α) (z i) (z j)) +
        2*(∑ i, ∑ j, α^(s/2-1)*sphereGaussianKernel2 (c*α) (X j) (z i)) := by
  classical
  have hres : ∀ i, ∀ j ∈ Finset.univ.erase i, IntegrableOn
      (fun α : ℝ => α^(s/2-1)*sphereGaussianKernel2 (c*α) (z i) (z j)) (Ioi R) :=
    fun i j hj => sphereGaussianPair2_scaled_tail_integrable hc hs hR
      (hz.ne (Finset.mem_erase.mp hj).1.symm)
  have hcross : ∀ i j, IntegrableOn
      (fun α : ℝ => α^(s/2-1)*sphereGaussianKernel2 (c*α) (X j) (z i)) (Ioi R) :=
    fun i j => sphereGaussianPair2_scaled_tail_integrable hc hs hR
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
end
end

section

/-! # Gaussian end controls on `S²` and on its triangular-lattice charts (stage S2-3)

Dimension-2 port of `LeechGaussianEnds24`: the unit sphere `S² ⊂ ℝ³`, the centred Gaussian profile
`F(α)` of a configuration at the density scale `sphereGaussianScale2 N α = α N/4`, and the
triangular lattice of covolume one in place of the Leech lattice.

* The standard Gaussian of the ambient space `ℝ³` has the density `(2π)^(-3/2) exp(-|z|²/2)`; the
  Gaussian defect of a configuration is a Gaussian integral of the squared modulus of a Fourier
  amplitude, so `√t³ D(t)` and `√α³ (F(α)+1)` are nondecreasing (the exponent is the ambient
  dimension `d+1 = 3`), and `F(α)+1 ≤ √2³ (F(β)+1)` for `α ≤ β ≤ 2α`.
* Small scales.  The budget `sphereGaussianSmallBudget2 q X = ∫_0^4 α^(q-1) (F(α)+1) dα`, for
  `0 < q < 1` (`q < d/2`), bounds `(F(α)+1) α^q` on `(0, 2]`; with `q = s/4` the weighted profile
  `α^(s/2-1) F(α)` is at most a constant times `α^(s/4-1)`.
* Large scales.  For `-1 < p ≤ 0` the Gaussian kernel is dominated pointwise by the short-range
  kernel, `K_{cα} ≤ 2 α^(-(p+1)) T_{c,p}` for `α ≥ 2`; with `p = s/4 - 1/2` the weighted profile is
  at most `2 D α^(s/4-3/2)` on `[2, ∞)`, `D` a bound of the short-range cost per point.
* The majorant of the two ends is integrable on `(0, ∞)` exactly for `0 < s < 2`, and
  `sphere2_riesz_upper_of_gaussian_budgets` gives the sharp upper bound of the normalized Riesz
  energy along a sequence with uniform budgets and the theta upper bound at every scale.
* Rows of lattice patches.  A finite patch of the triangular lattice in a near-flat chart of `S²`
  has Gaussian rows bounded by `Θ(β) - 1`, `Θ` the theta function of the lattice; the tail
  `Θ(β) - 1 ≤ exp(-(2π/√3)(β-1)) (Θ(1) - 1)` has the rate `2π/√3` of the minimal squared norm
  `2/√3` of the lattice (it is `2π` for the even Leech lattice).  Midpoint grids and
  boundary-corrected grids of patches are covered, and separated patches have exponentially
  small cross rows at the density scale. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
namespace SphericalRiesz
open Boundary

/-! ## The standard Gaussian of `ℝ³` and the monotonicity of the centred profile -/

/-- Lebesgue density of the standard Gaussian on `AmbientD 2 = ℝ³`. -/
def stdGaussianDensity3 (z : (AmbientD 2)) : ℝ :=
  ((2*Real.pi)^((3:ℝ)/2))⁻¹*Real.exp (-(1/2)*‖z‖^2)

theorem stdGaussianDensity3_nonneg (z : (AmbientD 2)) : 0 ≤ stdGaussianDensity3 z := by
  unfold stdGaussianDensity3
  positivity

theorem stdGaussianDensity3_continuous : Continuous stdGaussianDensity3 := by
  unfold stdGaussianDensity3
  fun_prop

theorem integrable_rexp_neg_mul_sq_norm3 {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : (AmbientD 2) => Real.exp (-b*‖z‖^2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := (AmbientD 2))
    (b := (b:ℂ)) (by simpa using hb) 0 0).norm
  refine h.congr (ae_of_all _ fun z => ?_)
  have he : (-(b:ℂ)*((‖z‖:ℝ):ℂ)^2+0*((⟪(0:(AmbientD 2)), z⟫:ℝ):ℂ)) = ((-b*‖z‖^2:ℝ):ℂ) := by
    push_cast
    ring
  simp only [he, Complex.norm_exp_ofReal]

/-- The finite measure with the standard Gaussian density. -/
def stdGaussianDensityMeasure3 : Measure (AmbientD 2) :=
  volume.withDensity (fun z => ENNReal.ofReal (stdGaussianDensity3 z))

theorem stdGaussianDensity3_integrable : Integrable stdGaussianDensity3 :=
  (integrable_rexp_neg_mul_sq_norm3 (b := 1/2) (by norm_num)).const_mul _

instance stdGaussianDensityMeasure3_finite : IsFiniteMeasure stdGaussianDensityMeasure3 :=
  isFiniteMeasure_withDensity_ofReal stdGaussianDensity3_integrable.2

theorem integral_stdGaussianDensityMeasure3 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : (AmbientD 2) → F) :
    ∫ z, g z ∂stdGaussianDensityMeasure3 = ∫ z, stdGaussianDensity3 z • g z := by
  rw [stdGaussianDensityMeasure3, integral_withDensity_eq_integral_toReal_smul
    stdGaussianDensity3_continuous.measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (stdGaussianDensity3_nonneg _)]

theorem integral_cexp_gaussian_char3 (t : (AmbientD 2)) :
    ∫ x : (AmbientD 2), Complex.exp (-(1/2:ℂ)*‖x‖^2+Complex.I*⟪t, x⟫) =
      (((2*Real.pi)^((3:ℝ)/2):ℝ):ℂ)*Complex.exp (-‖t‖^2/2) := by
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

theorem charFun_stdGaussianDensityMeasure3 (t : (AmbientD 2)) :
    charFun stdGaussianDensityMeasure3 t = Complex.exp (-‖t‖^2/2) := by
  rw [charFun_apply, integral_stdGaussianDensityMeasure3]
  have key : ∀ x : (AmbientD 2), stdGaussianDensity3 x • Complex.exp (⟪x, t⟫*Complex.I) =
      ((((2*Real.pi)^((3:ℝ)/2))⁻¹:ℝ):ℂ)*
        Complex.exp (-(1/2:ℂ)*‖x‖^2+Complex.I*⟪t, x⟫) := by
    intro x
    rw [stdGaussianDensity3, Complex.real_smul, Complex.ofReal_mul, mul_assoc, Complex.ofReal_exp,
      ← Complex.exp_add, real_inner_comm]
    congr 2
    push_cast
    ring
  simp_rw [key]
  rw [integral_const_mul, integral_cexp_gaussian_char3, ← mul_assoc, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (by positivity), Complex.ofReal_one, one_mul]

/-- The standard Gaussian on `(AmbientD 2)` has the Lebesgue density `stdGaussianDensity3`. -/
theorem stdGaussian_ambient3_eq : stdGaussian (AmbientD 2) = stdGaussianDensityMeasure3 := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_stdGaussian, charFun_stdGaussianDensityMeasure3]

theorem integral_stdGaussian_ambient3 (g : (AmbientD 2) → ℝ) :
    ∫ z, g z ∂stdGaussian (AmbientD 2) = ∫ z, stdGaussianDensity3 z*g z := by
  rw [stdGaussian_ambient3_eq, integral_stdGaussianDensityMeasure3]
  rfl

/-- Fourier amplitude of the signed measure `Σ δ_{xᵢ} - M σ` at the frequency `w`. -/
def sphereGaussianAmplitude2 {N : ℕ} (M : ℝ) (X : (ConfigurationD 2) N) (w : (AmbientD 2)) : ℂ :=
  (∑ i, Complex.exp (⟪(X i:(AmbientD 2)), w⟫*Complex.I))-(M:ℂ)*charFun ambientSphereProbability2 w

theorem sphereGaussianAmplitude2_continuous {N : ℕ} (M : ℝ) (X : (ConfigurationD 2) N) :
    Continuous (sphereGaussianAmplitude2 M X) := by
  have hc : Continuous (charFun ambientSphereProbability2) := continuous_charFun
  unfold sphereGaussianAmplitude2
  fun_prop

theorem sphereGaussianAmplitude2_norm_le {N : ℕ} (M : ℝ) (X : (ConfigurationD 2) N) (w : (AmbientD 2)) :
    ‖sphereGaussianAmplitude2 M X w‖ ≤ N+|M| := by
  unfold sphereGaussianAmplitude2
  have h1 : ‖∑ i, Complex.exp (⟪(X i:(AmbientD 2)), w⟫*Complex.I)‖ ≤ N := by
    calc ‖∑ i, Complex.exp (⟪(X i:(AmbientD 2)), w⟫*Complex.I)‖
        ≤ ∑ i, ‖Complex.exp (⟪(X i:(AmbientD 2)), w⟫*Complex.I)‖ := norm_sum_le _ _
      _ = N := by simp [Complex.norm_exp_ofReal_mul_I]
  have h2 : ‖(M:ℂ)*charFun ambientSphereProbability2 w‖ ≤ |M| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (norm_charFun_le_one _)
  exact (norm_sub_le _ _).trans (add_le_add h1 h2)

theorem sphereGaussianDefect2_eq_amplitude {N : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (M : ℝ) (X : (ConfigurationD 2) N) :
    sphereGaussianDefect2 t M X = ∫ z,
      Complex.normSq (sphereGaussianAmplitude2 M X (Real.sqrt (2*t) • z)) ∂stdGaussian (AmbientD 2) := by
  rw [sphereGaussianDefect2_eq_diffuse ht, diffuseGaussianDefect_eq_normSq ht]
  rfl

/-- Lebesgue form of the neutralized defect: Gaussian weight `e^{-|w|²/(4t)}` on `|φ(w)|²`. -/
theorem sphereGaussianDefect2_eq_lebesgue {N : ℕ} {t : ℝ} (ht : 0 < t)
    (M : ℝ) (X : (ConfigurationD 2) N) :
    sphereGaussianDefect2 t M X = (Real.sqrt (2*t)^3)⁻¹*(((2*Real.pi)^((3:ℝ)/2))⁻¹*
      ∫ w, Real.exp (-(4*t)⁻¹*‖w‖^2)*Complex.normSq (sphereGaussianAmplitude2 M X w)) := by
  rw [sphereGaussianDefect2_eq_amplitude ht.le, integral_stdGaussian_ambient3]
  set R := Real.sqrt (2*t) with hRdef
  have hR : 0 < R := Real.sqrt_pos.mpr (by positivity)
  have hR2 : R^2 = 2*t := Real.sq_sqrt (by positivity)
  set G : (AmbientD 2) → ℝ := fun w => ((2*Real.pi)^((3:ℝ)/2))⁻¹*
    (Real.exp (-(4*t)⁻¹*‖w‖^2)*Complex.normSq (sphereGaussianAmplitude2 M X w)) with hG
  have hGz : ∀ z : (AmbientD 2), stdGaussianDensity3 z*
      Complex.normSq (sphereGaussianAmplitude2 M X (R • z)) = G (R • z) := by
    intro z
    simp only [hG, stdGaussianDensity3, norm_smul, Real.norm_eq_abs, abs_of_pos hR, mul_pow, hR2]
    have he : -(4*t)⁻¹*(2*t*‖z‖^2) = -(1/2)*‖z‖^2 := by
      field_simp
      ring
    rw [he]
    ring
  simp_rw [hGz]
  rw [Measure.integral_comp_smul volume G R, finrank_euclideanSpace_fin, smul_eq_mul,
    abs_of_pos (by positivity), hG, integral_const_mul]

theorem sphereGaussianDefect2_sqrt_pow_mul_eq {N : ℕ} {t : ℝ} (ht : 0 < t)
    (M : ℝ) (X : (ConfigurationD 2) N) :
    Real.sqrt t^3*sphereGaussianDefect2 t M X = (Real.sqrt 2^3)⁻¹*(((2*Real.pi)^((3:ℝ)/2))⁻¹*
      ∫ w, Real.exp (-(4*t)⁻¹*‖w‖^2)*Complex.normSq (sphereGaussianAmplitude2 M X w)) := by
  rw [sphereGaussianDefect2_eq_lebesgue ht, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), mul_pow]
  have h1 : 0 < Real.sqrt t^3 := pow_pos (Real.sqrt_pos.mpr ht) _
  have h2 : 0 < Real.sqrt 2^3 := pow_pos (Real.sqrt_pos.mpr (by norm_num)) _
  field_simp

theorem sphereGaussianAmplitude2_weighted_integrable {N : ℕ} {t : ℝ} (ht : 0 < t)
    (M : ℝ) (X : (ConfigurationD 2) N) :
    Integrable (fun w : (AmbientD 2) =>
      Real.exp (-(4*t)⁻¹*‖w‖^2)*Complex.normSq (sphereGaussianAmplitude2 M X w)) := by
  apply (integrable_rexp_neg_mul_sq_norm3 (b := (4*t)⁻¹) (by positivity)).mul_bdd
    (Complex.continuous_normSq.comp (sphereGaussianAmplitude2_continuous M X)).aestronglyMeasurable
    (c := ((N:ℝ)+|M|)^2)
  refine ae_of_all _ fun w => ?_
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) (sphereGaussianAmplitude2_norm_le M X w) 2

/-- `√t³ · D(t)` is nondecreasing in `t > 0`. -/
theorem sphereGaussianDefect2_sqrt_pow_mul_mono {N : ℕ} {t t' : ℝ} (ht : 0 < t) (htt : t ≤ t')
    (M : ℝ) (X : (ConfigurationD 2) N) :
    Real.sqrt t^3*sphereGaussianDefect2 t M X ≤ Real.sqrt t'^3*sphereGaussianDefect2 t' M X := by
  have ht' : 0 < t' := ht.trans_le htt
  rw [sphereGaussianDefect2_sqrt_pow_mul_eq ht, sphereGaussianDefect2_sqrt_pow_mul_eq ht']
  have hc : 0 ≤ (Real.sqrt 2^3)⁻¹ := by positivity
  have hc' : 0 ≤ ((2*Real.pi)^((3:ℝ)/2))⁻¹ := by positivity
  apply mul_le_mul_of_nonneg_left _ hc
  apply mul_le_mul_of_nonneg_left _ hc'
  apply integral_mono_of_nonneg
    (ae_of_all _ fun w => mul_nonneg (Real.exp_pos _).le (Complex.normSq_nonneg _))
    (sphereGaussianAmplitude2_weighted_integrable ht' M X)
  refine ae_of_all _ fun w => ?_
  apply mul_le_mul_of_nonneg_right _ (Complex.normSq_nonneg _)
  apply Real.exp_le_exp.mpr
  have hinv : (4*t')⁻¹ ≤ (4*t)⁻¹ := inv_anti₀ (by positivity) (by linarith)
  nlinarith [sq_nonneg ‖w‖]

theorem sphereGaussianCenteredScaled2_add_one {N : ℕ} (hN : 0 < N) {α : ℝ} (hα : 0 ≤ α)
    (X : (ConfigurationD 2) N) :
    sphereGaussianCenteredScaled2 α X+1 =
      sphereGaussianDefect2 (sphereGaussianScale2 N α) (N:ℝ) X/(N:ℝ) := by
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hs : 0 ≤ sphereGaussianScale2 N α := by
    rw [sphereGaussianScale2_eq_factor]
    exact mul_nonneg (sphereGaussianDensityFactor2_pos hN).le hα
  rw [sphereGaussianDefect2_charge_N hs, sphereGaussianCenteredScaled2]
  field_simp
  ring

theorem sphereGaussianCenteredScaled2_add_one_nonneg {N : ℕ} (hN : 0 < N) {α : ℝ} (hα : 0 ≤ α)
    (X : (ConfigurationD 2) N) : 0 ≤ sphereGaussianCenteredScaled2 α X+1 := by
  have hs : 0 ≤ sphereGaussianScale2 N α := by
    rw [sphereGaussianScale2_eq_factor]
    exact mul_nonneg (sphereGaussianDensityFactor2_pos hN).le hα
  rw [sphereGaussianCenteredScaled2_add_one hN hα]
  exact div_nonneg (sphereGaussianDefect2_nonneg hs _ X) (Nat.cast_nonneg N)

/-- PSD monotonicity of the density-scaled centered profile: `√α³ (F(α)+1)` is nondecreasing. -/
theorem sphereGaussianCenteredScaled2_sqrt_pow_mono {N : ℕ} (hN : 0 < N) (X : (ConfigurationD 2) N)
    {α α' : ℝ} (hα : 0 < α) (hαα : α ≤ α') :
    Real.sqrt α^3*(sphereGaussianCenteredScaled2 α X+1) ≤
      Real.sqrt α'^3*(sphereGaussianCenteredScaled2 α' X+1) := by
  have hα' : 0 < α' := hα.trans_le hαα
  set c := sphereGaussianDensityFactor2 N with hcdef
  have hc : 0 < c := sphereGaussianDensityFactor2_pos hN
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  rw [sphereGaussianCenteredScaled2_add_one hN hα.le, sphereGaussianCenteredScaled2_add_one hN hα'.le,
    sphereGaussianScale2_eq_factor, sphereGaussianScale2_eq_factor]
  have hm := sphereGaussianDefect2_sqrt_pow_mul_mono (mul_pos hc hα)
    (mul_le_mul_of_nonneg_left hαα hc.le) (N:ℝ) X
  rw [Real.sqrt_mul hc.le, Real.sqrt_mul hc.le, mul_pow, mul_pow] at hm
  have hc9 : 0 < Real.sqrt c^3 := pow_pos (Real.sqrt_pos.mpr hc) _
  rw [← hcdef]
  have key : ∀ a : ℝ, Real.sqrt a^3*(sphereGaussianDefect2 (c*a) (N:ℝ) X/(N:ℝ)) =
      (Real.sqrt c^3*(N:ℝ))⁻¹*(Real.sqrt c^3*Real.sqrt a^3*sphereGaussianDefect2 (c*a) (N:ℝ) X) := by
    intro a
    field_simp
  rw [key, key]
  exact mul_le_mul_of_nonneg_left hm (by positivity)

/-- Doubling form of the monotonicity: `F(α)+1 ≤ √2³ (F(β)+1)` for `α ≤ β ≤ 2α`. -/
theorem sphereGaussianCenteredScaled2_doubling {N : ℕ} (hN : 0 < N) (X : (ConfigurationD 2) N)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 2*α) :
    sphereGaussianCenteredScaled2 α X+1 ≤ Real.sqrt 2^3*(sphereGaussianCenteredScaled2 β X+1) := by
  have hm := sphereGaussianCenteredScaled2_sqrt_pow_mono hN X hα hαβ
  have hβ0 : 0 ≤ sphereGaussianCenteredScaled2 β X+1 :=
    sphereGaussianCenteredScaled2_add_one_nonneg hN (hα.le.trans hαβ) X
  have hsq : Real.sqrt β ≤ Real.sqrt 2*Real.sqrt α := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hβ
  have hpow : Real.sqrt β^3 ≤ Real.sqrt 2^3*Real.sqrt α^3 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 3
  have hα9 : 0 < Real.sqrt α^3 := pow_pos (Real.sqrt_pos.mpr hα) _
  have h2 : Real.sqrt α^3*(sphereGaussianCenteredScaled2 α X+1) ≤
      Real.sqrt α^3*(Real.sqrt 2^3*(sphereGaussianCenteredScaled2 β X+1)) := by
    calc
      _ ≤ Real.sqrt β^3*(sphereGaussianCenteredScaled2 β X+1) := hm
      _ ≤ (Real.sqrt 2^3*Real.sqrt α^3)*(sphereGaussianCenteredScaled2 β X+1) :=
        mul_le_mul_of_nonneg_right hpow hβ0
      _ = _ := by ring
  exact le_of_mul_le_mul_left h2 hα9

/-! ## The small-scale budget -/

/-- An actual Gaussian PSD budget on the macroscopic interval. -/
def sphereGaussianSmallBudget2 {N : ℕ} (q : ℝ) (X : (ConfigurationD 2) N) : ℝ :=
  ∫ α in Ioc (0:ℝ) 4, α^(q-1)*(sphereGaussianCenteredScaled2 α X+1)

theorem sphereGaussianSmallBudget2_integrable {N : ℕ} (hN : 0 < N)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (X : (ConfigurationD 2) N) :
    IntegrableOn (fun α : ℝ => α^(q-1)*(sphereGaussianCenteredScaled2 α X+1)) (Ioc 0 4) := by
  have hf := (sphereGaussianCenteredScaled2_weighted_integrable_rpow
    (s := 2*q) (by linarith) (by linarith) hN X).mono_set (s := Ioc (0:ℝ) 4) Ioc_subset_Ioi_self
  have hw : IntegrableOn (fun α : ℝ => α^(q-1)) (Ioc 0 4) := by
    exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < q-1) (a := 0) (b := 4)).1
  have he : (fun α : ℝ => α^(q-1)*(sphereGaussianCenteredScaled2 α X+1)) =
      (fun α => α^(q-1)*sphereGaussianCenteredScaled2 α X) + (fun α => α^(q-1)) := by
    funext α; simp only [Pi.add_apply]; ring
  rw [he]
  have hqeq : 2*q/2-1 = q-1 := by ring
  rw [hqeq] at hf
  exact hf.add hw

theorem sphereGaussianSmallBudget2_nonneg {N : ℕ} (hN : 0 < N)
    (q : ℝ) (X : (ConfigurationD 2) N) : 0 ≤ sphereGaussianSmallBudget2 q X := by
  apply setIntegral_nonneg measurableSet_Ioc
  intro α hα
  exact mul_nonneg (Real.rpow_nonneg hα.1.le _)
    (sphereGaussianCenteredScaled2_add_one_nonneg hN hα.1.le X)

/-- PSD doubling turns a Gaussian integral budget into a pointwise small-scale bound. -/
theorem sphereGaussianCenteredScaled2_small_budget_bound {N : ℕ} (hN : 0 < N)
    {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (X : (ConfigurationD 2) N)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 2) :
    (sphereGaussianCenteredScaled2 α X+1)*α^q ≤
      (Real.sqrt 2^3*q/(2^q-1))*sphereGaussianSmallBudget2 q X := by
  let F := fun β => sphereGaussianCenteredScaled2 β X+1
  let κ : ℝ := Real.sqrt 2^3
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hi := sphereGaussianSmallBudget2_integrable hN hq hq1 X
  have hsub : Ioc α (2*α) ⊆ Ioc (0:ℝ) 4 := fun β hβ => ⟨hα.trans hβ.1,by linarith [hβ.2]⟩
  have hw : IntegrableOn (fun β : ℝ => β^(q-1)) (Ioc α (2*α)) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < q-1)).1
  have hid : (∫ β in Ioc α (2*α), β^(q-1)) = α^q*(2^q-1)/q := by
    rw [← intervalIntegral.integral_of_le (by linarith), integral_rpow (Or.inl (by linarith)),
      show q-1+1=q by ring, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hα.le]
    ring
  have hl : F α/κ*(α^q*(2^q-1)/q) ≤ sphereGaussianSmallBudget2 q X := by
    calc
      _ = ∫ β in Ioc α (2*α), (F α/κ)*β^(q-1) := by rw [integral_const_mul,hid]
      _ ≤ ∫ β in Ioc α (2*α), β^(q-1)*F β := by
        apply setIntegral_mono_on (hw.const_mul _) (hi.mono_set hsub) measurableSet_Ioc
        intro β hβ
        have hd := sphereGaussianCenteredScaled2_doubling hN X hα hβ.1.le hβ.2
        have hd' : F α/κ ≤ F β := (div_le_iff₀ hκ).mpr (by simpa [F,κ,mul_comm] using hd)
        exact (mul_le_mul_of_nonneg_right hd' (Real.rpow_nonneg (hα.le.trans hβ.1.le) _)).trans_eq (mul_comm _ _)
      _ ≤ sphereGaussianSmallBudget2 q X := by
        apply setIntegral_mono_set hi
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with β hβ
          exact mul_nonneg (Real.rpow_nonneg hβ.1.le _)
            (sphereGaussianCenteredScaled2_add_one_nonneg hN hβ.1.le X)
        · exact hsub.eventuallyLE
  have h2 : 0 < (2:ℝ)^q-1 := by
    have := Real.one_lt_rpow (by norm_num : (1:ℝ) < 2) hq
    linarith
  have he : (F α/κ*(α^q*(2^q-1)/q))*(κ*q/(2^q-1)) = F α*α^q := by
    field_simp
  have hb := mul_le_mul_of_nonneg_right hl (by positivity : 0 ≤ κ*q/(2^q-1))
  rw [he] at hb
  exact hb.trans_eq (mul_comm _ _)

/-- The uniform budget at `q = s/4` (in `(0, 1/2)` for `0 < s < 2`) gives an integrable
small-alpha upper power. -/
theorem sphereGaussianCenteredScaled2_small_weighted_bound {N : ℕ} (hN : 0 < N)
    {s B : ℝ} (hs : 0 < s) (hs2 : s < 2) (X : (ConfigurationD 2) N)
    (hB : sphereGaussianSmallBudget2 (s/4) X ≤ B)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 2) :
    α^(s/2-1)*sphereGaussianCenteredScaled2 α X ≤
      (Real.sqrt 2^3*(s/4)/(2^(s/4)-1))*B*α^(s/4-1) := by
  have h := sphereGaussianCenteredScaled2_small_budget_bound hN
    (q := s/4) (by linarith) (by linarith) X hα hα1
  have hconst : 0 ≤ Real.sqrt 2^3*(s/4)/(2^(s/4)-1) := by
    have := Real.one_lt_rpow (by norm_num : (1:ℝ) < 2) (by linarith : 0 < s/4)
    positivity
  have hb := h.trans (mul_le_mul_of_nonneg_left hB hconst)
  have hq : 0 < α^(s/4) := Real.rpow_pos_of_pos hα _
  have hf : sphereGaussianCenteredScaled2 α X ≤
      (Real.sqrt 2^3*(s/4)/(2^(s/4)-1))*B/α^(s/4) := by
    apply (le_div_iff₀ hq).mpr
    nlinarith
  calc
    _ ≤ α^(s/2-1)*((Real.sqrt 2^3*(s/4)/(2^(s/4)-1))*B/α^(s/4)) :=
      mul_le_mul_of_nonneg_left hf (Real.rpow_nonneg hα.le _)
    _ = _ := by
      have hp : α^(s/2-1)/α^(s/4) = α^(s/4-1) := by
        rw [← Real.rpow_sub hα]
        congr 1
        ring
      calc
        _ = ((Real.sqrt 2^3*(s/4)/(2^(s/4)-1))*B)*(α^(s/2-1)/α^(s/4)) := by ring
        _ = _ := by rw [hp]

/-! ## Theta row bounds for patches of the triangular lattice -/

/-- Every finite subset of the triangular lattice is bounded by its theta tail. -/
theorem finiteHexGaussian_row_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : ι ↪ hexLattice) (i : ι) {β : ℝ} (hβ : 0 < β) :
    (∑ j ∈ Finset.univ.erase i, Real.exp (-(Real.pi*β*‖((U j-U i : hexLattice) : HexAmbient)‖^2))) ≤
      hexGaussianThetaReal2 β-1 := by
  classical
  let f : hexLattice → ℝ := fun u => Real.exp (-(Real.pi*β*‖(u : HexAmbient)‖^2))
  have hf : HasSum f (hexGaussianThetaReal2 β) :=
    Complex.hasSum_ofReal.mp (hexLatticeGaussian_hasSum hβ)
  have hf0 : f 0 = 1 := by simp [f]
  have hup := hf.update (0 : hexLattice) 0
  rw [hf0] at hup
  let V : ι → hexLattice := fun j => U j-U i
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

/-- A lower distance estimate for a physical patch of the triangular lattice controls its full
Gaussian row. -/
theorem hexPatchGaussian_row_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : ι ↪ hexLattice) (Y : ι → (SphereD 2)) {ell t : ℝ} (hell : 0 < ell) (ht : 0 < t)
    (hd : ∀ i j, ell*‖((U j-U i : hexLattice) : HexAmbient)‖ ≤ dist (Y i) (Y j)) (i : ι) :
    (∑ j ∈ Finset.univ.erase i, sphereGaussianKernel2 t (Y i) (Y j)) ≤
      hexGaussianThetaReal2 (t*ell^2/Real.pi)-1 := by
  have hβ : 0 < t*ell^2/Real.pi := by positivity
  apply le_trans _ (finiteHexGaussian_row_le U i hβ)
  apply Finset.sum_le_sum
  intro j _
  unfold sphereGaussianKernel2
  apply Real.exp_le_exp.mpr
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ ell*‖((U j-U i : hexLattice) : HexAmbient)‖) (hd i j) 2
  have he : Real.pi*(t*ell^2/Real.pi) = t*ell^2 := by field_simp
  rw [he,mul_pow] at *
  nlinarith

/-- The exponential form of the row bound: the theta tail decays with the rate `2π/√3` of the
minimal squared norm `2/√3` of the triangular lattice. -/
theorem hexPatchGaussian_row_exp_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : ι ↪ hexLattice) (Y : ι → (SphereD 2)) {ell t : ℝ} (hell : 0 < ell) (ht : 0 < t)
    (hd : ∀ i j, ell*‖((U j-U i : hexLattice) : HexAmbient)‖ ≤ dist (Y i) (Y j))
    (hscale : 1 ≤ t*ell^2/Real.pi) (i : ι) :
    (∑ j ∈ Finset.univ.erase i, sphereGaussianKernel2 t (Y i) (Y j)) ≤
      Real.exp (-(2*Real.pi/Real.sqrt 3)*(t*ell^2/Real.pi-1))*(hexGaussianThetaReal2 1-1) :=
  (hexPatchGaussian_row_le U Y hell ht hd i).trans (hexGaussianThetaReal2_tail_le hscale)


theorem equalAreaHexPatch_dist_eq (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c x y : Fin 2 → ℝ) {ε : ℝ} (hε : 0 < ε) :
    dist (equalAreaHexPatch g v c ε x) (equalAreaHexPatch g v c ε y) =
      ε*dist (equalAreaNormalizedHexPatch g v c ε x) (equalAreaNormalizedHexPatch g v c ε y) := by
  rw [equalAreaNormalizedHexPatch_eq,equalAreaNormalizedHexPatch_eq,dist_eq_norm,dist_eq_norm,
    ← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hε)]
  have he : (equalAreaHexPatch g v c ε x-equalAreaHexPatch g v c ε c)-
      (equalAreaHexPatch g v c ε y-equalAreaHexPatch g v c ε c) =
      equalAreaHexPatch g v c ε x-equalAreaHexPatch g v c ε y := by abel
  rw [he,← mul_assoc,mul_inv_cancel₀ hε.ne',one_mul]

/-- The theta row estimate applies to the actual near-flat sphere charts. -/
theorem equalAreaHexPatch_gaussian_row_uniform {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
      (v c : Fin 2 → ℝ), ‖v‖ ≤ ρ → ∀ (hc : c ∈ UnitCube 2)
      (ε : ℝ) (hε : 0 < ε), ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8),
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] (U : ι ↪ hexLattice) (x : ι → UnitCube 2)
      (a : ℝ), 0 < a →
      (∀ i j, dist (WithLp.toLp 2 (hexMap (x i)) : HexAmbient)
        (WithLp.toLp 2 (hexMap (x j))) = a*‖((U j-U i : hexLattice) : HexAmbient)‖) →
      ∀ t : ℝ, 0 < t → ∀ i : ι,
      (∑ j ∈ Finset.univ.erase i, sphereGaussianKernel2 t
        (equalAreaHexCubeEmbedding2 g v c ε hε hc hsmall (x i))
        (equalAreaHexCubeEmbedding2 g v c ε hε hc hsmall (x j))) ≤
      hexGaussianThetaReal2 (t*((1-η)*ε*a)^2/Real.pi)-1 := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := equalAreaNormalizedHexPatch_relative_distance_uniform η hη
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro g v c hv hc ε hε hs hsmall ι _ _ U x a ha hflat t ht i
  have hη0 : 0 < 1-η := by linarith
  apply hexPatchGaussian_row_le U _ (by positivity : 0 < (1-η)*ε*a) ht _ i
  intro j k
  change _ ≤ dist (equalAreaHexPatch g v c ε (x j)) (equalAreaHexPatch g v c ε (x k))
  rw [equalAreaHexPatch_dist_eq g v c _ _ hε]
  have hd := (abs_le.mp (hb v hv ε hε hs g c hc (x j) (x j).property (x k) (x k).property)).1
  rw [hflat] at hd
  nlinarith

/-- Cross pairs between separated physical patches have an exponential Gaussian bound. -/
theorem separatedGaussian2_cross_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : ι → (SphereD 2)) (Y : κ → (SphereD 2)) {δ t : ℝ} (hδ : 0 ≤ δ) (ht : 0 ≤ t)
    (hd : ∀ i j, δ ≤ dist (X i) (Y j)) :
    (∑ i, ∑ j, sphereGaussianKernel2 t (X i) (Y j)) ≤
      (Fintype.card ι:ℝ)*(Fintype.card κ:ℝ)*Real.exp (-(t*δ^2)) := by
  calc
    _ ≤ (∑ _ : ι, ∑ _ : κ, Real.exp (-(t*δ^2))) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      unfold sphereGaussianKernel2
      apply Real.exp_le_exp.mpr
      have hsq := pow_le_pow_left₀ hδ (hd i j) 2
      nlinarith
    _ = _ := by simp; ring

/-- At the actual density scale even N times a separated Gaussian cross row vanishes.  (In
dimension two the scale is linear in `N` and the positivity of the sizes is not used; the
hypothesis keeps the arguments of the dimension-24 statement.) -/
theorem sphereGaussianScale2_separated_tendsto {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (_hNp : ∀ k, 0 < N k) {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) :
    Tendsto (fun k => (N k:ℝ)*Real.exp (-(sphereGaussianScale2 (N k) α*δ^2))) atTop (𝓝 0) := by
  have hc := sphereGaussianScale2_tendsto hN hα
  have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    (hc.atTop_mul_const (by positivity : 0 < δ^2))
  have he : ∀ k, (N k:ℝ)*Real.exp (-(sphereGaussianScale2 (N k) α*δ^2)) =
      (4/(α*δ^2))*
      ((sphereGaussianScale2 (N k) α*δ^2)^1*Real.exp (-(sphereGaussianScale2 (N k) α*δ^2))) := by
    intro k
    have h1 : (α*δ^2)*(α*δ^2)⁻¹ = 1 := mul_inv_cancel₀ (mul_pos hα (pow_pos hδ 2)).ne'
    have hx : (N k:ℝ) = 4/(α*δ^2)*(sphereGaussianScale2 (N k) α*δ^2) := by
      rw [sphereGaussianScale2_eq_quarter]
      linear_combination (-(N k:ℝ))*h1
    linear_combination Real.exp (-(sphereGaussianScale2 (N k) α*δ^2))*hx
  simpa only [mul_zero] using (ht.const_mul _).congr (fun k => (he k).symm)

/-! ## The large-scale control by the short-range cost -/

/-- A stronger Mellin tail kernel also gives pointwise Gaussian domination.  For a nonpositive
exponent the weight `β^p` is nonincreasing, so on `(α/2, α]` it is at least its value at `α`:
`(α/2) α^p K_{cα} ≤ T_{c,p}`, with the constant `2`.  (For `p ≥ 0`, as in the dimension-24 chain,
the value at `α/2` is used and the constant is `2^(p+1)`.) -/
theorem gaussian2_le_shortRange_pointwise {c p α : ℝ} (hc : 0 < c) (hp : -1 < p) (hp0 : p ≤ 0)
    (hα : 2 ≤ α) {x y : (SphereD 2)} (hxy : x ≠ y) :
    sphereGaussianKernel2 (c*α) x y ≤
      2*α^(-(p+1))*shortRangeKernel2 c p x y := by
  have hα0 : 0 < α := by linarith
  have hi := sphereGaussianPair2_scaled_tail_integrable (c := c) (s := 2*(p+1)) hc
    (by linarith) zero_le_one hxy
  have hpe : 2*(p+1)/2-1 = p := by ring
  rw [hpe] at hi
  have hsub : Ioc (α/2) α ⊆ Ioi (1:ℝ) := fun β hβ => by
    have hb : α/2 < β := hβ.1
    change 1 < β
    linarith
  have hlow : (α/2)*α^p*sphereGaussianKernel2 (c*α) x y ≤ shortRangeKernel2 c p x y := by
    calc
      _ = (∫ β in Ioc (α/2) α, α^p*sphereGaussianKernel2 (c*α) x y) := by
        rw [setIntegral_const,Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal (by linarith)]
        simp only [smul_eq_mul]
        ring
      _ ≤ (∫ β in Ioc (α/2) α, β^p*sphereGaussianKernel2 (c*β) x y) := by
        apply setIntegral_mono_on (integrable_const _) (hi.mono_set hsub) measurableSet_Ioc
        intro β hβ
        have hβ0 : 0 < β := by linarith [hβ.1]
        have hg : sphereGaussianKernel2 (c*α) x y ≤ sphereGaussianKernel2 (c*β) x y := by
          unfold sphereGaussianKernel2
          apply Real.exp_le_exp.mpr
          have hmul := mul_le_mul_of_nonneg_left hβ.2
            (mul_nonneg hc.le (sq_nonneg (dist x y)))
          nlinarith
        exact mul_le_mul (Real.rpow_le_rpow_of_nonpos hβ0 hβ.2 hp0) hg
          (sphereGaussianKernel2_nonneg _ _ _) (Real.rpow_nonneg hβ0.le _)
      _ ≤ shortRangeKernel2 c p x y := by
        apply setIntegral_mono_set hi
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with β hβ
          exact mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hβ.le) _) (sphereGaussianKernel2_nonneg _ _ _)
        · exact hsub.eventuallyLE
  have hpow : 0 < (α/2)*α^p := mul_pos (by linarith) (Real.rpow_pos_of_pos hα0 _)
  have hinv : ((α/2)*α^p)⁻¹ = 2*α^(-(p+1)) := by
    rw [Real.rpow_neg hα0.le, Real.rpow_add_one hα0.ne']
    ring
  calc
    _ ≤ ((α/2)*α^p)⁻¹*shortRangeKernel2 c p x y := by
      rw [← div_eq_inv_mul,le_div_iff₀ hpow]
      simpa only [mul_comm] using hlow
    _ = _ := by rw [hinv]

/-- A uniform actual tail-kernel budget controls the weighted centered profile at infinity.  The
exponent of the kernel is `p = s/4 - 1/2` (it is `s/4 + (d-4)/4` in dimension `d`), in `(-1/2, 0)`
for `0 < s < 2`; the bound is `2 D α^((s/2-1)-(p+1)) = 2 D α^(s/4-3/2)`. -/
theorem sphereGaussianCenteredScaled2_large_budget_bound {N : ℕ} (hN : 0 < N)
    {s D : ℝ} (hs : 0 < s) (hs2 : s < 2) (X : (ConfigurationD 2) N)
    (hD : cellPairSum (shortRangeKernel2 (sphereGaussianDensityFactor2 N) (s/4-1/2)) X/(N:ℝ) ≤ D)
    {α : ℝ} (hα : 2 ≤ α) :
    α^(s/2-1)*sphereGaussianCenteredScaled2 α X ≤
      2*D*α^(s/4-3/2) := by
  classical
  have hα0 : 0 < α := by linarith
  let A : ℝ := 2*α^(-(s/4+1/2))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hNR : 0 < (N:ℝ) := by exact_mod_cast hN
  have hrow : (∑ i, ∑ j ∈ Finset.univ.erase i,
      sphereGaussianKernel2 (sphereGaussianScale2 N α) (X i) (X j)) ≤
      A*cellPairSum (shortRangeKernel2 (sphereGaussianDensityFactor2 N) (s/4-1/2)) X := by
    unfold cellPairSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    calc
      _ ≤ (∑ j ∈ Finset.univ.erase i, A*shortRangeKernel2
        (sphereGaussianDensityFactor2 N) (s/4-1/2) (X i) (X j)) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [sphereGaussianScale2_eq_factor]
        simpa only [A,show s/4-1/2+1=s/4+1/2 by ring] using
          gaussian2_le_shortRange_pointwise (sphereGaussianDensityFactor2_pos hN)
            (by linarith : -1 < s/4-1/2) (by linarith : s/4-1/2 ≤ 0) hα
            (X.injective.ne (Finset.mem_erase.mp hj).1.symm)
      _ ≤ (∑ j : Fin N, A*shortRangeKernel2
          (sphereGaussianDensityFactor2 N) (s/4-1/2) (X i) (X j)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ =>
          mul_nonneg hA (shortRangeKernel2_nonneg _ _ _ _))
  have hcenter : sphereGaussianCenteredScaled2 α X ≤
      A*(cellPairSum (shortRangeKernel2 (sphereGaussianDensityFactor2 N) (s/4-1/2)) X/(N:ℝ)) := by
    have hoff := sphereGaussianOffDiagonal2_eq_full_sub (sphereGaussianScale2 N α) X
    have hbg := sphereGaussianBackground2_nonneg (sphereGaussianScale2 N α)
    have he : sphereGaussianOffDiagonal2 (sphereGaussianScale2 N α) X/(N:ℝ) =
        (∑ i, ∑ j, sphereGaussianKernel2 (sphereGaussianScale2 N α) (X i) (X j))/(N:ℝ)-1 := by
      rw [hoff,sub_div,div_self hNR.ne']
    calc
      _ ≤ sphereGaussianOffDiagonal2 (sphereGaussianScale2 N α) X/(N:ℝ) := by
        rw [he]
        unfold sphereGaussianCenteredScaled2
        nlinarith [mul_nonneg hNR.le hbg]
      _ ≤ (A*cellPairSum (shortRangeKernel2 (sphereGaussianDensityFactor2 N) (s/4-1/2)) X)/(N:ℝ) :=
        div_le_div_of_nonneg_right hrow hNR.le
      _ = _ := by ring
  have hb := hcenter.trans (mul_le_mul_of_nonneg_left hD hA)
  calc
    _ ≤ α^(s/2-1)*(A*D) := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hα0.le _)
    _ = _ := by
      change α^(s/2-1)*(2*α^(-(s/4+1/2))*D) = 2*D*α^(s/4-3/2)
      rw [show α^(s/2-1)*(2*α^(-(s/4+1/2))*D) =
        (2*D)*(α^(s/2-1)*α^(-(s/4+1/2))) by ring,
        ← Real.rpow_add hα0,show s/2-1+ -(s/4+1/2)=s/4-3/2 by ring]

/-! ## The majorant and the upper bound from Gaussian budgets, for `0 < s < 2` -/

/-- An explicit majorant, with actual Gaussian budgets as its constants: `C_s |B| α^(s/4-1)` on
`(0, 2]` and `2 |D| α^(s/4-3/2)` on `(2, ∞)`. -/
def sphereGaussianUpperMajorant2 (s B D α : ℝ) : ℝ :=
  if α ≤ 2 then (Real.sqrt 2^3*(s/4)/(2^(s/4)-1))*|B| *α^(s/4-1)
  else 2*|D| *α^(s/4-3/2)

theorem sphereGaussianUpperMajorant2_nonneg {s : ℝ} (hs : 0 < s) (B D : ℝ)
    {α : ℝ} (hα : 0 < α) : 0 ≤ sphereGaussianUpperMajorant2 s B D α := by
  have h2 : 0 < (2:ℝ)^(s/4)-1 := by
    have := Real.one_lt_rpow (by norm_num : (1:ℝ) < 2) (by linarith : 0 < s/4)
    linarith
  unfold sphereGaussianUpperMajorant2
  split_ifs <;> positivity

/-- The majorant is integrable on `(0, ∞)`: at `0` because `s/4-1 > -1`, at infinity because
`s/4-3/2 < -1`, that is `s < 2`. -/
theorem sphereGaussianUpperMajorant2_integrable {s : ℝ} (hs : 0 < s) (hs2 : s < 2) (B D : ℝ) :
    IntegrableOn (sphereGaussianUpperMajorant2 s B D) (Ioi 0) := by
  have hi0 : IntegrableOn (fun α : ℝ => α^(s/4-1)) (Ioo 0 2) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0:ℝ) < 2)).mpr (by linarith)
  have hj0 : IntegrableOn (fun α : ℝ => α^(s/4-3/2)) (Ioi 2) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hi1 : IntegrableOn (fun α : ℝ => (Real.sqrt 2^3*(s/4)/(2^(s/4)-1))*|B| *α^(s/4-1)) (Ioo 0 2) := hi0.const_mul _
  have hj1 : IntegrableOn (fun α : ℝ => 2*|D| *α^(s/4-3/2)) (Ioi 2) := hj0.const_mul _
  have hi := hi1.integrable_indicator measurableSet_Ioo
  have hj := hj1.integrable_indicator measurableSet_Ioi
  apply (hi.add hj).integrableOn.congr
  have hne : ∀ᵐ α : ℝ ∂volume.restrict (Ioi 0), α ≠ 2 := by
    have hm : ({2}:Set ℝ)ᶜ ∈ ae (volume.restrict (Ioi 0)) :=
      compl_mem_ae_iff.mpr (measure_singleton (2:ℝ))
    filter_upwards [hm] with α hα
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hα
  filter_upwards [ae_restrict_mem measurableSet_Ioi,hne] with α hα hne
  dsimp only [sphereGaussianUpperMajorant2,Pi.add_apply]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [ite_eq_left hlt.le,indicator_of_mem (show α ∈ Ioo 0 2 from ⟨hα,hlt⟩),
      indicator_of_notMem (show α ∉ Ioi 2 by simpa using hlt.le),add_zero]
  · rw [ite_eq_right (not_le.mpr hgt),indicator_of_notMem (notMem_Ioo_of_ge hgt.le),
      indicator_of_mem (show α ∈ Ioi 2 from hgt),zero_add]

/-- The explicit Gaussian budgets discharge the integrable-majorant premise of the upper bridge:
a uniform small budget at `q = s/4`, a uniform short-range cost per point at `p = s/4 - 1/2` and
the theta upper bound of the full Gaussian sums at every scale give the sharp upper bound of the
normalized Riesz energy, for `0 < s < 2`. -/
theorem sphere2_riesz_upper_of_gaussian_budgets {s : ℝ} (hs : 0 < s) (hs2 : s < 2)
    {N : ℕ → ℕ} (hNt : Tendsto N atTop atTop) (hN : ∀ k, 0 < N k)
    (X : ∀ k, (ConfigurationD 2) (N k)) (B D : ℝ)
    (hB : ∀ k, sphereGaussianSmallBudget2 (s/4) (X k) ≤ B)
    (hD : ∀ k, cellPairSum (shortRangeKernel2 (sphereGaussianDensityFactor2 (N k)) (s/4-1/2))
      (X k)/(N k:ℝ) ≤ D)
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      sphereGaussianFullScaled2 α (X k) ≤ hexGaussianThetaReal2 α+ε) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
      normalizedEnergyRpow2 s (X k) ≤ sphereRieszCoefficient2 s+η := by
  apply sphere2_riesz_upper_of_full_profile hs hs2 hNt hN X
    (sphereGaussianUpperMajorant2_integrable hs hs2 B D)
    (fun α hα => sphereGaussianUpperMajorant2_nonneg hs B D hα) _ hp
  intro k α hα
  unfold sphereGaussianUpperMajorant2
  split_ifs with hsmall
  · exact sphereGaussianCenteredScaled2_small_weighted_bound (hN k) hs hs2 (X k)
      ((hB k).trans (le_abs_self B)) hα hsmall
  · exact sphereGaussianCenteredScaled2_large_budget_bound (hN k) hs hs2 (X k)
      ((hD k).trans (le_abs_self D)) (le_of_not_ge hsmall)

/-! ## Midpoint grids and boundary-corrected grids of lattice patches -/

/-- Concrete `n²` midpoint coordinates for a finite patch of the triangular lattice. -/
def hexMidpointGrid2 (n : ℕ) (hn : 0 < n) (u : Fin 2 → Fin n) : UnitCube 2 :=
  ⟨fun i => ((u i:ℝ)+1/2)/(n:ℝ), by
    intro i
    have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
    have hu : (u i:ℝ)+1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt (u i).isLt
    exact ⟨by positivity, (div_le_one hnR).mpr (by linarith)⟩⟩

/-- The lattice points with integer coordinates in `{0, …, n-1}²`. -/
def hexGridLattice2 (n : ℕ) : (Fin 2 → Fin n) ↪ hexLattice where
  toFun u := ⟨hexIntegerPoint (fun i => (u i:ℤ)), (hexLattice_mem_iff _).mpr ⟨_,rfl⟩⟩
  inj' := by
    intro u w h
    have h' := congrArg (fun z : hexLattice => WithLp.ofLp (z : HexAmbient)) h
    have hc := hexMap_injective h'
    funext i
    apply Fin.ext
    have hi : ((u i).val : ℝ) = ((w i).val : ℝ) := by simpa using congrFun hc i
    exact_mod_cast hi

theorem hexMidpointGrid2_card (n : ℕ) : Fintype.card (Fin 2 → Fin n) = n^2 := by
  simp only [Fintype.card_fun, Fintype.card_fin]

theorem hexMidpointGrid2_flat_distance (n : ℕ) (hn : 0 < n) (u w : Fin 2 → Fin n) :
    dist (WithLp.toLp 2 (hexMap (hexMidpointGrid2 n hn u)) : HexAmbient)
      (WithLp.toLp 2 (hexMap (hexMidpointGrid2 n hn w))) =
      (n:ℝ)⁻¹*‖((hexGridLattice2 n w-hexGridLattice2 n u : hexLattice) : HexAmbient)‖ := by
  have he : (hexMidpointGrid2 n hn u : Fin 2 → ℝ)-hexMidpointGrid2 n hn w =
      (n:ℝ)⁻¹ • (fun i => (u i:ℝ)-(w i:ℝ)) := by
    funext i
    simp only [hexMidpointGrid2,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv]
    ring
  rw [dist_eq_norm,← WithLp.toLp_sub,← map_sub,he,map_smul,WithLp.toLp_smul,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)⁻¹)]
  congr 1
  change ‖WithLp.toLp 2 (hexMap (fun i => (u i:ℝ)-(w i:ℝ)))‖ =
    ‖hexIntegerPoint (fun i => (w i:ℤ))-hexIntegerPoint (fun i => (u i:ℤ))‖
  rw [norm_sub_rev]
  rw [hexIntegerPoint,hexIntegerPoint,← WithLp.toLp_sub,← map_sub]
  simp only [Int.cast_natCast]
  rfl

/-- Actual sphere midpoint patches have a theta row bound uniform in the refinement n. -/
theorem equalAreaHexMidpoint2_gaussian_rows {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
      (v c : Fin 2 → ℝ), ‖v‖ ≤ ρ → ∀ (hc : c ∈ UnitCube 2)
      (ε : ℝ) (hε : 0 < ε), ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) (n : ℕ) (hn : 0 < n)
      (t : ℝ), 0 < t → ∀ u : Fin 2 → Fin n,
      (∑ w ∈ Finset.univ.erase u, sphereGaussianKernel2 t
        (equalAreaHexCubeEmbedding2 g v c ε hε hc hsmall (hexMidpointGrid2 n hn u))
        (equalAreaHexCubeEmbedding2 g v c ε hε hc hsmall (hexMidpointGrid2 n hn w))) ≤
      hexGaussianThetaReal2 (t*((1-η)*ε/(n:ℝ))^2/Real.pi)-1 := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := equalAreaHexPatch_gaussian_row_uniform hη hη1
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro g v c hv hc ε hε hs hsmall n hn t ht u
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  simpa only [div_eq_mul_inv] using hb g v c hv hc ε hε hs hsmall (hexGridLattice2 n)
    (hexMidpointGrid2 n hn) (n:ℝ)⁻¹ (inv_pos.mpr hnR)
    (hexMidpointGrid2_flat_distance n hn) t ht u


/-- The actual flat derivative has a positive norm, with no additional hypothesis. -/
theorem equalAreaFlatDerivative2_norm_pos : 0 < ‖equalAreaFlatDerivative2‖ := by
  by_contra h
  have hz : equalAreaFlatDerivative2 = 0 := norm_eq_zero.mp
    (le_antisymm (le_of_not_gt h) (norm_nonneg _))
  have hc := equalAreaHex_distance_controls_coordinates (fun _ : Fin 2 => (1 : ℝ)) 0
  rw [← equalAreaFlatDerivative2_dist, hz] at hc
  norm_num at hc

/-- Boundary corrections retain control by their distinct integer labels. -/
theorem correctedRule2_label_sub_le {n : ℕ} (hn : 8 ≤ n) (u w : NodeIndex n) :
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

/-- The lattice points whose integer coordinates are the midpoint labels of the nodes of the
boundary-corrected rule. -/
def hexCorrectedLabel2 (n : ℕ) (hn : 8 ≤ n) :
    (Fin 2 → NodeIndex n) ↪ hexLattice where
  toFun u := ⟨hexIntegerPoint (fun i => (midpointLabel n (u i):ℤ)),
    (hexLattice_mem_iff _).mpr ⟨_,rfl⟩⟩
  inj' := by
    intro u w h
    have hc := hexMap_injective (congrArg (fun z : hexLattice => WithLp.ofLp (z : HexAmbient)) h)
    funext i
    apply midpointLabel_injective hn
    have hi : (midpointLabel n (u i):ℝ) = (midpointLabel n (w i):ℝ) := by
      simpa using congrFun hc i
    exact_mod_cast hi

/-- All boundary-corrected nodes admit one lattice-label distance bound. -/
theorem hexCorrectedLabel2_norm_le {n : ℕ} (hn : 8 ≤ n)
    (u w : Fin 2 → NodeIndex n) :
    ‖((hexCorrectedLabel2 n hn w-hexCorrectedLabel2 n hn u : hexLattice) : HexAmbient)‖ ≤
      (2*(n:ℝ)*‖equalAreaFlatDerivative2‖)*‖cubeNode 2 n u-cubeNode 2 n w‖ := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  let z : Fin 2 → ℝ := fun i => (midpointLabel n (u i):ℝ)-(midpointLabel n (w i):ℝ)
  have hz : ‖z‖ ≤ (2*(n:ℝ))*‖cubeNode 2 n u-cubeNode 2 n w‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    have h := correctedRule2_label_sub_le hn (u i) (w i)
    have he : |unscaledRuleNode n (u i)-unscaledRuleNode n (w i)| =
        (n:ℝ)*|cubeNode 2 n u i-cubeNode 2 n w i| := by
      simp only [cubeNode,ruleNode,← sub_div,abs_div,abs_of_pos hnR]
      field_simp
    rw [he] at h
    calc ‖z i‖ ≤ 2*((n:ℝ)*|cubeNode 2 n u i-cubeNode 2 n w i|) := h
      _ ≤ (2*(n:ℝ))*‖cubeNode 2 n u-cubeNode 2 n w‖ := by
        have hi := norm_le_pi_norm (cubeNode 2 n u-cubeNode 2 n w) i
        simp only [Pi.sub_apply,Real.norm_eq_abs] at hi
        nlinarith
  have he : ‖((hexCorrectedLabel2 n hn w-hexCorrectedLabel2 n hn u : hexLattice) : HexAmbient)‖ =
      ‖equalAreaFlatDerivative2 z‖ := by
    conv_rhs =>
      rw [← dist_zero_right, ← map_zero equalAreaFlatDerivative2,
        equalAreaFlatDerivative2_dist, map_zero, WithLp.toLp_zero, dist_zero_right]
    change ‖hexIntegerPoint (fun i => (midpointLabel n (w i):ℤ))-
      hexIntegerPoint (fun i => (midpointLabel n (u i):ℤ))‖ = ‖WithLp.toLp 2 (hexMap z)‖
    rw [norm_sub_rev,hexIntegerPoint,hexIntegerPoint,← WithLp.toLp_sub,← map_sub]
    rfl
  rw [he]
  calc
    _ ≤ ‖equalAreaFlatDerivative2‖*‖z‖ := equalAreaFlatDerivative2.le_opNorm z
    _ ≤ ‖equalAreaFlatDerivative2‖*((2*(n:ℝ))*‖cubeNode 2 n u-cubeNode 2 n w‖) :=
      mul_le_mul_of_nonneg_left hz (norm_nonneg _)
    _ = _ := by ring

/-- The actual boundary-corrected foreground rows have a uniform Gaussian theta bound. -/
theorem equalAreaHexCorrected2_gaussian_row {n : ℕ} (hn : 8 ≤ n)
    (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (v c : Fin 2 → ℝ)
    (hc : c ∈ UnitCube 2) {ε : ℝ} (hε : 0 < ε)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) {L t : ℝ} (hL : 0 < L) (ht : 0 < t)
    (hlower : ∀ x ∈ UnitCube 2, ∀ y ∈ UnitCube 2,
      L*‖x-y‖ ≤ dist (equalAreaNormalizedHexPatch g v c ε x) (equalAreaNormalizedHexPatch g v c ε y))
    (u : Fin 2 → NodeIndex n) :
    (∑ w ∈ Finset.univ.erase u, sphereGaussianKernel2 t
      (equalAreaHexCubeEmbedding2 g v c ε hε hc hsmall
        ⟨cubeNode 2 n u,fun i => ⟨(cubeNode_mem_open 2 n hn u i).1.le,(cubeNode_mem_open 2 n hn u i).2.le⟩⟩)
      (equalAreaHexCubeEmbedding2 g v c ε hε hc hsmall
        ⟨cubeNode 2 n w,fun i => ⟨(cubeNode_mem_open 2 n hn w i).1.le,(cubeNode_mem_open 2 n hn w i).2.le⟩⟩)) ≤
    hexGaussianThetaReal2 (t*(ε*L/(2*(n:ℝ)*‖equalAreaFlatDerivative2‖))^2/Real.pi)-1 := by
  have hflat := equalAreaFlatDerivative2_norm_pos
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  apply hexPatchGaussian_row_le (hexCorrectedLabel2 n hn) _ (by positivity) ht _ u
  intro i j
  change _ ≤ dist (equalAreaHexPatch g v c ε (cubeNode 2 n i))
    (equalAreaHexPatch g v c ε (cubeNode 2 n j))
  rw [equalAreaHexPatch_dist_eq g v c _ _ hε]
  have hi : cubeNode 2 n i ∈ UnitCube 2 := fun k => ⟨(cubeNode_mem_open 2 n hn i k).1.le,(cubeNode_mem_open 2 n hn i k).2.le⟩
  have hj : cubeNode 2 n j ∈ UnitCube 2 := fun k => ⟨(cubeNode_mem_open 2 n hn j k).1.le,(cubeNode_mem_open 2 n hn j k).2.le⟩
  have hgeom := hlower _ hi _ hj
  have hlabel := hexCorrectedLabel2_norm_le hn i j
  have hden : 0 < 2*(n:ℝ)*‖equalAreaFlatDerivative2‖ := by positivity
  have hdiv : ‖((hexCorrectedLabel2 n hn j-hexCorrectedLabel2 n hn i : hexLattice) :
      HexAmbient)‖/(2*(n:ℝ)*‖equalAreaFlatDerivative2‖) ≤ ‖cubeNode 2 n i-cubeNode 2 n j‖ :=
    (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hlabel)
  calc
    _ = ε*L*(‖((hexCorrectedLabel2 n hn j-hexCorrectedLabel2 n hn i : hexLattice) : HexAmbient)‖ /
      (2*(n:ℝ)*‖equalAreaFlatDerivative2‖)) := by ring
    _ ≤ ε*L*‖cubeNode 2 n i-cubeNode 2 n j‖ := mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ ≤ _ := by nlinarith


end SphericalRiesz
end
end
