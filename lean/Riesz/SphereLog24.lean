import Riesz.SphereRieszNeg24
import Riesz.SphereLogEnergy8
import Riesz.SphereLogCoefficient8
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Riesz.SphereLogConstPair8

/-! The logarithmic energy on S²⁴: Mellin form, universal lower bound and coefficient (stage LOG of
the S²⁴ chain; dimension-24 ports of the S⁸ modules).

The module has four parts.

* `SphereLogEnergy24`: the Frullani and Mellin form of the logarithmic energy,
  `(E_log - W N² + (N/24) log N)/N = ½ (J_N + κ - log π + (1/12) log A₂₄)` with
  `J_N = ∫ α⁻¹ (F_N(α) + 1_{(0,1)}(α)) dα`.
* `SphereLogLower24`: the Leech logarithmic profile and the universal lower bound by Fatou, under
  the sharp Gaussian profile of the sphere (from all-scale Leech contact certificates, stage
  G24).
* `SphereLogCoefficient24`: the coefficient `C_log = ½ Re Z'(0) + (1/24) log A₂₄`, where
  `Z(u) = ζ_Λ(2u)` is written through a continuation which is differentiable at `0` (the value
  of `π^u Λ(u)/Γ(u)` at `u = 0` in Mathlib is `0`, not the value `-1` of the continuation).
* `SphereLogConstPair24`: `W` is the actual double integral of `-log |x - y|`, and the lower
  bound in the form of the conjecture.

The dimension-free lemmas (`frullani_exp`, `logGaussianConst`, …) are imported from the S⁸
modules.  The upper bound is in `Riesz.SphereLogUpper24`. -/

section

/-! Logarithmic energy on the actual unit S²⁴ (stage LOG, Mellin layer).

Frullani's integral gives `-log d = ½ ∫₀^∞ t⁻¹ (e^(-t d²) - e^(-t)) dt` for `d > 0` (dimension
free, `Riesz.SphereLogEnergy8`). Summing over ordered pairs of distinct points and subtracting the
same integral of the actual Gaussian background `B` of S²⁴ gives, with the full neutralized defect
`D(t) = Σ_{i,j} e^(-t|x_i-x_j|²) - N² B(t)`,
`2 (E_log - W N²) = ∫ t⁻¹ (D(t) - N (1 - e^(-t))) dt`. In density scale `t = c_N α`
(`c_N = π (N/A₂₄)^(1/12)`) and with `κ = ∫ α⁻¹ (e^(-α) - 1_{(0,1)}(α)) dα`, this is
`(E_log - W N² + (N/24) log N)/N = ½ (J_N + κ - log π + (1/12) log A₂₄)`,
`J_N = ∫ α⁻¹ (F_N(α) + 1_{(0,1)}(α)) dα`, with the same centred profile `F_N` as for the Riesz
exponents. The `-(N/24) log N` term of the logarithmic asymptotics comes from `log c_N`.

The last part records the integrability of the integrand of `J_N` on the three ranges `(0,w]`,
`(w,A]`, `(A,∞)` (`0 < w ≤ 1 ≤ A`) in the form needed for an upper bound of `J_N`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SphericalRiesz

theorem sphereGaussianPair24_frullani {N : ℕ} (X : ConfigurationD 24 N) {i j : Fin N}
    (hij : i ≠ j) :
    IntegrableOn (fun t : ℝ => t⁻¹*(sphereGaussianKernel24 t (X i) (X j)-Real.exp (-t))) (Ioi 0) ∧
    (∫ t in Ioi 0, t⁻¹*(sphereGaussianKernel24 t (X i) (X j)-Real.exp (-t))) =
      2*(-Real.log (dist (X i) (X j))) := by
  have h := gaussianPair_frullani (offDiagonal_dist_posD X hij)
  have he : (fun t : ℝ => t⁻¹*(sphereGaussianKernel24 t (X i) (X j)-Real.exp (-t))) =
      (fun t : ℝ => t⁻¹*(Real.exp (-((dist (X i) (X j))^2*t))-Real.exp (-t))) := by
    funext t
    simp only [sphereGaussianKernel24, mul_comm t]
  rw [he]
  exact h

theorem sphereGaussianOffDiagonal24_frullani {N : ℕ} (X : ConfigurationD 24 N) :
    IntegrableOn (fun t : ℝ => t⁻¹*(sphereGaussianOffDiagonal24 t X-((N:ℝ)^2-N)*Real.exp (-t)))
      (Ioi 0) ∧
    (∫ t in Ioi 0, t⁻¹*(sphereGaussianOffDiagonal24 t X-((N:ℝ)^2-N)*Real.exp (-t))) =
      2*energyLogD X := by
  have hpt : ∀ t : ℝ, t⁻¹*(sphereGaussianOffDiagonal24 t X-((N:ℝ)^2-N)*Real.exp (-t)) =
      ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
        t⁻¹*(sphereGaussianKernel24 t (X i) (X j)-Real.exp (-t)) := by
    intro t
    unfold sphereGaussianOffDiagonal24
    have hc : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, Real.exp (-t) = ((N:ℝ)-1)*Real.exp (-t) := by
      intro i
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, hc, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hrow (i : Fin N) : IntegrableOn (fun t : ℝ => ∑ j ∈ Finset.univ.erase i,
      t⁻¹*(sphereGaussianKernel24 t (X i) (X j)-Real.exp (-t))) (Ioi 0) :=
    integrable_finsetSum _ (fun j hj =>
      (sphereGaussianPair24_frullani X (Finset.mem_erase.mp hj).1.symm).1)
  have hfun : (fun t : ℝ => t⁻¹*(sphereGaussianOffDiagonal24 t X-((N:ℝ)^2-N)*Real.exp (-t))) =
      fun t : ℝ => ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
        t⁻¹*(sphereGaussianKernel24 t (X i) (X j)-Real.exp (-t)) := funext hpt
  rw [hfun]
  refine ⟨integrable_finsetSum _ (fun i _ => hrow i), ?_⟩
  rw [integral_finsetSum _ (fun i _ => hrow i)]
  unfold energyLogD
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j hj =>
    (sphereGaussianPair24_frullani X (Finset.mem_erase.mp hj).1.symm).1), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact (sphereGaussianPair24_frullani X (Finset.mem_erase.mp hj).1.symm).2

theorem sphereGaussianBackground24_log_integrable :
    IntegrableOn (fun t : ℝ => t⁻¹*(sphereGaussianBackground24 t-Real.exp (-t))) (Ioi 0) := by
  have hcont : ContinuousOn (fun t : ℝ => t⁻¹*(sphereGaussianBackground24 t-Real.exp (-t)))
      (Ioi 0) :=
    (continuousOn_inv₀.mono (fun t ht => ne_of_gt ht)).mul
      ((sphereGaussianBackground24_continuousOn.mono Ioi_subset_Ici_self).sub
        (by fun_prop : Continuous (fun t : ℝ => Real.exp (-t))).continuousOn)
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  apply IntegrableOn.union
  · refine Integrable.mono' (integrableOn_const (C := (5:ℝ)) (by simp)) ((hcont.mono
      Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : (0:ℝ) < t := ht.1
    have h1 := sphereGaussianBackground24_le_one ht0.le
    have h2 := sphereGaussianBackground24_ge_one_sub ht0.le
    obtain ⟨h3, h4⟩ := one_sub_exp_neg_bounds ht0.le
    have h5 : |sphereGaussianBackground24 t-Real.exp (-t)| ≤ 5*t := by
      rw [abs_le]
      constructor
      · linarith [min_le_left t 1]
      · linarith [min_le_left t 1]
    rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos ht0]
    calc t⁻¹ * |sphereGaussianBackground24 t-Real.exp (-t)| ≤ t⁻¹*(5*t) :=
          mul_le_mul_of_nonneg_left h5 (inv_nonneg.mpr ht0.le)
      _ = 5 := by field_simp
  · have hdom : IntegrableOn
        (fun t : ℝ => (316234143225/8192:ℝ)*t^(-2:ℝ)+Real.exp (-1*t)) (Ioi 1) :=
      ((integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul _).add
        (exp_neg_integrableOn_Ioi 1 one_pos)
    refine Integrable.mono' hdom ((hcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1:ℝ) < t := ht
    have ht0 : (0:ℝ) < t := by linarith
    have hB0 := sphereGaussianBackground24_nonneg t
    have hB := (sphereGaussianBackground24_min_bound ht0).trans (min_le_right _ _)
    have hE := Real.exp_pos (-t)
    have hinv : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht1.le
    have ht212 : t^2 ≤ t^12 := pow_le_pow_right₀ ht1.le (by norm_num)
    have hq : (316234143225/8192:ℝ)/t^12 ≤ (316234143225/8192:ℝ)*t^(-2:ℝ) := by
      rw [Real.rpow_neg ht0.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast,
        ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) ht212
    have hBt : sphereGaussianBackground24 t*t⁻¹ ≤ sphereGaussianBackground24 t := by
      have := mul_le_mul_of_nonneg_left hinv hB0
      rwa [mul_one] at this
    have hEt : t⁻¹*Real.exp (-t) ≤ Real.exp (-t) := by
      have := mul_le_mul_of_nonneg_right hinv hE.le
      rwa [one_mul] at this
    rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos ht0]
    calc t⁻¹ * |sphereGaussianBackground24 t-Real.exp (-t)|
        ≤ t⁻¹*(sphereGaussianBackground24 t+Real.exp (-t)) := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ht0.le)
          rw [abs_le]; constructor <;> linarith
      _ = sphereGaussianBackground24 t*t⁻¹+t⁻¹*Real.exp (-t) := by ring
      _ ≤ (316234143225/8192:ℝ)*t^(-2:ℝ)+Real.exp (-1*t) := by
          rw [neg_one_mul]
          linarith

/-- The continuous logarithmic energy constant of the actual uniform S²⁴ (Mellin form). -/
def sphereLogConst24 : ℝ :=
  (1/2)*∫ t in Ioi 0, t⁻¹*(sphereGaussianBackground24 t-Real.exp (-t))

theorem sphereGaussianFullDefect24_log_mellin {N : ℕ} (X : ConfigurationD 24 N) :
    IntegrableOn (fun t : ℝ => t⁻¹*(sphereGaussianFullDefect24 t X-(N:ℝ)*(1-Real.exp (-t))))
      (Ioi 0) ∧
    (∫ t in Ioi 0, t⁻¹*(sphereGaussianFullDefect24 t X-(N:ℝ)*(1-Real.exp (-t)))) =
      2*(energyLogD X-sphereLogConst24*(N:ℝ)^2) := by
  obtain ⟨h1, h2⟩ := sphereGaussianOffDiagonal24_frullani X
  have hb := sphereGaussianBackground24_log_integrable.const_mul ((N:ℝ)^2)
  have hpt : ∀ t : ℝ, t⁻¹*(sphereGaussianFullDefect24 t X-(N:ℝ)*(1-Real.exp (-t))) =
      t⁻¹*(sphereGaussianOffDiagonal24 t X-((N:ℝ)^2-N)*Real.exp (-t))-
        (N:ℝ)^2*(t⁻¹*(sphereGaussianBackground24 t-Real.exp (-t))) := by
    intro t
    unfold sphereGaussianFullDefect24
    rw [sphereGaussianSum24_diagonal]
    ring
  have hfun : (fun t : ℝ => t⁻¹*(sphereGaussianFullDefect24 t X-(N:ℝ)*(1-Real.exp (-t)))) =
      fun t : ℝ => t⁻¹*(sphereGaussianOffDiagonal24 t X-((N:ℝ)^2-N)*Real.exp (-t))-
        (N:ℝ)^2*(t⁻¹*(sphereGaussianBackground24 t-Real.exp (-t))) := funext hpt
  rw [hfun]
  refine ⟨h1.sub hb, ?_⟩
  rw [integral_sub h1 hb, h2, integral_const_mul]
  unfold sphereLogConst24
  ring

/-- The logarithmic profile integral `J_N = ∫ α⁻¹ (F_N(α) + 1_{(0,1)}(α)) dα`. -/
def sphereLogProfileIntegral24 {N : ℕ} (X : ConfigurationD 24 N) : ℝ :=
  ∫ α in Ioi 0, α⁻¹*(sphereGaussianCenteredScaled24 α X+(Ioo (0:ℝ) 1).indicator 1 α)

/-- The normalized logarithmic energy `(E_log - W N² + (N/24) log N)/N`. -/
def normalizedEnergyLog24 {N : ℕ} (X : ConfigurationD 24 N) : ℝ :=
  (energyLogD X-sphereLogConst24*(N:ℝ)^2+(N:ℝ)/24*Real.log N)/(N:ℝ)

theorem sphereGaussianCenteredScaled24_log_integrable {N : ℕ} (hN : 0 < N)
    (X : ConfigurationD 24 N) :
    IntegrableOn (fun α : ℝ =>
      α⁻¹*(sphereGaussianCenteredScaled24 α X+(Ioo (0:ℝ) 1).indicator 1 α)) (Ioi 0) := by
  have hc := sphereGaussianDensityFactor24_pos hN
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 := (inv_mellin_scale hc (sphereGaussianFullDefect24_log_mellin X).1).1
  have h2 := logGaussian_integrable hc
  have h3 : IntegrableOn (fun α : ℝ => (N:ℝ)⁻¹*(α⁻¹*(sphereGaussianFullDefect24
      (sphereGaussianDensityFactor24 N*α) X-
        (N:ℝ)*(1-Real.exp (-(sphereGaussianDensityFactor24 N*α))))))
      (Ioi 0) := h1.const_mul _
  refine (h3.sub h2).congr_fun (fun α _ => ?_) measurableSet_Ioi
  simp only [Pi.sub_apply]
  rw [sphereGaussianFullDefect24_scaled hN]
  field_simp
  ring

/-- Density-scale Mellin form of the normalized logarithmic energy. -/
theorem normalizedEnergyLog24_gaussian_mellin {N : ℕ} (hN : 0 < N) (X : ConfigurationD 24 N) :
    normalizedEnergyLog24 X = (1/2)*(sphereLogProfileIntegral24 X+logGaussianConst-
      Real.log Real.pi+(1/12)*Real.log ((sphereAreaD 24).real univ)) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hA : 0 < (sphereAreaD 24).real univ := sphereAreaD_univ_pos 24
  have hc := sphereGaussianDensityFactor24_pos hN
  set c := sphereGaussianDensityFactor24 N with hcdef
  obtain ⟨hm1, hm2⟩ := sphereGaussianFullDefect24_log_mellin X
  obtain ⟨hs1, hs2⟩ := inv_mellin_scale hc hm1
  rw [hm2] at hs2
  have hpt : ∀ α : ℝ, α⁻¹*(sphereGaussianFullDefect24 (c*α) X-(N:ℝ)*(1-Real.exp (-(c*α)))) =
      (N:ℝ)*(α⁻¹*(sphereGaussianCenteredScaled24 α X+(Ioo (0:ℝ) 1).indicator 1 α))+
        (N:ℝ)*(α⁻¹*(Real.exp (-(c*α))-(Ioo (0:ℝ) 1).indicator 1 α)) := by
    intro α
    rw [hcdef, sphereGaussianFullDefect24_scaled hN]
    ring
  simp_rw [hpt] at hs2
  rw [integral_add ((sphereGaussianCenteredScaled24_log_integrable hN X).const_mul _)
    ((logGaussian_integrable hc).const_mul _), integral_const_mul, integral_const_mul,
    logGaussian_integral hc] at hs2
  have hlogc : Real.log c =
      Real.log Real.pi+(1/12)*(Real.log N-Real.log ((sphereAreaD 24).real univ)) := by
    rw [hcdef]
    unfold sphereGaussianDensityFactor24 sphereGaussianScale24
    rw [mul_one, Real.log_mul Real.pi_pos.ne' (by positivity), Real.log_rpow (by positivity),
      Real.log_div hNR.ne' hA.ne']
  unfold normalizedEnergyLog24
  unfold sphereLogProfileIntegral24
  rw [hlogc] at hs2
  rw [div_eq_iff hNR.ne']
  linear_combination (-1/2:ℝ)*hs2

/-! ### The three ranges `(0,w]`, `(w,A]`, `(A,∞)` of the profile integral

These statements have no counterpart in the `S⁸` file. For `0 < w ≤ 1 ≤ A` the integrand of
`J_N` is `α⁻¹ (F_N(α) + 1) ≥ 0` on the macroscopic end `(0,w]` (up to the point `α = 1`),
`α⁻¹ (F_N(α) + 1_{(0,1)}(α))` on the window `(w,A]`, and `α⁻¹ F_N(α)` on the tail `(A,∞)`. -/

/-- The integrand of `J_N` is integrable on every window `(w,A]`, `0 ≤ w`. -/
theorem sphereGaussianCenteredScaled24_log_integrableOn_Ioc {N : ℕ} (hN : 0 < N)
    (X : ConfigurationD 24 N) {w : ℝ} (hw : 0 ≤ w) (A : ℝ) :
    IntegrableOn (fun α : ℝ =>
      α⁻¹*(sphereGaussianCenteredScaled24 α X+(Ioo (0:ℝ) 1).indicator 1 α)) (Ioc w A) :=
  (sphereGaussianCenteredScaled24_log_integrable hN X).mono_set
    (fun α hα => (lt_of_le_of_lt hw hα.1 : (0:ℝ) < α))

/-- The integrand of `J_N` is integrable on every tail `(A,∞)`, `0 ≤ A`. -/
theorem sphereGaussianCenteredScaled24_log_integrableOn_Ioi {N : ℕ} (hN : 0 < N)
    (X : ConfigurationD 24 N) {A : ℝ} (hA : 0 ≤ A) :
    IntegrableOn (fun α : ℝ =>
      α⁻¹*(sphereGaussianCenteredScaled24 α X+(Ioo (0:ℝ) 1).indicator 1 α)) (Ioi A) :=
  (sphereGaussianCenteredScaled24_log_integrable hN X).mono_set (Ioi_subset_Ioi hA)

/-- On the macroscopic end `(0,w]`, `w ≤ 1`, the integrand of `J_N` is `α⁻¹ (F_N(α) + 1)`. -/
theorem sphereGaussianCenteredScaled24_log_small_integrable {N : ℕ} (hN : 0 < N)
    (X : ConfigurationD 24 N) {w : ℝ} (hw1 : w ≤ 1) :
    IntegrableOn (fun α : ℝ => α⁻¹*(sphereGaussianCenteredScaled24 α X+1)) (Ioc 0 w) := by
  have hne : ∀ᵐ α : ℝ ∂volume.restrict (Ioc 0 w), α ≠ 1 := by
    apply Filter.Eventually.mono (compl_mem_ae_iff.mpr (measure_singleton (1 : ℝ)) :
      ∀ᵐ α : ℝ ∂volume.restrict (Ioc 0 w), α ∈ ({1} : Set ℝ)ᶜ)
    intro α hα
    simpa using hα
  refine ((sphereGaussianCenteredScaled24_log_integrable hN X).mono_set
    Ioc_subset_Ioi_self).congr_fun_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc, hne] with α hα hα1
  have hmem : α ∈ Ioo (0:ℝ) 1 := ⟨hα.1, lt_of_le_of_ne (hα.2.trans hw1) hα1⟩
  simp only [indicator_of_mem hmem, Pi.one_apply]

/-- On the tail `(A,∞)`, `1 ≤ A`, the integrand of `J_N` is `α⁻¹ F_N(α)`. -/
theorem sphereGaussianCenteredScaled24_log_large_integrable {N : ℕ} (hN : 0 < N)
    (X : ConfigurationD 24 N) {A : ℝ} (hA : 1 ≤ A) :
    IntegrableOn (fun α : ℝ => α⁻¹*sphereGaussianCenteredScaled24 α X) (Ioi A) := by
  refine ((sphereGaussianCenteredScaled24_log_integrable hN X).mono_set
    (Ioi_subset_Ioi (by linarith : (0:ℝ) ≤ A))).congr_fun (fun α hα => ?_) measurableSet_Ioi
  have hα1 : (1:ℝ) ≤ α := hA.trans (le_of_lt hα)
  have hnot : α ∉ Ioo (0:ℝ) 1 := notMem_Ioo_of_ge hα1
  simp only [indicator_of_notMem hnot, add_zero]

/-- The macroscopic end of `J_N` is nonnegative. -/
theorem sphereGaussianCenteredScaled24_log_small_nonneg {N : ℕ} (hN : 0 < N)
    (X : ConfigurationD 24 N) (w : ℝ) :
    0 ≤ ∫ α in Ioc (0:ℝ) w, α⁻¹*(sphereGaussianCenteredScaled24 α X+1) := by
  apply setIntegral_nonneg measurableSet_Ioc
  intro α hα
  exact mul_nonneg (inv_nonneg.mpr hα.1.le)
    (sphereGaussianCenteredScaled24_add_one_nonneg hN hα.1.le X)

/-- Splitting of `J_N` at `0 < w ≤ 1 ≤ A` into the macroscopic end, the window and the tail. -/
theorem sphereLogProfileIntegral24_split {N : ℕ} (hN : 0 < N) (X : ConfigurationD 24 N)
    {w A : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) (hA : 1 ≤ A) :
    sphereLogProfileIntegral24 X =
      (∫ α in Ioc 0 w, α⁻¹*(sphereGaussianCenteredScaled24 α X+1))+
      (∫ α in Ioc w A,
        α⁻¹*(sphereGaussianCenteredScaled24 α X+(Ioo (0:ℝ) 1).indicator 1 α))+
      ∫ α in Ioi A, α⁻¹*sphereGaussianCenteredScaled24 α X := by
  have hsplit := setIntegral_Ioi_zero_split
    (sphereGaussianCenteredScaled24_log_integrable hN X) hw (hw1.trans hA)
  have hne : ∀ᵐ α : ℝ ∂volume.restrict (Ioc 0 w), α ≠ 1 := by
    apply Filter.Eventually.mono (compl_mem_ae_iff.mpr (measure_singleton (1 : ℝ)) :
      ∀ᵐ α : ℝ ∂volume.restrict (Ioc 0 w), α ∈ ({1} : Set ℝ)ᶜ)
    intro α hα
    simpa using hα
  have h1 : (∫ α in Ioc 0 w,
      α⁻¹*(sphereGaussianCenteredScaled24 α X+(Ioo (0:ℝ) 1).indicator 1 α)) =
      ∫ α in Ioc 0 w, α⁻¹*(sphereGaussianCenteredScaled24 α X+1) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hne] with α hα hα1
    have hmem : α ∈ Ioo (0:ℝ) 1 := ⟨hα.1, lt_of_le_of_ne (hα.2.trans hw1) hα1⟩
    simp only [indicator_of_mem hmem, Pi.one_apply]
  have h3 : (∫ α in Ioi A,
      α⁻¹*(sphereGaussianCenteredScaled24 α X+(Ioo (0:ℝ) 1).indicator 1 α)) =
      ∫ α in Ioi A, α⁻¹*sphereGaussianCenteredScaled24 α X := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro α hα
    have hα1 : (1:ℝ) ≤ α := hA.trans (le_of_lt hα)
    have hnot : α ∉ Ioo (0:ℝ) 1 := notMem_Ioo_of_ge hα1
    simp only [indicator_of_notMem hnot, add_zero]
  rw [← h1, ← h3]
  exact hsplit

/-- For `-2 < s < 0` and `w ≤ 1` the macroscopic end of the logarithmic profile integral is at
most the macroscopic end of exponent `s`: the weight `α^(s/2-1)` dominates `α⁻¹` on `(0,1]`. -/
theorem sphereGaussianCenteredScaled24_log_macroEnd_le_neg {s : ℝ} (hs : -2 < s) (hs0 : s < 0)
    {N : ℕ} (hN : 0 < N) (X : ConfigurationD 24 N) {w : ℝ} (hw1 : w ≤ 1) :
    (∫ α in Ioc (0:ℝ) w, α⁻¹*(sphereGaussianCenteredScaled24 α X+1)) ≤
      ∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled24 α X+1) := by
  apply setIntegral_mono_on (sphereGaussianCenteredScaled24_log_small_integrable hN X hw1)
    ((sphereGaussianCenteredScaled24_neg_integrable hs hs0 hN X).mono_set Ioc_subset_Ioi_self)
    measurableSet_Ioc
  intro α hα
  have hα0 : (0:ℝ) < α := hα.1
  have hle : α^(-1:ℝ) ≤ α^(s/2-1) :=
    Real.rpow_le_rpow_of_exponent_ge hα0 (hα.2.trans hw1) (by linarith)
  rw [Real.rpow_neg_one] at hle
  exact mul_le_mul_of_nonneg_right hle
    (sphereGaussianCenteredScaled24_add_one_nonneg hN hα0.le X)

end SphericalRiesz
end
end

section

/-! The universal sharp lower bound for the logarithmic energy on S²⁴ (stage LOG, first half).

With `J_N = ∫ α⁻¹ (F_N(α) + 1_{(0,1)}(α)) dα` and the Leech profile
`g(α) = α⁻¹ (Θ(α) - α⁻¹² - 1 + 1_{(0,1)}(α))` (integrable: it is the real part of
`α⁻¹ f_modif(α)` of the strong FE pair of weight 12 minus `1_{(1,∞)} α⁻¹³`), Fatou with the
majorant `1_{(1,∞)} α⁻¹³` (from `F ≥ -min(1, α⁻¹²)`) and `F + 1 ≥ 0` on `(0,1)` gives
`liminf J_N ≥ ∫ g` uniformly over configurations. Hence, under the sharp sphere Gaussian
profile (stage G24: all-scale Leech contact certificates), for every `η > 0` and all large `N`
and every configuration,
`(E_log - W N² + (N/24) log N)/N ≥ C_log - η`,
`C_log = ½ (∫ g + κ - log π + (1/12) log A₂₄)`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SphericalRiesz

/-- The weighted logarithmic Leech profile `α⁻¹ (Θ(α) - α⁻¹² - 1 + 1_{(0,1)}(α))`. -/
def leechGaussianLogProfile24 (α : ℝ) : ℝ :=
  α⁻¹*(leechGaussianThetaReal24 α-(α^12)⁻¹-1+(Ioo (0:ℝ) 1).indicator 1 α)

theorem leechGaussianLogProfile24_ae :
    leechGaussianLogProfile24 =ᵐ[volume.restrict (Ioi 0)]
      (fun t : ℝ => (((t:ℂ)^((0:ℂ)-1)) • leechThetaFEPair.f_modif t).re -
        (Ioi 1).indicator (fun t : ℝ => t^(-13:ℝ)) t) := by
  have hne : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), t ≠ 1 := by
    apply Filter.Eventually.mono (compl_mem_ae_iff.mpr (measure_singleton (1 : ℝ)) :
      ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), t ∈ ({1} : Set ℝ)ᶜ)
    intro t ht
    simpa using ht
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hne] with t ht ht1
  have ht0 : 0 < t := ht
  have hc : (t:ℂ)^((0:ℂ)-1) = ((t⁻¹:ℝ):ℂ) := by
    rw [zero_sub, Complex.cpow_neg_one, Complex.ofReal_inv]
  have h12 : ((t^(-(12:ℝ)) : ℝ) : ℂ) = ((t:ℂ)^12)⁻¹ := by
    rw [Real.rpow_neg ht0.le, Real.rpow_ofNat, Complex.ofReal_inv, Complex.ofReal_pow]
  have h13 : t^(-13:ℝ) = t⁻¹*(t^12)⁻¹ := by
    rw [Real.rpow_neg ht0.le, show (13:ℝ) = ((13:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  have hθ : (leechThetaImag t).re = leechGaussianThetaReal24 t := by
    rw [leechThetaImag_eq_real ht0, Complex.ofReal_re]
  simp only [WeakFEPair.f_modif, leechThetaFEPair, Pi.add_apply, hc, smul_eq_mul]
  unfold leechGaussianLogProfile24
  rw [← hθ]
  rcases lt_or_gt_of_ne ht1 with hsmall | hlarge
  · have hA : t ∉ Ioi (1:ℝ) := by simpa using hsmall.le
    have hB : t ∈ Ioo (0:ℝ) 1 := ⟨ht0, hsmall⟩
    simp only [indicator_of_notMem hA, indicator_of_mem hB, h12, Pi.one_apply, one_mul,
      sub_zero]
    try rw [Complex.re_ofReal_mul]
    have hre : (0+(leechThetaImag t-((t:ℂ)^12)⁻¹*1)).re = (leechThetaImag t).re-(t^12)⁻¹ := by
      rw [zero_add, mul_one, Complex.sub_re, ← Complex.ofReal_pow, ← Complex.ofReal_inv,
        Complex.ofReal_re]
    rw [hre]
    ring
  · have hA : t ∈ Ioi (1:ℝ) := hlarge
    have hB : t ∉ Ioo (0:ℝ) 1 := notMem_Ioo_of_ge hlarge.le
    simp only [indicator_of_notMem hB, indicator_of_mem hA, add_zero]
    rw [Complex.re_ofReal_mul, h13]
    simp only [Complex.sub_re, Complex.one_re]
    ring

theorem leechGaussianLogProfile24_integrable :
    IntegrableOn leechGaussianLogProfile24 (Ioi 0) := by
  have hmod : IntegrableOn
      (fun t : ℝ => ((t:ℂ)^((0:ℂ)-1)) • leechThetaFEPair.f_modif t) (Ioi 0) :=
    (leechThetaFEPair.isStrongFEPair_toStrongFEPair.hasMellin (0:ℂ)).1
  have h13 : IntegrableOn (fun t : ℝ => t^(-13:ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hl := (h13.integrable_indicator measurableSet_Ioi).integrableOn (s := Ioi 0)
  exact (hmod.re.sub hl).congr_fun_ae leechGaussianLogProfile24_ae.symm

/-- The majorant `1_{(1,∞)} α⁻¹ α⁻¹²` for the logarithmic Fatou argument. -/
def logMajorant24 (α : ℝ) : ℝ := (Ioi (1:ℝ)).indicator (fun α => α⁻¹*(α^12)⁻¹) α

theorem logMajorant24_integrable : IntegrableOn logMajorant24 (Ioi 0) := by
  have h13 : IntegrableOn (fun t : ℝ => t^(-13:ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have h13' : IntegrableOn (fun t : ℝ => t⁻¹*(t^12)⁻¹) (Ioi 1) := by
    refine h13.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht0 : (0:ℝ) < t := lt_trans zero_lt_one ht
    dsimp only
    rw [Real.rpow_neg ht0.le, show (13:ℝ) = ((13:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  exact (h13'.integrable_indicator measurableSet_Ioi).integrableOn

theorem logMajorant24_nonneg {α : ℝ} (hα : 0 < α) : 0 ≤ logMajorant24 α := by
  unfold logMajorant24
  by_cases h : α ∈ Ioi (1:ℝ)
  · rw [indicator_of_mem h]; positivity
  · rw [indicator_of_notMem h]

theorem sphereGaussianCenteredScaled24_log_lower {N : ℕ} (hN : 0 < N) {α : ℝ} (hα : 0 < α)
    (hα1 : α ≠ 1) (X : ConfigurationD 24 N) :
    -logMajorant24 α ≤
      α⁻¹*(sphereGaussianCenteredScaled24 α X+(Ioo (0:ℝ) 1).indicator 1 α) := by
  rcases lt_or_gt_of_ne hα1 with hsmall | hlarge
  · have hB : α ∈ Ioo (0:ℝ) 1 := ⟨hα, hsmall⟩
    have hA : α ∉ Ioi (1:ℝ) := by simpa using hsmall.le
    unfold logMajorant24
    rw [indicator_of_notMem hA, indicator_of_mem hB, Pi.one_apply, neg_zero]
    exact mul_nonneg (inv_nonneg.mpr hα.le)
      (sphereGaussianCenteredScaled24_add_one_nonneg hN hα.le X)
  · have hA : α ∈ Ioi (1:ℝ) := hlarge
    have hB : α ∉ Ioo (0:ℝ) 1 := notMem_Ioo_of_ge hlarge.le
    unfold logMajorant24
    rw [indicator_of_mem hA, indicator_of_notMem hB, add_zero]
    have h := sphereGaussianCenteredScaled24_weighted_lower_rpow hN 0 hα X
    rw [sphereGaussianMajorant24_large 0 hlarge.le] at h
    have he : α^((0:ℝ)/2-1) = α⁻¹ := by
      rw [show (0:ℝ)/2-1 = -1 by norm_num, Real.rpow_neg_one]
    have he13 : α^((0:ℝ)/2-13) = α⁻¹*(α^12)⁻¹ := by
      rw [show (0:ℝ)/2-13 = -13 by norm_num, Real.rpow_neg hα.le,
        show (13:ℝ) = ((13:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      field_simp
    rw [he, he13] at h
    exact h

theorem sphereGaussianCenteredScaled24_log_profile_eventually
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, ConfigurationD 24 (N k))
    {α : ℝ} (hα : 0 < α)
    (hp : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      leechGaussianThetaReal24 α-ε ≤ sphereGaussianFullScaled24 α (X k)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      leechGaussianLogProfile24 α-ε ≤
        α⁻¹*(sphereGaussianCenteredScaled24 α (X k)+(Ioo (0:ℝ) 1).indicator 1 α) := by
  intro ε hε
  have hw : 0 < α⁻¹ := inv_pos.mpr hα
  filter_upwards [hp (ε*α) (mul_pos hε hα)] with k hk
  have hb : sphereGaussianFullScaled24 α (X k)-(α^12)⁻¹-1 ≤
      sphereGaussianCenteredScaled24 α (X k) := by
    simpa only [sphereGaussianFullScaled24, sphereGaussianCenteredScaled24] using
      sphereGaussianCentered24_flat_baseline_lower (hN k) hα (X k)
  have he : α⁻¹*(ε*α) = ε := by field_simp
  unfold leechGaussianLogProfile24
  nlinarith [mul_le_mul_of_nonneg_left hk hw.le, mul_le_mul_of_nonneg_left hb hw.le]

theorem sphereGaussianSequence_log_integral_lower24
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, ConfigurationD 24 (N k))
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      leechGaussianThetaReal24 α-ε ≤ sphereGaussianFullScaled24 α (X k))
    {C : ℝ} (hC : ∀ k, sphereLogProfileIntegral24 (X k) ≤ C) :
    (∫ α : ℝ in Ioi 0, leechGaussianLogProfile24 α) ≤ C := by
  have hne : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), t ≠ 1 := by
    apply Filter.Eventually.mono (compl_mem_ae_iff.mpr (measure_singleton (1 : ℝ)) :
      ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), t ∈ ({1} : Set ℝ)ᶜ)
    intro t ht
    simpa using ht
  exact integral_le_of_eventual_lower_profile
    (μ := volume.restrict (Ioi (0:ℝ)))
    (g := leechGaussianLogProfile24) (M := logMajorant24)
    (f := fun k α =>
      α⁻¹*(sphereGaussianCenteredScaled24 α (X k)+(Ioo (0:ℝ) 1).indicator 1 α))
    leechGaussianLogProfile24_integrable
    (fun k => sphereGaussianCenteredScaled24_log_integrable (hN k) (X k))
    logMajorant24_integrable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact logMajorant24_nonneg hα)
    (by
      intro k
      filter_upwards [ae_restrict_mem measurableSet_Ioi, hne] with α hα hα1
      exact sphereGaussianCenteredScaled24_log_lower (hN k) hα hα1 (X k))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact sphereGaussianCenteredScaled24_log_profile_eventually hN X hα (hp α hα))
    hC

/-- The conjectured logarithmic coefficient, as a Gaussian profile integral. -/
def sphereLogCoefficient24 : ℝ :=
  (1/2)*((∫ α : ℝ in Ioi 0, leechGaussianLogProfile24 α)+logGaussianConst-
    Real.log Real.pi+(1/12)*Real.log ((sphereAreaD 24).real univ))

/-- Universal sharp lower bound for the logarithmic energy from the pointwise sharp sphere
Gaussian profile. -/
theorem sphere24_log_lower_of_gaussian_profile (hp : SphereGaussianSharpProfileLower24) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ X : ConfigurationD 24 N, sphereLogCoefficient24-η ≤ normalizedEnergyLog24 X := by
  classical
  intro η hη
  by_contra h
  have hbad : ∀ k : ℕ, ∃ N : ℕ, k+1 ≤ N ∧
      ∃ X : ConfigurationD 24 N, normalizedEnergyLog24 X < sphereLogCoefficient24-η := by
    intro k
    by_contra hk
    apply h
    refine ⟨k+1, fun N hN X => ?_⟩
    by_contra hX
    exact hk ⟨N, hN, X, lt_of_not_ge hX⟩
  choose N hN X hX using hbad
  have hN0 : ∀ k, 0 < N k := by intro k; have := hN k; omega
  have ht : Tendsto N atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    filter_upwards [eventually_ge_atTop M] with k hk
    have := hN k
    omega
  set K := logGaussianConst-Real.log Real.pi+(1/12)*Real.log ((sphereAreaD 24).real univ)
    with hK
  have hJ : ∀ k, sphereLogProfileIntegral24 (X k) ≤
      (∫ α : ℝ in Ioi 0, leechGaussianLogProfile24 α)-2*η := by
    intro k
    have h1 := normalizedEnergyLog24_gaussian_mellin (hN0 k) (X k)
    have h2 := hX k
    unfold sphereLogCoefficient24 at h2
    rw [h1] at h2
    linarith
  have hc := sphereGaussianSequence_log_integral_lower24 hN0 X (hp N ht hN0 X) hJ
  linarith

/-- The universal logarithmic lower bound under all-scale Leech contact certificates
(stage G24). -/
theorem sphere24_log_lower_of_contact
    (hG24 : ∀ β : ℝ, 0 < β → ∃ f, LeechGaussianContactCertificate24 β f) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ X : ConfigurationD 24 N, sphereLogCoefficient24-η ≤ normalizedEnergyLog24 X :=
  sphere24_log_lower_of_gaussian_profile (sphereGaussianSharpProfileLower24_of_contact hG24)

/-! ### The profile on the ranges `(0,1)` and `[1,∞)`

These statements have no counterpart in the `S⁸` file: on `(0,1)` the profile is the nonnegative
function `α⁻¹ (Θ(α) - α⁻¹²)`, on `[1,∞)` it is `α⁻¹ (Θ(α) - α⁻¹² - 1)`. -/

theorem leechGaussianLogProfile24_of_lt_one {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    leechGaussianLogProfile24 α = α⁻¹*(leechGaussianThetaReal24 α-(α^12)⁻¹) := by
  have hmem : α ∈ Ioo (0:ℝ) 1 := ⟨hα, hα1⟩
  unfold leechGaussianLogProfile24
  rw [indicator_of_mem hmem, Pi.one_apply]
  ring

theorem leechGaussianLogProfile24_of_one_le {α : ℝ} (hα1 : 1 ≤ α) :
    leechGaussianLogProfile24 α = α⁻¹*(leechGaussianThetaReal24 α-(α^12)⁻¹-1) := by
  have hnot : α ∉ Ioo (0:ℝ) 1 := notMem_Ioo_of_ge hα1
  unfold leechGaussianLogProfile24
  rw [indicator_of_notMem hnot, add_zero]

theorem leechGaussianLogProfile24_nonneg_of_lt_one {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    0 ≤ leechGaussianLogProfile24 α := by
  rw [leechGaussianLogProfile24_of_lt_one hα hα1]
  exact mul_nonneg (inv_nonneg.mpr hα.le)
    (sub_nonneg.mpr (leechGaussianThetaReal24_ge_inv_pow hα))

end SphericalRiesz
end
end

section

/-! The logarithmic coefficient on S²⁴ in closed form (stage LOG).

`κ = ∫ α⁻¹ (e^(-α) - 1_{(0,1)}) = Γ'(1)` is dimension free (`Riesz.SphereLogCoefficient8`). The
Leech profile integral is `∫ g = Re Λ₀(0) - 1/12`, and `Λ₀(u) = Λ(u) + 1/u + 1/(12-u)` with
`Λ(u) = π^(-u) Γ(u) Z(u)` on `(0,1)`, where `Z(u) = ζ_Λ(2u)` is the Epstein zeta function of the
Leech lattice in the variable `u = s/2` of `leechEpsteinZeta`.

There is no closed product for `Z` in this project, and `leechEpsteinZeta u = π^u Λ(u)/Γ(u)` has
the value `0` at `u = 0` (`Γ(0) = 0` and division by zero in Mathlib), not the value of the
continuation. The continuation near `0` is written with the entire function `1/Γ`:
`Z(u) = π^u (Λ₀(u)/Γ(u) - 1/Γ(u+1) - 1/((12-u) Γ(u)))` (`leechEpsteinZetaCont`). It agrees with
`leechEpsteinZeta` for `u ≠ 0`, is differentiable at every `u ≠ 12`, and `Z(0) = -1`; only these
general facts of the functional-equation pair are used. With `H(u) = Γ(u+1) π^(-u) Re Z(u)`,
`Re Λ₀(u) = (H(u) - H(0))/u + 1/(12-u)`, so `Re Λ₀(0) = H'(0) + 1/12` and
`∫ g = -Γ'(1) + log π + Re Z'(0)`. The Euler constants cancel:
`C_log = ½ Re Z'(0) + (1/24) log A₂₄`, the derivative being in the variable `u`
(`½ Z'(0)` is the derivative of the Leech Epstein zeta function `s ↦ ζ_Λ(s)` at `s = 0`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SphericalRiesz

/-- The Leech logarithmic profile integral through the entire part `Λ₀` of the completed
theta. -/
theorem leechGaussianLogProfile24_integral_eq :
    (∫ α in Ioi 0, leechGaussianLogProfile24 α) = (leechThetaFEPair.Λ₀ 0).re-1/12 := by
  rw [integral_congr_ae leechGaussianLogProfile24_ae]
  have hmod : IntegrableOn
      (fun t : ℝ => ((t:ℂ)^((0:ℂ)-1)) • leechThetaFEPair.f_modif t) (Ioi 0) :=
    (leechThetaFEPair.isStrongFEPair_toStrongFEPair.hasMellin (0:ℂ)).1
  have h13 : IntegrableOn (fun t : ℝ => t^(-13:ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hl := (h13.integrable_indicator measurableSet_Ioi).integrableOn (s := Ioi 0)
  have hre : IntegrableOn
      (fun t : ℝ => (((t:ℂ)^((0:ℂ)-1)) • leechThetaFEPair.f_modif t).re) (Ioi 0) :=
    hmod.re
  rw [integral_sub hre hl]
  have h1 : (∫ t in Ioi (0:ℝ), (((t:ℂ)^((0:ℂ)-1)) • leechThetaFEPair.f_modif t).re) =
      (leechThetaFEPair.Λ₀ 0).re := by
    have h := integral_re hmod
    change (∫ t : ℝ in Ioi 0, (((t:ℂ)^((0:ℂ)-1)) • leechThetaFEPair.f_modif t).re) =
      (∫ t : ℝ in Ioi 0, ((t:ℂ)^((0:ℂ)-1)) • leechThetaFEPair.f_modif t).re at h
    rw [h]
    rfl
  have h2 : (∫ t in Ioi (0:ℝ), (Ioi 1).indicator (fun t : ℝ => t^(-13:ℝ)) t) = 1/12 := by
    rw [setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1)),
      integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
    norm_num
  rw [h1, h2]

/-- The completed Leech theta function through its entire part: `Λ(u) = Λ₀(u) - 1/u - 1/(12-u)`
(constant terms `1`, root number `1`, weight `12`). -/
theorem leechThetaCompleted_eq_Λ₀ (u : ℂ) :
    leechThetaCompleted u = leechThetaFEPair.Λ₀ u-1/u-1/(12-u) := by
  have h : leechThetaFEPair.Λ₀ u =
      leechThetaCompleted u+(1/u) • (1:ℂ)+((1:ℂ)/((12:ℝ)-u)) • (1:ℂ) :=
    leechThetaFEPair.Λ₀_eq u
  have h12 : ((12:ℝ):ℂ) = 12 := by norm_num
  rw [smul_eq_mul, smul_eq_mul, mul_one, mul_one, h12] at h
  rw [h]
  ring

/-- The Epstein zeta function of the Leech lattice in the variable `u = s/2`, continued to a
neighbourhood of `u = 0`: `π^u (Λ₀(u)/Γ(u) - 1/Γ(u+1) - 1/((12-u) Γ(u)))` with the entire
function `1/Γ`. For `u ≠ 0` this is `leechEpsteinZeta u = π^u Λ(u)/Γ(u)`; at `u = 0` it has the
value `-1` of the continuation, whereas `leechEpsteinZeta 0 = 0` because `Γ(0) = 0` in
Mathlib. -/
def leechEpsteinZetaCont (u : ℂ) : ℂ :=
  (Real.pi : ℂ)^u*(leechThetaFEPair.Λ₀ u*(Complex.Gamma u)⁻¹-(Complex.Gamma (u+1))⁻¹-
    (12-u)⁻¹*(Complex.Gamma u)⁻¹)

/-- Away from `0` the continuation is `leechEpsteinZeta`. -/
theorem leechEpsteinZetaCont_eq {u : ℂ} (hu : u ≠ 0) :
    leechEpsteinZetaCont u = leechEpsteinZeta u := by
  unfold leechEpsteinZetaCont leechEpsteinZeta
  rw [leechThetaCompleted_eq_Λ₀, Complex.Gamma_add_one u hu]
  ring

/-- `ζ_Λ(0) = -1`. -/
theorem leechEpsteinZetaCont_zero : leechEpsteinZetaCont 0 = -1 := by
  simp [leechEpsteinZetaCont]

/-- The continuation is differentiable away from the pole `u = 12`, in particular at `0`. -/
theorem leechEpsteinZetaCont_differentiableAt {u : ℂ} (h12 : u ≠ 12) :
    DifferentiableAt ℂ leechEpsteinZetaCont u := by
  have hπ : DifferentiableAt ℂ (fun v : ℂ => (Real.pi : ℂ)^v) u :=
    differentiableAt_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hΛ : DifferentiableAt ℂ leechThetaFEPair.Λ₀ u := leechThetaFEPair.differentiable_Λ₀ u
  have hΓ : DifferentiableAt ℂ (fun v : ℂ => (Complex.Gamma v)⁻¹) u :=
    Complex.differentiable_one_div_Gamma u
  have hΓ1 : DifferentiableAt ℂ (fun v : ℂ => (Complex.Gamma (v+1))⁻¹) u :=
    DifferentiableAt.comp (g := fun s : ℂ => (Complex.Gamma s)⁻¹) (f := fun v : ℂ => v+1) u
      (Complex.differentiable_one_div_Gamma (u+1)) (differentiableAt_id.add_const (1:ℂ))
  have h12' : (12:ℂ)-u ≠ 0 := sub_ne_zero.mpr (Ne.symm h12)
  have hinv : DifferentiableAt ℂ (fun v : ℂ => ((12:ℂ)-v)⁻¹) u :=
    (differentiableAt_id.const_sub (12:ℂ)).inv h12'
  exact hπ.mul (((hΛ.mul hΓ).sub hΓ1).sub (hinv.mul hΓ))

/-- Where `Γ(u) ≠ 0` and `u ≠ 0` the completed function is `π^(-u) Γ(u)` times the continued
Epstein function. -/
theorem leechThetaCompleted_eq_cont {u : ℂ} (hu : u ≠ 0) (hΓ : Complex.Gamma u ≠ 0) :
    leechThetaCompleted u =
      (Real.pi : ℂ)^(-u)*Complex.Gamma u*leechEpsteinZetaCont u := by
  have hπ : (Real.pi : ℂ)^u ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have h1 : ((Real.pi : ℂ)^u)⁻¹*(Real.pi : ℂ)^u = 1 := inv_mul_cancel₀ hπ
  have h2 : Complex.Gamma u/Complex.Gamma u = 1 := div_self hΓ
  rw [leechEpsteinZetaCont_eq hu, Complex.cpow_neg]
  unfold leechEpsteinZeta
  linear_combination
    (-(leechThetaCompleted u)*(Complex.Gamma u/Complex.Gamma u))*h1-leechThetaCompleted u*h2

/-- A function which agrees with `leechEpsteinZeta` on a punctured neighbourhood of `0` and is
continuous at `0` has the derivative of the continuation at `0`. -/
theorem deriv_eq_deriv_leechEpsteinZetaCont_zero {Z : ℂ → ℂ}
    (hZ : ∀ᶠ u in 𝓝[≠] (0:ℂ), Z u = leechEpsteinZeta u) (hZc : ContinuousAt Z 0) :
    deriv Z 0 = deriv leechEpsteinZetaCont 0 := by
  have hcont : ContinuousAt leechEpsteinZetaCont 0 :=
    (leechEpsteinZetaCont_differentiableAt (by norm_num)).continuousAt
  have hev : ∀ᶠ u in 𝓝[≠] (0:ℂ), Z u = leechEpsteinZetaCont u := by
    filter_upwards [hZ, self_mem_nhdsWithin] with u hu (hu0 : u ≠ 0)
    rw [hu, leechEpsteinZetaCont_eq hu0]
  have h0 : Z 0 = leechEpsteinZetaCont 0 :=
    tendsto_nhds_unique_of_eventuallyEq (hZc.tendsto.mono_left nhdsWithin_le_nhds)
      (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev
  have hfull : Z =ᶠ[𝓝 0] leechEpsteinZetaCont := by
    filter_upwards [eventually_nhdsWithin_iff.mp hev] with u hu
    by_cases h : u = 0
    · rw [h]
      exact h0
    · exact hu h
  exact hfull.deriv_eq

/-- `Re Λ₀(0) = H'(0) + 1/12` with `H(u) = Γ(u+1) π^(-u) Re Z(u)`. -/
theorem leechThetaFEPair_Λ₀_zero_re :
    (leechThetaFEPair.Λ₀ 0).re =
      -deriv Real.Gamma 1+Real.log Real.pi+(deriv leechEpsteinZetaCont 0).re+1/12 := by
  set e : ℝ → ℝ := fun u => (leechEpsteinZetaCont (u:ℂ)).re with he
  have he0 : e 0 = -1 := by
    simp only [he, Complex.ofReal_zero, leechEpsteinZetaCont_zero, Complex.neg_re,
      Complex.one_re]
  have hde : HasDerivAt e (deriv leechEpsteinZetaCont 0).re 0 := by
    have h := ((leechEpsteinZetaCont_differentiableAt (u := ((0:ℝ):ℂ))
      (by norm_num)).hasDerivAt).real_of_complex
    simpa only [Complex.ofReal_zero] using h
  have hdG : HasDerivAt (fun u : ℝ => Real.Gamma (u+1)) (deriv Real.Gamma 1) 0 := by
    have hd : HasDerivAt Real.Gamma (deriv Real.Gamma 1) (0+1) := by
      rw [zero_add]
      exact (Real.differentiableAt_Gamma (fun m h => by
        have : (0:ℝ) ≤ m := Nat.cast_nonneg m
        linarith)).hasDerivAt
    exact hd.comp_add_const 0 1
  have hdP : HasDerivAt (fun u : ℝ => Real.pi^(-u)) (-Real.log Real.pi) 0 := by
    have h := (Real.hasStrictDerivAt_const_rpow Real.pi_pos (-0)).hasDerivAt.comp (0:ℝ)
      (hasDerivAt_neg 0)
    simp only [neg_zero, Real.rpow_zero, one_mul, mul_neg, mul_one] at h
    exact h
  set H : ℝ → ℝ := fun u => Real.Gamma (u+1)*Real.pi^(-u)*e u with hH
  have hdH : HasDerivAt H
      (-deriv Real.Gamma 1+Real.log Real.pi+(deriv leechEpsteinZetaCont 0).re) 0 := by
    have h := (hdG.mul hdP).mul hde
    convert h using 1
    simp only [Pi.mul_apply, zero_add, Real.Gamma_one, neg_zero, Real.rpow_zero, he0]
    ring
  have hH0 : H 0 = -1 := by
    simp only [hH, zero_add, Real.Gamma_one, neg_zero, Real.rpow_zero, he0]
    ring
  -- the slope limit
  have hs := hdH.tendsto_slope_zero_right
  -- `Re Λ₀(u)` on `(0,1)`
  have hΛ₀ : ∀ u : ℝ, 0 < u → u < 1 →
      (leechThetaFEPair.Λ₀ (u:ℂ)).re = u⁻¹ • (H (0+u)-H 0)+1/(12-u) := by
    intro u hu0 hu1
    have hu0' : (u:ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
    have h12 : (12:ℝ)-u ≠ 0 := by linarith
    have hΓ0 : Complex.Gamma (u:ℂ) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by simpa using hu0)
    rw [leechThetaFEPair.Λ₀_eq]
    change (leechThetaCompleted (u:ℂ)+(1/(u:ℂ)) • (1:ℂ)+
      ((1:ℂ)/((12:ℝ)-(u:ℂ))) • (1:ℂ)).re = _
    rw [leechThetaCompleted_eq_cont hu0' hΓ0]
    have hG : Complex.Gamma (u:ℂ) = ((Real.Gamma u : ℝ) : ℂ) := Complex.Gamma_ofReal u
    have hP : (Real.pi : ℂ)^(-(u:ℂ)) = ((Real.pi^(-u) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow Real.pi_pos.le]
      push_cast
      ring_nf
    have hinv : (1/(u:ℂ)) • (1:ℂ) = ((1/u : ℝ) : ℂ) := by
      rw [smul_eq_mul, mul_one]; push_cast; ring
    have hinv12 : ((1:ℂ)/((12:ℝ)-(u:ℂ))) • (1:ℂ) = ((1/(12-u) : ℝ) : ℂ) := by
      rw [smul_eq_mul, mul_one]; push_cast; ring
    rw [hG, hP, hinv, hinv12, Complex.add_re, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_re, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    have hΓu : Real.Gamma u = Real.Gamma (u+1)/u := by
      rw [Real.Gamma_add_one hu0.ne']
      field_simp
    have hE0 : (leechEpsteinZetaCont ((0:ℝ):ℂ)).re = -1 := he0
    simp only [hH, he, zero_add, Real.Gamma_one, neg_zero, Real.rpow_zero, smul_eq_mul]
    rw [hΓu, hE0]
    field_simp
    ring
  -- `Re Λ₀` is continuous at `0`
  have hc : Tendsto (fun u : ℝ => (leechThetaFEPair.Λ₀ (u:ℂ)).re) (𝓝[>] 0)
      (𝓝 (leechThetaFEPair.Λ₀ 0).re) := by
    have hcont : Continuous (fun u : ℝ => (leechThetaFEPair.Λ₀ (u:ℂ)).re) :=
      Complex.continuous_re.comp (leechThetaFEPair.differentiable_Λ₀.continuous.comp
        Complex.continuous_ofReal)
    have := hcont.tendsto 0
    simp only [Complex.ofReal_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h12 : Tendsto (fun u : ℝ => 1/(12-u)) (𝓝[>] 0) (𝓝 (1/12)) := by
    have hc12 : ContinuousAt (fun u : ℝ => 1/(12-u)) 0 :=
      continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by norm_num)
    have := hc12.tendsto
    simp only [sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun u : ℝ => (leechThetaFEPair.Λ₀ (u:ℂ)).re) (𝓝[>] 0)
      (𝓝 ((-deriv Real.Gamma 1+Real.log Real.pi+(deriv leechEpsteinZetaCont 0).re)+1/12)) := by
    apply (hs.add h12).congr'
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with u hu
    exact (hΛ₀ u hu.1 hu.2).symm
  exact tendsto_nhds_unique hc hlim

/-- The logarithmic coefficient through the Leech Epstein derivative at `0`:
`C_log = ½ Re Z'(0) + (1/24) log A₂₄`, `Z(u) = ζ_Λ(2u)` (derivative in the variable `u`). -/
theorem sphereLogCoefficient24_eq_epstein :
    sphereLogCoefficient24 =
      (1/2)*(deriv leechEpsteinZetaCont 0).re+(1/24)*Real.log ((sphereAreaD 24).real univ) := by
  unfold sphereLogCoefficient24
  rw [leechGaussianLogProfile24_integral_eq, leechThetaFEPair_Λ₀_zero_re,
    logGaussianConst_eq_deriv_Gamma]
  ring

/-- The same derivative in terms of `leechEpsteinZeta` alone: `Re Z'(0)` is the right slope at
`0` of `u ↦ Re ζ_Λ(2u)` against the value `-1`. -/
theorem leechEpsteinZeta_slope_tendsto :
    Tendsto (fun u : ℝ => u⁻¹*((leechEpsteinZeta (u:ℂ)).re+1)) (𝓝[>] 0)
      (𝓝 (deriv leechEpsteinZetaCont 0).re) := by
  set e : ℝ → ℝ := fun u => (leechEpsteinZetaCont (u:ℂ)).re with he
  have he0 : e 0 = -1 := by
    simp only [he, Complex.ofReal_zero, leechEpsteinZetaCont_zero, Complex.neg_re,
      Complex.one_re]
  have hde : HasDerivAt e (deriv leechEpsteinZetaCont 0).re 0 := by
    have h := ((leechEpsteinZetaCont_differentiableAt (u := ((0:ℝ):ℂ))
      (by norm_num)).hasDerivAt).real_of_complex
    simpa only [Complex.ofReal_zero] using h
  apply hde.tendsto_slope_zero_right.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu0 : (0:ℝ) < u := hu
  have hu0' : (u:ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
  have heu : e u = (leechEpsteinZeta (u:ℂ)).re := by
    simp only [he, leechEpsteinZetaCont_eq hu0']
  rw [zero_add, he0, heu, smul_eq_mul, sub_neg_eq_add]

/-- The logarithmic coefficient with the area of `S²⁴` written out:
`C_log = ½ Re Z'(0) + (13/24) log 2 + ½ log π - (1/24) log 316234143225`. -/
theorem sphereLogCoefficient24_eq_epstein_area :
    sphereLogCoefficient24 =
      (1/2)*(deriv leechEpsteinZetaCont 0).re+(13/24)*Real.log 2+(1/2)*Real.log Real.pi-
        (1/24)*Real.log 316234143225 := by
  rw [sphereLogCoefficient24_eq_epstein, sphereArea24_univ_real]
  have hπ : 0 < Real.pi := Real.pi_pos
  rw [Real.log_div (by positivity) (by norm_num), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow]
  push_cast
  ring

/-- Universal sharp lower bound for the logarithmic energy on S²⁴ with the coefficient
`½ Re Z'(0) + (1/24) log A₂₄`, under all-scale Leech contact certificates (stage G24). -/
theorem sphere24_log_lower_epstein
    (hG24 : ∀ β : ℝ, 0 < β → ∃ f, LeechGaussianContactCertificate24 β f) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 24 N,
      (1/2)*(deriv leechEpsteinZetaCont 0).re+(1/24)*Real.log ((sphereAreaD 24).real univ)-η ≤
        normalizedEnergyLog24 X := by
  rw [← sphereLogCoefficient24_eq_epstein]
  exact sphere24_log_lower_of_contact hG24

end SphericalRiesz
end
end

section

/-! The logarithmic constant of S²⁴ is the actual double integral (stage LOG).

On the unit sphere `d = |x - y| ≤ 2`, so `log (2/d) = ½ ∫ t⁻¹ (e^(-t d²) - e^(-4t)) dt` has a
nonnegative integrand (Frullani with `a = d²`, `b = 4`; `Riesz.SphereLogConstPair8`). Tonelli in
`[0,∞]` off the null diagonal gives `∫∫ log (2/|x-y|) = ½ ∫ t⁻¹ (B(t) - e^(-4t)) dt < ∞`, and
`-log d = log (2/d) - log 2` together with `½ ∫ t⁻¹ (e^(-4t) - e^(-t)) dt = -log 2` identifies
`W_log = ½ ∫ t⁻¹ (B(t) - e^(-t)) dt` with `∫∫ -log |x - y| dσ dσ`. Hence the logarithmic lower
bound holds in the form of the conjecture. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace SphericalRiesz

theorem sphereLogPair24_ofReal_mellin {x y : SphereD 24} (hxy : x ≠ y) :
    ENNReal.ofReal (Real.log (2/dist x y)) = ENNReal.ofReal (1/2) *
      ∫⁻ t in Ioi 0, ENNReal.ofReal (t⁻¹*(sphereGaussianKernel24 t x y-Real.exp (-(4*t)))) := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hd2 := sphere24_dist_le_two x y
  have hpos : ∀ t ∈ Ioi (0:ℝ), 0 ≤ t⁻¹*(sphereGaussianKernel24 t x y-Real.exp (-(4*t))) := by
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    apply mul_nonneg (inv_nonneg.mpr ht0.le)
    have hdd : (dist x y)^2 ≤ 4 := by nlinarith [hd.le]
    have : t*(dist x y)^2 ≤ 4*t := by nlinarith [mul_le_mul_of_nonneg_left hdd ht0.le]
    simp only [sphereGaussianKernel24]
    linarith [Real.exp_le_exp.mpr (neg_le_neg this)]
  obtain ⟨hint, hval⟩ := frullani_exp_pair (a := (dist x y)^2) (b := 4) (by positivity)
    (by norm_num)
  have hint' : IntegrableOn
      (fun t : ℝ => t⁻¹*(sphereGaussianKernel24 t x y-Real.exp (-(4*t)))) (Ioi 0) := by
    refine hint.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [sphereGaussianKernel24, mul_comm t]
  have hval' : (∫ t in Ioi 0, t⁻¹*(sphereGaussianKernel24 t x y-Real.exp (-(4*t)))) =
      2*Real.log (2/dist x y) := by
    rw [← setIntegral_congr_fun measurableSet_Ioi (fun t _ => by
      simp only [sphereGaussianKernel24, mul_comm t] :
        ∀ t ∈ Ioi (0:ℝ), t⁻¹*(Real.exp (-((dist x y)^2*t))-Real.exp (-(4*t))) =
          t⁻¹*(sphereGaussianKernel24 t x y-Real.exp (-(4*t)))), hval,
      Real.log_div (by norm_num) hd.ne', Real.log_pow, show (4:ℝ) = 2^2 by norm_num,
      Real.log_pow]
    push_cast
    ring
  rw [← ofReal_integral_eq_lintegral_ofReal hint'
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hpos t ht), hval', ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

theorem sphereGaussianBackground24_ge_exp {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-(4*t)) ≤ sphereGaussianBackground24 t := by
  have hle : ∀ p : SphereD 24 × SphereD 24,
      Real.exp (-(4*t)) ≤ sphereGaussianKernel24 t p.1 p.2 := by
    intro p
    have hd2 := sphere24_dist_le_two p.1 p.2
    have hd0 : 0 ≤ dist p.1 p.2 := dist_nonneg
    have hdd : (dist p.1 p.2)^2 ≤ 4 := by nlinarith
    have : t*(dist p.1 p.2)^2 ≤ 4*t := by nlinarith [mul_le_mul_of_nonneg_left hdd ht]
    simp only [sphereGaussianKernel24]
    exact Real.exp_le_exp.mpr (neg_le_neg this)
  have h := integral_mono
    (integrable_const (Real.exp (-(4*t)))
      (μ := (sphereProbabilityD 24).prod (sphereProbabilityD 24)))
    (sphereGaussianKernel24_pair_integrable ht) hle
  unfold sphereGaussianBackground24
  simpa using h

theorem sphereGaussianBackground24_log4_integrable :
    IntegrableOn (fun t : ℝ => t⁻¹*(sphereGaussianBackground24 t-Real.exp (-(4*t)))) (Ioi 0) := by
  have h1 := sphereGaussianBackground24_log_integrable
  have h2 := (frullani_exp (a := 4) (by norm_num)).1
  have he : (fun t : ℝ => t⁻¹*(sphereGaussianBackground24 t-Real.exp (-(4*t)))) =
      fun t => t⁻¹*(sphereGaussianBackground24 t-Real.exp (-t))-
        t⁻¹*(Real.exp (-(4*t))-Real.exp (-t)) := by
    funext t; ring
  rw [he]
  exact h1.sub h2

theorem sphereLogPair24_lintegral :
    ∫⁻ p : SphereD 24 × SphereD 24, ENNReal.ofReal (Real.log (2/dist p.1 p.2))
        ∂((sphereProbabilityD 24).prod (sphereProbabilityD 24)) =
      ENNReal.ofReal
        ((1/2)*∫ t in Ioi 0, t⁻¹*(sphereGaussianBackground24 t-Real.exp (-(4*t)))) := by
  set μ := (sphereProbabilityD 24).prod (sphereProbabilityD 24) with hμ
  set F : ℝ → SphereD 24 × SphereD 24 → ℝ≥0∞ :=
    fun t p => ENNReal.ofReal (t⁻¹*(sphereGaussianKernel24 t p.1 p.2-Real.exp (-(4*t))))
    with hF
  have hFm : Measurable (Function.uncurry F) := by
    simp only [hF, Function.uncurry_def, sphereGaussianKernel24]
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
  have hae : (fun p : SphereD 24 × SphereD 24 =>
      ENNReal.ofReal (Real.log (2/dist p.1 p.2))) =ᵐ[μ]
      (fun p => ENNReal.ofReal (1/2) * ∫⁻ t in Ioi 0, F t p) := by
    have hnull : μ {p : SphereD 24 × SphereD 24 | p.1 = p.2} = 0 :=
      sphereProbability24_prod_diagonal_null
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with p hp
    exact sphereLogPair24_ofReal_mellin hp
  have hmeas : Measurable (fun p : SphereD 24 × SphereD 24 => ∫⁻ t in Ioi 0, F t p) :=
    Measurable.lintegral_prod_left' (μ := volume.restrict (Ioi (0:ℝ))) hFm
  rw [lintegral_congr_ae hae, lintegral_const_mul _ hmeas,
    lintegral_lintegral_swap (f := fun (p : SphereD 24 × SphereD 24) (t : ℝ) => F t p)
      ((hFm.comp measurable_swap).aemeasurable)]
  have hin : ∀ t ∈ Ioi (0:ℝ), ∫⁻ p, F t p ∂μ =
      ENNReal.ofReal (t⁻¹*(sphereGaussianBackground24 t-Real.exp (-(4*t)))) := by
    intro t ht
    have ht0 : 0 ≤ t := (show (0:ℝ) < t from ht).le
    have hi : Integrable (fun p : SphereD 24 × SphereD 24 =>
        t⁻¹*(sphereGaussianKernel24 t p.1 p.2-Real.exp (-(4*t)))) μ :=
      ((sphereGaussianKernel24_pair_integrable ht0).sub (integrable_const _)).const_mul _
    have hnn : ∀ p : SphereD 24 × SphereD 24,
        0 ≤ t⁻¹*(sphereGaussianKernel24 t p.1 p.2-Real.exp (-(4*t))) := by
      intro p
      apply mul_nonneg (inv_nonneg.mpr ht0)
      have hd2 := sphere24_dist_le_two p.1 p.2
      have hd0 : 0 ≤ dist p.1 p.2 := dist_nonneg
      have hdd : (dist p.1 p.2)^2 ≤ 4 := by nlinarith
      have : t*(dist p.1 p.2)^2 ≤ 4*t := by nlinarith [mul_le_mul_of_nonneg_left hdd ht0]
      simp only [sphereGaussianKernel24]
      linarith [Real.exp_le_exp.mpr (neg_le_neg this)]
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnn),
      integral_const_mul, integral_sub (sphereGaussianKernel24_pair_integrable ht0)
        (integrable_const _)]
    simp [sphereGaussianBackground24]
  rw [setLIntegral_congr_fun measurableSet_Ioi hin,
    ← ofReal_integral_eq_lintegral_ofReal sphereGaussianBackground24_log4_integrable
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : (0:ℝ) < t := ht
        apply mul_nonneg (inv_nonneg.mpr ht0.le)
        linarith [sphereGaussianBackground24_ge_exp ht0.le]),
    ← ENNReal.ofReal_mul (by norm_num)]

theorem sphereLogPair24_nonneg (p : SphereD 24 × SphereD 24) :
    0 ≤ Real.log (2/dist p.1 p.2) := by
  rcases eq_or_lt_of_le (dist_nonneg : 0 ≤ dist p.1 p.2) with h | h
  · rw [← h, div_zero, Real.log_zero]
  · apply Real.log_nonneg
    rw [le_div_iff₀ h]
    linarith [sphere24_dist_le_two p.1 p.2]

theorem sphereLogPair24_integrable :
    Integrable (fun p : SphereD 24 × SphereD 24 => Real.log (2/dist p.1 p.2))
      ((sphereProbabilityD 24).prod (sphereProbabilityD 24)) := by
  have hm : Measurable (fun p : SphereD 24 × SphereD 24 => Real.log (2/dist p.1 p.2)) :=
    Real.measurable_log.comp (measurable_const.div
      (continuous_dist.comp (continuous_fst.prodMk continuous_snd)).measurable)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall sphereLogPair24_nonneg),
    sphereLogPair24_lintegral]
  exact ENNReal.ofReal_lt_top

/-- `W_log` is the actual double integral of `-log |x - y|`. -/
theorem sphereLogConst24_eq_pair_integral :
    sphereLogConst24 = ∫ p : SphereD 24 × SphereD 24, -Real.log (dist p.1 p.2)
      ∂((sphereProbabilityD 24).prod (sphereProbabilityD 24)) := by
  set μ := (sphereProbabilityD 24).prod (sphereProbabilityD 24) with hμ
  have hI4 := sphereGaussianBackground24_log4_integrable
  have hnnI : 0 ≤ (1/2)*∫ t in Ioi 0,
      t⁻¹*(sphereGaussianBackground24 t-Real.exp (-(4*t))) := by
    apply mul_nonneg (by norm_num)
    apply setIntegral_nonneg measurableSet_Ioi
    intro t ht
    have ht0 : (0:ℝ) < t := ht
    apply mul_nonneg (inv_nonneg.mpr ht0.le)
    linarith [sphereGaussianBackground24_ge_exp ht0.le]
  have hlog2 : (∫ p, Real.log (2/dist p.1 p.2) ∂μ) =
      (1/2)*∫ t in Ioi 0, t⁻¹*(sphereGaussianBackground24 t-Real.exp (-(4*t))) := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall sphereLogPair24_nonneg)
        sphereLogPair24_integrable.aestronglyMeasurable, sphereLogPair24_lintegral,
      ENNReal.toReal_ofReal hnnI]
  have hae : (fun p : SphereD 24 × SphereD 24 => -Real.log (dist p.1 p.2)) =ᵐ[μ]
      (fun p => Real.log (2/dist p.1 p.2)-Real.log 2) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp sphereProbability24_prod_diagonal_null]
      with p hp
    have hd : 0 < dist p.1 p.2 := dist_pos.mpr hp
    rw [Real.log_div (by norm_num) hd.ne']
    ring
  have hc : (∫ _p : SphereD 24 × SphereD 24, Real.log 2 ∂μ) = Real.log 2 := by
    simp [hμ]
  rw [integral_congr_ae hae, integral_sub sphereLogPair24_integrable (integrable_const _),
    hlog2, hc]
  obtain ⟨h4i, h4v⟩ := frullani_exp (a := 4) (by norm_num)
  have hsplit : (∫ t in Ioi 0, t⁻¹*(sphereGaussianBackground24 t-Real.exp (-t))) =
      (∫ t in Ioi 0, t⁻¹*(sphereGaussianBackground24 t-Real.exp (-(4*t))))+
        ∫ t in Ioi 0, t⁻¹*(Real.exp (-(4*t))-Real.exp (-t)) := by
    rw [← integral_add hI4 h4i]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    ring
  unfold sphereLogConst24
  rw [hsplit, h4v, show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
  push_cast
  ring

/-- The universal sharp lower bound for the logarithmic energy on S²⁴ in the form of the
conjecture: actual double integral of `-log |x - y|`, the `-(N/24) log N` term and the
coefficient `½ Re Z'(0) + (1/24) log A₂₄` (`Z(u) = ζ_Λ(2u)` the continued Leech Epstein zeta
function), under all-scale Leech contact certificates (stage G24). -/
theorem sphere24_log_lower_conjecture_form
    (hG24 : ∀ β : ℝ, 0 < β → ∃ f, LeechGaussianContactCertificate24 β f) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 24 N,
      (1/2)*(deriv leechEpsteinZetaCont 0).re+(1/24)*Real.log ((sphereAreaD 24).real univ)-η ≤
        (energyLogD X-(∫ p : SphereD 24 × SphereD 24, -Real.log (dist p.1 p.2)
          ∂((sphereProbabilityD 24).prod (sphereProbabilityD 24)))*(N:ℝ)^2+
            (N:ℝ)/24*Real.log N)/(N:ℝ) := by
  rw [← sphereLogConst24_eq_pair_integral]
  exact sphere24_log_lower_epstein hG24

end SphericalRiesz
end
end
