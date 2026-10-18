import Riesz.SphereRieszNegTransfer8
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral

/-! Logarithmic energy on the actual unit S⁸ (stage LOG, Mellin layer).

Frullani's integral gives `-log d = ½ ∫₀^∞ t⁻¹ (e^(-t d²) - e^(-t)) dt` for `d > 0`. Summing over
ordered pairs of distinct points and subtracting the same integral of the actual Gaussian
background `B` gives, with the full neutralized defect `D(t) = Σ_{i,j} e^(-t|x_i-x_j|²) - N² B(t)`,
`2 (E_log - W N²) = ∫ t⁻¹ (D(t) - N (1 - e^(-t))) dt`. In density scale `t = c_N α`
(`c_N = π (N/A₈)^(1/4)`) and with `κ = ∫ α⁻¹ (e^(-α) - 1_{(0,1)}(α)) dα`, this is
`(E_log - W N² + (N/8) log N)/N = ½ (J_N + κ - log π + ¼ log A₈)`,
`J_N = ∫ α⁻¹ (F_N(α) + 1_{(0,1)}(α)) dα`, with the same centred profile `F_N` as for the Riesz
exponents. The `-(N/8) log N` term of the logarithmic asymptotics comes from `log c_N`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SphericalRiesz

theorem exp_sub_exp_bound {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    |Real.exp (-(a*x))-Real.exp (-x)| ≤ |a-1| * x * Real.exp (-(min a 1*x)) := by
  rcases le_total a 1 with h | h
  · rw [min_eq_left h]
    have he : Real.exp (-x) = Real.exp (-(a*x))*Real.exp (-((1-a)*x)) := by
      rw [← Real.exp_add]; congr 1; ring
    obtain ⟨h1, h2⟩ := one_sub_exp_neg_bounds (mul_nonneg (by linarith : (0:ℝ) ≤ 1-a) hx)
    have h3 : 1-Real.exp (-((1-a)*x)) ≤ (1-a)*x := h2.trans (min_le_left _ _)
    have hE := Real.exp_pos (-(a*x))
    rw [he, abs_of_nonpos (by linarith : a-1 ≤ 0)]
    rw [abs_of_nonneg (by nlinarith)]
    nlinarith
  · rw [min_eq_right h]
    have he : Real.exp (-(a*x)) = Real.exp (-x)*Real.exp (-((a-1)*x)) := by
      rw [← Real.exp_add]; congr 1; ring
    obtain ⟨h1, h2⟩ := one_sub_exp_neg_bounds (mul_nonneg (by linarith : (0:ℝ) ≤ a-1) hx)
    have h3 : 1-Real.exp (-((a-1)*x)) ≤ (a-1)*x := h2.trans (min_le_left _ _)
    have hE := Real.exp_pos (-x)
    rw [he, abs_of_nonneg (by linarith : 0 ≤ a-1)]
    rw [abs_of_nonpos (by nlinarith), one_mul]
    nlinarith

/-- Frullani's integral for the Gaussian: `∫₀^∞ t⁻¹ (e^(-a t) - e^(-t)) dt = -log a`. -/
theorem frullani_exp {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t⁻¹*(Real.exp (-(a*t))-Real.exp (-t))) (Ioi 0) ∧
    (∫ t in Ioi 0, t⁻¹*(Real.exp (-(a*t))-Real.exp (-t))) = -Real.log a := by
  set m := min a 1 with hm_def
  have hm : 0 < m := lt_min ha one_pos
  have hint : IntegrableOn (fun t : ℝ => t⁻¹*(Real.exp (-(a*t))-Real.exp (-t))) (Ioi 0) := by
    have hdom : IntegrableOn (fun t : ℝ => |a-1| * Real.exp (-m*t)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hm).const_mul _
    refine Integrable.mono' hdom ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      exact (continuousOn_inv₀.mono (fun t ht => ne_of_gt ht)).mul
        (by fun_prop : Continuous (fun t : ℝ => Real.exp (-(a*t))-Real.exp (-t))).continuousOn
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0:ℝ) < t := ht
      rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos ht0]
      have hb := exp_sub_exp_bound ha ht0.le
      calc t⁻¹ * |Real.exp (-(a*t))-Real.exp (-t)| ≤ t⁻¹*(|a-1| * t * Real.exp (-(m*t))) :=
            mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr ht0.le)
        _ = |a-1| * Real.exp (-m*t) := by
            rw [neg_mul]
            field_simp
  refine ⟨hint, ?_⟩
  have hf : LocallyIntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) :=
    (Real.continuous_exp.comp continuous_neg).locallyIntegrable.locallyIntegrableOn _
  have hL : Tendsto (fun x : ℝ => Real.exp (-x)) (𝓝[>] 0) (𝓝 1) := by
    have := ((Real.continuous_exp.comp continuous_neg).tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
    simp only [Function.comp_apply, neg_zero, Real.exp_zero] at this
    exact this
  have hR : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hint' : IntegrableOn (fun x : ℝ => x⁻¹ • ((fun x : ℝ => Real.exp (-x)) (a*x) -
      (fun x : ℝ => Real.exp (-x)) (1*x))) (Ioi 0) := by
    refine hint.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [smul_eq_mul]
  have h := Frullani.integral_Ioi_eq (f := fun x : ℝ => Real.exp (-x)) hf ha one_pos hL hR hint'
  have hl : (∫ x in Ioi (0:ℝ), x⁻¹ • ((fun x : ℝ => Real.exp (-x)) (a*x) -
      (fun x : ℝ => Real.exp (-x)) (1*x))) =
      ∫ t in Ioi 0, t⁻¹*(Real.exp (-(a*t))-Real.exp (-t)) := by
    congr 1
    funext x
    simp [smul_eq_mul]
  rw [hl] at h
  rw [h, smul_eq_mul, sub_zero, mul_one, one_div, Real.log_inv]

theorem gaussianPair_frullani {d : ℝ} (hd : 0 < d) :
    IntegrableOn (fun t : ℝ => t⁻¹*(Real.exp (-(d^2*t))-Real.exp (-t))) (Ioi 0) ∧
    (∫ t in Ioi 0, t⁻¹*(Real.exp (-(d^2*t))-Real.exp (-t))) = 2*(-Real.log d) := by
  obtain ⟨h1, h2⟩ := frullani_exp (a := d^2) (by positivity)
  refine ⟨h1, ?_⟩
  rw [h2, Real.log_pow]
  push_cast
  ring

/-- The ordered logarithmic energy `Σ_{i≠j} log (1/|x_i - x_j|)`. -/
def energyLog {N : ℕ} (X : Configuration N) : ℝ :=
  ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, -Real.log (dist (X i) (X j))

theorem sphereGaussianPair8_frullani {N : ℕ} (X : Configuration N) {i j : Fin N} (hij : i ≠ j) :
    IntegrableOn (fun t : ℝ => t⁻¹*(sphereGaussianKernel8 t (X i) (X j)-Real.exp (-t))) (Ioi 0) ∧
    (∫ t in Ioi 0, t⁻¹*(sphereGaussianKernel8 t (X i) (X j)-Real.exp (-t))) =
      2*(-Real.log (dist (X i) (X j))) := by
  have h := gaussianPair_frullani (offDiagonal_dist_pos X hij)
  have he : (fun t : ℝ => t⁻¹*(sphereGaussianKernel8 t (X i) (X j)-Real.exp (-t))) =
      (fun t : ℝ => t⁻¹*(Real.exp (-((dist (X i) (X j))^2*t))-Real.exp (-t))) := by
    funext t
    simp only [sphereGaussianKernel8, mul_comm t]
  rw [he]
  exact h

theorem sphereGaussianOffDiagonal8_frullani {N : ℕ} (X : Configuration N) :
    IntegrableOn (fun t : ℝ => t⁻¹*(sphereGaussianOffDiagonal8 t X-((N:ℝ)^2-N)*Real.exp (-t)))
      (Ioi 0) ∧
    (∫ t in Ioi 0, t⁻¹*(sphereGaussianOffDiagonal8 t X-((N:ℝ)^2-N)*Real.exp (-t))) =
      2*energyLog X := by
  have hpt : ∀ t : ℝ, t⁻¹*(sphereGaussianOffDiagonal8 t X-((N:ℝ)^2-N)*Real.exp (-t)) =
      ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
        t⁻¹*(sphereGaussianKernel8 t (X i) (X j)-Real.exp (-t)) := by
    intro t
    unfold sphereGaussianOffDiagonal8
    have hc : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, Real.exp (-t) = ((N:ℝ)-1)*Real.exp (-t) := by
      intro i
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, hc, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hrow (i : Fin N) : IntegrableOn (fun t : ℝ => ∑ j ∈ Finset.univ.erase i,
      t⁻¹*(sphereGaussianKernel8 t (X i) (X j)-Real.exp (-t))) (Ioi 0) :=
    integrable_finsetSum _ (fun j hj =>
      (sphereGaussianPair8_frullani X (Finset.mem_erase.mp hj).1.symm).1)
  have hfun : (fun t : ℝ => t⁻¹*(sphereGaussianOffDiagonal8 t X-((N:ℝ)^2-N)*Real.exp (-t))) =
      fun t : ℝ => ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i,
        t⁻¹*(sphereGaussianKernel8 t (X i) (X j)-Real.exp (-t)) := funext hpt
  rw [hfun]
  refine ⟨integrable_finsetSum _ (fun i _ => hrow i), ?_⟩
  rw [integral_finsetSum _ (fun i _ => hrow i)]
  unfold energyLog
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j hj =>
    (sphereGaussianPair8_frullani X (Finset.mem_erase.mp hj).1.symm).1), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact (sphereGaussianPair8_frullani X (Finset.mem_erase.mp hj).1.symm).2

theorem sphereGaussianBackground8_log_integrable :
    IntegrableOn (fun t : ℝ => t⁻¹*(sphereGaussianBackground8 t-Real.exp (-t))) (Ioi 0) := by
  have hcont : ContinuousOn (fun t : ℝ => t⁻¹*(sphereGaussianBackground8 t-Real.exp (-t)))
      (Ioi 0) :=
    (continuousOn_inv₀.mono (fun t ht => ne_of_gt ht)).mul
      ((sphereGaussianBackground8_continuousOn.mono Ioi_subset_Ici_self).sub
        (by fun_prop : Continuous (fun t : ℝ => Real.exp (-t))).continuousOn)
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  apply IntegrableOn.union
  · refine Integrable.mono' (integrableOn_const (C := (5:ℝ)) (by simp)) ((hcont.mono
      Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : (0:ℝ) < t := ht.1
    have h1 := sphereGaussianBackground8_le_one ht0.le
    have h2 := sphereGaussianBackground8_ge_one_sub ht0.le
    obtain ⟨h3, h4⟩ := one_sub_exp_neg_bounds ht0.le
    have h5 : |sphereGaussianBackground8 t-Real.exp (-t)| ≤ 5*t := by
      rw [abs_le]
      constructor
      · linarith [min_le_left t 1]
      · linarith [min_le_left t 1]
    rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos ht0]
    calc t⁻¹ * |sphereGaussianBackground8 t-Real.exp (-t)| ≤ t⁻¹*(5*t) :=
          mul_le_mul_of_nonneg_left h5 (inv_nonneg.mpr ht0.le)
      _ = 5 := by field_simp
  · have hdom : IntegrableOn (fun t : ℝ => (105/32:ℝ)*t^(-2:ℝ)+Real.exp (-1*t)) (Ioi 1) :=
      ((integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul _).add
        (exp_neg_integrableOn_Ioi 1 one_pos)
    refine Integrable.mono' hdom ((hcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1:ℝ) < t := ht
    have ht0 : (0:ℝ) < t := by linarith
    have hB0 := sphereGaussianBackground8_nonneg t
    have hB := (sphereGaussianBackground8_min_bound ht0).trans (min_le_right _ _)
    have hE := Real.exp_pos (-t)
    have hinv : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht1.le
    have ht24 : t^2 ≤ t^4 := pow_le_pow_right₀ ht1.le (by norm_num)
    have hq : (105/32:ℝ)/t^4 ≤ (105/32:ℝ)*t^(-2:ℝ) := by
      rw [Real.rpow_neg ht0.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast,
        ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) ht24
    have hBt : sphereGaussianBackground8 t*t⁻¹ ≤ sphereGaussianBackground8 t := by
      have := mul_le_mul_of_nonneg_left hinv hB0
      rwa [mul_one] at this
    have hEt : t⁻¹*Real.exp (-t) ≤ Real.exp (-t) := by
      have := mul_le_mul_of_nonneg_right hinv hE.le
      rwa [one_mul] at this
    rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos ht0]
    calc t⁻¹ * |sphereGaussianBackground8 t-Real.exp (-t)|
        ≤ t⁻¹*(sphereGaussianBackground8 t+Real.exp (-t)) := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ht0.le)
          rw [abs_le]; constructor <;> linarith
      _ = sphereGaussianBackground8 t*t⁻¹+t⁻¹*Real.exp (-t) := by ring
      _ ≤ (105/32:ℝ)*t^(-2:ℝ)+Real.exp (-1*t) := by
          rw [neg_one_mul]
          linarith

/-- The continuous logarithmic energy constant of the actual uniform S⁸ (Mellin form). -/
def sphereLogConst8 : ℝ :=
  (1/2)*∫ t in Ioi 0, t⁻¹*(sphereGaussianBackground8 t-Real.exp (-t))

theorem sphereGaussianFullDefect8_log_mellin {N : ℕ} (X : Configuration N) :
    IntegrableOn (fun t : ℝ => t⁻¹*(sphereGaussianFullDefect8 t X-(N:ℝ)*(1-Real.exp (-t))))
      (Ioi 0) ∧
    (∫ t in Ioi 0, t⁻¹*(sphereGaussianFullDefect8 t X-(N:ℝ)*(1-Real.exp (-t)))) =
      2*(energyLog X-sphereLogConst8*(N:ℝ)^2) := by
  obtain ⟨h1, h2⟩ := sphereGaussianOffDiagonal8_frullani X
  have hb := sphereGaussianBackground8_log_integrable.const_mul ((N:ℝ)^2)
  have hpt : ∀ t : ℝ, t⁻¹*(sphereGaussianFullDefect8 t X-(N:ℝ)*(1-Real.exp (-t))) =
      t⁻¹*(sphereGaussianOffDiagonal8 t X-((N:ℝ)^2-N)*Real.exp (-t))-
        (N:ℝ)^2*(t⁻¹*(sphereGaussianBackground8 t-Real.exp (-t))) := by
    intro t
    unfold sphereGaussianFullDefect8
    rw [sphereGaussianSum8_diagonal]
    ring
  have hfun : (fun t : ℝ => t⁻¹*(sphereGaussianFullDefect8 t X-(N:ℝ)*(1-Real.exp (-t)))) =
      fun t : ℝ => t⁻¹*(sphereGaussianOffDiagonal8 t X-((N:ℝ)^2-N)*Real.exp (-t))-
        (N:ℝ)^2*(t⁻¹*(sphereGaussianBackground8 t-Real.exp (-t))) := funext hpt
  rw [hfun]
  refine ⟨h1.sub hb, ?_⟩
  rw [integral_sub h1 hb, h2, integral_const_mul]
  unfold sphereLogConst8
  ring

/-- Change of variables `t = c α` for the scale-invariant weight `t⁻¹`. -/
theorem inv_mellin_scale {c : ℝ} (hc : 0 < c) {h : ℝ → ℝ}
    (hi : IntegrableOn (fun t : ℝ => t⁻¹*h t) (Ioi 0)) :
    IntegrableOn (fun α : ℝ => α⁻¹*h (c*α)) (Ioi 0) ∧
    (∫ α in Ioi 0, α⁻¹*h (c*α)) = ∫ t in Ioi 0, t⁻¹*h t := by
  set g : ℝ → ℝ := fun t => t⁻¹*h t with hg
  have hcomp : ∀ α ∈ Ioi (0:ℝ), α⁻¹*h (c*α) = c*g (c*α) := by
    intro α hα
    have hα0 : (0:ℝ) < α := hα
    simp only [hg]
    field_simp
  have hgc : IntegrableOn (fun α : ℝ => g (c*α)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff g 0 hc).mpr
    simpa only [mul_zero] using hi
  constructor
  · exact IntegrableOn.congr_fun (Integrable.const_mul hgc c) (fun α hα => (hcomp α hα).symm)
      measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi hcomp, integral_const_mul,
      integral_comp_mul_left_Ioi g 0 hc, mul_zero, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ hc.ne', one_mul]

/-- `κ = ∫₀^∞ α⁻¹ (e^(-α) - 1_{(0,1)}(α)) dα` (Euler's constant with a minus sign). -/
def logGaussianConst : ℝ :=
  ∫ α in Ioi 0, α⁻¹*(Real.exp (-α)-(Ioo (0:ℝ) 1).indicator 1 α)

theorem logGaussian_integrable {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun α : ℝ => α⁻¹*(Real.exp (-(c*α))-(Ioo (0:ℝ) 1).indicator 1 α)) (Ioi 0) := by
  have h1 := (frullani_exp hc).1
  have hk : IntegrableOn (fun α : ℝ => α⁻¹*(Real.exp (-α)-(Ioo (0:ℝ) 1).indicator 1 α))
      (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
    apply IntegrableOn.union
    · refine Integrable.mono' (integrableOn_const (C := (1:ℝ)) (by simp)) ?_ ?_
      · have hm : Measurable (fun α : ℝ => α⁻¹*(Real.exp (-α)-(Ioo (0:ℝ) 1).indicator 1 α)) :=
          measurable_inv.mul ((Real.measurable_exp.comp measurable_neg).sub
            (measurable_const.indicator measurableSet_Ioo))
        exact hm.aestronglyMeasurable
      · have hne : ∀ᵐ α : ℝ ∂volume.restrict (Ioc 0 1), α ≠ 1 := by
          apply Filter.Eventually.mono (compl_mem_ae_iff.mpr (measure_singleton (1 : ℝ)) :
            ∀ᵐ α : ℝ ∂volume.restrict (Ioc 0 1), α ∈ ({1} : Set ℝ)ᶜ)
          intro α hα
          simpa using hα
        filter_upwards [ae_restrict_mem measurableSet_Ioc, hne] with α hα hα1
        have hmem : α ∈ Ioo (0:ℝ) 1 := ⟨hα.1, lt_of_le_of_ne hα.2 hα1⟩
        rw [indicator_of_mem hmem, Pi.one_apply, Real.norm_eq_abs, abs_mul, abs_inv,
          abs_of_pos hα.1]
        obtain ⟨h3, h4⟩ := one_sub_exp_neg_bounds hα.1.le
        rw [abs_of_nonpos (by linarith), neg_sub]
        calc α⁻¹*(1-Real.exp (-α)) ≤ α⁻¹*α :=
              mul_le_mul_of_nonneg_left (h4.trans (min_le_left _ _)) (inv_nonneg.mpr hα.1.le)
          _ = 1 := inv_mul_cancel₀ hα.1.ne'
    · refine Integrable.mono' (exp_neg_integrableOn_Ioi 1 one_pos) ?_ ?_
      · exact ((measurable_inv.mul ((Real.measurable_exp.comp measurable_neg).sub
          (measurable_const.indicator measurableSet_Ioo))).aestronglyMeasurable)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
        have hα1 : (1:ℝ) < α := hα
        have hnot : α ∉ Ioo (0:ℝ) 1 := fun h => by linarith [h.2]
        rw [indicator_of_notMem hnot, sub_zero, Real.norm_eq_abs, abs_mul, abs_inv,
          abs_of_pos (by linarith), abs_of_pos (Real.exp_pos _), neg_one_mul]
        calc α⁻¹*Real.exp (-α) ≤ 1*Real.exp (-α) :=
              mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hα1.le) (Real.exp_pos _).le
          _ = Real.exp (-α) := one_mul _
  refine (h1.add hk).congr_fun (fun α _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]
  ring

theorem logGaussian_integral {c : ℝ} (hc : 0 < c) :
    (∫ α in Ioi 0, α⁻¹*(Real.exp (-(c*α))-(Ioo (0:ℝ) 1).indicator 1 α)) =
      logGaussianConst-Real.log c := by
  obtain ⟨h1, h2⟩ := frullani_exp hc
  have hk : IntegrableOn (fun α : ℝ => α⁻¹*(Real.exp (-α)-(Ioo (0:ℝ) 1).indicator 1 α))
      (Ioi 0) := by
    have := logGaussian_integrable (c := 1) one_pos
    simpa using this
  have he : (fun α : ℝ => α⁻¹*(Real.exp (-(c*α))-(Ioo (0:ℝ) 1).indicator 1 α)) =
      fun α : ℝ => α⁻¹*(Real.exp (-(c*α))-Real.exp (-α))+
        α⁻¹*(Real.exp (-α)-(Ioo (0:ℝ) 1).indicator 1 α) := by
    funext α
    ring
  rw [he, integral_add h1 hk, h2]
  unfold logGaussianConst
  ring

/-- The logarithmic profile integral `J_N = ∫ α⁻¹ (F_N(α) + 1_{(0,1)}(α)) dα`. -/
def sphereLogProfileIntegral8 {N : ℕ} (X : Configuration N) : ℝ :=
  ∫ α in Ioi 0, α⁻¹*(sphereGaussianCenteredScaled8 α X+(Ioo (0:ℝ) 1).indicator 1 α)

/-- The normalized logarithmic energy `(E_log - W N² + (N/8) log N)/N`. -/
def normalizedEnergyLog8 {N : ℕ} (X : Configuration N) : ℝ :=
  (energyLog X-sphereLogConst8*(N:ℝ)^2+(N:ℝ)/8*Real.log N)/(N:ℝ)

theorem sphereGaussianCenteredScaled8_log_integrable {N : ℕ} (hN : 0 < N) (X : Configuration N) :
    IntegrableOn (fun α : ℝ =>
      α⁻¹*(sphereGaussianCenteredScaled8 α X+(Ioo (0:ℝ) 1).indicator 1 α)) (Ioi 0) := by
  have hc := sphereGaussianDensityFactor8_pos hN
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h1 := (inv_mellin_scale hc (sphereGaussianFullDefect8_log_mellin X).1).1
  have h2 := logGaussian_integrable hc
  have h3 : IntegrableOn (fun α : ℝ => (N:ℝ)⁻¹*(α⁻¹*(sphereGaussianFullDefect8
      (sphereGaussianDensityFactor8 N*α) X-(N:ℝ)*(1-Real.exp (-(sphereGaussianDensityFactor8 N*α))))))
      (Ioi 0) := h1.const_mul _
  refine (h3.sub h2).congr_fun (fun α _ => ?_) measurableSet_Ioi
  simp only [Pi.sub_apply]
  rw [sphereGaussianFullDefect8_scaled hN]
  field_simp
  ring

/-- Density-scale Mellin form of the normalized logarithmic energy. -/
theorem normalizedEnergyLog8_gaussian_mellin {N : ℕ} (hN : 0 < N) (X : Configuration N) :
    normalizedEnergyLog8 X = (1/2)*(sphereLogProfileIntegral8 X+logGaussianConst-
      Real.log Real.pi+(1/4)*Real.log (sphereArea8.real univ)) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
  have hc := sphereGaussianDensityFactor8_pos hN
  set c := sphereGaussianDensityFactor8 N with hcdef
  obtain ⟨hm1, hm2⟩ := sphereGaussianFullDefect8_log_mellin X
  obtain ⟨hs1, hs2⟩ := inv_mellin_scale hc hm1
  rw [hm2] at hs2
  have hpt : ∀ α : ℝ, α⁻¹*(sphereGaussianFullDefect8 (c*α) X-(N:ℝ)*(1-Real.exp (-(c*α)))) =
      (N:ℝ)*(α⁻¹*(sphereGaussianCenteredScaled8 α X+(Ioo (0:ℝ) 1).indicator 1 α))+
        (N:ℝ)*(α⁻¹*(Real.exp (-(c*α))-(Ioo (0:ℝ) 1).indicator 1 α)) := by
    intro α
    rw [hcdef, sphereGaussianFullDefect8_scaled hN]
    ring
  simp_rw [hpt] at hs2
  rw [integral_add ((sphereGaussianCenteredScaled8_log_integrable hN X).const_mul _)
    ((logGaussian_integrable hc).const_mul _), integral_const_mul, integral_const_mul,
    logGaussian_integral hc] at hs2
  have hlogc : Real.log c = Real.log Real.pi+(1/4)*(Real.log N-Real.log (sphereArea8.real univ)) := by
    rw [hcdef]
    unfold sphereGaussianDensityFactor8 sphereGaussianScale8
    rw [mul_one, Real.log_mul Real.pi_pos.ne' (by positivity), Real.log_rpow (by positivity),
      Real.log_div hNR.ne' hA.ne']
  unfold normalizedEnergyLog8
  unfold sphereLogProfileIntegral8
  rw [hlogc] at hs2
  rw [div_eq_iff hNR.ne']
  linear_combination (-1/2:ℝ)*hs2

#print axioms exp_sub_exp_bound
#print axioms frullani_exp
#print axioms gaussianPair_frullani
#print axioms sphereGaussianPair8_frullani
#print axioms sphereGaussianOffDiagonal8_frullani
#print axioms sphereGaussianBackground8_log_integrable
#print axioms sphereGaussianFullDefect8_log_mellin
#print axioms inv_mellin_scale
#print axioms logGaussian_integrable
#print axioms logGaussian_integral
#print axioms sphereGaussianCenteredScaled8_log_integrable
#print axioms normalizedEnergyLog8_gaussian_mellin

end SphericalRiesz
