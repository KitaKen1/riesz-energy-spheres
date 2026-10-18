import E8Leech.WindowScales

/-!
# Matching the BRR logarithmic window and exponential error

Fix the known exponent `p = 25/78`. For `η = K * δ^p`, write
`δ = exp (-u)` and `v = p*u - log K`. Bound `log v` between half of
`log u` and `log u` by using the lower bound `v ≥ (p/2)*u`.
This avoids differentiating `u/log u`, and even avoids a square-root comparison.
These are scalar estimates only; no BRR or CKMRV theorem is asserted here.
-/

namespace E8Leech

open Filter

theorem scaled_excess_exp_neg {K : ℝ} (hK : 0 < K) (p u : ℝ) :
    K * (Real.exp (-u)) ^ p = Real.exp (-(p * u - Real.log K)) := by
  rw [exp_neg_rpow]
  calc
    _ = Real.exp (Real.log K) * Real.exp (-p * u) := by rw [Real.exp_log hK]
    _ = Real.exp (Real.log K + -p * u) := (Real.exp_add _ _).symm
    _ = Real.exp (-(p * u - Real.log K)) := by congr 1; ring

theorem scaled_log_parameter_bounds {p K u : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hK : 1 ≤ K) (hu : 1 < u)
    (hshift : 2 * Real.log K / p ≤ u) :
    p / 2 * u ≤ p * u - Real.log K ∧ p * u - Real.log K ≤ u := by
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hs : 2 * Real.log K ≤ u * p := (div_le_iff₀ hp).mp hshift
  have hpu : p * u ≤ u := by nlinarith
  constructor <;> nlinarith

theorem scaled_log_denominator_bounds {p K u : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hK : 1 ≤ K) (hu : 1 < u)
    (hshift : 2 * Real.log K / p ≤ u)
    (hlog : -2 * Real.log (p / 2) ≤ Real.log u) :
    0 < Real.log (p * u - Real.log K) ∧
      Real.log u / 2 ≤ Real.log (p * u - Real.log K) ∧
      Real.log (p * u - Real.log K) ≤ Real.log u := by
  have hb := scaled_log_parameter_bounds hp hp1 hK hu hshift
  have hsmall : 0 < p / 2 * u := mul_pos (by linarith) (by linarith)
  have hlow := Real.log_le_log hsmall hb.1
  rw [Real.log_mul (by linarith : p / 2 ≠ 0) (by linarith : u ≠ 0)] at hlow
  have hhalf : Real.log u / 2 ≤ Real.log (p * u - Real.log K) := by linarith
  exact ⟨lt_of_lt_of_le (half_pos (Real.log_pos hu)) hhalf, hhalf,
    Real.log_le_log (hsmall.trans_le hb.1) hb.2⟩

theorem scaled_observationRadius_bounds {p K u : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hK : 1 ≤ K) (hu : 1 < u)
    (hshift : 2 * Real.log K / p ≤ u)
    (hlog : -2 * Real.log (p / 2) ≤ Real.log u) :
    0 < observationRadius (K * (Real.exp (-u)) ^ p) ∧
      p / 2 * observationRadius (Real.exp (-u)) ≤
        observationRadius (K * (Real.exp (-u)) ^ p) ∧
      observationRadius (K * (Real.exp (-u)) ^ p) ≤
        2 * p * observationRadius (Real.exp (-u)) := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  rw [scaled_excess_exp_neg hK0, observationRadius_exp_neg, observationRadius_exp_neg]
  have hb := scaled_log_parameter_bounds hp hp1 hK hu hshift
  have hd := scaled_log_denominator_bounds hp hp1 hK hu hshift hlog
  have hv : 0 < p * u - Real.log K := (mul_pos (by linarith) (by linarith)).trans_le hb.1
  have hu0 : 0 < u := by linarith
  have hlu : 0 < Real.log u := Real.log_pos hu
  have hlow : p / 2 * (u / Real.log u) ≤
      (p * u - Real.log K) / Real.log (p * u - Real.log K) := by
    calc
      _ = (p / 2 * u) / Real.log u := by ring
      _ ≤ (p * u - Real.log K) / Real.log u := div_le_div_of_nonneg_right hb.1 hlu.le
      _ ≤ (p * u - Real.log K) / Real.log (p * u - Real.log K) :=
        div_le_div_of_nonneg_left hv.le hd.1 hd.2.2
  have hhigh : (p * u - Real.log K) / Real.log (p * u - Real.log K) ≤
      2 * p * (u / Real.log u) := by
    calc
      _ ≤ (p * u - Real.log K) / (Real.log u / 2) :=
        div_le_div_of_nonneg_left hv.le (half_pos hlu) hd.2.1
      _ ≤ (p * u) / (Real.log u / 2) :=
        div_le_div_of_nonneg_right (by linarith [Real.log_nonneg hK]) (half_pos hlu).le
      _ = 2 * p * (u / Real.log u) := by ring
  exact ⟨div_pos hv hd.1, hlow, hhigh⟩

theorem eventually_scaled_observationRadius_bounds (p K : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hK : 1 ≤ K) :
    ∀ᶠ u : ℝ in atTop,
      0 < observationRadius (K * (Real.exp (-u)) ^ p) ∧
      p / 2 * observationRadius (Real.exp (-u)) ≤
        observationRadius (K * (Real.exp (-u)) ^ p) ∧
      observationRadius (K * (Real.exp (-u)) ^ p) ≤
        2 * p * observationRadius (Real.exp (-u)) := by
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    eventually_ge_atTop (2 * Real.log K / p),
    eventually_ge_atTop (Real.exp (-2 * Real.log (p / 2)))] with u hu hs hl
  have hu1 : 1 < u := lt_of_lt_of_le (by simp : 1 < Real.exp 1) hu
  have hlog : -2 * Real.log (p / 2) ≤ Real.log u := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hl
  exact scaled_observationRadius_bounds hp hp1 hK hu1 hs hlog

/-- The expanded ball contains a radius-`Rη` ball and fits the BRR diameter budget. -/
theorem brr_expanded_radius_bounds {Rδ Rη a : ℝ}
    (hRδ : 0 ≤ Rδ) (hlow : (25 / 156 : ℝ) * Rδ ≤ Rη)
    (hhigh : Rη ≤ (25 / 39 : ℝ) * Rδ) (ha1 : 1 ≤ a) (ha2 : a ≤ 2) :
    Rη ≤ a * Rδ ∧ 2 * (a * Rδ) ≤ (624 / 25 : ℝ) * Rη := by
  constructor <;> nlinarith

theorem brr_diameter_constants :
    (624 / 25 : ℝ) ≤ 2 ^ (20 : ℕ) ∧ (624 / 25 : ℝ) ≤ 2 ^ (140 : ℕ) := by
  norm_num

theorem brr_exponential_factor_le {K c u : ℝ} (hc : 0 ≤ c)
    (hu : 1 < u) (hlog : 400 * c ≤ Real.log u)
    (hupper : observationRadius (K * (Real.exp (-u)) ^ (25 / 78 : ℝ)) ≤
      (25 / 39 : ℝ) * observationRadius (Real.exp (-u))) :
    c * observationRadius (K * (Real.exp (-u)) ^ (25 / 78 : ℝ)) ≤ u / 624 := by
  have hlu : 0 < Real.log u := Real.log_pos hu
  have hmul : c * ((25 / 39 : ℝ) * observationRadius (Real.exp (-u))) ≤ u / 624 := by
    rw [observationRadius_exp_neg]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 624)).mpr
    have hfrac : c * (25 / 39 * (u / Real.log u)) * 624 = 400 * c * u / Real.log u := by ring
    rw [hfrac]
    apply (div_le_iff₀ hlu).mpr
    nlinarith
  exact (mul_le_mul_of_nonneg_left hupper hc).trans hmul

/-- Retain the positive exponent margin `49/624 - 1/13 = 1/624`. -/
theorem brr_position_error_exp_neg {K c u : ℝ} (hK : 1 ≤ K) (hc : 0 ≤ c)
    (hu : 1 < u) (hlog : 400 * c ≤ Real.log u)
    (hupper : observationRadius (K * (Real.exp (-u)) ^ (25 / 78 : ℝ)) ≤
      (25 / 39 : ℝ) * observationRadius (Real.exp (-u))) :
    Real.exp (c * observationRadius (K * (Real.exp (-u)) ^ (25 / 78 : ℝ))) *
        (K * (Real.exp (-u)) ^ (25 / 78 : ℝ)) ^ (1 / 4 : ℝ) ≤
      K ^ (1 / 4 : ℝ) * (Real.exp (-u)) ^ (49 / 624 : ℝ) := by
  have he := brr_exponential_factor_le hc hu hlog hupper
  rw [Real.mul_rpow (by linarith : 0 ≤ K) (Real.rpow_nonneg (Real.exp_pos _).le _),
    ← Real.rpow_mul (Real.exp_pos _).le]
  norm_num
  simp only [exp_neg_rpow]
  calc
    _ = K ^ (1 / 4 : ℝ) * Real.exp
        (c * observationRadius (K * Real.exp (-(25 / 78 : ℝ) * u)) -
          (25 / 312 : ℝ) * u) := by
            rw [sub_eq_add_neg, Real.exp_add]
            ring
    _ ≤ K ^ (1 / 4 : ℝ) * Real.exp (-(49 / 624 : ℝ) * u) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
      apply Real.exp_le_exp.mpr
      rw [exp_neg_rpow] at he
      linarith

theorem brr_position_error_one_thirteenth_exp_neg {K c u : ℝ}
    (hK : 1 ≤ K) (hc : 0 ≤ c) (hu : 1 < u) (hlog : 400 * c ≤ Real.log u)
    (hupper : observationRadius (K * (Real.exp (-u)) ^ (25 / 78 : ℝ)) ≤
      (25 / 39 : ℝ) * observationRadius (Real.exp (-u))) :
    Real.exp (c * observationRadius (K * (Real.exp (-u)) ^ (25 / 78 : ℝ))) *
        (K * (Real.exp (-u)) ^ (25 / 78 : ℝ)) ^ (1 / 4 : ℝ) ≤
      K ^ (1 / 4 : ℝ) * (Real.exp (-u)) ^ (1 / 13 : ℝ) := by
  apply (brr_position_error_exp_neg hK hc hu hlog hupper).trans
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
  exact Real.rpow_le_rpow_of_exponent_ge (Real.exp_pos _)
    (Real.exp_le_one_iff.mpr (by linarith)) (by norm_num)

theorem eventually_scaled_excess_small (p K η₀ : ℝ)
    (hp : 0 < p) (hK : 0 < K) (hη₀ : 0 < η₀) :
    ∀ᶠ u : ℝ in atTop, 0 < K * (Real.exp (-u)) ^ p ∧
      K * (Real.exp (-u)) ^ p < η₀ := by
  filter_upwards [eventually_polynomial_exp_lt 0 p (η₀ / K) hp (div_pos hη₀ hK)] with u hu
  have hpos := Real.exp_pos (-p * u)
  have hlt : Real.exp (-p * u) < η₀ / K := by
    simpa only [Real.rpow_zero, one_mul] using hu
  rw [exp_neg_rpow]
  exact ⟨mul_pos hK hpos, by nlinarith [(lt_div_iff₀ hK).mp hlt]⟩

theorem eventually_brr_scale_parameters (K c η₀ : ℝ)
    (hK : 1 ≤ K) (hc : 0 ≤ c) (hη₀ : 0 < η₀) :
    ∀ᶠ u : ℝ in atTop,
      0 < K * (Real.exp (-u)) ^ (25 / 78 : ℝ) ∧
      K * (Real.exp (-u)) ^ (25 / 78 : ℝ) < η₀ ∧
      0 < observationRadius (K * (Real.exp (-u)) ^ (25 / 78 : ℝ)) ∧
      (25 / 156 : ℝ) * observationRadius (Real.exp (-u)) ≤
        observationRadius (K * (Real.exp (-u)) ^ (25 / 78 : ℝ)) ∧
      observationRadius (K * (Real.exp (-u)) ^ (25 / 78 : ℝ)) ≤
        (25 / 39 : ℝ) * observationRadius (Real.exp (-u)) ∧
      Real.exp (c * observationRadius (K * (Real.exp (-u)) ^ (25 / 78 : ℝ))) *
          (K * (Real.exp (-u)) ^ (25 / 78 : ℝ)) ^ (1 / 4 : ℝ) ≤
        K ^ (1 / 4 : ℝ) * (Real.exp (-u)) ^ (1 / 13 : ℝ) := by
  filter_upwards [eventually_scaled_observationRadius_bounds (25 / 78) K
      (by norm_num) (by norm_num) hK,
    eventually_scaled_excess_small (25 / 78) K η₀ (by norm_num) (by linarith) hη₀,
    eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (Real.exp (400 * c))]
    with u hw hη hu hcU
  have hu1 : 1 < u := lt_of_lt_of_le (by simp : 1 < Real.exp 1) hu
  have hlog : 400 * c ≤ Real.log u := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hcU
  have hlow : (25 / 156 : ℝ) * observationRadius (Real.exp (-u)) ≤
      observationRadius (K * (Real.exp (-u)) ^ (25 / 78 : ℝ)) := by
    norm_num at hw
    exact hw.2.1
  have hhigh : observationRadius (K * (Real.exp (-u)) ^ (25 / 78 : ℝ)) ≤
      (25 / 39 : ℝ) * observationRadius (Real.exp (-u)) := by
    norm_num at hw
    exact hw.2.2
  exact ⟨hη.1, hη.2, hw.1, hlow, hhigh,
    brr_position_error_one_thirteenth_exp_neg hK hc hu1 hlog hhigh⟩

/-- All constants precede `δ`; in particular this threshold has no law parameter. -/
theorem exists_small_brr_scale_parameters (K c η₀ : ℝ)
    (hK : 1 ≤ K) (hc : 0 ≤ c) (hη₀ : 0 < η₀) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        0 < K * δ ^ (25 / 78 : ℝ) ∧ K * δ ^ (25 / 78 : ℝ) < η₀ ∧
        0 < observationRadius (K * δ ^ (25 / 78 : ℝ)) ∧
        (25 / 156 : ℝ) * observationRadius δ ≤
          observationRadius (K * δ ^ (25 / 78 : ℝ)) ∧
        observationRadius (K * δ ^ (25 / 78 : ℝ)) ≤
          (25 / 39 : ℝ) * observationRadius δ ∧
        Real.exp (c * observationRadius (K * δ ^ (25 / 78 : ℝ))) *
            (K * δ ^ (25 / 78 : ℝ)) ^ (1 / 4 : ℝ) ≤ K ^ (1 / 4 : ℝ) * δ ^ (1 / 13 : ℝ) := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp (eventually_brr_scale_parameters K c η₀ hK hc hη₀)
  let U := max M (Real.exp 1 + 1)
  have hMU : M ≤ U := le_max_left _ _
  have hEU : Real.exp 1 < U := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  refine ⟨Real.exp (-U), Real.exp_pos _, Real.exp_lt_exp.mpr (by linarith), ?_⟩
  intro δ hδ hsmall
  have hlog : Real.log δ < -U := by
    simpa only [Real.log_exp] using Real.log_lt_log hδ hsmall
  have h := hM (-Real.log δ) (by linarith : M ≤ -Real.log δ)
  simpa only [neg_neg, Real.exp_log hδ] using h

theorem inverse_contraction_bounds {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    1 ≤ (1 - t)⁻¹ ∧ (1 - t)⁻¹ ≤ 2 := by
  have hpos : 0 < 1 - t := by linarith
  constructor
  · exact (one_le_inv₀ hpos).mpr (by linarith)
  · apply (inv_le_iff_one_le_mul₀ hpos).mpr
    linarith

theorem exists_small_brr_restoration_parameters (K c η₀ : ℝ)
    (hK : 1 ≤ K) (hc : 0 ≤ c) (hη₀ : 0 < η₀) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < Real.exp (-Real.exp 1) ∧
      ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        0 < δ ^ (1 / 3 : ℝ) ∧ δ ^ (1 / 3 : ℝ) ≤ 1 / 2 ∧
        0 < K * δ ^ (25 / 78 : ℝ) ∧ K * δ ^ (25 / 78 : ℝ) < η₀ ∧
        0 < observationRadius (K * δ ^ (25 / 78 : ℝ)) ∧
        observationRadius (K * δ ^ (25 / 78 : ℝ)) ≤
          (1 - δ ^ (1 / 3 : ℝ))⁻¹ * observationRadius δ ∧
        2 * ((1 - δ ^ (1 / 3 : ℝ))⁻¹ * observationRadius δ) ≤
          (624 / 25 : ℝ) * observationRadius (K * δ ^ (25 / 78 : ℝ)) ∧
        Real.exp (c * observationRadius (K * δ ^ (25 / 78 : ℝ))) *
            (K * δ ^ (25 / 78 : ℝ)) ^ (1 / 4 : ℝ) ≤ K ^ (1 / 4 : ℝ) * δ ^ (1 / 13 : ℝ) ∧
        4 * δ ^ (1 / 3 : ℝ) * observationRadius δ ≤ δ ^ (1 / 13 : ℝ) := by
  obtain ⟨δ₁, h₁, hs₁, hb⟩ := exists_small_brr_scale_parameters K c η₀ hK hc hη₀
  obtain ⟨δ₂, h₂, hs₂, hr⟩ := exists_one_third_restoration_parameters
  refine ⟨min δ₁ δ₂, lt_min h₁ h₂, lt_of_le_of_lt (min_le_left _ _) hs₁, ?_⟩
  intro δ hδ hsmall
  have hb' := hb δ hδ (hsmall.trans_le (min_le_left _ _))
  have hr' := hr δ hδ (hsmall.trans_le (min_le_right _ _))
  have ha := inverse_contraction_bounds hr'.1.le hr'.2.1
  have hball := brr_expanded_radius_bounds hr'.2.2.2.1.le hb'.2.2.2.1
    hb'.2.2.2.2.1 ha.1 ha.2
  exact ⟨hr'.1, hr'.2.1, hb'.1, hb'.2.1, hb'.2.2.1, hball.1, hball.2,
    hb'.2.2.2.2.2, hr'.2.2.2.2⟩

end E8Leech
