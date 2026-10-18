import E8Leech.CKMRVLaplaceHolomorphic

/-!
# Holomorphy in `τ` of the Leech plus Laplace integral (CKMRV (5.1), P4d-3)

`K₊⁽²⁴⁾(τ, z) = C⁻¹ (Δ(z)⁻¹ A(τ, z) + B(τ, z) / (Δ(z)² (j(τ) − j(z))))`. Its `τ`-coefficients
span the four functions `A₀, A₁, A₂, j A₁`; in this basis
`K₊ = C⁻¹ ∑_c coef_c(τ) (a_c(z)/Δ(z) + b_c(z) / (Δ(z)² (j(τ) − j(z))))`.

* On `t ≥ 1` each term is `O(t² e^{2πt})`, integrable against `e^{−πr²t}` for `r² > 2`.
* On `0 < t ≤ 1` the single terms are too large; they are rewritten with
  `1/(a − x) = −1/x − a/x² + a²/(x² (a − x))` at `x = j(z)`:
  `a_c/Δ + b_c/(Δ² (j(τ) − j)) = (a_c E₄³ − b_c)/(Δ E₄³) − j(τ) b_c/E₄⁶ + j(τ)² b_c/(E₄⁶ (j(τ) − j))`.
  Known answer first: after `z ↦ −1/z` every `a_c E₄³ − b_c` is `O(s²)`, because in the chosen
  basis the constant `s`-coefficients cancel inside each factor (for instance
  `(8640 E₄ − 12096 E₂²) E₄³ + 3456 E₁₄ E₂ = O(q²)`). So every piece is bounded near `t = 0`.

Each piece is a constant or a Stieltjes transform of `j(it) ∈ [1728, ∞)` over `(0, 1]` or
`(1, ∞)`, and the integral is a polynomial in `j(τ)` and the coefficients with holomorphic
coefficients off the cut.
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Asymptotics MeasureTheory Set Metric
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm

/-! ## Stieltjes transforms over a measurable set -/

theorem integrableOn_stieltjes_set {g h : ℝ → ℂ} {G : ℝ → ℝ} {C : Set ℂ} {s : Set ℝ}
    (hC : IsClosed C) (hCne : C.Nonempty) (hs : MeasurableSet s) (hG : IntegrableOn G s)
    (hg : ContinuousOn g s) (hh : ContinuousOn h s) (hhC : ∀ t ∈ s, h t ∈ C)
    (hgG : ∀ t ∈ s, ‖g t‖ ≤ G t * (1 + ‖h t‖)) {w : ℂ} (hw : w ∉ C) :
    IntegrableOn (fun t => g t / (w - h t)) s := by
  have hδ : 0 < infDist w C := (hC.notMem_iff_infDist_pos hCne).mp hw
  set κ := infDist w C / (1 + ‖w‖ + infDist w C) with hκ
  have hκ0 : 0 < κ := div_pos hδ (by positivity)
  have hlow : ∀ t ∈ s, κ * (1 + ‖h t‖) ≤ ‖w - h t‖ := fun t ht =>
    one_add_norm_le_of_dist hδ (norm_sub_ge_infDist (hhC t ht))
  have hne : ∀ t ∈ s, w - h t ≠ 0 := fun t ht h0 => by
    have h1 := hlow t ht
    rw [h0, norm_zero] at h1
    nlinarith [mul_pos hκ0 (by positivity : (0 : ℝ) < 1 + ‖h t‖)]
  refine Integrable.mono' (Integrable.div_const hG κ)
    ((hg.div (continuousOn_const.sub hh) hne).aestronglyMeasurable hs) ?_
  refine (ae_restrict_iff' hs).mpr (Eventually.of_forall fun t ht => ?_)
  have hG0 : 0 ≤ G t := nonneg_of_norm_le_mul (norm_nonneg _) (hgG t ht)
  rw [norm_div, div_le_div_iff₀ (norm_pos_iff.mpr (hne t ht)) hκ0]
  calc ‖g t‖ * κ ≤ G t * (1 + ‖h t‖) * κ := mul_le_mul_of_nonneg_right (hgG t ht) hκ0.le
    _ = G t * (κ * (1 + ‖h t‖)) := by ring
    _ ≤ G t * ‖w - h t‖ := mul_le_mul_of_nonneg_left (hlow t ht) hG0

theorem differentiableOn_stieltjes_set {g h : ℝ → ℂ} {G : ℝ → ℝ} {C : Set ℂ} {s : Set ℝ}
    (hC : IsClosed C) (hCne : C.Nonempty) (hs : MeasurableSet s) (hG : IntegrableOn G s)
    (hg : ContinuousOn g s) (hh : ContinuousOn h s) (hhC : ∀ t ∈ s, h t ∈ C)
    (hgG : ∀ t ∈ s, ‖g t‖ ≤ G t * (1 + ‖h t‖)) :
    DifferentiableOn ℂ (fun w => ∫ t in s, g t / (w - h t)) Cᶜ := by
  intro w₀ hw₀
  have hδ : 0 < infDist w₀ C := (hC.notMem_iff_infDist_pos hCne).mp hw₀
  set δ := infDist w₀ C with hδdef
  set κ := δ / 2 / (1 + ‖w₀‖ + δ) with hκdef
  have hκ0 : 0 < κ := div_pos (half_pos hδ) (by positivity)
  have hlow : ∀ w ∈ ball w₀ (δ / 2), ∀ t ∈ s, κ * (1 + ‖h t‖) ≤ ‖w - h t‖ := by
    intro w hw t ht
    have h1 : δ ≤ ‖w₀ - h t‖ := norm_sub_ge_infDist (hhC t ht)
    have h2 : ‖w - w₀‖ < δ / 2 := by rw [← dist_eq_norm]; exact hw
    have h3 : ‖w₀ - h t‖ ≤ ‖w - h t‖ + ‖w - w₀‖ := by
      calc ‖w₀ - h t‖ = ‖(w - h t) - (w - w₀)‖ := by congr 1; ring
        _ ≤ ‖w - h t‖ + ‖w - w₀‖ := norm_sub_le _ _
    have h4 : ‖h t‖ ≤ ‖w₀‖ + ‖w₀ - h t‖ := by simpa using norm_sub_le w₀ (w₀ - h t)
    have hA : δ / 2 ≤ ‖w - h t‖ := by linarith
    have hx : ‖h t‖ ≤ ‖w₀‖ + ‖w - h t‖ + δ / 2 := by linarith
    rw [hκdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hx (by positivity : (0 : ℝ) ≤ δ / 2),
      mul_le_mul_of_nonneg_right hA (by positivity : (0 : ℝ) ≤ 1 + ‖w₀‖ + δ / 2)]
  have hne : ∀ w ∈ ball w₀ (δ / 2), ∀ t ∈ s, w - h t ≠ 0 := fun w hw t ht h0 => by
    have h1 := hlow w hw t ht
    rw [h0, norm_zero] at h1
    nlinarith [mul_pos hκ0 (by positivity : (0 : ℝ) < 1 + ‖h t‖)]
  have hw₀b : w₀ ∈ ball w₀ (δ / 2) := mem_ball_self (half_pos hδ)
  have hdiff : ∀ w ∈ ball w₀ (δ / 2), ∀ t ∈ s,
      HasDerivAt (fun w => g t / (w - h t)) (-g t / (w - h t) ^ 2) w := by
    intro w hw t ht
    have hd := (hasDerivAt_const w (g t)).div ((hasDerivAt_id' w).sub_const (h t))
      (hne w hw t ht)
    exact hd.congr_deriv (by ring)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict s) (F := fun w t => g t / (w - h t))
    (F' := fun w t => -g t / (w - h t) ^ 2) (bound := fun t => G t / κ ^ 2)
    (ball_mem_nhds w₀ (half_pos hδ)) ?_ ?_ ?_ ?_ ?_ ?_
  · exact key.2.differentiableAt.differentiableWithinAt
  · filter_upwards [ball_mem_nhds w₀ (half_pos hδ)] with w hw
    exact (hg.div (continuousOn_const.sub hh) (hne w hw)).aestronglyMeasurable hs
  · exact integrableOn_stieltjes_set hC hCne hs hG hg hh hhC hgG hw₀
  · exact (hg.neg.div ((continuousOn_const.sub hh).pow 2)
      fun t ht => pow_ne_zero 2 (hne w₀ hw₀b t ht)).aestronglyMeasurable hs
  · refine (ae_restrict_iff' hs).mpr (Eventually.of_forall fun t ht w hw => ?_)
    have hG0 : 0 ≤ G t := nonneg_of_norm_le_mul (norm_nonneg _) (hgG t ht)
    have hl := hlow w hw t ht
    have hpos : 0 < ‖w - h t‖ := norm_pos_iff.mpr (hne w hw t ht)
    have h1 : κ ^ 2 * (1 + ‖h t‖) ≤ ‖w - h t‖ ^ 2 := by
      have hsq : (κ * (1 + ‖h t‖)) ^ 2 ≤ ‖w - h t‖ ^ 2 := pow_le_pow_left₀ (by positivity) hl 2
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg κ) (by positivity : (0 : ℝ) ≤ 1 + ‖h t‖))
        (norm_nonneg (h t))]
    show ‖-g t / (w - h t) ^ 2‖ ≤ G t / κ ^ 2
    rw [norm_div, norm_neg, norm_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    calc ‖g t‖ * κ ^ 2 ≤ G t * (1 + ‖h t‖) * κ ^ 2 :=
          mul_le_mul_of_nonneg_right (hgG t ht) (by positivity)
      _ = G t * (κ ^ 2 * (1 + ‖h t‖)) := by ring
      _ ≤ G t * ‖w - h t‖ ^ 2 := mul_le_mul_of_nonneg_left h1 hG0
  · exact Integrable.div_const hG _
  · exact (ae_restrict_iff' hs).mpr (Eventually.of_forall fun t ht w hw => hdiff w hw t ht)

theorem jCut_nonempty : jCut.Nonempty := ⟨1728, by simp [jCut]⟩

/-! ## Integrability on `(0, 1]` and on `(1, ∞)` -/

theorem integrableOn_Ioc_of_isBigO {f : ℝ → ℂ} (hcont : ContinuousOn f (Ioc 0 1))
    (h0 : f =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ)) : IntegrableOn f (Ioc 0 1) := by
  obtain ⟨C, hC⟩ := h0.bound
  obtain ⟨u, hu, huS⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hC
  set δ : ℝ := min u 1 / 2 with hδdef
  have hmin : (0 : ℝ) < min u 1 := lt_min hu one_pos
  have hδ : 0 < δ := by positivity
  have hδu : δ < u := by
    have := min_le_left u 1
    rw [hδdef]
    linarith
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := δ) (b := 1)).exists_bound_of_continuousOn
    (hcont.mono fun t ht => ⟨lt_of_lt_of_le hδ ht.1, ht.2⟩)
  refine ⟨hcont.aestronglyMeasurable measurableSet_Ioc,
    HasFiniteIntegral.restrict_of_bounded (max M C) (by simp) ?_⟩
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
  by_cases htδ : δ ≤ t
  · exact (hM t ⟨htδ, ht.2⟩).trans (le_max_left _ _)
  · have hft : ‖f t‖ ≤ C * ‖(1 : ℝ)‖ := huS ⟨ht.1, (not_le.mp htδ).trans hδu⟩
    rw [norm_one, mul_one] at hft
    exact hft.trans (le_max_right _ _)

theorem integrableOn_Ioi_one_mul_exp_of_isBigO {f : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Ici 1)) (hinf : f =O[atTop] fun t => t * Real.exp (a * t)) :
    IntegrableOn (fun t => f t * (Real.exp (-b * t) : ℂ)) (Ioi 1) := by
  set g : ℝ → ℂ := fun t => f t * (Real.exp (-b * t) : ℂ) with hg_def
  have hgc : ContinuousOn g (Ici 1) :=
    hcont.mul (by fun_prop : Continuous fun t : ℝ => (Real.exp (-b * t) : ℂ)).continuousOn
  set ε : ℝ := (b - a) / 2
  have hε : 0 < ε := by simp only [ε]; linarith
  have hnorm : (fun t => ‖g t‖) =O[atTop] fun t => Real.exp (-ε * t) := by
    have he : (fun t : ℝ => (Real.exp (-b * t) : ℂ)) =O[atTop] fun t => Real.exp (-b * t) :=
      IsBigO.of_bound 1 (Eventually.of_forall fun t => by rw [Complex.norm_real, one_mul])
    have h1 : g =O[atTop] fun t => t * Real.exp (a * t) * Real.exp (-b * t) := hinf.mul he
    have h2 : (fun t : ℝ => t * Real.exp (a * t) * Real.exp (-b * t)) =O[atTop]
        fun t => Real.exp (-ε * t) := by
      refine IsBigO.of_bound (1 / ε) ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      have hexp : t * Real.exp (a * t) * Real.exp (-b * t) =
          t * Real.exp (-ε * t) * Real.exp (-ε * t) := by
        rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
        congr 2
        simp only [ε]
        ring
      have hlin : t ≤ Real.exp (ε * t) / ε := by
        rw [le_div_iff₀ hε]
        nlinarith [Real.add_one_le_exp (ε * t)]
      have hprod : t * Real.exp (-ε * t) ≤ 1 / ε := by
        calc t * Real.exp (-ε * t) ≤ Real.exp (ε * t) / ε * Real.exp (-ε * t) :=
              mul_le_mul_of_nonneg_right hlin (Real.exp_pos _).le
          _ = 1 / ε := by
              rw [div_mul_eq_mul_div, ← Real.exp_add]
              simp
      rw [hexp, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (mul_nonneg ht.le (Real.exp_pos _).le) (Real.exp_pos _).le),
        abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le
    exact (h1.trans h2).norm_left
  have hint := integrable_of_isBigO_exp_neg hε hgc.norm hnorm
  exact (integrable_norm_iff
    ((hgc.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)).mp hint

theorem isBigO_sq_mul_exp_shift {c ε : ℝ} (hε : 0 < ε) :
    (fun t : ℝ => t ^ 2 * Real.exp (c * t)) =O[atTop] fun t => t * Real.exp ((c + ε) * t) := by
  refine ((isBigO_sq_mul_exp hε).mul (isBigO_refl (fun t : ℝ => Real.exp (c * t)) atTop))
    |>.congr_right fun t => ?_
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem isBigO_cuspS_sq_inv_mul_sq {f : ℍ → ℂ}
    (hf : f =O[atImInfty] fun z : ℍ => ‖cuspS z‖ ^ 2) :
    (fun z => (cuspS z ^ 2)⁻¹ * f z) =O[atImInfty] fun _ => (1 : ℝ) := by
  obtain ⟨C, hC⟩ := hf.bound
  refine IsBigO.of_bound C ?_
  filter_upwards [hC] with z hz
  have hs : 0 < ‖cuspS z‖ := norm_pos_iff.mpr (cuspS_ne_zero z)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hz
  rw [norm_mul, norm_inv, norm_pow, norm_one, mul_one, inv_mul_le_iff₀ (by positivity)]
  linarith

theorem isBigO_div_discriminant_mul_of_hasExp3_sq {f : ℍ → ℂ} {k : ℂ} (hf : HasExp3 f 0 0 k) :
    (fun z => f z / (ModularForm.discriminant z * ModularForm.E₄ z ^ 3)) =O[atImInfty]
      fun _ => (1 : ℝ) := by
  have hP := hasExp3_discriminantCuspQuot_inv.tendsto
  have hE := (hasExp3_eisensteinFour.tendsto.pow 3).inv₀ (by norm_num : (1 : ℂ) ^ 3 ≠ 0)
  refine (((isBigO_cuspS_sq_inv_mul_sq hf.isBigO_sq).mul
    ((hP.mul hE).isBigO_one ℝ)).congr_right fun _ => one_mul _).congr_left fun z => ?_
  rw [discriminant_eq_cuspS_sq_mul, div_eq_mul_inv]
  ring

/-! ## The Leech plus kernel in a basis of `τ`-coefficients -/

/-- The `τ`-coefficients `A₀, A₁, A₂, j A₁`. -/
def leechPlusCoef (τ : ℍ) : Fin 4 → ℂ :=
  ![leechPlusA0 τ, leechPlusA1 τ, leechPlusA2 τ, kleinModularJ τ * leechPlusA1 τ]

/-- The `Δ⁻¹`-part of the `z`-factors. -/
def leechPlusAc (z : ℍ) : Fin 4 → ℂ :=
  ![6 * (ModularForm.E₄ z * (z : ℂ) ^ 2 - ckmrvTildePhiBasis z 2),
    8640 * (ModularForm.E₄ z * (z : ℂ) ^ 2) - 12096 * ckmrvTildePhiBasis z 2,
    6 * (ModularForm.E₄ z * (z : ℂ) ^ 2 - ckmrvTildePhiBasis z 2),
    12 * (ckmrvTildePhiBasis z 2 - ModularForm.E₄ z * (z : ℂ) ^ 2)]

/-- The `(Δ² (j(τ) − j))⁻¹`-part of the `z`-factors. -/
def leechPlusBc (z : ℍ) : Fin 4 → ℂ :=
  ![1728 * (ckmrvTildePhiBasis z 2 * ModularForm.discriminant z),
    -3456 * (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z * ckmrvTildePhiBasis z 1),
    1728 * (ModularForm.E₄ z * (z : ℂ) ^ 2 * ModularForm.discriminant z), 0]

/-- `S`-transform of `a_c E₄³ − b_c`, divided by `w¹⁴`. -/
def leechPlusCS (w : ℍ) : Fin 4 → ℂ :=
  ![6 * ((ModularForm.E₄ w - EisensteinSeries.E2 w ^ 2) * ModularForm.E₄ w ^ 3) -
      1728 * (EisensteinSeries.E2 w ^ 2 * ModularForm.discriminant w),
    (8640 * ModularForm.E₄ w - 12096 * EisensteinSeries.E2 w ^ 2) * ModularForm.E₄ w ^ 3 +
      3456 * (ModularForm.E₄ w ^ 2 * ModularForm.E₆ w * EisensteinSeries.E2 w),
    6 * ((ModularForm.E₄ w - EisensteinSeries.E2 w ^ 2) * ModularForm.E₄ w ^ 3) -
      1728 * (ModularForm.E₄ w * ModularForm.discriminant w),
    12 * ((EisensteinSeries.E2 w ^ 2 - ModularForm.E₄ w) * ModularForm.E₄ w ^ 3)]

/-- `S`-transform of `b_c`, divided by `w¹⁴`. -/
def leechPlusBS (w : ℍ) : Fin 4 → ℂ :=
  ![1728 * (EisensteinSeries.E2 w ^ 2 * ModularForm.discriminant w),
    -3456 * (ModularForm.E₄ w ^ 2 * ModularForm.E₆ w * EisensteinSeries.E2 w),
    1728 * (ModularForm.E₄ w * ModularForm.discriminant w), 0]

theorem leechPlusAz_eq_sum (τ z : ℍ) :
    leechPlusAz τ z = ∑ c, leechPlusCoef τ c * leechPlusAc z c := by
  rw [Fin.sum_univ_four]
  have h0 : leechPlusCoef τ 0 * leechPlusAc z 0 = leechPlusA0 τ *
      (6 * (ModularForm.E₄ z * (z : ℂ) ^ 2 - ckmrvTildePhiBasis z 2)) := rfl
  have h1 : leechPlusCoef τ 1 * leechPlusAc z 1 = leechPlusA1 τ *
      (8640 * (ModularForm.E₄ z * (z : ℂ) ^ 2) - 12096 * ckmrvTildePhiBasis z 2) := rfl
  have h2 : leechPlusCoef τ 2 * leechPlusAc z 2 = leechPlusA2 τ *
      (6 * (ModularForm.E₄ z * (z : ℂ) ^ 2 - ckmrvTildePhiBasis z 2)) := rfl
  have h3 : leechPlusCoef τ 3 * leechPlusAc z 3 = kleinModularJ τ * leechPlusA1 τ *
      (12 * (ckmrvTildePhiBasis z 2 - ModularForm.E₄ z * (z : ℂ) ^ 2)) := rfl
  rw [h0, h1, h2, h3, leechPlusAz, leechPlusP0, leechPlusP2]
  ring

theorem leechPlusBz_eq_sum (τ z : ℍ) :
    leechPlusBz τ z = ∑ c, leechPlusCoef τ c * leechPlusBc z c := by
  rw [Fin.sum_univ_four]
  have h0 : leechPlusCoef τ 0 * leechPlusBc z 0 = leechPlusA0 τ *
      (1728 * (ckmrvTildePhiBasis z 2 * ModularForm.discriminant z)) := rfl
  have h1 : leechPlusCoef τ 1 * leechPlusBc z 1 = leechPlusA1 τ *
      (-3456 * (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z * ckmrvTildePhiBasis z 1)) := rfl
  have h2 : leechPlusCoef τ 2 * leechPlusBc z 2 = leechPlusA2 τ *
      (1728 * (ModularForm.E₄ z * (z : ℂ) ^ 2 * ModularForm.discriminant z)) := rfl
  have h3 : leechPlusCoef τ 3 * leechPlusBc z 3 = kleinModularJ τ * leechPlusA1 τ * 0 := rfl
  rw [h0, h1, h2, h3, leechPlusBz]
  ring

theorem coe_S_smul_sq_mul (w : ℍ) : ((ModularGroup.S • w : ℍ) : ℂ) ^ 2 * (w : ℂ) ^ 2 = 1 := by
  rw [coe_S_smul, div_pow, neg_sq, one_pow, one_div_mul_cancel (pow_ne_zero 2 w.ne_zero)]

theorem leechPlusAc_S_zero (w : ℍ) :
    leechPlusAc (ModularGroup.S • w) 0 * ModularForm.E₄ (ModularGroup.S • w) ^ 3 -
      leechPlusBc (ModularGroup.S • w) 0 = (w : ℂ) ^ 14 * leechPlusCS w 0 := by
  have hq := coe_S_smul_sq_mul w
  show 6 * (ModularForm.E₄ (ModularGroup.S • w) * ((ModularGroup.S • w : ℍ) : ℂ) ^ 2 -
      ckmrvTildePhiBasis (ModularGroup.S • w) 2) * ModularForm.E₄ (ModularGroup.S • w) ^ 3 -
      1728 * (ckmrvTildePhiBasis (ModularGroup.S • w) 2 *
        ModularForm.discriminant (ModularGroup.S • w)) =
    (w : ℂ) ^ 14 * (6 * ((ModularForm.E₄ w - EisensteinSeries.E2 w ^ 2) * ModularForm.E₄ w ^ 3) -
      1728 * (EisensteinSeries.E2 w ^ 2 * ModularForm.discriminant w))
  rw [eisensteinFour_S, ckmrvTildePhiBasis_S_two, discriminant_S]
  linear_combination (6 * (w : ℂ) ^ 14 * ModularForm.E₄ w ^ 4) * hq

theorem leechPlusAc_S_one (w : ℍ) :
    leechPlusAc (ModularGroup.S • w) 1 * ModularForm.E₄ (ModularGroup.S • w) ^ 3 -
      leechPlusBc (ModularGroup.S • w) 1 = (w : ℂ) ^ 14 * leechPlusCS w 1 := by
  have hq := coe_S_smul_sq_mul w
  show (8640 * (ModularForm.E₄ (ModularGroup.S • w) * ((ModularGroup.S • w : ℍ) : ℂ) ^ 2) -
      12096 * ckmrvTildePhiBasis (ModularGroup.S • w) 2) *
        ModularForm.E₄ (ModularGroup.S • w) ^ 3 -
      -3456 * (ModularForm.E₄ (ModularGroup.S • w) ^ 2 * ModularForm.E₆ (ModularGroup.S • w) *
        ckmrvTildePhiBasis (ModularGroup.S • w) 1) =
    (w : ℂ) ^ 14 * ((8640 * ModularForm.E₄ w - 12096 * EisensteinSeries.E2 w ^ 2) *
      ModularForm.E₄ w ^ 3 +
        3456 * (ModularForm.E₄ w ^ 2 * ModularForm.E₆ w * EisensteinSeries.E2 w))
  rw [eisensteinFour_S, eisensteinSix_S, ckmrvTildePhiBasis_S_one, ckmrvTildePhiBasis_S_two]
  linear_combination (8640 * (w : ℂ) ^ 14 * ModularForm.E₄ w ^ 4) * hq

theorem leechPlusAc_S_two (w : ℍ) :
    leechPlusAc (ModularGroup.S • w) 2 * ModularForm.E₄ (ModularGroup.S • w) ^ 3 -
      leechPlusBc (ModularGroup.S • w) 2 = (w : ℂ) ^ 14 * leechPlusCS w 2 := by
  have hq := coe_S_smul_sq_mul w
  show 6 * (ModularForm.E₄ (ModularGroup.S • w) * ((ModularGroup.S • w : ℍ) : ℂ) ^ 2 -
      ckmrvTildePhiBasis (ModularGroup.S • w) 2) * ModularForm.E₄ (ModularGroup.S • w) ^ 3 -
      1728 * (ModularForm.E₄ (ModularGroup.S • w) * ((ModularGroup.S • w : ℍ) : ℂ) ^ 2 *
        ModularForm.discriminant (ModularGroup.S • w)) =
    (w : ℂ) ^ 14 * (6 * ((ModularForm.E₄ w - EisensteinSeries.E2 w ^ 2) * ModularForm.E₄ w ^ 3) -
      1728 * (ModularForm.E₄ w * ModularForm.discriminant w))
  rw [eisensteinFour_S, ckmrvTildePhiBasis_S_two, discriminant_S]
  linear_combination (6 * (w : ℂ) ^ 14 * ModularForm.E₄ w ^ 4 -
    1728 * (w : ℂ) ^ 14 * ModularForm.E₄ w * ModularForm.discriminant w) * hq

theorem leechPlusAc_S_three (w : ℍ) :
    leechPlusAc (ModularGroup.S • w) 3 * ModularForm.E₄ (ModularGroup.S • w) ^ 3 -
      leechPlusBc (ModularGroup.S • w) 3 = (w : ℂ) ^ 14 * leechPlusCS w 3 := by
  have hq := coe_S_smul_sq_mul w
  show 12 * (ckmrvTildePhiBasis (ModularGroup.S • w) 2 -
      ModularForm.E₄ (ModularGroup.S • w) * ((ModularGroup.S • w : ℍ) : ℂ) ^ 2) *
        ModularForm.E₄ (ModularGroup.S • w) ^ 3 - 0 =
    (w : ℂ) ^ 14 * (12 * ((EisensteinSeries.E2 w ^ 2 - ModularForm.E₄ w) * ModularForm.E₄ w ^ 3))
  rw [eisensteinFour_S, ckmrvTildePhiBasis_S_two]
  linear_combination (-12 * (w : ℂ) ^ 14 * ModularForm.E₄ w ^ 4) * hq

theorem leechPlusAc_S (w : ℍ) (c : Fin 4) :
    leechPlusAc (ModularGroup.S • w) c * ModularForm.E₄ (ModularGroup.S • w) ^ 3 -
      leechPlusBc (ModularGroup.S • w) c = (w : ℂ) ^ 14 * leechPlusCS w c := by
  fin_cases c
  · exact leechPlusAc_S_zero w
  · exact leechPlusAc_S_one w
  · exact leechPlusAc_S_two w
  · exact leechPlusAc_S_three w

theorem leechPlusBc_S (w : ℍ) (c : Fin 4) :
    leechPlusBc (ModularGroup.S • w) c = (w : ℂ) ^ 14 * leechPlusBS w c := by
  have hq := coe_S_smul_sq_mul w
  fin_cases c
  · show 1728 * (ckmrvTildePhiBasis (ModularGroup.S • w) 2 *
        ModularForm.discriminant (ModularGroup.S • w)) =
      (w : ℂ) ^ 14 * (1728 * (EisensteinSeries.E2 w ^ 2 * ModularForm.discriminant w))
    rw [ckmrvTildePhiBasis_S_two, discriminant_S]
    ring
  · show -3456 * (ModularForm.E₄ (ModularGroup.S • w) ^ 2 * ModularForm.E₆ (ModularGroup.S • w) *
        ckmrvTildePhiBasis (ModularGroup.S • w) 1) =
      (w : ℂ) ^ 14 * (-3456 * (ModularForm.E₄ w ^ 2 * ModularForm.E₆ w * EisensteinSeries.E2 w))
    rw [eisensteinFour_S, eisensteinSix_S, ckmrvTildePhiBasis_S_one]
    ring
  · show 1728 * (ModularForm.E₄ (ModularGroup.S • w) * ((ModularGroup.S • w : ℍ) : ℂ) ^ 2 *
        ModularForm.discriminant (ModularGroup.S • w)) =
      (w : ℂ) ^ 14 * (1728 * (ModularForm.E₄ w * ModularForm.discriminant w))
    rw [eisensteinFour_S, discriminant_S]
    linear_combination (1728 * (w : ℂ) ^ 14 * ModularForm.E₄ w * ModularForm.discriminant w) * hq
  · show (0 : ℂ) = (w : ℂ) ^ 14 * 0
    ring

theorem exists_hasExp3_leechPlusCS (c : Fin 4) :
    ∃ k : ℂ, HasExp3 (fun w => leechPlusCS w c) 0 0 k := by
  have h4 := hasExp3_eisensteinFour
  have h2 := hasExp3_eisensteinTwo
  have h43 := hasExp3_eisensteinFour_cube
  have hΔ := hasExp3_discriminant
  fin_cases c
  · exact ⟨_, ((((h4.sub h2.pow).mul h43).const_mul 6).sub
      ((h2.pow.mul hΔ).const_mul 1728)).congr_coeff (by norm_num) (by norm_num) rfl⟩
  · exact ⟨_, ((((h4.const_mul 8640).sub (h2.pow.const_mul 12096)).mul h43).add
      ((hasExp3_eisensteinFourteen.mul h2).const_mul 3456)).congr_coeff
      (by norm_num) (by norm_num) rfl⟩
  · exact ⟨_, ((((h4.sub h2.pow).mul h43).const_mul 6).sub
      ((h4.mul hΔ).const_mul 1728)).congr_coeff (by norm_num) (by norm_num) rfl⟩
  · exact ⟨_, (((h2.pow.sub h4).mul h43).const_mul 12).congr_coeff
      (by norm_num) (by norm_num) rfl⟩

theorem isBigO_leechPlusCS_div (c : Fin 4) :
    (fun w : ℍ => leechPlusCS w c / (ModularForm.discriminant w * ModularForm.E₄ w ^ 3))
      =O[atImInfty] fun _ => (1 : ℝ) := by
  obtain ⟨k, hk⟩ := exists_hasExp3_leechPlusCS c
  exact isBigO_div_discriminant_mul_of_hasExp3_sq hk

theorem isBigO_leechPlusBS_div (c : Fin 4) :
    (fun w : ℍ => leechPlusBS w c / (ModularForm.E₄ w ^ 3) ^ 2) =O[atImInfty]
      fun _ => (1 : ℝ) := by
  have h4 := hasExp3_eisensteinFour.tendsto
  have h6 := hasExp3_eisensteinSix.tendsto
  have h2 := hasExp3_eisensteinTwo.tendsto
  have hΔ := hasExp3_discriminant.tendsto
  have hE := ((h4.pow 3).pow 2).inv₀ (by norm_num : ((1 : ℂ) ^ 3) ^ 2 ≠ 0)
  fin_cases c
  · refine (((((h2.pow 2).mul hΔ).const_mul 1728).mul hE).isBigO_one ℝ).congr_left fun w => ?_
    rw [div_eq_mul_inv]
    rfl
  · refine (((((h4.pow 2).mul h6).mul h2).const_mul (-3456)).mul hE |>.isBigO_one ℝ).congr_left
      fun w => ?_
    rw [div_eq_mul_inv]
    rfl
  · refine ((((h4.mul hΔ).const_mul 1728).mul hE).isBigO_one ℝ).congr_left fun w => ?_
    rw [div_eq_mul_inv]
    rfl
  · exact (isBigO_zero _ _).congr_left fun w => (zero_div _).symm

/-! ## Bounds at the two ends -/

theorem continuous_leechPlusAc (c : Fin 4) : Continuous fun z => leechPlusAc z c := by
  have h4 := (ModularFormClass.holo ModularForm.E₄).continuous
  have hz := UpperHalfPlane.continuous_coe
  have hp2 := continuous_ckmrvTildePhiBasis 2
  fin_cases c
  · exact continuous_const.mul ((h4.mul (hz.pow 2)).sub hp2)
  · exact (continuous_const.mul (h4.mul (hz.pow 2))).sub (continuous_const.mul hp2)
  · exact continuous_const.mul ((h4.mul (hz.pow 2)).sub hp2)
  · exact continuous_const.mul (hp2.sub (h4.mul (hz.pow 2)))

theorem continuous_leechPlusBc (c : Fin 4) : Continuous fun z => leechPlusBc z c := by
  have h4 := (ModularFormClass.holo ModularForm.E₄).continuous
  have h6 := (ModularFormClass.holo ModularForm.E₆).continuous
  have hΔ := mdifferentiable_modularDiscriminant.continuous
  have hz := UpperHalfPlane.continuous_coe
  fin_cases c
  · exact continuous_const.mul ((continuous_ckmrvTildePhiBasis 2).mul hΔ)
  · exact continuous_const.mul (((h4.pow 2).mul h6).mul (continuous_ckmrvTildePhiBasis 1))
  · exact continuous_const.mul ((h4.mul (hz.pow 2)).mul hΔ)
  · exact continuous_const

theorem isBigO_leechPlusAc (c : Fin 4) :
    (fun z => leechPlusAc z c) =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ ^ 2 := by
  have hE := (hasExp3_eisensteinFour.tendsto.isBigO_one ℝ).mul isBigO_coe_sq_norm_coe_sq
  have hE' : (fun z : ℍ => ModularForm.E₄ z * (z : ℂ) ^ 2) =O[atImInfty]
      fun z : ℍ => ‖(z : ℂ)‖ ^ 2 := hE.congr_right fun _ => one_mul _
  have hp := isBigO_ckmrvTildePhiBasis_two_sq
  fin_cases c
  · exact (hE'.sub hp).const_mul_left 6
  · exact (hE'.const_mul_left 8640).sub (hp.const_mul_left 12096)
  · exact (hE'.sub hp).const_mul_left 6
  · exact (hp.sub hE').const_mul_left 12

theorem isBigO_leechPlusBc (c : Fin 4) :
    (fun z => leechPlusBc z c) =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ ^ 2 := by
  have h4 := hasExp3_eisensteinFour.tendsto.isBigO_one ℝ
  have hΔ := hasExp3_discriminant.tendsto.isBigO_one ℝ
  have h46 := (((hasExp3_eisensteinFour.tendsto.pow 2).mul
    hasExp3_eisensteinSix.tendsto).isBigO_one ℝ)
  fin_cases c
  · exact ((isBigO_ckmrvTildePhiBasis_two_sq.mul hΔ).congr_right fun _ => mul_one _)
      |>.const_mul_left 1728
  · exact ((h46.mul isBigO_ckmrvTildePhiBasis_one_sq).congr_right fun _ => one_mul _)
      |>.const_mul_left (-3456)
  · exact (((h4.mul isBigO_coe_sq_norm_coe_sq).mul hΔ).congr_right fun _ => by ring)
      |>.const_mul_left 1728
  · exact isBigO_zero _ _

theorem isBigO_div_discriminant_of_sq {f : ℍ → ℂ}
    (hf : f =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ ^ 2) :
    (fun z => f z / ModularForm.discriminant z) =O[atImInfty]
      fun z : ℍ => Real.exp (2 * π * z.im) * ‖(z : ℂ)‖ ^ 2 := by
  have hP := hasExp3_discriminantCuspQuot_inv.tendsto
  refine ((isBigO_cuspS_sq_inv.mul (hf.mul (hP.isBigO_one ℝ))).congr_left fun z => ?_)
    |>.congr_right fun z => by ring
  rw [discriminant_eq_cuspS_sq_mul, div_eq_mul_inv]
  ring

theorem isBigO_div_discriminant_mul_of_sq {f : ℍ → ℂ}
    (hf : f =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ ^ 2) :
    (fun z => f z / (ModularForm.discriminant z * ModularForm.E₄ z ^ 3)) =O[atImInfty]
      fun z : ℍ => Real.exp (2 * π * z.im) * ‖(z : ℂ)‖ ^ 2 := by
  have hE := (hasExp3_eisensteinFour.tendsto.pow 3).inv₀ (by norm_num : (1 : ℂ) ^ 3 ≠ 0)
  refine (isBigO_div_discriminant_of_sq ((hf.mul (hE.isBigO_one ℝ)).congr_right
    fun _ => mul_one _)).congr_left fun z => ?_
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

theorem isBigO_comp_imagPt_sq_exp {f : ℍ → ℂ}
    (hf : f =O[atImInfty] fun z : ℍ => Real.exp (2 * π * z.im) * ‖(z : ℂ)‖ ^ 2) {ε : ℝ}
    (hε : 0 < ε) :
    (fun t => f (imagPt t)) =O[atTop] fun t => t * Real.exp ((2 * π + ε) * t) := by
  refine ((hf.comp_tendsto tendsto_imagPt_atTop).trans (IsBigO.of_bound 1 ?_)).trans
    (isBigO_sq_mul_exp_shift hε)
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [Function.comp_apply, norm_coe_imagPt ht, im_imagPt ht, one_mul]
  rw [mul_comm]

/-! ## The two representations of the integrand -/

theorem ckmrvLeechPlusKernel_mul_eq_far (τ z : ℍ) (e : ℂ) :
    ckmrvLeechPlusKernel τ z * e = (1728 * ckmrvPlusScale)⁻¹ * ∑ c, leechPlusCoef τ c *
      (leechPlusAc z c / ModularForm.discriminant z * e +
        leechPlusBc z c / ModularForm.discriminant z ^ 2 * e /
          (kleinModularJ τ - kleinModularJ z)) := by
  rw [ckmrvLeechPlusKernel_eq_sing, leechPlusAz_eq_sum, leechPlusBz_eq_sum, Fin.sum_univ_four,
    Fin.sum_univ_four, Fin.sum_univ_four]
  ring

theorem leechPlus_term_near {A b e D a x E : ℂ} (hD : D ≠ 0) (hE : E ≠ 0) (hax : a - x ≠ 0)
    (hJ : x * D = E) :
    A / D * e + b / D ^ 2 * e / (a - x) =
      (A * E - b) / (D * E) * e - a * (b / E ^ 2 * e) + a ^ 2 * (b / E ^ 2 * e) / (a - x) := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hJ
    exact hE hJ.symm
  rw [← hJ]
  field_simp
  ring

theorem ckmrvLeechPlusKernel_mul_eq_near (τ z : ℍ) (hg : kleinModularJ τ - kleinModularJ z ≠ 0)
    (hE : ModularForm.E₄ z ≠ 0) (e : ℂ) :
    ckmrvLeechPlusKernel τ z * e = (1728 * ckmrvPlusScale)⁻¹ * ∑ c, leechPlusCoef τ c *
      ((leechPlusAc z c * ModularForm.E₄ z ^ 3 - leechPlusBc z c) /
          (ModularForm.discriminant z * ModularForm.E₄ z ^ 3) * e -
        kleinModularJ τ * (leechPlusBc z c / (ModularForm.E₄ z ^ 3) ^ 2 * e) +
        kleinModularJ τ ^ 2 * (leechPlusBc z c / (ModularForm.E₄ z ^ 3) ^ 2 * e) /
          (kleinModularJ τ - kleinModularJ z)) := by
  rw [ckmrvLeechPlusKernel_mul_eq_far]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [leechPlus_term_near (ModularForm.discriminant_ne_zero z) (pow_ne_zero 3 hE) hg
    (kleinModularJ_mul_discriminant z)]

/-! ## The pieces of the Laplace integral -/

/-- `a_c(it)/Δ(it)`, the far polynomial part. -/
def leechPlusF1 (c : Fin 4) (t : ℝ) : ℂ :=
  leechPlusAc (imagPt t) c / ModularForm.discriminant (imagPt t)

/-- The far Stieltjes numerator. -/
def leechPlusG1 (b : ℝ) (c : Fin 4) (t : ℝ) : ℂ :=
  leechPlusBc (imagPt t) c / ModularForm.discriminant (imagPt t) ^ 2 * (Real.exp (-b * t) : ℂ)

/-- The near polynomial part `(a_c E₄³ − b_c)/(Δ E₄³)`. -/
def leechPlusF3 (c : Fin 4) (t : ℝ) : ℂ :=
  (leechPlusAc (imagPt t) c * ModularForm.E₄ (imagPt t) ^ 3 - leechPlusBc (imagPt t) c) /
    (ModularForm.discriminant (imagPt t) * ModularForm.E₄ (imagPt t) ^ 3)

/-- The near Stieltjes numerator `b_c/E₄⁶`. -/
def leechPlusF4 (c : Fin 4) (t : ℝ) : ℂ :=
  leechPlusBc (imagPt t) c / (ModularForm.E₄ (imagPt t) ^ 3) ^ 2

theorem continuousOn_leechPlusF1 (c : Fin 4) : ContinuousOn (leechPlusF1 c) (Ioi 0) :=
  (continuousOn_comp_imagPt (continuous_leechPlusAc c)).div
    (continuousOn_comp_imagPt mdifferentiable_modularDiscriminant.continuous)
    fun _ _ => ModularForm.discriminant_ne_zero _

theorem continuousOn_leechPlusF3 (c : Fin 4) : ContinuousOn (leechPlusF3 c) (Ioi 0) :=
  ((continuousOn_comp_imagPt (((continuous_leechPlusAc c).mul
    ((ModularFormClass.holo ModularForm.E₄).continuous.pow 3)).sub
      (continuous_leechPlusBc c)))).div
    (continuousOn_comp_imagPt (mdifferentiable_modularDiscriminant.continuous.mul
      ((ModularFormClass.holo ModularForm.E₄).continuous.pow 3)))
    fun _ ht => mul_ne_zero (ModularForm.discriminant_ne_zero _)
      (pow_ne_zero 3 (eisensteinFour_imagPt_ne_zero ht))

theorem continuousOn_leechPlusF4 (c : Fin 4) : ContinuousOn (leechPlusF4 c) (Ioi 0) :=
  (continuousOn_comp_imagPt (continuous_leechPlusBc c)).div
    (continuousOn_comp_imagPt (((ModularFormClass.holo ModularForm.E₄).continuous.pow 3).pow 2))
    fun _ ht => pow_ne_zero 2 (pow_ne_zero 3 (eisensteinFour_imagPt_ne_zero ht))

theorem isBigO_leechPlusF3_zero (c : Fin 4) :
    leechPlusF3 c =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) := by
  have hΦ := (isBigO_leechPlusCS_div c).comp_tendsto tendsto_imagPt_inv
  have ht10 : (fun t : ℝ => -(t : ℂ) ^ 10) =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) :=
    ((Continuous.tendsto (by fun_prop : Continuous fun t : ℝ => -(t : ℂ) ^ 10) 0).mono_left
      nhdsWithin_le_nhds).isBigO_one ℝ
  refine ((hΦ.mul ht10).congr_right fun _ => one_mul _).congr' ?_
    (Eventually.of_forall fun _ => rfl)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (0 : ℝ) < t := ht
  have hS := S_smul_imagPt_inv ht0
  have hp10 := coe_imagPt_inv_pow_ten ht0
  have hE : ModularForm.E₄ (imagPt t⁻¹) ≠ 0 := eisensteinFour_imagPt_ne_zero (inv_pos.mpr ht0)
  have hΔ : ModularForm.discriminant (imagPt t⁻¹) ≠ 0 := ModularForm.discriminant_ne_zero _
  have hw : ((imagPt t⁻¹ : ℍ) : ℂ) ≠ 0 := UpperHalfPlane.ne_zero _
  simp only [Function.comp_apply, leechPlusF3]
  rw [← hS, leechPlusAc_S, discriminant_S, eisensteinFour_S, div_mul_eq_mul_div,
    div_eq_div_iff (mul_ne_zero hΔ (pow_ne_zero 3 hE))
      (mul_ne_zero (mul_ne_zero (pow_ne_zero 12 hw) hΔ)
        (pow_ne_zero 3 (mul_ne_zero (pow_ne_zero 4 hw) hE)))]
  linear_combination (leechPlusCS (imagPt t⁻¹) c * ModularForm.discriminant (imagPt t⁻¹) *
    ModularForm.E₄ (imagPt t⁻¹) ^ 3 * ((imagPt t⁻¹ : ℍ) : ℂ) ^ 14) * hp10

theorem isBigO_leechPlusF4_zero (c : Fin 4) :
    leechPlusF4 c =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) := by
  have hΦ := (isBigO_leechPlusBS_div c).comp_tendsto tendsto_imagPt_inv
  have ht10 : (fun t : ℝ => -(t : ℂ) ^ 10) =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) :=
    ((Continuous.tendsto (by fun_prop : Continuous fun t : ℝ => -(t : ℂ) ^ 10) 0).mono_left
      nhdsWithin_le_nhds).isBigO_one ℝ
  refine ((hΦ.mul ht10).congr_right fun _ => one_mul _).congr' ?_
    (Eventually.of_forall fun _ => rfl)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (0 : ℝ) < t := ht
  have hS := S_smul_imagPt_inv ht0
  have hp10 := coe_imagPt_inv_pow_ten ht0
  have hE : ModularForm.E₄ (imagPt t⁻¹) ≠ 0 := eisensteinFour_imagPt_ne_zero (inv_pos.mpr ht0)
  have hw : ((imagPt t⁻¹ : ℍ) : ℂ) ≠ 0 := UpperHalfPlane.ne_zero _
  simp only [Function.comp_apply, leechPlusF4]
  rw [← hS, leechPlusBc_S, eisensteinFour_S, div_mul_eq_mul_div,
    div_eq_div_iff (pow_ne_zero 2 (pow_ne_zero 3 hE))
      (pow_ne_zero 2 (pow_ne_zero 3 (mul_ne_zero (pow_ne_zero 4 hw) hE)))]
  linear_combination (leechPlusBS (imagPt t⁻¹) c * (ModularForm.E₄ (imagPt t⁻¹) ^ 3) ^ 2 *
    ((imagPt t⁻¹ : ℍ) : ℂ) ^ 14) * hp10

theorem integrableOn_leechPlusF3 (b : ℝ) (c : Fin 4) :
    IntegrableOn (fun t => leechPlusF3 c t * (Real.exp (-b * t) : ℂ)) (Ioc 0 1) := by
  have he : (fun t : ℝ => (Real.exp (-b * t) : ℂ)) =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) :=
    ((Continuous.tendsto (by fun_prop : Continuous fun t : ℝ => (Real.exp (-b * t) : ℂ)) 0).mono_left
      nhdsWithin_le_nhds).isBigO_one ℝ
  exact integrableOn_Ioc_of_isBigO (((continuousOn_leechPlusF3 c).mono Ioc_subset_Ioi_self).mul
    (by fun_prop : Continuous fun t : ℝ => (Real.exp (-b * t) : ℂ)).continuousOn)
    (((isBigO_leechPlusF3_zero c).mul he).congr_right fun _ => one_mul _)

theorem integrableOn_leechPlusF4 (b : ℝ) (c : Fin 4) :
    IntegrableOn (fun t => leechPlusF4 c t * (Real.exp (-b * t) : ℂ)) (Ioc 0 1) := by
  have he : (fun t : ℝ => (Real.exp (-b * t) : ℂ)) =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) :=
    ((Continuous.tendsto (by fun_prop : Continuous fun t : ℝ => (Real.exp (-b * t) : ℂ)) 0).mono_left
      nhdsWithin_le_nhds).isBigO_one ℝ
  exact integrableOn_Ioc_of_isBigO (((continuousOn_leechPlusF4 c).mono Ioc_subset_Ioi_self).mul
    (by fun_prop : Continuous fun t : ℝ => (Real.exp (-b * t) : ℂ)).continuousOn)
    (((isBigO_leechPlusF4_zero c).mul he).congr_right fun _ => one_mul _)

theorem integrableOn_leechPlusF1 {b : ℝ} (hb : 2 * π < b) (c : Fin 4) :
    IntegrableOn (fun t => leechPlusF1 c t * (Real.exp (-b * t) : ℂ)) (Ioi 1) :=
  integrableOn_Ioi_one_mul_exp_of_isBigO (b := b) (a := 2 * π + (b - 2 * π) / 2) (by linarith)
    ((continuousOn_leechPlusF1 c).mono fun t (ht : 1 ≤ t) => lt_of_lt_of_le one_pos ht)
    (isBigO_comp_imagPt_sq_exp (isBigO_div_discriminant_of_sq (isBigO_leechPlusAc c))
      (by linarith))

theorem integrableOn_leechPlusG1_bound {b : ℝ} (hb : 2 * π < b) (c : Fin 4) :
    IntegrableOn (fun t => ‖leechPlusBc (imagPt t) c /
      (ModularForm.discriminant (imagPt t) * ModularForm.E₄ (imagPt t) ^ 3) *
        (Real.exp (-b * t) : ℂ)‖) (Ioi 1) := by
  have hcont : ContinuousOn (fun t : ℝ => leechPlusBc (imagPt t) c /
      (ModularForm.discriminant (imagPt t) * ModularForm.E₄ (imagPt t) ^ 3)) (Ioi 0) :=
    (continuousOn_comp_imagPt (continuous_leechPlusBc c)).div
      (continuousOn_comp_imagPt (mdifferentiable_modularDiscriminant.continuous.mul
        ((ModularFormClass.holo ModularForm.E₄).continuous.pow 3)))
      fun _ ht => mul_ne_zero (ModularForm.discriminant_ne_zero _)
        (pow_ne_zero 3 (eisensteinFour_imagPt_ne_zero ht))
  exact (integrableOn_Ioi_one_mul_exp_of_isBigO (b := b) (a := 2 * π + (b - 2 * π) / 2)
    (by linarith) (hcont.mono fun t (ht : 1 ≤ t) => lt_of_lt_of_le one_pos ht)
    (isBigO_comp_imagPt_sq_exp (isBigO_div_discriminant_mul_of_sq (isBigO_leechPlusBc c))
      (by linarith))).norm

theorem continuousOn_leechPlusG1 (b : ℝ) (c : Fin 4) : ContinuousOn (leechPlusG1 b c) (Ioi 0) :=
  ((continuousOn_comp_imagPt (continuous_leechPlusBc c)).div
    (continuousOn_comp_imagPt (mdifferentiable_modularDiscriminant.continuous.pow 2))
    fun _ _ => pow_ne_zero 2 (ModularForm.discriminant_ne_zero _)).mul
    (by fun_prop : Continuous fun t : ℝ => (Real.exp (-b * t) : ℂ)).continuousOn

theorem norm_leechPlusG1_le (b : ℝ) (c : Fin 4) {t : ℝ} (ht : 0 < t) :
    ‖leechPlusG1 b c t‖ ≤ ‖leechPlusBc (imagPt t) c /
      (ModularForm.discriminant (imagPt t) * ModularForm.E₄ (imagPt t) ^ 3) *
        (Real.exp (-b * t) : ℂ)‖ * (1 + ‖kleinModularJ (imagPt t)‖) := by
  have h := norm_div_discriminant_sq_le (leechPlusBc (imagPt t) c)
    (eisensteinFour_imagPt_ne_zero ht)
  rw [leechPlusG1, norm_mul, norm_mul]
  calc ‖leechPlusBc (imagPt t) c / ModularForm.discriminant (imagPt t) ^ 2‖ *
        ‖(Real.exp (-b * t) : ℂ)‖ ≤
      ‖leechPlusBc (imagPt t) c /
        (ModularForm.discriminant (imagPt t) * ModularForm.E₄ (imagPt t) ^ 3)‖ *
        (1 + ‖kleinModularJ (imagPt t)‖) * ‖(Real.exp (-b * t) : ℂ)‖ :=
        mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = _ := by ring

/-- The far Stieltjes transform. -/
def leechPlusPsi1 (b : ℝ) (c : Fin 4) (w : ℂ) : ℂ :=
  ∫ t in Ioi 1, leechPlusG1 b c t / (w - kleinModularJ (imagPt t))

/-- The near Stieltjes transform. -/
def leechPlusPsi4 (b : ℝ) (c : Fin 4) (w : ℂ) : ℂ :=
  ∫ t in Ioc 0 1, leechPlusF4 c t * (Real.exp (-b * t) : ℂ) / (w - kleinModularJ (imagPt t))

theorem stieltjes_data_far {b : ℝ} (hb : 2 * π < b) (c : Fin 4) :
    IntegrableOn (fun t => ‖leechPlusBc (imagPt t) c /
      (ModularForm.discriminant (imagPt t) * ModularForm.E₄ (imagPt t) ^ 3) *
        (Real.exp (-b * t) : ℂ)‖) (Ioi 1) ∧
    ContinuousOn (leechPlusG1 b c) (Ioi 1) ∧
    ContinuousOn (fun t => kleinModularJ (imagPt t)) (Ioi 1) ∧
    (∀ t ∈ Ioi (1 : ℝ), kleinModularJ (imagPt t) ∈ jCut) ∧
    (∀ t ∈ Ioi (1 : ℝ), ‖leechPlusG1 b c t‖ ≤ ‖leechPlusBc (imagPt t) c /
      (ModularForm.discriminant (imagPt t) * ModularForm.E₄ (imagPt t) ^ 3) *
        (Real.exp (-b * t) : ℂ)‖ * (1 + ‖kleinModularJ (imagPt t)‖)) := by
  have hpos : ∀ t ∈ Ioi (1 : ℝ), (0 : ℝ) < t := fun t ht => lt_trans one_pos ht
  exact ⟨integrableOn_leechPlusG1_bound hb c,
    (continuousOn_leechPlusG1 b c).mono fun t ht => hpos t ht,
    continuousOn_kleinModularJ_imagPt.mono fun t ht => hpos t ht,
    fun t ht => kleinModularJ_imagPt_mem_jCut (hpos t ht),
    fun t ht => norm_leechPlusG1_le b c (hpos t ht)⟩

theorem stieltjes_data_near (b : ℝ) (c : Fin 4) :
    IntegrableOn (fun t => ‖leechPlusF4 c t * (Real.exp (-b * t) : ℂ)‖) (Ioc 0 1) ∧
    ContinuousOn (fun t => leechPlusF4 c t * (Real.exp (-b * t) : ℂ)) (Ioc 0 1) ∧
    ContinuousOn (fun t => kleinModularJ (imagPt t)) (Ioc 0 1) ∧
    (∀ t ∈ Ioc (0 : ℝ) 1, kleinModularJ (imagPt t) ∈ jCut) ∧
    (∀ t ∈ Ioc (0 : ℝ) 1, ‖leechPlusF4 c t * (Real.exp (-b * t) : ℂ)‖ ≤
      ‖leechPlusF4 c t * (Real.exp (-b * t) : ℂ)‖ * (1 + ‖kleinModularJ (imagPt t)‖)) :=
  ⟨(integrableOn_leechPlusF4 b c).norm,
    ((continuousOn_leechPlusF4 c).mono Ioc_subset_Ioi_self).mul
      (by fun_prop : Continuous fun t : ℝ => (Real.exp (-b * t) : ℂ)).continuousOn,
    continuousOn_kleinModularJ_imagPt.mono Ioc_subset_Ioi_self,
    fun t ht => kleinModularJ_imagPt_mem_jCut ht.1,
    fun t _ => le_mul_of_one_le_right (norm_nonneg _)
      (by linarith [norm_nonneg (kleinModularJ (imagPt t))])⟩

theorem integrableOn_leechPlusPsi1 {b : ℝ} (hb : 2 * π < b) (c : Fin 4) {w : ℂ}
    (hw : w ∉ jCut) :
    IntegrableOn (fun t => leechPlusG1 b c t / (w - kleinModularJ (imagPt t))) (Ioi 1) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := stieltjes_data_far hb c
  exact integrableOn_stieltjes_set isClosed_jCut jCut_nonempty measurableSet_Ioi h1 h2 h3 h4 h5 hw

theorem differentiableOn_leechPlusPsi1 {b : ℝ} (hb : 2 * π < b) (c : Fin 4) :
    DifferentiableOn ℂ (leechPlusPsi1 b c) jCutᶜ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := stieltjes_data_far hb c
  exact differentiableOn_stieltjes_set isClosed_jCut jCut_nonempty measurableSet_Ioi h1 h2 h3 h4 h5

theorem integrableOn_leechPlusPsi4 (b : ℝ) (c : Fin 4) {w : ℂ} (hw : w ∉ jCut) :
    IntegrableOn (fun t => leechPlusF4 c t * (Real.exp (-b * t) : ℂ) /
      (w - kleinModularJ (imagPt t))) (Ioc 0 1) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := stieltjes_data_near b c
  exact integrableOn_stieltjes_set isClosed_jCut jCut_nonempty measurableSet_Ioc h1 h2 h3 h4 h5 hw

theorem differentiableOn_leechPlusPsi4 (b : ℝ) (c : Fin 4) :
    DifferentiableOn ℂ (leechPlusPsi4 b c) jCutᶜ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := stieltjes_data_near b c
  exact differentiableOn_stieltjes_set isClosed_jCut jCut_nonempty measurableSet_Ioc h1 h2 h3 h4 h5

/-! ## The integral identity and holomorphy -/

theorem kleinModularJ_imagPt_ne_zero {t : ℝ} (ht : 0 < t) : kleinModularJ (imagPt t) ≠ 0 := by
  intro h0
  have h := (kleinModularJ_imagPt_mem_jCut ht).2
  rw [h0, zero_re] at h
  norm_num at h

/-- **The Leech plus Laplace integral in terms of constants and Stieltjes transforms.** -/
theorem integral_ckmrvLeechPlusKernel_eq {τ : ℍ} (hτ : kleinModularJ τ ∉ jCut) {b : ℝ}
    (hb : 2 * π < b) :
    ∫ t in Ioi 0, ckmrvLeechPlusKernel τ (imagPt t) * (Real.exp (-b * t) : ℂ) =
      (1728 * ckmrvPlusScale)⁻¹ * ∑ c, leechPlusCoef τ c *
        ((∫ t in Ioc 0 1, leechPlusF3 c t * (Real.exp (-b * t) : ℂ)) -
          kleinModularJ τ * (∫ t in Ioc 0 1, leechPlusF4 c t * (Real.exp (-b * t) : ℂ)) +
          kleinModularJ τ ^ 2 * leechPlusPsi4 b c (kleinModularJ τ) +
          ((∫ t in Ioi 1, leechPlusF1 c t * (Real.exp (-b * t) : ℂ)) +
            leechPlusPsi1 b c (kleinModularJ τ))) := by
  have hnear : EqOn (fun t => ckmrvLeechPlusKernel τ (imagPt t) * (Real.exp (-b * t) : ℂ))
      (fun t => (1728 * ckmrvPlusScale)⁻¹ * ∑ c, leechPlusCoef τ c *
        (leechPlusF3 c t * (Real.exp (-b * t) : ℂ) -
          kleinModularJ τ * (leechPlusF4 c t * (Real.exp (-b * t) : ℂ)) +
          kleinModularJ τ ^ 2 * (leechPlusF4 c t * (Real.exp (-b * t) : ℂ) /
            (kleinModularJ τ - kleinModularJ (imagPt t))))) (Ioc 0 1) := by
    intro t ht
    have h := ckmrvLeechPlusKernel_mul_eq_near τ (imagPt t)
      (kleinModularJ_sub_imagPt_ne_zero hτ ht.1) (eisensteinFour_imagPt_ne_zero ht.1)
      (Real.exp (-b * t) : ℂ)
    beta_reduce
    rw [h]
    simp only [leechPlusF3, leechPlusF4]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hfar : EqOn (fun t => ckmrvLeechPlusKernel τ (imagPt t) * (Real.exp (-b * t) : ℂ))
      (fun t => (1728 * ckmrvPlusScale)⁻¹ * ∑ c, leechPlusCoef τ c *
        (leechPlusF1 c t * (Real.exp (-b * t) : ℂ) +
          leechPlusG1 b c t / (kleinModularJ τ - kleinModularJ (imagPt t)))) (Ioi 1) := by
    intro t _
    beta_reduce
    rw [ckmrvLeechPlusKernel_mul_eq_far]
    rfl
  have hintNear : ∀ c ∈ Finset.univ, IntegrableOn (fun t => leechPlusCoef τ c *
      (leechPlusF3 c t * (Real.exp (-b * t) : ℂ) -
        kleinModularJ τ * (leechPlusF4 c t * (Real.exp (-b * t) : ℂ)) +
        kleinModularJ τ ^ 2 * (leechPlusF4 c t * (Real.exp (-b * t) : ℂ) /
          (kleinModularJ τ - kleinModularJ (imagPt t))))) (Ioc 0 1) := fun c _ =>
    ((((integrableOn_leechPlusF3 b c).sub ((integrableOn_leechPlusF4 b c).const_mul _)).add
      ((integrableOn_leechPlusPsi4 b c hτ).const_mul _))).const_mul _
  have hintFar : ∀ c ∈ Finset.univ, IntegrableOn (fun t => leechPlusCoef τ c *
      (leechPlusF1 c t * (Real.exp (-b * t) : ℂ) +
        leechPlusG1 b c t / (kleinModularJ τ - kleinModularJ (imagPt t)))) (Ioi 1) := fun c _ =>
    ((integrableOn_leechPlusF1 hb c).add (integrableOn_leechPlusPsi1 hb c hτ)).const_mul _
  have hK0 : IntegrableOn (fun t => ckmrvLeechPlusKernel τ (imagPt t) *
      (Real.exp (-b * t) : ℂ)) (Ioc 0 1) :=
    IntegrableOn.congr_fun ((integrable_finsetSum _ hintNear).const_mul _) hnear.symm
      measurableSet_Ioc
  have hK1 : IntegrableOn (fun t => ckmrvLeechPlusKernel τ (imagPt t) *
      (Real.exp (-b * t) : ℂ)) (Ioi 1) :=
    IntegrableOn.congr_fun ((integrable_finsetSum _ hintFar).const_mul _) hfar.symm
      measurableSet_Ioi
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hK0 hK1,
    setIntegral_congr_fun measurableSet_Ioc hnear, setIntegral_congr_fun measurableSet_Ioi hfar,
    integral_const_mul, integral_const_mul, integral_finsetSum _ hintNear,
    integral_finsetSum _ hintFar, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_const_mul, integral_const_mul, ← mul_add]
  congr 1
  have hA : IntegrableOn (fun t => leechPlusF3 c t * (Real.exp (-b * t) : ℂ) -
      kleinModularJ τ * (leechPlusF4 c t * (Real.exp (-b * t) : ℂ))) (Ioc 0 1) :=
    (integrableOn_leechPlusF3 b c).sub ((integrableOn_leechPlusF4 b c).const_mul _)
  have hB : IntegrableOn (fun t => kleinModularJ τ ^ 2 * (leechPlusF4 c t *
      (Real.exp (-b * t) : ℂ) / (kleinModularJ τ - kleinModularJ (imagPt t)))) (Ioc 0 1) :=
    (integrableOn_leechPlusPsi4 b c hτ).const_mul _
  rw [integral_add hA hB,
    integral_sub (integrableOn_leechPlusF3 b c) ((integrableOn_leechPlusF4 b c).const_mul _),
    integral_const_mul, integral_const_mul,
    integral_add (integrableOn_leechPlusF1 hb c) (integrableOn_leechPlusPsi1 hb c hτ)]
  rfl

theorem mdifferentiable_leechPlusCoef (c : Fin 4) : MDiff (fun τ => leechPlusCoef τ c) := by
  have h4 := ModularFormClass.holo ModularForm.E₄
  have h6 := ModularFormClass.holo ModularForm.E₆
  have hΔ := mdifferentiable_modularDiscriminant
  fin_cases c
  · exact mdifferentiable_coe.mul ((h4.pow 2).mul h6)
  · exact (mdifferentiable_ckmrvPhiBasis 1).mul hΔ
  · exact (mdifferentiable_ckmrvPhiBasis 2).mul (h4.mul h6)
  · exact mdifferentiable_kleinModularJ.mul ((mdifferentiable_ckmrvPhiBasis 1).mul hΔ)

/-- **CKMRV (5.1), Leech plus kernel: holomorphy in `τ`** (`r² > 2`). -/
theorem differentiableOn_ckmrvLeechPlusLaplace {r : ℝ} (hr : 2 < r ^ 2) :
    DifferentiableOn ℂ (fun τ : ℂ => ∫ t in Ioi 0,
      ckmrvLeechPlusKernel (UpperHalfPlane.ofComplex τ) (imagPt t) *
        (Real.exp (-(π * r ^ 2) * t) : ℂ))
      {τ : ℂ | 0 < τ.im ∧ kleinModularJ (UpperHalfPlane.ofComplex τ) ∉ jCut} := by
  have hb : 2 * π < π * r ^ 2 := by nlinarith [Real.pi_pos]
  have hJ : DifferentiableOn ℂ (kleinModularJ ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp mdifferentiable_kleinModularJ
  set V := {τ : ℂ | 0 < τ.im ∧ kleinModularJ (UpperHalfPlane.ofComplex τ) ∉ jCut} with hV
  have hJV : DifferentiableOn ℂ (fun τ : ℂ => kleinModularJ (UpperHalfPlane.ofComplex τ)) V :=
    hJ.mono fun τ hτ => hτ.1
  have hsum : DifferentiableOn ℂ (fun τ : ℂ => (1728 * ckmrvPlusScale)⁻¹ *
      ∑ c, leechPlusCoef (UpperHalfPlane.ofComplex τ) c *
        ((∫ t in Ioc 0 1, leechPlusF3 c t * (Real.exp (-(π * r ^ 2) * t) : ℂ)) -
          kleinModularJ (UpperHalfPlane.ofComplex τ) *
            (∫ t in Ioc 0 1, leechPlusF4 c t * (Real.exp (-(π * r ^ 2) * t) : ℂ)) +
          kleinModularJ (UpperHalfPlane.ofComplex τ) ^ 2 *
            leechPlusPsi4 (π * r ^ 2) c (kleinModularJ (UpperHalfPlane.ofComplex τ)) +
          ((∫ t in Ioi 1, leechPlusF1 c t * (Real.exp (-(π * r ^ 2) * t) : ℂ)) +
            leechPlusPsi1 (π * r ^ 2) c (kleinModularJ (UpperHalfPlane.ofComplex τ))))) V := by
    refine DifferentiableOn.const_mul (DifferentiableOn.fun_sum fun c _ => ?_) _
    have ha : DifferentiableOn ℂ ((fun τ => leechPlusCoef τ c) ∘ UpperHalfPlane.ofComplex)
        {z : ℂ | 0 < z.im} :=
      UpperHalfPlane.mdifferentiable_iff.mp (mdifferentiable_leechPlusCoef c)
    have hP4 := (differentiableOn_leechPlusPsi4 (π * r ^ 2) c).comp hJV fun τ hτ => hτ.2
    have hP1 := (differentiableOn_leechPlusPsi1 hb c).comp hJV fun τ hτ => hτ.2
    exact (ha.mono fun τ hτ => hτ.1).mul ((((differentiableOn_const _).sub
      (hJV.mul (differentiableOn_const _))).add ((hJV.pow 2).mul hP4)).add
        ((differentiableOn_const _).add hP1))
  refine hsum.congr fun τ hτ => ?_
  exact integral_ckmrvLeechPlusKernel_eq hτ.2 hb

end E8Leech
