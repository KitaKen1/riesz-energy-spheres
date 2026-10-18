import E8Leech.CKMRVLaplaceAxisMinus

/-!
# Holomorphy of the Laplace integrals in `τ` (CKMRV (5.1), P4d-3)

Known answer first: the `τ`-dependence of the kernels is algebraic in `j(τ)`. For `d = 8`,
`K₋(τ, z) = c⁻¹ ∑ⱼ aⱼ(τ) nⱼ(z) / (Δ(z) (j(τ) − j(z)))`, so

  `∫₀^∞ K₋(τ, it) e^{−bt} dt = c⁻¹ ∑ⱼ aⱼ(τ) Φⱼ(j(τ))`,
  `Φⱼ(w) = ∫₀^∞ nⱼ(it) e^{−bt} / (Δ(it) (w − j(it))) dt`.

`Φⱼ` is a Stieltjes transform of the values `j(it) ∈ [1728, ∞)`, hence holomorphic off this ray
(`jCut`). The only estimate needed is `|Δ| (1 + |j|) ≥ |Δ j| = |E₄|³`, which turns the weight
`1/(Δ (w − j))` into `1/E₄³` uniformly in `w` near a point off the cut; `E₄(it)` does not vanish.
So no uniform-in-`τ` cusp expansion is needed for this step.

Generic part: `integrableOn_stieltjes`, `differentiableOn_stieltjes` (differentiation under the
integral with the explicit derivative `−g/(w − h)²`).
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Asymptotics MeasureTheory Set Metric
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm

/-! ## Stieltjes transforms -/

/-- The values of `j` on the imaginary axis: the ray `[1728, ∞)`. -/
def jCut : Set ℂ := {x | x.im = 0 ∧ 1728 ≤ x.re}

theorem isClosed_jCut : IsClosed jCut :=
  (isClosed_eq Complex.continuous_im continuous_const).inter
    (isClosed_le continuous_const Complex.continuous_re)

theorem kleinModularJ_imagPt_mem_jCut {t : ℝ} (ht : 0 < t) : kleinModularJ (imagPt t) ∈ jCut :=
  ⟨kleinImaginaryJ_im ht, kleinImaginaryJ_re_ge_1728 ht⟩

theorem continuousOn_kleinModularJ_imagPt :
    ContinuousOn (fun t => kleinModularJ (imagPt t)) (Ioi 0) :=
  continuousOn_comp_imagPt continuous_kleinModularJ

theorem norm_sub_ge_infDist {C : Set ℂ} {w x : ℂ} (hx : x ∈ C) : infDist w C ≤ ‖w - x‖ := by
  rw [← dist_eq_norm]
  exact infDist_le_dist_of_mem hx

theorem one_add_norm_le_of_dist {w x : ℂ} {δ : ℝ} (hδ : 0 < δ) (hwx : δ ≤ ‖w - x‖) :
    δ / (1 + ‖w‖ + δ) * (1 + ‖x‖) ≤ ‖w - x‖ := by
  have hD : 0 < 1 + ‖w‖ + δ := by positivity
  have hx : ‖x‖ ≤ ‖w‖ + ‖w - x‖ := by simpa using norm_sub_le w (w - x)
  rw [div_mul_eq_mul_div, div_le_iff₀ hD]
  nlinarith [mul_le_mul_of_nonneg_left hx hδ.le,
    mul_le_mul_of_nonneg_right hwx (by positivity : (0 : ℝ) ≤ 1 + ‖w‖)]

theorem nonneg_of_norm_le_mul {a : ℂ} {G x : ℝ} (hx : 0 ≤ x) (h : ‖a‖ ≤ G * (1 + x)) :
    0 ≤ G := by
  rcases lt_or_ge G 0 with hneg | hpos
  · have := mul_neg_of_neg_of_pos hneg (by positivity : (0 : ℝ) < 1 + x)
    linarith [norm_nonneg a]
  · exact hpos

/-- A Stieltjes transform `∫ g(t) / (w − h(t)) dt` with `h(t)` in a closed set `C` converges off
`C` when `|g| ≤ G (1 + |h|)` with `G` integrable. -/
theorem integrableOn_stieltjes {g h : ℝ → ℂ} {G : ℝ → ℝ} {C : Set ℂ} (hC : IsClosed C)
    (hG : IntegrableOn G (Ioi 0)) (hg : ContinuousOn g (Ioi 0)) (hh : ContinuousOn h (Ioi 0))
    (hhC : ∀ t ∈ Ioi (0 : ℝ), h t ∈ C) (hgG : ∀ t ∈ Ioi (0 : ℝ), ‖g t‖ ≤ G t * (1 + ‖h t‖))
    {w : ℂ} (hw : w ∉ C) : IntegrableOn (fun t => g t / (w - h t)) (Ioi 0) := by
  have hδ : 0 < infDist w C := (hC.notMem_iff_infDist_pos ⟨_, hhC 1 (mem_Ioi.mpr one_pos)⟩).mp hw
  set κ := infDist w C / (1 + ‖w‖ + infDist w C) with hκ
  have hκ0 : 0 < κ := div_pos hδ (by positivity)
  have hlow : ∀ t ∈ Ioi (0 : ℝ), κ * (1 + ‖h t‖) ≤ ‖w - h t‖ := fun t ht =>
    one_add_norm_le_of_dist hδ (norm_sub_ge_infDist (hhC t ht))
  have hne : ∀ t ∈ Ioi (0 : ℝ), w - h t ≠ 0 := fun t ht h0 => by
    have h1 := hlow t ht
    rw [h0, norm_zero] at h1
    nlinarith [mul_pos hκ0 (by positivity : (0 : ℝ) < 1 + ‖h t‖)]
  have hcont : ContinuousOn (fun t => g t / (w - h t)) (Ioi 0) :=
    hg.div (continuousOn_const.sub hh) hne
  refine Integrable.mono' (Integrable.div_const hG κ)
    (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have hG0 : 0 ≤ G t := nonneg_of_norm_le_mul (norm_nonneg _) (hgG t ht)
  rw [norm_div, div_le_div_iff₀ (norm_pos_iff.mpr (hne t ht)) hκ0]
  calc ‖g t‖ * κ ≤ G t * (1 + ‖h t‖) * κ := mul_le_mul_of_nonneg_right (hgG t ht) hκ0.le
    _ = G t * (κ * (1 + ‖h t‖)) := by ring
    _ ≤ G t * ‖w - h t‖ := mul_le_mul_of_nonneg_left (hlow t ht) hG0

/-- A Stieltjes transform is holomorphic off the closed set carrying `h`. -/
theorem differentiableOn_stieltjes {g h : ℝ → ℂ} {G : ℝ → ℝ} {C : Set ℂ} (hC : IsClosed C)
    (hG : IntegrableOn G (Ioi 0)) (hg : ContinuousOn g (Ioi 0)) (hh : ContinuousOn h (Ioi 0))
    (hhC : ∀ t ∈ Ioi (0 : ℝ), h t ∈ C) (hgG : ∀ t ∈ Ioi (0 : ℝ), ‖g t‖ ≤ G t * (1 + ‖h t‖)) :
    DifferentiableOn ℂ (fun w => ∫ t in Ioi 0, g t / (w - h t)) Cᶜ := by
  intro w₀ hw₀
  have hδ : 0 < infDist w₀ C := (hC.notMem_iff_infDist_pos ⟨_, hhC 1 (mem_Ioi.mpr one_pos)⟩).mp hw₀
  set δ := infDist w₀ C with hδdef
  set κ := δ / 2 / (1 + ‖w₀‖ + δ) with hκdef
  have hκ0 : 0 < κ := div_pos (half_pos hδ) (by positivity)
  have hlow : ∀ w ∈ ball w₀ (δ / 2), ∀ t ∈ Ioi (0 : ℝ), κ * (1 + ‖h t‖) ≤ ‖w - h t‖ := by
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
  have hne : ∀ w ∈ ball w₀ (δ / 2), ∀ t ∈ Ioi (0 : ℝ), w - h t ≠ 0 := fun w hw t ht h0 => by
    have h1 := hlow w hw t ht
    rw [h0, norm_zero] at h1
    nlinarith [mul_pos hκ0 (by positivity : (0 : ℝ) < 1 + ‖h t‖)]
  have hw₀b : w₀ ∈ ball w₀ (δ / 2) := mem_ball_self (half_pos hδ)
  have hdiff : ∀ w ∈ ball w₀ (δ / 2), ∀ t ∈ Ioi (0 : ℝ),
      HasDerivAt (fun w => g t / (w - h t)) (-g t / (w - h t) ^ 2) w := by
    intro w hw t ht
    have hd := (hasDerivAt_const w (g t)).div ((hasDerivAt_id' w).sub_const (h t))
      (hne w hw t ht)
    exact hd.congr_deriv (by ring)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ))) (F := fun w t => g t / (w - h t))
    (F' := fun w t => -g t / (w - h t) ^ 2) (bound := fun t => G t / κ ^ 2)
    (ball_mem_nhds w₀ (half_pos hδ)) ?_ ?_ ?_ ?_ ?_ ?_
  · exact key.2.differentiableAt.differentiableWithinAt
  · filter_upwards [ball_mem_nhds w₀ (half_pos hδ)] with w hw
    exact (hg.div (continuousOn_const.sub hh) (hne w hw)).aestronglyMeasurable measurableSet_Ioi
  · exact integrableOn_stieltjes hC hG hg hh hhC hgG hw₀
  · exact (hg.neg.div ((continuousOn_const.sub hh).pow 2)
      fun t ht => pow_ne_zero 2 (hne w₀ hw₀b t ht)).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht w hw => ?_)
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
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun t ht w hw => hdiff w hw t ht)

/-! ## The weight `1/Δ` against `1/E₄³` -/

theorem norm_div_discriminant_le (n : ℂ) {z : ℍ} (hE : ModularForm.E₄ z ≠ 0) :
    ‖n / ModularForm.discriminant z‖ ≤
      ‖n / ModularForm.E₄ z ^ 3‖ * (1 + ‖kleinModularJ z‖) := by
  have hΔ := ModularForm.discriminant_ne_zero z
  have h3 : ‖ModularForm.E₄ z‖ ^ 3 = ‖kleinModularJ z‖ * ‖ModularForm.discriminant z‖ := by
    rw [← norm_pow, ← kleinModularJ_mul_discriminant z, norm_mul]
  rw [norm_div, norm_div, norm_pow, div_mul_eq_mul_div,
    div_le_div_iff₀ (norm_pos_iff.mpr hΔ) (pow_pos (norm_pos_iff.mpr hE) 3), h3]
  nlinarith [mul_nonneg (norm_nonneg n) (norm_nonneg (ModularForm.discriminant z)),
    norm_nonneg (kleinModularJ z)]

/-! ## Dimension eight, minus kernel -/

/-- The three `z`-factors of `K₋⁽⁸⁾`. -/
def eightMinusN (z : ℍ) : Fin 3 → ℂ :=
  ![ModularForm.E₄ z * ModularForm.E₆ z * ckmrvL z, ModularForm.E₄ z ^ 2 * thetaW z,
    ModularForm.E₆ z * (thetaU z ^ 2 - thetaV z ^ 2)]

/-- Their `S`-transforms, divided by `z¹⁰`. -/
def eightMinusNS (z : ℍ) : Fin 3 → ℂ :=
  ![ModularForm.E₄ z * ModularForm.E₆ z * ckmrvLS z, -(ModularForm.E₄ z ^ 2 * thetaV z),
    ModularForm.E₆ z * (thetaU z ^ 2 - thetaW z ^ 2)]

theorem eightMinusN_S_zero (z : ℍ) :
    eightMinusN (ModularGroup.S • z) 0 = (z : ℂ) ^ 10 * eightMinusNS z 0 := by
  show ModularForm.E₄ (ModularGroup.S • z) * ModularForm.E₆ (ModularGroup.S • z) *
    ckmrvL (ModularGroup.S • z) = (z : ℂ) ^ 10 * (ModularForm.E₄ z * ModularForm.E₆ z * ckmrvLS z)
  rw [eisensteinFour_S, eisensteinSix_S, ckmrvL_S]
  ring

theorem eightMinusN_S_one (z : ℍ) :
    eightMinusN (ModularGroup.S • z) 1 = (z : ℂ) ^ 10 * eightMinusNS z 1 := by
  show ModularForm.E₄ (ModularGroup.S • z) ^ 2 * thetaW (ModularGroup.S • z) =
    (z : ℂ) ^ 10 * -(ModularForm.E₄ z ^ 2 * thetaV z)
  rw [eisensteinFour_S, thetaW_S]
  ring

theorem eightMinusN_S_two (z : ℍ) :
    eightMinusN (ModularGroup.S • z) 2 = (z : ℂ) ^ 10 * eightMinusNS z 2 := by
  show ModularForm.E₆ (ModularGroup.S • z) *
      (thetaU (ModularGroup.S • z) ^ 2 - thetaV (ModularGroup.S • z) ^ 2) =
    (z : ℂ) ^ 10 * (ModularForm.E₆ z * (thetaU z ^ 2 - thetaW z ^ 2))
  rw [eisensteinSix_S, thetaU_S, thetaV_S]
  ring

theorem eightMinusN_S (z : ℍ) (j : Fin 3) :
    eightMinusN (ModularGroup.S • z) j = (z : ℂ) ^ 10 * eightMinusNS z j := by
  fin_cases j
  · exact eightMinusN_S_zero z
  · exact eightMinusN_S_one z
  · exact eightMinusN_S_two z

theorem eightMinusSingNum_eq_sum (τ z : ℍ) :
    eightMinusSingNum τ z = ∑ j, eightMinusTauCoeff j τ * eightMinusN z j := by
  simp only [eightMinusSingNum, eightMinusN, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

theorem continuous_eightMinusN (j : Fin 3) : Continuous fun z => eightMinusN z j := by
  have h4 := (ModularFormClass.holo ModularForm.E₄).continuous
  have h6 := (ModularFormClass.holo ModularForm.E₆).continuous
  have hL := continuous_ckmrvL
  have hU := mdifferentiable_thetaU.continuous
  have hV := mdifferentiable_thetaV.continuous
  have hW := mdifferentiable_thetaW.continuous
  fin_cases j <;> simp only [eightMinusN, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] <;> fun_prop

theorem tendsto_eightMinusNS_div (j : Fin 3) :
    Tendsto (fun z : ℍ => eightMinusNS z j / ModularForm.E₄ z ^ 3) atImInfty (𝓝 0) := by
  have h4 := hasExp3_eisensteinFour.tendsto
  have h6 := hasExp3_eisensteinSix.tendsto
  have hLS := hasExp3_ckmrvLS.tendsto
  have hU := hasExp3_thetaU.tendsto
  have hV := hasExp3_thetaV.tendsto
  have hW := hasExp3_thetaW.tendsto
  have hE3 := (h4.pow 3).inv₀ (by norm_num : (1 : ℂ) ^ 3 ≠ 0)
  fin_cases j
  · simpa [eightMinusNS, div_eq_mul_inv] using ((h4.mul h6).mul hLS).mul hE3
  · simpa [eightMinusNS, div_eq_mul_inv] using (((h4.pow 2).mul hV).neg).mul hE3
  · simpa [eightMinusNS, div_eq_mul_inv] using (h6.mul ((hU.pow 2).sub (hW.pow 2))).mul hE3

theorem isBigO_eightMinusN_div (j : Fin 3) :
    (fun z : ℍ => eightMinusN z j / ModularForm.E₄ z ^ 3) =O[atImInfty]
      fun z : ℍ => ‖(z : ℂ)‖ := by
  have h4 := hasExp3_eisensteinFour.tendsto
  have h6 := hasExp3_eisensteinSix.tendsto
  have hU := hasExp3_thetaU.tendsto
  have hV := hasExp3_thetaV.tendsto
  have hW := hasExp3_thetaW.tendsto
  have hE3 := (h4.pow 3).inv₀ (by norm_num : (1 : ℂ) ^ 3 ≠ 0)
  fin_cases j
  · have hL : (fun z : ℍ => ckmrvL z) =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ :=
      ((hasExp3_ckmrvL_sub.isBigO_one.trans isBigO_one_real_norm_coe).add
        isBigO_linear_norm_coe).congr_left fun z => by ring
    have hc := ((h4.mul h6).mul hE3).isBigO_one ℝ
    refine ((hc.mul hL).congr_left fun z => ?_).congr_right fun z => one_mul _
    simp only [eightMinusN, Fin.zero_eta, Matrix.cons_val_zero, div_eq_mul_inv]
    ring
  · have hc := (((h4.pow 2).mul hW).mul hE3).isBigO_one ℝ
    refine (hc.trans isBigO_one_real_norm_coe).congr_left fun z => ?_
    simp only [eightMinusN, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, div_eq_mul_inv]
  · have hc := ((h6.mul ((hU.pow 2).sub (hV.pow 2))).mul hE3).isBigO_one ℝ
    refine (hc.trans isBigO_one_real_norm_coe).congr_left fun z => ?_
    simp only [eightMinusN, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, div_eq_mul_inv]

theorem continuousOn_eightMinusN_div_imagPt (j : Fin 3) :
    ContinuousOn (fun t : ℝ => eightMinusN (imagPt t) j / ModularForm.E₄ (imagPt t) ^ 3)
      (Ioi 0) :=
  (continuousOn_comp_imagPt (continuous_eightMinusN j)).div
    (continuousOn_comp_imagPt ((ModularFormClass.holo ModularForm.E₄).continuous.pow 3))
    fun _ ht => pow_ne_zero 3 (eisensteinFour_imagPt_ne_zero ht)

/-- Near `t = 0`: `nⱼ(it)/E₄(it)³ = −t² (nⱼ^S/E₄³)(i/t)` is bounded. -/
theorem isBigO_eightMinusN_div_imagPt_zero (j : Fin 3) :
    (fun t : ℝ => eightMinusN (imagPt t) j / ModularForm.E₄ (imagPt t) ^ 3)
      =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) := by
  have hΦ := ((tendsto_eightMinusNS_div j).comp tendsto_imagPt_inv).isBigO_one ℝ
  have ht2 : (fun t : ℝ => -(t : ℂ) ^ 2) =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) :=
    ((Continuous.tendsto (by fun_prop : Continuous fun t : ℝ => -(t : ℂ) ^ 2) 0).mono_left
      nhdsWithin_le_nhds).isBigO_one ℝ
  refine ((hΦ.mul ht2).congr_right fun _ => one_mul _).congr' ?_
    (Eventually.of_forall fun _ => rfl)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (0 : ℝ) < t := ht
  have hS := S_smul_imagPt_inv ht0
  have hsq := coe_imagPt_inv_sq ht0
  have hE : ModularForm.E₄ (imagPt t⁻¹) ≠ 0 := eisensteinFour_imagPt_ne_zero (inv_pos.mpr ht0)
  have hw : ((imagPt t⁻¹ : ℍ) : ℂ) ≠ 0 := UpperHalfPlane.ne_zero _
  simp only [Function.comp_apply]
  rw [← hS, eightMinusN_S, eisensteinFour_S, div_mul_eq_mul_div,
    div_eq_div_iff (pow_ne_zero 3 hE) (pow_ne_zero 3 (mul_ne_zero (pow_ne_zero 4 hw) hE))]
  linear_combination (((imagPt t⁻¹ : ℍ) : ℂ) ^ 10 * eightMinusNS (imagPt t⁻¹) j *
    ModularForm.E₄ (imagPt t⁻¹) ^ 3) * hsq

theorem isBigO_eightMinusN_div_imagPt_atTop (j : Fin 3) :
    (fun t : ℝ => eightMinusN (imagPt t) j / ModularForm.E₄ (imagPt t) ^ 3) =O[atTop]
      fun t => t * Real.exp (0 * t) := by
  refine ((isBigO_eightMinusN_div j).comp_tendsto tendsto_imagPt_atTop).trans
    (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [Function.comp_apply, norm_coe_imagPt ht, zero_mul, Real.exp_zero, mul_one,
    Real.norm_eq_abs, abs_of_pos ht, one_mul, le_refl]

theorem integrableOn_eightMinusN_div {b : ℝ} (hb : 0 < b) (j : Fin 3) :
    IntegrableOn (fun t : ℝ => ‖eightMinusN (imagPt t) j / ModularForm.E₄ (imagPt t) ^ 3 *
      (Real.exp (-b * t) : ℂ)‖) (Ioi 0) :=
  (integrableOn_Ioi_mul_exp_of_isBigO hb (continuousOn_eightMinusN_div_imagPt j)
    (isBigO_eightMinusN_div_imagPt_zero j) (isBigO_eightMinusN_div_imagPt_atTop j)).norm

/-- The numerators of the Stieltjes transforms for `K₋⁽⁸⁾`. -/
def eightMinusG (b : ℝ) (j : Fin 3) (t : ℝ) : ℂ :=
  eightMinusN (imagPt t) j / ModularForm.discriminant (imagPt t) * (Real.exp (-b * t) : ℂ)

/-- `Φⱼ(w) = ∫₀^∞ nⱼ(it) e^{−bt} / (Δ(it) (w − j(it))) dt`. -/
def eightMinusStieltjes (b : ℝ) (j : Fin 3) (w : ℂ) : ℂ :=
  ∫ t in Ioi 0, eightMinusG b j t / (w - kleinModularJ (imagPt t))

theorem continuousOn_eightMinusG (b : ℝ) (j : Fin 3) : ContinuousOn (eightMinusG b j) (Ioi 0) :=
  ((continuousOn_comp_imagPt (continuous_eightMinusN j)).div
    (continuousOn_comp_imagPt mdifferentiable_modularDiscriminant.continuous)
    fun _ _ => ModularForm.discriminant_ne_zero _).mul
    (by fun_prop : Continuous fun t : ℝ => (Real.exp (-b * t) : ℂ)).continuousOn

theorem norm_eightMinusG_le (b : ℝ) (j : Fin 3) {t : ℝ} (ht : 0 < t) :
    ‖eightMinusG b j t‖ ≤ ‖eightMinusN (imagPt t) j / ModularForm.E₄ (imagPt t) ^ 3 *
      (Real.exp (-b * t) : ℂ)‖ * (1 + ‖kleinModularJ (imagPt t)‖) := by
  have h := norm_div_discriminant_le (eightMinusN (imagPt t) j)
    (eisensteinFour_imagPt_ne_zero ht)
  rw [eightMinusG, norm_mul, norm_mul]
  calc ‖eightMinusN (imagPt t) j / ModularForm.discriminant (imagPt t)‖ *
        ‖(Real.exp (-b * t) : ℂ)‖ ≤
      ‖eightMinusN (imagPt t) j / ModularForm.E₄ (imagPt t) ^ 3‖ *
        (1 + ‖kleinModularJ (imagPt t)‖) * ‖(Real.exp (-b * t) : ℂ)‖ :=
        mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = _ := by ring

theorem integrableOn_eightMinusStieltjes {b : ℝ} (hb : 0 < b) (j : Fin 3) {w : ℂ}
    (hw : w ∉ jCut) :
    IntegrableOn (fun t => eightMinusG b j t / (w - kleinModularJ (imagPt t))) (Ioi 0) :=
  integrableOn_stieltjes isClosed_jCut (integrableOn_eightMinusN_div hb j)
    (continuousOn_eightMinusG b j) continuousOn_kleinModularJ_imagPt
    (fun _ ht => kleinModularJ_imagPt_mem_jCut ht) (fun _ ht => norm_eightMinusG_le b j ht) hw

theorem differentiableOn_eightMinusStieltjes {b : ℝ} (hb : 0 < b) (j : Fin 3) :
    DifferentiableOn ℂ (eightMinusStieltjes b j) jCutᶜ :=
  differentiableOn_stieltjes isClosed_jCut (integrableOn_eightMinusN_div hb j)
    (continuousOn_eightMinusG b j) continuousOn_kleinModularJ_imagPt
    (fun _ ht => kleinModularJ_imagPt_mem_jCut ht) (fun _ ht => norm_eightMinusG_le b j ht)

theorem ckmrvEightMinusKernel_mul_eq_sum (τ z : ℍ) (e : ℂ) :
    ckmrvEightMinusKernel τ z * e = ckmrvMinusScale⁻¹ * ∑ j, eightMinusTauCoeff j τ *
      (eightMinusN z j / ModularForm.discriminant z * e / (kleinModularJ τ - kleinModularJ z)) := by
  rw [ckmrvEightMinusKernel_eq_sing, eightMinusSingNum_eq_sum, Fin.sum_univ_three,
    Fin.sum_univ_three]
  ring

theorem ckmrvEightMinusKernel_imagPt_mul_eq_sum (τ : ℍ) (b t : ℝ) :
    ckmrvEightMinusKernel τ (imagPt t) * (Real.exp (-b * t) : ℂ) =
      ckmrvMinusScale⁻¹ * ∑ j, eightMinusTauCoeff j τ *
        (eightMinusG b j t / (kleinModularJ τ - kleinModularJ (imagPt t))) :=
  ckmrvEightMinusKernel_mul_eq_sum τ (imagPt t) _

/-- **The Laplace integral as a combination of Stieltjes transforms.** -/
theorem integral_ckmrvEightMinusKernel_eq {τ : ℍ} (hτ : kleinModularJ τ ∉ jCut) {b : ℝ}
    (hb : 0 < b) :
    ∫ t in Ioi 0, ckmrvEightMinusKernel τ (imagPt t) * (Real.exp (-b * t) : ℂ) =
      ckmrvMinusScale⁻¹ * ∑ j, eightMinusTauCoeff j τ *
        eightMinusStieltjes b j (kleinModularJ τ) := by
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun t _ => ckmrvEightMinusKernel_imagPt_mul_eq_sum τ b t),
    integral_const_mul, integral_finsetSum _ fun j _ =>
      (integrableOn_eightMinusStieltjes hb j hτ).const_mul (eightMinusTauCoeff j τ)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  rfl

theorem mdifferentiable_ckmrvModularFactor_two : MDiff (fun τ => ckmrvModularFactor τ 2) := by
  rw [show (fun τ : ℍ => ckmrvModularFactor τ 2) = fun τ =>
      ModularForm.E₄ τ ^ 2 * ModularForm.E₆ τ / ModularForm.discriminant τ from
    funext fun τ => by rw [ckmrvModularFactor_two_eq, div_eq_mul_inv]]
  exact (((ModularFormClass.holo ModularForm.E₄).pow 2).mul
    (ModularFormClass.holo ModularForm.E₆)).div mdifferentiable_modularDiscriminant
    ModularForm.discriminant_ne_zero

theorem mdifferentiable_eightMinusTauCoeff_zero : MDiff (fun τ => eightMinusTauCoeff 0 τ) := by
  rw [show (fun τ : ℍ => eightMinusTauCoeff 0 τ) = fun τ => -(2 * 1728) * ModularForm.E₄ τ from
    funext eightMinusTauCoeff_zero]
  exact mdifferentiable_const.mul (ModularFormClass.holo ModularForm.E₄)

theorem mdifferentiable_eightMinusTauCoeff_one : MDiff (fun τ => eightMinusTauCoeff 1 τ) := by
  have hp1 := mdifferentiable_ckmrvPsiBasis 1
  have hp2 := mdifferentiable_ckmrvPsiBasis 2
  have hJ := mdifferentiable_kleinModularJ
  rw [show (fun τ : ℍ => eightMinusTauCoeff 1 τ) = fun τ =>
      (ckmrvPsiBasis τ 1 - ckmrvPsiBasis τ 2) * kleinModularJ τ -
        ckmrvPsiBasis τ 1 * (kleinModularJ τ - ckmrvModularFactor τ 2) +
          1728 * ckmrvPsiBasis τ 2 from funext eightMinusTauCoeff_one]
  exact (((hp1.sub hp2).mul hJ).sub (hp1.mul (hJ.sub mdifferentiable_ckmrvModularFactor_two))).add
    (mdifferentiable_const.mul hp2)

theorem mdifferentiable_eightMinusTauCoeff_two : MDiff (fun τ => eightMinusTauCoeff 2 τ) := by
  have hp1 := mdifferentiable_ckmrvPsiBasis 1
  have hp2 := mdifferentiable_ckmrvPsiBasis 2
  have hJ := mdifferentiable_kleinModularJ
  rw [show (fun τ : ℍ => eightMinusTauCoeff 2 τ) = fun τ =>
      -((ckmrvPsiBasis τ 1 - ckmrvPsiBasis τ 2) * kleinModularJ τ) +
        ckmrvPsiBasis τ 1 * (kleinModularJ τ - ckmrvModularFactor τ 2) from
    funext eightMinusTauCoeff_two]
  exact ((hp1.sub hp2).mul hJ).neg.add (hp1.mul (hJ.sub mdifferentiable_ckmrvModularFactor_two))

theorem mdifferentiable_eightMinusTauCoeff (j : Fin 3) :
    MDiff (fun τ => eightMinusTauCoeff j τ) := by
  fin_cases j
  · exact mdifferentiable_eightMinusTauCoeff_zero
  · exact mdifferentiable_eightMinusTauCoeff_one
  · exact mdifferentiable_eightMinusTauCoeff_two

/-- **CKMRV (5.1), `d = 8`, minus kernel: holomorphy in `τ`.** Off the cut `j(τ) ∈ [1728, ∞)`
the Laplace integral `∫₀^∞ K₋(τ, it) e^{−πr²t} dt` is holomorphic in `τ`. -/
theorem differentiableOn_ckmrvEightMinusLaplace {r : ℝ} (hr : r ≠ 0) :
    DifferentiableOn ℂ (fun τ : ℂ => ∫ t in Ioi 0,
      ckmrvEightMinusKernel (UpperHalfPlane.ofComplex τ) (imagPt t) *
        (Real.exp (-(π * r ^ 2) * t) : ℂ))
      {τ : ℂ | 0 < τ.im ∧ kleinModularJ (UpperHalfPlane.ofComplex τ) ∉ jCut} := by
  have hb : 0 < π * r ^ 2 := by positivity
  have hJ : DifferentiableOn ℂ (kleinModularJ ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp mdifferentiable_kleinModularJ
  have hsum : DifferentiableOn ℂ (fun τ : ℂ => ckmrvMinusScale⁻¹ *
      ∑ j, eightMinusTauCoeff j (UpperHalfPlane.ofComplex τ) *
        eightMinusStieltjes (π * r ^ 2) j (kleinModularJ (UpperHalfPlane.ofComplex τ)))
      {τ : ℂ | 0 < τ.im ∧ kleinModularJ (UpperHalfPlane.ofComplex τ) ∉ jCut} := by
    refine DifferentiableOn.const_mul (DifferentiableOn.fun_sum fun j _ => ?_) _
    have ha : DifferentiableOn ℂ ((fun τ => eightMinusTauCoeff j τ) ∘ UpperHalfPlane.ofComplex)
        {z : ℂ | 0 < z.im} :=
      UpperHalfPlane.mdifferentiable_iff.mp (mdifferentiable_eightMinusTauCoeff j)
    exact (ha.mono fun τ hτ => hτ.1).mul ((differentiableOn_eightMinusStieltjes hb j).comp
      (hJ.mono fun τ hτ => hτ.1) fun τ hτ => hτ.2)
  refine hsum.congr fun τ hτ => ?_
  exact integral_ckmrvEightMinusKernel_eq hτ.2 hb

/-! ## Dimension eight, plus kernel -/

theorem isBigO_one_norm_coe_sq :
    (fun _ : ℍ => (1 : ℝ)) =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ ^ 2 := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_one_le_norm_coe] with z hz
  rw [norm_one, one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith

theorem isBigO_coe_norm_coe_sq :
    (fun z : ℍ => (z : ℂ)) =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ ^ 2 := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_one_le_norm_coe] with z hz
  rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith

theorem isBigO_coe_sq_norm_coe_sq :
    (fun z : ℍ => (z : ℂ) ^ 2) =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ ^ 2 :=
  IsBigO.of_bound 1 (Eventually.of_forall fun z => by
    rw [one_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg (by positivity)])

theorem isBigO_sq_mul_exp {ε : ℝ} (hε : 0 < ε) :
    (fun t : ℝ => t ^ 2) =O[atTop] fun t => t * Real.exp (ε * t) := by
  refine IsBigO.of_bound (1 / ε) ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  have hlin : t ≤ Real.exp (ε * t) / ε := by
    rw [le_div_iff₀ hε]
    nlinarith [Real.add_one_le_exp (ε * t)]
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_nonneg (mul_nonneg ht (Real.exp_pos _).le)]
  calc t ^ 2 = t * t := by ring
    _ ≤ t * (Real.exp (ε * t) / ε) := mul_le_mul_of_nonneg_left hlin ht
    _ = 1 / ε * (t * Real.exp (ε * t)) := by ring

/-- The three `z`-factors of the singular part of `K₊⁽⁸⁾`. -/
def eightPlusM (z : ℍ) : Fin 3 → ℂ :=
  ![ModularForm.discriminant z * (z : ℂ) ^ 2,
    ModularForm.E₄ z * ModularForm.E₆ z * ckmrvTildePhiBasis z 1,
    ModularForm.E₄ z ^ 2 * ckmrvTildePhiBasis z 2]

/-- Their `S`-transforms, divided by `z¹⁰`. -/
def eightPlusMS (z : ℍ) : Fin 3 → ℂ :=
  ![ModularForm.discriminant z, ModularForm.E₄ z * ModularForm.E₆ z * EisensteinSeries.E2 z,
    ModularForm.E₄ z ^ 2 * EisensteinSeries.E2 z ^ 2]

/-- The `τ`-coefficients of the singular part of `K₊⁽⁸⁾`. -/
def eightPlusB (τ : ℍ) : Fin 3 → ℂ :=
  ![ckmrvPhiBasis τ 2 * ckmrvModularFactor τ 2, -2 * (ckmrvPhiBasis τ 1 * ModularForm.E₄ τ),
    ckmrvPhiBasis τ 0 * ModularForm.E₆ τ]

/-- The coefficient of the polynomial part `z²` of `K₊⁽⁸⁾`. -/
def eightPlusP (τ : ℍ) : ℂ :=
  ckmrvPhiBasis τ 0 * ModularForm.E₆ τ - 2 * (ckmrvPhiBasis τ 1 * ModularForm.E₄ τ)

theorem eightPlusSingNum_eq_sum (τ z : ℍ) :
    eightPlusSingNum τ z = ∑ j, eightPlusB τ j * eightPlusM z j := by
  rw [Fin.sum_univ_three]
  have h0 : eightPlusB τ 0 * eightPlusM z 0 = ckmrvPhiBasis τ 2 * ckmrvModularFactor τ 2 *
      (ModularForm.discriminant z * (z : ℂ) ^ 2) := rfl
  have h1 : eightPlusB τ 1 * eightPlusM z 1 = -2 * (ckmrvPhiBasis τ 1 * ModularForm.E₄ τ) *
      (ModularForm.E₄ z * ModularForm.E₆ z * ckmrvTildePhiBasis z 1) := rfl
  have h2 : eightPlusB τ 2 * eightPlusM z 2 = ckmrvPhiBasis τ 0 * ModularForm.E₆ τ *
      (ModularForm.E₄ z ^ 2 * ckmrvTildePhiBasis z 2) := rfl
  rw [h0, h1, h2, eightPlusSingNum]
  ring

theorem eightPlusM_S_zero (z : ℍ) :
    eightPlusM (ModularGroup.S • z) 0 = (z : ℂ) ^ 10 * eightPlusMS z 0 := by
  show ModularForm.discriminant (ModularGroup.S • z) * ((ModularGroup.S • z : ℍ) : ℂ) ^ 2 =
    (z : ℂ) ^ 10 * ModularForm.discriminant z
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  rw [discriminant_S, coe_S_smul]
  field_simp

theorem eightPlusM_S_one (z : ℍ) :
    eightPlusM (ModularGroup.S • z) 1 = (z : ℂ) ^ 10 * eightPlusMS z 1 := by
  show ModularForm.E₄ (ModularGroup.S • z) * ModularForm.E₆ (ModularGroup.S • z) *
      ckmrvTildePhiBasis (ModularGroup.S • z) 1 =
    (z : ℂ) ^ 10 * (ModularForm.E₄ z * ModularForm.E₆ z * EisensteinSeries.E2 z)
  rw [eisensteinFour_S, eisensteinSix_S, ckmrvTildePhiBasis_S_one]
  ring

theorem eightPlusM_S_two (z : ℍ) :
    eightPlusM (ModularGroup.S • z) 2 = (z : ℂ) ^ 10 * eightPlusMS z 2 := by
  show ModularForm.E₄ (ModularGroup.S • z) ^ 2 * ckmrvTildePhiBasis (ModularGroup.S • z) 2 =
    (z : ℂ) ^ 10 * (ModularForm.E₄ z ^ 2 * EisensteinSeries.E2 z ^ 2)
  rw [eisensteinFour_S, ckmrvTildePhiBasis_S_two]
  ring

theorem eightPlusM_S (z : ℍ) (j : Fin 3) :
    eightPlusM (ModularGroup.S • z) j = (z : ℂ) ^ 10 * eightPlusMS z j := by
  fin_cases j
  · exact eightPlusM_S_zero z
  · exact eightPlusM_S_one z
  · exact eightPlusM_S_two z

theorem continuous_eightPlusM (j : Fin 3) : Continuous fun z => eightPlusM z j := by
  have h4 := (ModularFormClass.holo ModularForm.E₄).continuous
  have h6 := (ModularFormClass.holo ModularForm.E₆).continuous
  have hΔ := mdifferentiable_modularDiscriminant.continuous
  fin_cases j
  · exact hΔ.mul (UpperHalfPlane.continuous_coe.pow 2)
  · exact (h4.mul h6).mul (continuous_ckmrvTildePhiBasis 1)
  · exact (h4.pow 2).mul (continuous_ckmrvTildePhiBasis 2)

theorem isBigO_eightPlusMS_div (j : Fin 3) :
    (fun z : ℍ => eightPlusMS z j / ModularForm.E₄ z ^ 3) =O[atImInfty] fun _ => (1 : ℝ) := by
  have h4 := hasExp3_eisensteinFour.tendsto
  have h6 := hasExp3_eisensteinSix.tendsto
  have h2 := hasExp3_eisensteinTwo.tendsto
  have hΔ := hasExp3_discriminant.tendsto
  have hE3 := (h4.pow 3).inv₀ (by norm_num : (1 : ℂ) ^ 3 ≠ 0)
  fin_cases j
  · refine ((hΔ.mul hE3).isBigO_one ℝ).congr_left fun z => ?_
    rw [div_eq_mul_inv]
    rfl
  · refine ((((h4.mul h6).mul h2).mul hE3).isBigO_one ℝ).congr_left fun z => ?_
    rw [div_eq_mul_inv]
    rfl
  · refine ((((h4.pow 2).mul (h2.pow 2)).mul hE3).isBigO_one ℝ).congr_left fun z => ?_
    rw [div_eq_mul_inv]
    rfl

theorem isBigO_ckmrvTildePhiBasis_one_sq :
    (fun z : ℍ => ckmrvTildePhiBasis z 1) =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ ^ 2 := by
  have h2 := hasExp3_eisensteinTwo.tendsto.isBigO_one ℝ
  exact (((isBigO_coe_sq_norm_coe_sq.mul h2).congr_right fun z => mul_one _).sub
    (isBigO_coe_norm_coe_sq.const_mul_left (6 * Complex.I / (Real.pi : ℂ)))).congr_left
    fun z => rfl

theorem isBigO_ckmrvTildePhiBasis_two_sq :
    (fun z : ℍ => ckmrvTildePhiBasis z 2) =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ ^ 2 := by
  have h2 := hasExp3_eisensteinTwo.tendsto
  exact ((((isBigO_coe_sq_norm_coe_sq.mul ((h2.pow 2).isBigO_one ℝ)).congr_right
    fun z => mul_one _).sub
    (((isBigO_coe_norm_coe_sq.const_mul_left (12 * Complex.I / (Real.pi : ℂ))).mul
      (h2.isBigO_one ℝ)).congr_right fun z => mul_one _)).sub
    ((isBigO_const_one ℝ (36 / (Real.pi : ℂ) ^ 2) atImInfty).trans
      isBigO_one_norm_coe_sq)).congr_left fun z => rfl

theorem isBigO_eightPlusM_div (j : Fin 3) :
    (fun z : ℍ => eightPlusM z j / ModularForm.E₄ z ^ 3) =O[atImInfty]
      fun z : ℍ => ‖(z : ℂ)‖ ^ 2 := by
  have h4 := hasExp3_eisensteinFour.tendsto
  have h6 := hasExp3_eisensteinSix.tendsto
  have hΔ := hasExp3_discriminant.tendsto
  have hE3 := (h4.pow 3).inv₀ (by norm_num : (1 : ℂ) ^ 3 ≠ 0)
  fin_cases j
  · refine ((((hΔ.mul hE3).isBigO_one ℝ).mul isBigO_coe_sq_norm_coe_sq).congr_left
      fun z => ?_).congr_right fun z => one_mul _
    show ModularForm.discriminant z * (ModularForm.E₄ z ^ 3)⁻¹ * (z : ℂ) ^ 2 =
      ModularForm.discriminant z * (z : ℂ) ^ 2 / ModularForm.E₄ z ^ 3
    rw [div_eq_mul_inv]
    ring
  · refine (((((h4.mul h6).mul hE3).isBigO_one ℝ).mul isBigO_ckmrvTildePhiBasis_one_sq).congr_left
      fun z => ?_).congr_right fun z => one_mul _
    show ModularForm.E₄ z * ModularForm.E₆ z * (ModularForm.E₄ z ^ 3)⁻¹ *
        ckmrvTildePhiBasis z 1 =
      ModularForm.E₄ z * ModularForm.E₆ z * ckmrvTildePhiBasis z 1 / ModularForm.E₄ z ^ 3
    rw [div_eq_mul_inv]
    ring
  · refine (((((h4.pow 2).mul hE3).isBigO_one ℝ).mul isBigO_ckmrvTildePhiBasis_two_sq).congr_left
      fun z => ?_).congr_right fun z => one_mul _
    show ModularForm.E₄ z ^ 2 * (ModularForm.E₄ z ^ 3)⁻¹ * ckmrvTildePhiBasis z 2 =
      ModularForm.E₄ z ^ 2 * ckmrvTildePhiBasis z 2 / ModularForm.E₄ z ^ 3
    rw [div_eq_mul_inv]
    ring

theorem continuousOn_eightPlusM_div_imagPt (j : Fin 3) :
    ContinuousOn (fun t : ℝ => eightPlusM (imagPt t) j / ModularForm.E₄ (imagPt t) ^ 3)
      (Ioi 0) :=
  (continuousOn_comp_imagPt (continuous_eightPlusM j)).div
    (continuousOn_comp_imagPt ((ModularFormClass.holo ModularForm.E₄).continuous.pow 3))
    fun _ ht => pow_ne_zero 3 (eisensteinFour_imagPt_ne_zero ht)

theorem isBigO_eightPlusM_div_imagPt_zero (j : Fin 3) :
    (fun t : ℝ => eightPlusM (imagPt t) j / ModularForm.E₄ (imagPt t) ^ 3)
      =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) := by
  have hΦ := (isBigO_eightPlusMS_div j).comp_tendsto tendsto_imagPt_inv
  have ht2 : (fun t : ℝ => -(t : ℂ) ^ 2) =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) :=
    ((Continuous.tendsto (by fun_prop : Continuous fun t : ℝ => -(t : ℂ) ^ 2) 0).mono_left
      nhdsWithin_le_nhds).isBigO_one ℝ
  refine ((hΦ.mul ht2).congr_right fun _ => one_mul _).congr' ?_
    (Eventually.of_forall fun _ => rfl)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (0 : ℝ) < t := ht
  have hS := S_smul_imagPt_inv ht0
  have hsq := coe_imagPt_inv_sq ht0
  have hE : ModularForm.E₄ (imagPt t⁻¹) ≠ 0 := eisensteinFour_imagPt_ne_zero (inv_pos.mpr ht0)
  have hw : ((imagPt t⁻¹ : ℍ) : ℂ) ≠ 0 := UpperHalfPlane.ne_zero _
  simp only [Function.comp_apply]
  rw [← hS, eightPlusM_S, eisensteinFour_S, div_mul_eq_mul_div,
    div_eq_div_iff (pow_ne_zero 3 hE) (pow_ne_zero 3 (mul_ne_zero (pow_ne_zero 4 hw) hE))]
  linear_combination (((imagPt t⁻¹ : ℍ) : ℂ) ^ 10 * eightPlusMS (imagPt t⁻¹) j *
    ModularForm.E₄ (imagPt t⁻¹) ^ 3) * hsq

theorem isBigO_eightPlusM_div_imagPt_atTop (j : Fin 3) :
    (fun t : ℝ => eightPlusM (imagPt t) j / ModularForm.E₄ (imagPt t) ^ 3) =O[atTop]
      fun t => t ^ 2 := by
  refine ((isBigO_eightPlusM_div j).comp_tendsto tendsto_imagPt_atTop).trans
    (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [Function.comp_apply, norm_coe_imagPt ht, one_mul, le_refl]

theorem integrableOn_eightPlusM_div {b : ℝ} (hb : 0 < b) (j : Fin 3) :
    IntegrableOn (fun t : ℝ => ‖eightPlusM (imagPt t) j / ModularForm.E₄ (imagPt t) ^ 3 *
      (Real.exp (-b * t) : ℂ)‖) (Ioi 0) :=
  (integrableOn_Ioi_mul_exp_of_isBigO (half_lt_self hb) (continuousOn_eightPlusM_div_imagPt j)
    (isBigO_eightPlusM_div_imagPt_zero j)
    ((isBigO_eightPlusM_div_imagPt_atTop j).trans (isBigO_sq_mul_exp (half_pos hb)))).norm

/-- The numerators of the Stieltjes transforms for `K₊⁽⁸⁾`. -/
def eightPlusG (b : ℝ) (j : Fin 3) (t : ℝ) : ℂ :=
  eightPlusM (imagPt t) j / ModularForm.discriminant (imagPt t) * (Real.exp (-b * t) : ℂ)

/-- `Ψⱼ(w) = ∫₀^∞ mⱼ(it) e^{−bt} / (Δ(it) (w − j(it))) dt`. -/
def eightPlusStieltjes (b : ℝ) (j : Fin 3) (w : ℂ) : ℂ :=
  ∫ t in Ioi 0, eightPlusG b j t / (w - kleinModularJ (imagPt t))

/-- `∫₀^∞ (it)² e^{−bt} dt`. -/
def eightPlusPoly (b : ℝ) : ℂ :=
  ∫ t in Ioi 0, ((imagPt t : ℍ) : ℂ) ^ 2 * (Real.exp (-b * t) : ℂ)

theorem continuousOn_eightPlusG (b : ℝ) (j : Fin 3) : ContinuousOn (eightPlusG b j) (Ioi 0) :=
  ((continuousOn_comp_imagPt (continuous_eightPlusM j)).div
    (continuousOn_comp_imagPt mdifferentiable_modularDiscriminant.continuous)
    fun _ _ => ModularForm.discriminant_ne_zero _).mul
    (by fun_prop : Continuous fun t : ℝ => (Real.exp (-b * t) : ℂ)).continuousOn

theorem norm_eightPlusG_le (b : ℝ) (j : Fin 3) {t : ℝ} (ht : 0 < t) :
    ‖eightPlusG b j t‖ ≤ ‖eightPlusM (imagPt t) j / ModularForm.E₄ (imagPt t) ^ 3 *
      (Real.exp (-b * t) : ℂ)‖ * (1 + ‖kleinModularJ (imagPt t)‖) := by
  have h := norm_div_discriminant_le (eightPlusM (imagPt t) j)
    (eisensteinFour_imagPt_ne_zero ht)
  rw [eightPlusG, norm_mul, norm_mul]
  calc ‖eightPlusM (imagPt t) j / ModularForm.discriminant (imagPt t)‖ *
        ‖(Real.exp (-b * t) : ℂ)‖ ≤
      ‖eightPlusM (imagPt t) j / ModularForm.E₄ (imagPt t) ^ 3‖ *
        (1 + ‖kleinModularJ (imagPt t)‖) * ‖(Real.exp (-b * t) : ℂ)‖ :=
        mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = _ := by ring

theorem integrableOn_eightPlusStieltjes {b : ℝ} (hb : 0 < b) (j : Fin 3) {w : ℂ}
    (hw : w ∉ jCut) :
    IntegrableOn (fun t => eightPlusG b j t / (w - kleinModularJ (imagPt t))) (Ioi 0) :=
  integrableOn_stieltjes isClosed_jCut (integrableOn_eightPlusM_div hb j)
    (continuousOn_eightPlusG b j) continuousOn_kleinModularJ_imagPt
    (fun _ ht => kleinModularJ_imagPt_mem_jCut ht) (fun _ ht => norm_eightPlusG_le b j ht) hw

theorem differentiableOn_eightPlusStieltjes {b : ℝ} (hb : 0 < b) (j : Fin 3) :
    DifferentiableOn ℂ (eightPlusStieltjes b j) jCutᶜ :=
  differentiableOn_stieltjes isClosed_jCut (integrableOn_eightPlusM_div hb j)
    (continuousOn_eightPlusG b j) continuousOn_kleinModularJ_imagPt
    (fun _ ht => kleinModularJ_imagPt_mem_jCut ht) (fun _ ht => norm_eightPlusG_le b j ht)

theorem integrableOn_eightPlusPoly {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => ((imagPt t : ℍ) : ℂ) ^ 2 * (Real.exp (-b * t) : ℂ)) (Ioi 0) := by
  refine integrableOn_Ioi_mul_exp_of_isBigO (half_lt_self hb)
    (continuousOn_comp_imagPt (UpperHalfPlane.continuous_coe.pow 2)) ?_ ?_
  · refine IsBigO.of_bound 1 ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    rw [norm_pow, norm_coe_imagPt ht.1, norm_one, one_mul]
    nlinarith [ht.1, ht.2]
  · refine (IsBigO.of_bound 1 ?_).trans (isBigO_sq_mul_exp (half_pos hb))
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [norm_pow, norm_coe_imagPt ht, one_mul]
    exact le_of_eq (by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)])

theorem ckmrvEightPlusKernel_mul_eq_sum (τ z : ℍ) (hg : kleinModularJ τ - kleinModularJ z ≠ 0)
    (e : ℂ) :
    ckmrvEightPlusKernel τ z * e = ckmrvPlusScale⁻¹ * (eightPlusP τ * ((z : ℂ) ^ 2 * e) +
      ∑ j, eightPlusB τ j *
        (eightPlusM z j / ModularForm.discriminant z * e / (kleinModularJ τ - kleinModularJ z))) := by
  rw [ckmrvEightPlusKernel_eq_sing τ z hg, eightPlusSingNum_eq_sum, Fin.sum_univ_three,
    Fin.sum_univ_three, eightPlusP]
  ring

theorem kleinModularJ_sub_imagPt_ne_zero {τ : ℍ} (hτ : kleinModularJ τ ∉ jCut) {t : ℝ}
    (ht : 0 < t) : kleinModularJ τ - kleinModularJ (imagPt t) ≠ 0 := fun h =>
  hτ ((sub_eq_zero.mp h) ▸ kleinModularJ_imagPt_mem_jCut ht)

theorem ckmrvEightPlusKernel_imagPt_mul_eq_sum {τ : ℍ} (hτ : kleinModularJ τ ∉ jCut) (b : ℝ)
    {t : ℝ} (ht : 0 < t) :
    ckmrvEightPlusKernel τ (imagPt t) * (Real.exp (-b * t) : ℂ) =
      ckmrvPlusScale⁻¹ * (eightPlusP τ * (((imagPt t : ℍ) : ℂ) ^ 2 * (Real.exp (-b * t) : ℂ)) +
        ∑ j, eightPlusB τ j * (eightPlusG b j t / (kleinModularJ τ - kleinModularJ (imagPt t)))) :=
  ckmrvEightPlusKernel_mul_eq_sum τ (imagPt t) (kleinModularJ_sub_imagPt_ne_zero hτ ht) _

/-- **The plus Laplace integral as a polynomial term plus Stieltjes transforms.** -/
theorem integral_ckmrvEightPlusKernel_eq {τ : ℍ} (hτ : kleinModularJ τ ∉ jCut) {b : ℝ}
    (hb : 0 < b) :
    ∫ t in Ioi 0, ckmrvEightPlusKernel τ (imagPt t) * (Real.exp (-b * t) : ℂ) =
      ckmrvPlusScale⁻¹ * (eightPlusP τ * eightPlusPoly b +
        ∑ j, eightPlusB τ j * eightPlusStieltjes b j (kleinModularJ τ)) := by
  have hsum : IntegrableOn (fun t => ∑ j, eightPlusB τ j *
      (eightPlusG b j t / (kleinModularJ τ - kleinModularJ (imagPt t)))) (Ioi 0) :=
    integrable_finsetSum _ fun j _ =>
      (integrableOn_eightPlusStieltjes hb j hτ).const_mul (eightPlusB τ j)
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht =>
      ckmrvEightPlusKernel_imagPt_mul_eq_sum hτ b ht), integral_const_mul]
  congr 1
  rw [integral_add ((integrableOn_eightPlusPoly hb).const_mul (eightPlusP τ)) hsum,
    integral_const_mul, integral_finsetSum _ fun j _ =>
      (integrableOn_eightPlusStieltjes hb j hτ).const_mul (eightPlusB τ j)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  rfl

theorem mdifferentiable_eightPlusB (j : Fin 3) : MDiff (fun τ => eightPlusB τ j) := by
  have h4 := ModularFormClass.holo ModularForm.E₄
  have h6 := ModularFormClass.holo ModularForm.E₆
  fin_cases j
  · exact (mdifferentiable_ckmrvPhiBasis 2).mul mdifferentiable_ckmrvModularFactor_two
  · exact mdifferentiable_const.mul ((mdifferentiable_ckmrvPhiBasis 1).mul h4)
  · exact (mdifferentiable_ckmrvPhiBasis 0).mul h6

theorem mdifferentiable_eightPlusP : MDiff eightPlusP :=
  ((mdifferentiable_ckmrvPhiBasis 0).mul (ModularFormClass.holo ModularForm.E₆)).sub
    (mdifferentiable_const.mul
      ((mdifferentiable_ckmrvPhiBasis 1).mul (ModularFormClass.holo ModularForm.E₄)))

/-- **CKMRV (5.1), `d = 8`, plus kernel: holomorphy in `τ`.** -/
theorem differentiableOn_ckmrvEightPlusLaplace {r : ℝ} (hr : r ≠ 0) :
    DifferentiableOn ℂ (fun τ : ℂ => ∫ t in Ioi 0,
      ckmrvEightPlusKernel (UpperHalfPlane.ofComplex τ) (imagPt t) *
        (Real.exp (-(π * r ^ 2) * t) : ℂ))
      {τ : ℂ | 0 < τ.im ∧ kleinModularJ (UpperHalfPlane.ofComplex τ) ∉ jCut} := by
  have hb : 0 < π * r ^ 2 := by positivity
  have hJ : DifferentiableOn ℂ (kleinModularJ ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp mdifferentiable_kleinModularJ
  have hP : DifferentiableOn ℂ (eightPlusP ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp mdifferentiable_eightPlusP
  have hsum : DifferentiableOn ℂ (fun τ : ℂ => ckmrvPlusScale⁻¹ *
      (eightPlusP (UpperHalfPlane.ofComplex τ) * eightPlusPoly (π * r ^ 2) +
        ∑ j, eightPlusB (UpperHalfPlane.ofComplex τ) j *
          eightPlusStieltjes (π * r ^ 2) j (kleinModularJ (UpperHalfPlane.ofComplex τ))))
      {τ : ℂ | 0 < τ.im ∧ kleinModularJ (UpperHalfPlane.ofComplex τ) ∉ jCut} := by
    refine DifferentiableOn.const_mul (DifferentiableOn.add
      ((hP.mono fun τ hτ => hτ.1).mul_const _) (DifferentiableOn.fun_sum fun j _ => ?_)) _
    have ha : DifferentiableOn ℂ ((fun τ => eightPlusB τ j) ∘ UpperHalfPlane.ofComplex)
        {z : ℂ | 0 < z.im} :=
      UpperHalfPlane.mdifferentiable_iff.mp (mdifferentiable_eightPlusB j)
    exact (ha.mono fun τ hτ => hτ.1).mul ((differentiableOn_eightPlusStieltjes hb j).comp
      (hJ.mono fun τ hτ => hτ.1) fun τ hτ => hτ.2)
  refine hsum.congr fun τ hτ => ?_
  exact integral_ckmrvEightPlusKernel_eq hτ.2 hb

/-! ## The Leech lattice, minus kernel

The four `z`-factors of the Leech minus numerator are individually too large near `t = 0`
(`e^{π/t}` after dividing by `Δ(it)`). Their `τ`-coefficients are linearly dependent:
`β = 2α − 3456Δ`. Regrouping along this relation leaves three `z`-factors whose `S`-transforms
are `O(s³)` individually (the `s` and `s²` coefficients cancel inside each factor), so the
Stieltjes argument applies term by term. -/

/-- The regrouped `z`-factors of the Leech minus numerator. -/
def leechMinusM (z : ℍ) : Fin 3 → ℂ :=
  ![ModularForm.E₄ z ^ 2 * ModularForm.E₆ z * ckmrvL z - ModularForm.E₄ z ^ 3 * thetaW z,
    ModularForm.discriminant z * thetaW z,
    ModularForm.E₄ z * ModularForm.E₆ z * (thetaU z ^ 2 - thetaV z ^ 2) +
      2 * (ModularForm.E₄ z ^ 3 * thetaW z)]

/-- Their `S`-transforms, divided by `z¹⁴`. -/
def leechMinusMS (z : ℍ) : Fin 3 → ℂ :=
  ![ModularForm.E₄ z ^ 2 * ModularForm.E₆ z * ckmrvLS z + ModularForm.E₄ z ^ 3 * thetaV z,
    -(ModularForm.discriminant z * thetaV z),
    ModularForm.E₄ z * ModularForm.E₆ z * (thetaU z ^ 2 - thetaW z ^ 2) -
      2 * (ModularForm.E₄ z ^ 3 * thetaV z)]

/-- The `τ`-coefficients. -/
def leechMinusB (τ : ℍ) : Fin 3 → ℂ :=
  ![-(2 * 1728) * ModularForm.discriminant τ,
    leechMinusBeta τ * kleinModularJ τ + leechMinusGamma τ, -leechMinusAlpha τ]

theorem leechMinusSingNum_eq_sum (τ z : ℍ) :
    leechMinusSingNum τ z = ∑ j, leechMinusB τ j * leechMinusM z j := by
  rw [Fin.sum_univ_three]
  have h0 : leechMinusB τ 0 * leechMinusM z 0 = -(2 * 1728) * ModularForm.discriminant τ *
      (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z * ckmrvL z - ModularForm.E₄ z ^ 3 * thetaW z) :=
    rfl
  have h1 : leechMinusB τ 1 * leechMinusM z 1 =
      (leechMinusBeta τ * kleinModularJ τ + leechMinusGamma τ) *
        (ModularForm.discriminant z * thetaW z) := rfl
  have h2 : leechMinusB τ 2 * leechMinusM z 2 = -leechMinusAlpha τ *
      (ModularForm.E₄ z * ModularForm.E₆ z * (thetaU z ^ 2 - thetaV z ^ 2) +
        2 * (ModularForm.E₄ z ^ 3 * thetaW z)) := rfl
  rw [h0, h1, h2]
  simp only [leechMinusSingNum, leechMinusNEll, leechMinusNZero, eightMinusDenZ, leechMinusBeta,
    ckmrvEll]
  ring

theorem leechMinusM_S_zero (z : ℍ) :
    leechMinusM (ModularGroup.S • z) 0 = (z : ℂ) ^ 14 * leechMinusMS z 0 := by
  show ModularForm.E₄ (ModularGroup.S • z) ^ 2 * ModularForm.E₆ (ModularGroup.S • z) *
      ckmrvL (ModularGroup.S • z) - ModularForm.E₄ (ModularGroup.S • z) ^ 3 *
        thetaW (ModularGroup.S • z) =
    (z : ℂ) ^ 14 * (ModularForm.E₄ z ^ 2 * ModularForm.E₆ z * ckmrvLS z +
      ModularForm.E₄ z ^ 3 * thetaV z)
  rw [eisensteinFour_S, eisensteinSix_S, ckmrvL_S, thetaW_S]
  ring

theorem leechMinusM_S_one (z : ℍ) :
    leechMinusM (ModularGroup.S • z) 1 = (z : ℂ) ^ 14 * leechMinusMS z 1 := by
  show ModularForm.discriminant (ModularGroup.S • z) * thetaW (ModularGroup.S • z) =
    (z : ℂ) ^ 14 * -(ModularForm.discriminant z * thetaV z)
  rw [discriminant_S, thetaW_S]
  ring

theorem leechMinusM_S_two (z : ℍ) :
    leechMinusM (ModularGroup.S • z) 2 = (z : ℂ) ^ 14 * leechMinusMS z 2 := by
  show ModularForm.E₄ (ModularGroup.S • z) * ModularForm.E₆ (ModularGroup.S • z) *
      (thetaU (ModularGroup.S • z) ^ 2 - thetaV (ModularGroup.S • z) ^ 2) +
        2 * (ModularForm.E₄ (ModularGroup.S • z) ^ 3 * thetaW (ModularGroup.S • z)) =
    (z : ℂ) ^ 14 * (ModularForm.E₄ z * ModularForm.E₆ z * (thetaU z ^ 2 - thetaW z ^ 2) -
      2 * (ModularForm.E₄ z ^ 3 * thetaV z))
  rw [eisensteinFour_S, eisensteinSix_S, thetaU_S, thetaV_S, thetaW_S]
  ring

theorem leechMinusM_S (z : ℍ) (j : Fin 3) :
    leechMinusM (ModularGroup.S • z) j = (z : ℂ) ^ 14 * leechMinusMS z j := by
  fin_cases j
  · exact leechMinusM_S_zero z
  · exact leechMinusM_S_one z
  · exact leechMinusM_S_two z

/-- Each regrouped `S`-factor is `O(s³)`: the `s` and `s²` coefficients cancel. -/
theorem hasExp3_leechMinusMS (j : Fin 3) : HasExp3 (fun z => leechMinusMS z j) 0 0 0 := by
  fin_cases j
  · exact ((hasExp3_eisensteinFourteen.mul hasExp3_ckmrvLS).add
      (hasExp3_eisensteinFour_cube.mul hasExp3_thetaV)).congr_coeff
      (by norm_num) (by norm_num) (by norm_num)
  · exact ((hasExp3_discriminant.mul hasExp3_thetaV).neg).congr_coeff
      (by norm_num) (by norm_num) (by norm_num)
  · exact ((hasExp3_eisensteinTen.mul hasExp3_thetaU_sq_sub_thetaW_sq).sub
      ((hasExp3_eisensteinFour_cube.mul hasExp3_thetaV).const_mul 2)).congr_coeff
      (by norm_num) (by norm_num) (by norm_num)

theorem isBigO_div_discriminant_mul_of_hasExp3 {f : ℍ → ℂ} (hf : HasExp3 f 0 0 0) :
    (fun z => f z / (ModularForm.discriminant z * ModularForm.E₄ z ^ 3)) =O[atImInfty]
      fun _ => (1 : ℝ) := by
  have h1 : (fun z => (cuspS z ^ 2)⁻¹ * f z) =O[atImInfty]
      fun z : ℍ => 1 * Real.exp (-π * z.im) :=
    isBigO_cuspS_sq_inv_mul (hf.isBigO_cube.congr_right fun z => (one_mul _).symm)
  have h2 : (fun z => (cuspS z ^ 2)⁻¹ * f z) =O[atImInfty] fun _ => (1 : ℝ) :=
    h1.trans (IsBigO.of_bound 1 (Eventually.of_forall fun z => by
      rw [one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one, one_mul]
      exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, z.im_pos])))
  have hP := hasExp3_discriminantCuspQuot_inv.tendsto
  have hE := (hasExp3_eisensteinFour.tendsto.pow 3).inv₀ (by norm_num : (1 : ℂ) ^ 3 ≠ 0)
  refine ((h2.mul ((hP.mul hE).isBigO_one ℝ)).congr_right fun _ => one_mul _).congr_left
    fun z => ?_
  rw [discriminant_eq_cuspS_sq_mul, div_eq_mul_inv]
  ring

theorem isBigO_leechMinusM_div (j : Fin 3) :
    (fun z : ℍ => leechMinusM z j / (ModularForm.discriminant z * ModularForm.E₄ z ^ 3))
      =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ * Real.exp (2 * π * z.im) := by
  have h4 := hasExp3_eisensteinFour.tendsto
  have h6 := hasExp3_eisensteinSix.tendsto
  have hU := hasExp3_thetaU.tendsto
  have hV := hasExp3_thetaV.tendsto
  have hW := hasExp3_thetaW.tendsto
  have hΔ := hasExp3_discriminant.tendsto
  have hP := hasExp3_discriminantCuspQuot_inv.tendsto
  have hE := (h4.pow 3).inv₀ (by norm_num : (1 : ℂ) ^ 3 ≠ 0)
  have hM : (fun z : ℍ => leechMinusM z j) =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ := by
    fin_cases j
    · have hL : (fun z : ℍ => ckmrvL z) =O[atImInfty] fun z : ℍ => ‖(z : ℂ)‖ :=
        ((hasExp3_ckmrvL_sub.isBigO_one.trans isBigO_one_real_norm_coe).add
          isBigO_linear_norm_coe).congr_left fun z => by ring
      exact ((((((h4.pow 2).mul h6).isBigO_one ℝ).mul hL).congr_right fun z => one_mul _).sub
        ((((h4.pow 3).mul hW).isBigO_one ℝ).trans isBigO_one_real_norm_coe)).congr_left
        fun z => rfl
    · exact (((hΔ.mul hW).isBigO_one ℝ).trans isBigO_one_real_norm_coe).congr_left fun z => rfl
    · exact (((((h4.mul h6).mul ((hU.pow 2).sub (hV.pow 2))).add
        (((h4.pow 3).mul hW).const_mul 2)).isBigO_one ℝ).trans
        isBigO_one_real_norm_coe).congr_left fun z => rfl
  refine ((isBigO_cuspS_sq_inv.mul (hM.mul ((hP.mul hE).isBigO_one ℝ))).congr_left
    fun z => ?_).congr_right fun z => ?_
  · rw [discriminant_eq_cuspS_sq_mul, div_eq_mul_inv]
    ring
  · ring

theorem continuous_leechMinusM (j : Fin 3) : Continuous fun z => leechMinusM z j := by
  have h4 := (ModularFormClass.holo ModularForm.E₄).continuous
  have h6 := (ModularFormClass.holo ModularForm.E₆).continuous
  have hΔ := mdifferentiable_modularDiscriminant.continuous
  have hL := continuous_ckmrvL
  have hU := mdifferentiable_thetaU.continuous
  have hV := mdifferentiable_thetaV.continuous
  have hW := mdifferentiable_thetaW.continuous
  fin_cases j
  · exact (((h4.pow 2).mul h6).mul hL).sub ((h4.pow 3).mul hW)
  · exact hΔ.mul hW
  · exact ((h4.mul h6).mul ((hU.pow 2).sub (hV.pow 2))).add
      (continuous_const.mul ((h4.pow 3).mul hW))

theorem continuousOn_leechMinusM_div_imagPt (j : Fin 3) :
    ContinuousOn (fun t : ℝ => leechMinusM (imagPt t) j /
      (ModularForm.discriminant (imagPt t) * ModularForm.E₄ (imagPt t) ^ 3)) (Ioi 0) :=
  (continuousOn_comp_imagPt (continuous_leechMinusM j)).div
    (continuousOn_comp_imagPt (mdifferentiable_modularDiscriminant.continuous.mul
      ((ModularFormClass.holo ModularForm.E₄).continuous.pow 3)))
    fun _ ht => mul_ne_zero (ModularForm.discriminant_ne_zero _)
      (pow_ne_zero 3 (eisensteinFour_imagPt_ne_zero ht))

theorem isBigO_leechMinusM_div_imagPt_zero (j : Fin 3) :
    (fun t : ℝ => leechMinusM (imagPt t) j /
      (ModularForm.discriminant (imagPt t) * ModularForm.E₄ (imagPt t) ^ 3))
      =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) := by
  have hΦ := (isBigO_div_discriminant_mul_of_hasExp3 (hasExp3_leechMinusMS j)).comp_tendsto
    tendsto_imagPt_inv
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
  simp only [Function.comp_apply]
  rw [← hS, leechMinusM_S, discriminant_S, eisensteinFour_S, div_mul_eq_mul_div,
    div_eq_div_iff (mul_ne_zero hΔ (pow_ne_zero 3 hE))
      (mul_ne_zero (mul_ne_zero (pow_ne_zero 12 hw) hΔ)
        (pow_ne_zero 3 (mul_ne_zero (pow_ne_zero 4 hw) hE)))]
  linear_combination (leechMinusMS (imagPt t⁻¹) j * ModularForm.discriminant (imagPt t⁻¹) *
    ModularForm.E₄ (imagPt t⁻¹) ^ 3 * ((imagPt t⁻¹ : ℍ) : ℂ) ^ 14) * hp10

theorem isBigO_leechMinusM_div_imagPt_atTop (j : Fin 3) :
    (fun t : ℝ => leechMinusM (imagPt t) j /
      (ModularForm.discriminant (imagPt t) * ModularForm.E₄ (imagPt t) ^ 3)) =O[atTop]
      fun t => t * Real.exp (2 * π * t) := by
  refine ((isBigO_leechMinusM_div j).comp_tendsto tendsto_imagPt_atTop).trans
    (IsBigO.of_bound 1 ?_)
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [Function.comp_apply, norm_coe_imagPt ht, im_imagPt ht, one_mul, le_refl]

theorem integrableOn_leechMinusM_div {b : ℝ} (hb : 2 * π < b) (j : Fin 3) :
    IntegrableOn (fun t : ℝ => ‖leechMinusM (imagPt t) j /
      (ModularForm.discriminant (imagPt t) * ModularForm.E₄ (imagPt t) ^ 3) *
        (Real.exp (-b * t) : ℂ)‖) (Ioi 0) :=
  (integrableOn_Ioi_mul_exp_of_isBigO hb (continuousOn_leechMinusM_div_imagPt j)
    (isBigO_leechMinusM_div_imagPt_zero j) (isBigO_leechMinusM_div_imagPt_atTop j)).norm

theorem norm_div_discriminant_sq_le (n : ℂ) {z : ℍ} (hE : ModularForm.E₄ z ≠ 0) :
    ‖n / ModularForm.discriminant z ^ 2‖ ≤
      ‖n / (ModularForm.discriminant z * ModularForm.E₄ z ^ 3)‖ * (1 + ‖kleinModularJ z‖) := by
  have h := norm_div_discriminant_le (n / ModularForm.discriminant z) hE
  rwa [div_div, div_div, ← sq] at h

/-- The numerators of the Stieltjes transforms for `K₋⁽²⁴⁾`. -/
def leechMinusG (b : ℝ) (j : Fin 3) (t : ℝ) : ℂ :=
  leechMinusM (imagPt t) j / ModularForm.discriminant (imagPt t) ^ 2 * (Real.exp (-b * t) : ℂ)

/-- `Φⱼ(w) = ∫₀^∞ mⱼ(it) e^{−bt} / (Δ(it)² (w − j(it))) dt`. -/
def leechMinusStieltjes (b : ℝ) (j : Fin 3) (w : ℂ) : ℂ :=
  ∫ t in Ioi 0, leechMinusG b j t / (w - kleinModularJ (imagPt t))

theorem continuousOn_leechMinusG (b : ℝ) (j : Fin 3) : ContinuousOn (leechMinusG b j) (Ioi 0) :=
  ((continuousOn_comp_imagPt (continuous_leechMinusM j)).div
    (continuousOn_comp_imagPt (mdifferentiable_modularDiscriminant.continuous.pow 2))
    fun _ _ => pow_ne_zero 2 (ModularForm.discriminant_ne_zero _)).mul
    (by fun_prop : Continuous fun t : ℝ => (Real.exp (-b * t) : ℂ)).continuousOn

theorem norm_leechMinusG_le (b : ℝ) (j : Fin 3) {t : ℝ} (ht : 0 < t) :
    ‖leechMinusG b j t‖ ≤ ‖leechMinusM (imagPt t) j /
      (ModularForm.discriminant (imagPt t) * ModularForm.E₄ (imagPt t) ^ 3) *
        (Real.exp (-b * t) : ℂ)‖ * (1 + ‖kleinModularJ (imagPt t)‖) := by
  have h := norm_div_discriminant_sq_le (leechMinusM (imagPt t) j)
    (eisensteinFour_imagPt_ne_zero ht)
  rw [leechMinusG, norm_mul, norm_mul]
  calc ‖leechMinusM (imagPt t) j / ModularForm.discriminant (imagPt t) ^ 2‖ *
        ‖(Real.exp (-b * t) : ℂ)‖ ≤
      ‖leechMinusM (imagPt t) j /
        (ModularForm.discriminant (imagPt t) * ModularForm.E₄ (imagPt t) ^ 3)‖ *
        (1 + ‖kleinModularJ (imagPt t)‖) * ‖(Real.exp (-b * t) : ℂ)‖ :=
        mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = _ := by ring

theorem integrableOn_leechMinusStieltjes {b : ℝ} (hb : 2 * π < b) (j : Fin 3) {w : ℂ}
    (hw : w ∉ jCut) :
    IntegrableOn (fun t => leechMinusG b j t / (w - kleinModularJ (imagPt t))) (Ioi 0) :=
  integrableOn_stieltjes isClosed_jCut (integrableOn_leechMinusM_div hb j)
    (continuousOn_leechMinusG b j) continuousOn_kleinModularJ_imagPt
    (fun _ ht => kleinModularJ_imagPt_mem_jCut ht) (fun _ ht => norm_leechMinusG_le b j ht) hw

theorem differentiableOn_leechMinusStieltjes {b : ℝ} (hb : 2 * π < b) (j : Fin 3) :
    DifferentiableOn ℂ (leechMinusStieltjes b j) jCutᶜ :=
  differentiableOn_stieltjes isClosed_jCut (integrableOn_leechMinusM_div hb j)
    (continuousOn_leechMinusG b j) continuousOn_kleinModularJ_imagPt
    (fun _ ht => kleinModularJ_imagPt_mem_jCut ht) (fun _ ht => norm_leechMinusG_le b j ht)

theorem ckmrvLeechMinusKernel_imagPt_mul_eq_sum (τ : ℍ) (b t : ℝ) :
    ckmrvLeechMinusKernel τ (imagPt t) * (Real.exp (-b * t) : ℂ) =
      ckmrvMinusScale⁻¹ * ∑ j, leechMinusB τ j *
        (leechMinusG b j t / (kleinModularJ τ - kleinModularJ (imagPt t))) := by
  rw [ckmrvLeechMinusKernel_eq_sing, leechMinusSingNum_eq_sum, Fin.sum_univ_three,
    Fin.sum_univ_three]
  simp only [leechMinusG]
  ring

/-- **The Leech minus Laplace integral as a combination of Stieltjes transforms.** -/
theorem integral_ckmrvLeechMinusKernel_eq {τ : ℍ} (hτ : kleinModularJ τ ∉ jCut) {b : ℝ}
    (hb : 2 * π < b) :
    ∫ t in Ioi 0, ckmrvLeechMinusKernel τ (imagPt t) * (Real.exp (-b * t) : ℂ) =
      ckmrvMinusScale⁻¹ * ∑ j, leechMinusB τ j * leechMinusStieltjes b j (kleinModularJ τ) := by
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun t _ => ckmrvLeechMinusKernel_imagPt_mul_eq_sum τ b t),
    integral_const_mul, integral_finsetSum _ fun j _ =>
      (integrableOn_leechMinusStieltjes hb j hτ).const_mul (leechMinusB τ j)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  rfl

theorem mdifferentiable_leechMinusAlpha : MDiff leechMinusAlpha :=
  ((mdifferentiable_ckmrvPsiBasis 1).mul ((ModularFormClass.holo ModularForm.E₄).mul
    (ModularFormClass.holo ModularForm.E₆))).sub
    ((mdifferentiable_ckmrvPsiBasis 2).mul ((ModularFormClass.holo ModularForm.E₄).pow 2))

theorem mdifferentiable_leechMinusB (j : Fin 3) : MDiff (fun τ => leechMinusB τ j) := by
  have hα := mdifferentiable_leechMinusAlpha
  have hΔ := mdifferentiable_modularDiscriminant
  have hJ := mdifferentiable_kleinModularJ
  fin_cases j
  · exact mdifferentiable_const.mul hΔ
  · exact (((mdifferentiable_const.mul hα).sub (mdifferentiable_const.mul hΔ)).mul hJ).add
      ((hJ.mul hα).add (mdifferentiable_const.mul ((mdifferentiable_ckmrvPsiBasis 2).mul
        ((ModularFormClass.holo ModularForm.E₄).pow 2))))
  · exact hα.neg

/-- **CKMRV (5.1), Leech minus kernel: holomorphy in `τ`** (`r² > 2`). -/
theorem differentiableOn_ckmrvLeechMinusLaplace {r : ℝ} (hr : 2 < r ^ 2) :
    DifferentiableOn ℂ (fun τ : ℂ => ∫ t in Ioi 0,
      ckmrvLeechMinusKernel (UpperHalfPlane.ofComplex τ) (imagPt t) *
        (Real.exp (-(π * r ^ 2) * t) : ℂ))
      {τ : ℂ | 0 < τ.im ∧ kleinModularJ (UpperHalfPlane.ofComplex τ) ∉ jCut} := by
  have hb : 2 * π < π * r ^ 2 := by nlinarith [Real.pi_pos]
  have hJ : DifferentiableOn ℂ (kleinModularJ ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp mdifferentiable_kleinModularJ
  have hsum : DifferentiableOn ℂ (fun τ : ℂ => ckmrvMinusScale⁻¹ *
      ∑ j, leechMinusB (UpperHalfPlane.ofComplex τ) j *
        leechMinusStieltjes (π * r ^ 2) j (kleinModularJ (UpperHalfPlane.ofComplex τ)))
      {τ : ℂ | 0 < τ.im ∧ kleinModularJ (UpperHalfPlane.ofComplex τ) ∉ jCut} := by
    refine DifferentiableOn.const_mul (DifferentiableOn.fun_sum fun j _ => ?_) _
    have ha : DifferentiableOn ℂ ((fun τ => leechMinusB τ j) ∘ UpperHalfPlane.ofComplex)
        {z : ℂ | 0 < z.im} :=
      UpperHalfPlane.mdifferentiable_iff.mp (mdifferentiable_leechMinusB j)
    exact (ha.mono fun τ hτ => hτ.1).mul ((differentiableOn_leechMinusStieltjes hb j).comp
      (hJ.mono fun τ hτ => hτ.1) fun τ hτ => hτ.2)
  refine hsum.congr fun τ hτ => ?_
  exact integral_ckmrvLeechMinusKernel_eq hτ.2 hb

end E8Leech
