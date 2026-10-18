import E8Leech.CKMRVLaplaceFull
import SpherePacking.ForMathlib.ContDiffOnByDeriv

/-!
# Smoothness in the radius of the subtracted Laplace transforms (CKMRV (5.3)/(5.4), P4d-5b)

If `g` is continuous on `(0, ∞)`, bounded near `0` and `O(t e^{a t})` at `∞`, then
`s ↦ ∫₀^∞ g(t) e^{−st} dt` is `C^∞` on `s > a`: the family `Lₙ(s) = ∫ g(t) (−t)ⁿ e^{−st} dt`
satisfies `Lₙ' = Lₙ₊₁` (differentiation under the integral sign, dominated on a ball around each
`s₀ > a`), and SPL's `contDiffOn_family_infty_of_hasDerivAt` upgrades this to `C^∞`.

Applied to `g = (K − G)(τ, i·)` for the four kernels, the subtracted transforms of
`CKMRVLaplaceFull` are `C^∞` in `b > −π` (`b > −π/2` for the Leech plus kernel), in particular
across `b = 0`.
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Asymptotics MeasureTheory Set Metric
open UpperHalfPlane hiding I
open scoped Real ContDiff

theorem isBigO_pow_mul_exp_shift (n : ℕ) {c ε : ℝ} (hε : 0 < ε) :
    (fun t : ℝ => t ^ n * Real.exp (c * t)) =O[atTop] fun t => t * Real.exp ((c + ε) * t) := by
  have h1 : (fun t : ℝ => t ^ n) =O[atTop] fun t => Real.exp (ε * t) :=
    (isLittleO_pow_exp_pos_mul_atTop n hε).isBigO
  have h2 : (fun t : ℝ => Real.exp (ε * t)) =O[atTop] fun t => t * Real.exp (ε * t) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (mul_nonneg (by linarith) (Real.exp_pos _).le), one_mul]
    exact le_mul_of_one_le_left (Real.exp_pos _).le ht
  refine ((h1.trans h2).mul (isBigO_refl (fun t : ℝ => Real.exp (c * t)) atTop)).congr_right
    fun t => ?_
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The derivative family of a Laplace transform. -/
def laplaceFamily (g : ℝ → ℂ) (n : ℕ) (s : ℝ) : ℂ :=
  ∫ t in Ioi 0, g t * ((-t : ℝ) : ℂ) ^ n * (Real.exp (-s * t) : ℂ)

theorem integrableOn_laplaceFamily_bound {g : ℝ → ℂ} {a : ℝ} (hg : ContinuousOn g (Ioi 0))
    (hg0 : g =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ))
    (hginf : g =O[atTop] fun t => t * Real.exp (a * t)) (n : ℕ) {b : ℝ} (hb : a < b) :
    IntegrableOn (fun t => g t * ((-t : ℝ) : ℂ) ^ n * (Real.exp (-b * t) : ℂ)) (Ioi 0) := by
  have hε : 0 < (b - a) / 2 := by linarith
  refine integrableOn_Ioi_mul_exp_of_isBigO (a := a + (b - a) / 2) (by linarith)
    (hg.mul (by fun_prop : Continuous fun t : ℝ => ((-t : ℝ) : ℂ) ^ n).continuousOn) ?_ ?_
  · have hp : (fun t : ℝ => ((-t : ℝ) : ℂ) ^ n) =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) :=
      ((Continuous.tendsto (by fun_prop : Continuous fun t : ℝ => ((-t : ℝ) : ℂ) ^ n) 0)
        |>.mono_left nhdsWithin_le_nhds).isBigO_one ℝ
    exact (hg0.mul hp).congr_right fun _ => one_mul _
  · have hp : (fun t : ℝ => ((-t : ℝ) : ℂ) ^ n) =O[atTop] fun t : ℝ => t ^ n :=
      IsBigO.of_bound 1 (Eventually.of_forall fun t => by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, one_mul,
          abs_pow])
    refine ((hginf.mul hp).trans ?_)
    refine ((isBigO_pow_mul_exp_shift (n + 1) (c := a) hε).congr_left fun t => ?_)
    ring

theorem hasDerivAt_laplaceFamily {g : ℝ → ℂ} {a : ℝ} (hg : ContinuousOn g (Ioi 0))
    (hg0 : g =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ))
    (hginf : g =O[atTop] fun t => t * Real.exp (a * t)) (n : ℕ) {s₀ : ℝ} (hs₀ : a < s₀) :
    HasDerivAt (laplaceFamily g n) (laplaceFamily g (n + 1) s₀) s₀ := by
  set δ := (s₀ - a) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hint := integrableOn_laplaceFamily_bound hg hg0 hginf (n + 1) (b := s₀ - δ)
    (by rw [hδ]; linarith)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun s t => g t * ((-t : ℝ) : ℂ) ^ n * (Real.exp (-s * t) : ℂ))
    (F' := fun s t => g t * ((-t : ℝ) : ℂ) ^ (n + 1) * (Real.exp (-s * t) : ℂ))
    (bound := fun t => ‖g t * ((-t : ℝ) : ℂ) ^ (n + 1) * (Real.exp (-(s₀ - δ) * t) : ℂ)‖)
    (ball_mem_nhds s₀ hδ0) ?_ ?_ ?_ ?_ hint.norm ?_
  · exact key.2
  · refine Eventually.of_forall fun s => ?_
    exact ((hg.mul (by fun_prop : Continuous fun t : ℝ => ((-t : ℝ) : ℂ) ^ n).continuousOn).mul
      (by fun_prop : Continuous fun t : ℝ => (Real.exp (-s * t) : ℂ)).continuousOn)
      |>.aestronglyMeasurable measurableSet_Ioi
  · exact integrableOn_laplaceFamily_bound hg hg0 hginf n hs₀
  · exact ((hg.mul (by fun_prop : Continuous fun t : ℝ => ((-t : ℝ) : ℂ) ^ (n + 1)).continuousOn).mul
      (by fun_prop : Continuous fun t : ℝ => (Real.exp (-s₀ * t) : ℂ)).continuousOn)
      |>.aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht s hs => ?_)
    have ht0 : (0 : ℝ) < t := ht
    have hs' : s₀ - δ ≤ s := by
      have := mem_ball.mp hs
      rw [Real.dist_eq] at this
      linarith [neg_abs_le (s - s₀)]
    have e1 : ‖(Real.exp (-s * t) : ℂ)‖ ≤ ‖(Real.exp (-(s₀ - δ) * t) : ℂ)‖ := by
      rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hs' ht0.le])
    calc ‖g t * ((-t : ℝ) : ℂ) ^ (n + 1) * (Real.exp (-s * t) : ℂ)‖
        = ‖g t * ((-t : ℝ) : ℂ) ^ (n + 1)‖ * ‖(Real.exp (-s * t) : ℂ)‖ := norm_mul _ _
      _ ≤ ‖g t * ((-t : ℝ) : ℂ) ^ (n + 1)‖ * ‖(Real.exp (-(s₀ - δ) * t) : ℂ)‖ :=
          mul_le_mul_of_nonneg_left e1 (norm_nonneg _)
      _ = ‖g t * ((-t : ℝ) : ℂ) ^ (n + 1) * (Real.exp (-(s₀ - δ) * t) : ℂ)‖ := (norm_mul _ _).symm
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t _ s _ => ?_)
    have hd : HasDerivAt (fun s : ℝ => Real.exp (-s * t)) (Real.exp (-s * t) * (-1 * t)) s :=
      ((hasDerivAt_neg s).mul_const t).exp
    have hd' := (hd.ofReal_comp).const_mul (g t * ((-t : ℝ) : ℂ) ^ n)
    refine hd'.congr_deriv ?_
    push_cast
    ring

theorem contDiffOn_laplace {g : ℝ → ℂ} {a : ℝ} (hg : ContinuousOn g (Ioi 0))
    (hg0 : g =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ))
    (hginf : g =O[atTop] fun t => t * Real.exp (a * t)) :
    ContDiffOn ℝ ∞ (fun s => ∫ t in Ioi 0, g t * (Real.exp (-s * t) : ℂ)) (Ioi a) := by
  have h := SpherePacking.ForMathlib.contDiffOn_family_infty_of_hasDerivAt (F := laplaceFamily g)
    isOpen_Ioi (fun n s hs => hasDerivAt_laplaceFamily hg hg0 hginf n hs) 0
  refine h.congr fun s _ => ?_
  simp [laplaceFamily]

/-! ## The four subtracted kernels -/

theorem continuousOn_sub_of_imagPt {k G : ℝ → ℂ} {A B C D : ℂ} {c : ℝ}
    (hk : ContinuousOn k (Ioi 0)) (hG : ∀ t, 0 < t → G t = cuspProfile A B C D c t) :
    ContinuousOn (fun t => k t - G t) (Ioi 0) :=
  hk.sub ((continuous_cuspProfile A B C D c).continuousOn.congr fun t ht => hG t ht)

theorem isBigO_sub_zero_of_imagPt {k G : ℝ → ℂ} {A B C D : ℂ} {c : ℝ}
    (hk : k =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ))
    (hG : ∀ t, 0 < t → G t = cuspProfile A B C D c t) :
    (fun t => k t - G t) =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) := by
  refine hk.sub ((((continuous_cuspProfile A B C D c).tendsto 0).mono_left
    nhdsWithin_le_nhds).isBigO_one ℝ |>.congr' ?_ (Eventually.of_forall fun _ => rfl))
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hG t ht).symm

/-- **(5.3), `d = 8`, minus kernel: the subtracted transform is `C^∞` in `b > −π`.** -/
theorem contDiffOn_ckmrvEightMinus_sub_G_laplace {τ : ℍ} (hτ : kleinModularJ τ ∉ jCut) :
    ContDiffOn ℝ ∞ (fun b => ∫ t in Ioi 0, (ckmrvEightMinusKernel τ (imagPt t) -
      ckmrvEightMinusG τ (imagPt t)) * (Real.exp (-b * t) : ℂ)) (Ioi (-π)) :=
  contDiffOn_laplace
    (continuousOn_sub_of_imagPt (continuousOn_ckmrvEightMinusKernel_imagPt τ
      (kleinModularJ_ne_imagPt_of_not_mem_jCut hτ)) fun _ ht => ckmrvEightMinusG_imagPt τ ht)
    (isBigO_sub_zero_of_imagPt (isBigO_ckmrvEightMinusKernel_imagPt_zero τ)
      fun _ ht => ckmrvEightMinusG_imagPt τ ht)
    (isBigO_comp_imagPt (w := fun x => x) (c := -π) (isBigO_ckmrvEightMinusKernel_sub_G τ))

/-- **(5.3), `d = 8`, plus kernel: the subtracted transform is `C^∞` in `b > −π`.** -/
theorem contDiffOn_ckmrvEightPlus_sub_G_laplace {τ : ℍ} (hτ : kleinModularJ τ ∉ jCut) :
    ContDiffOn ℝ ∞ (fun b => ∫ t in Ioi 0, (ckmrvEightPlusKernel τ (imagPt t) -
      ckmrvEightPlusG τ (imagPt t)) * (Real.exp (-b * t) : ℂ)) (Ioi (-π)) :=
  contDiffOn_laplace
    (continuousOn_sub_of_imagPt (continuousOn_ckmrvEightPlusKernel_imagPt τ
      (kleinModularJ_ne_imagPt_of_not_mem_jCut hτ)) fun _ ht => ckmrvEightPlusG_imagPt τ ht)
    (isBigO_sub_zero_of_imagPt (isBigO_ckmrvEightPlusKernel_imagPt_zero τ)
      fun _ ht => ckmrvEightPlusG_imagPt τ ht)
    (isBigO_mul_exp_neg_pi_sq (isBigO_comp_imagPt (w := fun x => x ^ 2) (c := -2 * π)
      (isBigO_ckmrvEightPlusKernel_sub_G τ)))

/-- **(5.4), Leech minus kernel: the subtracted transform is `C^∞` in `b > −π`.** -/
theorem contDiffOn_ckmrvLeechMinus_sub_G_laplace {τ : ℍ} (hτ : kleinModularJ τ ∉ jCut) :
    ContDiffOn ℝ ∞ (fun b => ∫ t in Ioi 0, (ckmrvLeechMinusKernel τ (imagPt t) -
      ckmrvLeechMinusG τ (imagPt t)) * (Real.exp (-b * t) : ℂ)) (Ioi (-π)) :=
  contDiffOn_laplace
    (continuousOn_sub_of_imagPt (continuousOn_ckmrvLeechMinusKernel_imagPt τ
      (kleinModularJ_ne_imagPt_of_not_mem_jCut hτ)) fun _ ht => ckmrvLeechMinusG_imagPt τ ht)
    (isBigO_sub_zero_of_imagPt (isBigO_ckmrvLeechMinusKernel_imagPt_zero τ)
      fun _ ht => ckmrvLeechMinusG_imagPt τ ht)
    (isBigO_comp_imagPt (w := fun x => x) (c := -π) (isBigO_ckmrvLeechMinusKernel_sub_G τ))

/-- **(5.4), Leech plus kernel: the subtracted transform is `C^∞` in `b > −π/2`.** -/
theorem contDiffOn_ckmrvLeechPlus_sub_G_laplace {τ : ℍ} (hτ : kleinModularJ τ ∉ jCut) :
    ContDiffOn ℝ ∞ (fun b => ∫ t in Ioi 0, (ckmrvLeechPlusKernel τ (imagPt t) -
      ckmrvLeechPlusG τ (imagPt t)) * (Real.exp (-b * t) : ℂ)) (Ioi (-π + π / 2)) :=
  contDiffOn_laplace
    (continuousOn_sub_of_imagPt (continuousOn_ckmrvLeechPlusKernel_imagPt τ
      (kleinModularJ_ne_imagPt_of_not_mem_jCut hτ)) fun _ ht => ckmrvLeechPlusG_imagPt τ ht)
    (isBigO_sub_zero_of_imagPt (isBigO_ckmrvLeechPlusKernel_imagPt_zero τ)
      fun _ ht => ckmrvLeechPlusG_imagPt τ ht)
    ((isBigO_comp_imagPt (w := fun x => x ^ 2) (c := -π)
      (isBigO_ckmrvLeechPlusKernel_sub_G τ)).trans
      (isBigO_sq_mul_exp_shift (c := -π) (ε := π / 2) (by positivity)))

end E8Leech
