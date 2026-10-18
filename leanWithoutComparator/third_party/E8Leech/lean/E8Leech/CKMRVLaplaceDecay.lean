import E8Leech.CKMRVRadialProfile
import SpherePacking.ForMathlib.ExpBounds

/-!
# Rapid decay in the radius of the CKMRV Laplace integrals (P4d-5d)

Near `t = 0` the kernels are super-exponentially small: `K(τ, it) = (K ∣ S)(τ, i/t) · (−t^k)`
and `(K ∣ S)(τ, w) = O(e^{−π Im w})` (Lemma 4.11, `z` side), so `K(τ, it) = O(e^{−π/t})`.
With the AM–GM bound `e^{−π/t} e^{−πst} ≤ e^{−2π√s}` (Sphere-Packing-Lean, `ExpBounds`) the
part of `∫₀^∞ K(τ, it) e^{−πst} dt` over `(0, δ]` is `O(e^{−2π√s})`, and the part over `(δ, ∞)`
is `O(e^{−πδs})`. Both are `O(s^{−k})` for every `k`. The same holds for the derivative
family `∫ K(τ, it) (−t)ⁿ e^{−πst} dt`, so every derivative of the radial profile decays faster
than any power: the input for the Schwartz property (SPL `RadialSchwartz`).
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Asymptotics MeasureTheory Set
open UpperHalfPlane hiding I
open scoped Real

/-! ## Super-exponential smallness near `t = 0` from the `S`-side -/

theorem isBigO_imagPt_zero_exp_of_S {f : ℍ → ℂ} {k : ℕ} {c : ℝ}
    (hS : (fun z : ℍ => f (ModularGroup.S • z) * (z : ℂ) ^ k) =O[atImInfty]
      fun z : ℍ => Real.exp (c * z.im)) :
    (fun t => f (imagPt t)) =O[𝓝[>] (0 : ℝ)] fun t => Real.exp (c / t) := by
  obtain ⟨C, hC⟩ := (hS.comp_tendsto tendsto_imagPt_inv).bound
  refine IsBigO.of_bound C ?_
  filter_upwards [hC, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht ht1
  have ht0 : (0 : ℝ) < t := ht1.1
  simp only [Function.comp_apply] at ht
  rw [im_imagPt (inv_pos.mpr ht0), norm_mul, norm_pow,
    norm_coe_imagPt (inv_pos.mpr ht0)] at ht
  have hpow : 1 ≤ (t⁻¹) ^ k := one_le_pow₀ ((one_le_inv₀ ht0).mpr ht1.2.le)
  rw [← S_smul_imagPt_inv ht0, div_eq_mul_inv, mul_comm c t⁻¹, ← mul_comm c]
  calc ‖f (ModularGroup.S • imagPt t⁻¹)‖
      ≤ ‖f (ModularGroup.S • imagPt t⁻¹)‖ * t⁻¹ ^ k :=
        le_mul_of_one_le_right (norm_nonneg _) hpow
    _ ≤ C * ‖Real.exp (c * t⁻¹)‖ := ht

theorem isBigO_exp_div_mono {c c' : ℝ} (h : c ≤ c') :
    (fun t : ℝ => Real.exp (c / t)) =O[𝓝[>] (0 : ℝ)] fun t => Real.exp (c' / t) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (0 : ℝ) < t := ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    abs_of_pos (Real.exp_pos _), one_mul]
  exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right h ht0.le)

/-! ## Decay of a Laplace transform -/

/-- If `g = O(e^{−π/t})` near `0` and `g = O(t e^{at})` at `∞`, then for every `k`,
`s^k ∫₀^∞ g(t) e^{−πst} dt` is bounded for large `s`. -/
theorem exists_bound_laplace_decay {g : ℝ → ℂ} {a : ℝ} (hg : ContinuousOn g (Ioi 0))
    (hg0 : g =O[𝓝[>] (0 : ℝ)] fun t => Real.exp (-π / t))
    (hginf : g =O[atTop] fun t => t * Real.exp (a * t)) (k : ℕ) :
    ∃ C S₀ : ℝ, ∀ s : ℝ, S₀ ≤ s →
      s ^ k * ‖∫ t in Ioi 0, g t * (Real.exp (-(π * s) * t) : ℂ)‖ ≤ C := by
  -- the bound near `0`
  obtain ⟨M, hM⟩ := hg0.bound
  obtain ⟨u, hu, huS⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hM
  set δ : ℝ := min u 1 / 2 with hδdef
  have hmin : (0 : ℝ) < min u 1 := lt_min hu one_pos
  have hδ : 0 < δ := by positivity
  have hδu : δ < u := by
    have := min_le_left u 1
    rw [hδdef]
    linarith
  have hM0 : 0 ≤ M := by
    have h := huS ⟨half_pos hu, half_lt_self hu⟩
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans h) (norm_pos_iff.mpr
      (Real.exp_pos _).ne')
  -- the far part: integrable with a fixed exponent
  set s₁ : ℝ := (|a| + 1) / π with hs₁
  have hπ := Real.pi_pos
  have ha1 : a < π * s₁ := by
    rw [hs₁, mul_div_cancel₀ _ hπ.ne']
    linarith [le_abs_self a]
  have hfar_int : IntegrableOn (fun t => g t * (Real.exp (-(π * s₁) * t) : ℂ)) (Ioi 0) :=
    integrableOn_Ioi_mul_exp_of_isBigO ha1 hg
      (hg0.trans (IsBigO.of_bound 1 (by
        filter_upwards [self_mem_nhdsWithin] with t ht
        have ht0 : (0 : ℝ) < t := ht
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one, one_mul]
        exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) ht0.le))))
      hginf
  set I₁ : ℝ := ∫ t in Ioi δ, ‖g t * (Real.exp (-(π * s₁) * t) : ℂ)‖
  have hI₁ : 0 ≤ I₁ := setIntegral_nonneg measurableSet_Ioi fun _ _ => norm_nonneg _
  -- the two polynomial-exponential bounds
  obtain ⟨C₁, hC₁⟩ := SpherePacking.ForMathlib.exists_bound_pow_mul_exp_neg_mul_sqrt k
    (b := 2 * π) (by positivity)
  obtain ⟨C₂, hC₂⟩ := SpherePacking.ForMathlib.exists_bound_pow_mul_exp_neg_mul k
    (b := π * δ) (by positivity)
  refine ⟨M * δ * C₁ + I₁ * Real.exp (π * s₁ * δ) * C₂, max s₁ 0, fun s hs => ?_⟩
  have hs0 : 0 ≤ s := le_trans (le_max_right _ _) hs
  have hss₁ : s₁ ≤ s := le_trans (le_max_left _ _) hs
  have hint_s : IntegrableOn (fun t => g t * (Real.exp (-(π * s) * t) : ℂ)) (Ioi 0) :=
    integrableOn_Ioi_mul_exp_of_isBigO (lt_of_lt_of_le ha1
      (mul_le_mul_of_nonneg_left hss₁ hπ.le)) hg
      (hg0.trans (IsBigO.of_bound 1 (by
        filter_upwards [self_mem_nhdsWithin] with t ht
        have ht0 : (0 : ℝ) < t := ht
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one, one_mul]
        exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) ht0.le))))
      hginf
  rw [← Ioc_union_Ioi_eq_Ioi hδ.le, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hint_s.mono_set Ioc_subset_Ioi_self) (hint_s.mono_set (Ioi_subset_Ioi hδ.le))]
  -- near part
  have hnear : ‖∫ t in Ioc 0 δ, g t * (Real.exp (-(π * s) * t) : ℂ)‖ ≤
      M * Real.exp (-2 * π * Real.sqrt s) * δ := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc (0 : ℝ) δ)
      (f := fun t => g t * (Real.exp (-(π * s) * t) : ℂ)) (C := M * Real.exp (-2 * π * Real.sqrt s))
      (by simp) (fun t ht => by
        have hgt : ‖g t‖ ≤ M * ‖Real.exp (-π / t)‖ := huS ⟨ht.1, lt_of_le_of_lt ht.2 hδu⟩
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hgt
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        have hamgm := SpherePacking.ForMathlib.exp_neg_pi_div_mul_exp_neg_pi_mul_le s t hs0 ht.1
        calc ‖g t‖ * Real.exp (-(π * s) * t)
            ≤ M * Real.exp (-π / t) * Real.exp (-(π * s) * t) :=
              mul_le_mul_of_nonneg_right hgt (Real.exp_pos _).le
          _ = M * (Real.exp (-π / t) * Real.exp (-π * s * t)) := by ring_nf
          _ ≤ M * Real.exp (-2 * π * Real.sqrt s) := mul_le_mul_of_nonneg_left hamgm hM0)
    have hvol : volume.real (Ioc (0 : ℝ) δ) = δ := by
      rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith), sub_zero]
    rwa [hvol] at h
  -- far part
  have hfar : ‖∫ t in Ioi δ, g t * (Real.exp (-(π * s) * t) : ℂ)‖ ≤
      I₁ * Real.exp (-(π * (s - s₁)) * δ) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_mul_const]
    refine setIntegral_mono_on (hint_s.mono_set (Ioi_subset_Ioi hδ.le)).norm
      ((hfar_int.mono_set (Ioi_subset_Ioi hδ.le)).norm.mul_const _) measurableSet_Ioi
      fun t ht => ?_
    have ht0 : (0 : ℝ) < t := lt_trans hδ ht
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _), mul_assoc,
      ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have h1 : 0 ≤ s - s₁ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left (le_of_lt ht) (mul_nonneg hπ.le h1)]
  have hsk : 0 ≤ s ^ k := pow_nonneg hs0 k
  have hb1 := hC₁ s hs0
  have hb2 := hC₂ s hs0
  have hexp : Real.exp (-(π * (s - s₁)) * δ) = Real.exp (π * s₁ * δ) * Real.exp (-(π * δ) * s) := by
    rw [← Real.exp_add]
    ring_nf
  calc s ^ k * ‖(∫ t in Ioc 0 δ, g t * (Real.exp (-(π * s) * t) : ℂ)) +
        ∫ t in Ioi δ, g t * (Real.exp (-(π * s) * t) : ℂ)‖
      ≤ s ^ k * (M * Real.exp (-2 * π * Real.sqrt s) * δ +
          I₁ * Real.exp (-(π * (s - s₁)) * δ)) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hnear hfar)) hsk
    _ = M * δ * (s ^ k * Real.exp (-(2 * π) * Real.sqrt s)) +
          I₁ * Real.exp (π * s₁ * δ) * (s ^ k * Real.exp (-(π * δ) * s)) := by
        rw [hexp]
        ring_nf
    _ ≤ M * δ * C₁ + I₁ * Real.exp (π * s₁ * δ) * C₂ := by
        gcongr

/-! ## The derivative family -/

theorem isBigO_mul_neg_pow_zero {g : ℝ → ℂ} {c : ℝ}
    (hg0 : g =O[𝓝[>] (0 : ℝ)] fun t => Real.exp (c / t)) (n : ℕ) :
    (fun t => g t * ((-t : ℝ) : ℂ) ^ n) =O[𝓝[>] (0 : ℝ)] fun t => Real.exp (c / t) := by
  have hp : (fun t : ℝ => ((-t : ℝ) : ℂ) ^ n) =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) :=
    ((Continuous.tendsto (by fun_prop : Continuous fun t : ℝ => ((-t : ℝ) : ℂ) ^ n) 0)
      |>.mono_left nhdsWithin_le_nhds).isBigO_one ℝ
  exact (hg0.mul hp).congr_right fun _ => mul_one _

theorem isBigO_mul_neg_pow_atTop {g : ℝ → ℂ} {a : ℝ}
    (hginf : g =O[atTop] fun t => t * Real.exp (a * t)) (n : ℕ) :
    (fun t => g t * ((-t : ℝ) : ℂ) ^ n) =O[atTop] fun t => t * Real.exp ((a + 1) * t) := by
  have hp : (fun t : ℝ => ((-t : ℝ) : ℂ) ^ n) =O[atTop] fun t : ℝ => t ^ n :=
    IsBigO.of_bound 1 (Eventually.of_forall fun t => by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, one_mul,
        abs_pow])
  exact (hginf.mul hp).trans ((isBigO_pow_mul_exp_shift (n + 1) (c := a) one_pos).congr_left
    fun t => by ring)

/-- Every derivative of the Laplace transform decays faster than any power. -/
theorem exists_bound_laplaceFamily_decay {g : ℝ → ℂ} {a : ℝ} (hg : ContinuousOn g (Ioi 0))
    (hg0 : g =O[𝓝[>] (0 : ℝ)] fun t => Real.exp (-π / t))
    (hginf : g =O[atTop] fun t => t * Real.exp (a * t)) (n k : ℕ) :
    ∃ C S₀ : ℝ, ∀ s : ℝ, S₀ ≤ s → s ^ k * ‖laplaceFamily g n (π * s)‖ ≤ C :=
  exists_bound_laplace_decay
    (hg.mul (by fun_prop : Continuous fun t : ℝ => ((-t : ℝ) : ℂ) ^ n).continuousOn)
    (isBigO_mul_neg_pow_zero hg0 n) (isBigO_mul_neg_pow_atTop hginf n) k

/-! ## The four kernels -/

theorem isBigO_ckmrvEightMinusKernel_imagPt_zero_exp (τ : ℍ) :
    (fun t => ckmrvEightMinusKernel τ (imagPt t)) =O[𝓝[>] (0 : ℝ)]
      fun t => Real.exp (-π / t) :=
  isBigO_imagPt_zero_exp_of_S (isBigO_ckmrvEightMinusKernel_S_right τ)

theorem isBigO_ckmrvEightPlusKernel_imagPt_zero_exp (τ : ℍ) :
    (fun t => ckmrvEightPlusKernel τ (imagPt t)) =O[𝓝[>] (0 : ℝ)]
      fun t => Real.exp (-π / t) :=
  (isBigO_imagPt_zero_exp_of_S (isBigO_ckmrvEightPlusKernel_S_right τ)).trans
    (isBigO_exp_div_mono (by linarith [Real.pi_pos]))

theorem isBigO_ckmrvLeechMinusKernel_imagPt_zero_exp (τ : ℍ) :
    (fun t => ckmrvLeechMinusKernel τ (imagPt t)) =O[𝓝[>] (0 : ℝ)]
      fun t => Real.exp (-π / t) :=
  isBigO_imagPt_zero_exp_of_S (isBigO_ckmrvLeechMinusKernel_S_right τ)

theorem isBigO_ckmrvLeechPlusKernel_imagPt_zero_exp (τ : ℍ) :
    (fun t => ckmrvLeechPlusKernel τ (imagPt t)) =O[𝓝[>] (0 : ℝ)]
      fun t => Real.exp (-π / t) :=
  (isBigO_imagPt_zero_exp_of_S (isBigO_ckmrvLeechPlusKernel_S_right τ)).trans
    (isBigO_exp_div_mono (by linarith [Real.pi_pos]))

/-- **Rapid decay, `d = 8`, minus kernel.** -/
theorem exists_bound_ckmrvEightMinus_laplace_decay {τ : ℍ} (hτ : kleinModularJ τ ∉ jCut)
    (n k : ℕ) : ∃ C S₀ : ℝ, ∀ s : ℝ, S₀ ≤ s →
      s ^ k * ‖laplaceFamily (fun t => ckmrvEightMinusKernel τ (imagPt t)) n (π * s)‖ ≤ C :=
  exists_bound_laplaceFamily_decay (continuousOn_ckmrvEightMinusKernel_imagPt τ
    (kleinModularJ_ne_imagPt_of_not_mem_jCut hτ)) (isBigO_ckmrvEightMinusKernel_imagPt_zero_exp τ)
    (isBigO_ckmrvEightMinusKernel_imagPt_atTop τ) n k

/-- **Rapid decay, `d = 8`, plus kernel.** -/
theorem exists_bound_ckmrvEightPlus_laplace_decay {τ : ℍ} (hτ : kleinModularJ τ ∉ jCut)
    (n k : ℕ) : ∃ C S₀ : ℝ, ∀ s : ℝ, S₀ ≤ s →
      s ^ k * ‖laplaceFamily (fun t => ckmrvEightPlusKernel τ (imagPt t)) n (π * s)‖ ≤ C :=
  exists_bound_laplaceFamily_decay (continuousOn_ckmrvEightPlusKernel_imagPt τ
    (kleinModularJ_ne_imagPt_of_not_mem_jCut hτ)) (isBigO_ckmrvEightPlusKernel_imagPt_zero_exp τ)
    (isBigO_ckmrvEightPlusKernel_imagPt_atTop τ) n k

/-- **Rapid decay, Leech minus kernel.** -/
theorem exists_bound_ckmrvLeechMinus_laplace_decay {τ : ℍ} (hτ : kleinModularJ τ ∉ jCut)
    (n k : ℕ) : ∃ C S₀ : ℝ, ∀ s : ℝ, S₀ ≤ s →
      s ^ k * ‖laplaceFamily (fun t => ckmrvLeechMinusKernel τ (imagPt t)) n (π * s)‖ ≤ C :=
  exists_bound_laplaceFamily_decay (continuousOn_ckmrvLeechMinusKernel_imagPt τ
    (kleinModularJ_ne_imagPt_of_not_mem_jCut hτ)) (isBigO_ckmrvLeechMinusKernel_imagPt_zero_exp τ)
    (isBigO_ckmrvLeechMinusKernel_imagPt_atTop τ) n k

/-- **Rapid decay, Leech plus kernel.** -/
theorem exists_bound_ckmrvLeechPlus_laplace_decay {τ : ℍ} (hτ : kleinModularJ τ ∉ jCut)
    (n k : ℕ) : ∃ C S₀ : ℝ, ∀ s : ℝ, S₀ ≤ s →
      s ^ k * ‖laplaceFamily (fun t => ckmrvLeechPlusKernel τ (imagPt t)) n (π * s)‖ ≤ C :=
  exists_bound_laplaceFamily_decay (continuousOn_ckmrvLeechPlusKernel_imagPt τ
    (kleinModularJ_ne_imagPt_of_not_mem_jCut hτ)) (isBigO_ckmrvLeechPlusKernel_imagPt_zero_exp τ)
    (isBigO_ckmrvLeechPlusKernel_imagPt_atTop τ) n k

end E8Leech
