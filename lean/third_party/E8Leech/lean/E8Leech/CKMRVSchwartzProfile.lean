import E8Leech.CKMRVLaplaceDecay

/-!
# Derivatives of `4 sin²(πs/2) ∫ g(t) e^{−πst} dt` decay rapidly (P4d-5e, generic part)

`4 sin²(πs/2) = 2 − e^{iπs} − e^{−iπs}`, so
`4 sin²(πs/2) ∫ g(t) e^{−πst} dt = 2 C₀(s) − C₋ᵢ(s) − Cᵢ(s)` with
`C_c(s) = ∫₀^∞ g(t) e^{−π(t + c)s} dt` (`c ∈ {0, −i, i}`). Each `C_c` is a Laplace transform with
a purely imaginary shift, so `|e^{−π(t + c)s}| = e^{−πts}`. Its derivative family
`∫ g(t) (−π(t + c))ⁿ e^{−π(t + c)s} dt` satisfies `Cₙ' = Cₙ₊₁`, and each member is bounded by
`π^n ∫ |g(t)| (t + 1)ⁿ e^{−πts} dt`, which decays faster than any power of `s`
(`CKMRVLaplaceDecay`). This avoids the Leibniz rule for the product with `sin²`.
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Asymptotics MeasureTheory Set Metric
open UpperHalfPlane hiding I
open scoped Real ContDiff

/-- The complex-shifted Laplace family `∫ g(t) (−π(t + c))ⁿ e^{−π(t + c)s} dt`. -/
def claplaceFamily (g : ℝ → ℂ) (c : ℂ) (n : ℕ) (s : ℝ) : ℂ :=
  ∫ t in Ioi 0, g t * (-(π : ℂ) * ((t : ℂ) + c)) ^ n * cexp (-(π : ℂ) * ((t : ℂ) + c) * s)

theorem norm_cexp_shift {c : ℂ} (hc : c.re = 0) (t s : ℝ) :
    ‖cexp (-(π : ℂ) * ((t : ℂ) + c) * s)‖ = Real.exp (-(π * s) * t) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.add_re, Complex.ofReal_im,
    Complex.neg_im, Complex.mul_im, Complex.add_im, hc]
  ring_nf

theorem norm_shift_pow_le {c : ℂ} (hc : ‖c‖ ≤ 1) {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    ‖(-(π : ℂ) * ((t : ℂ) + c)) ^ n‖ ≤ (π * (t + 1)) ^ n := by
  rw [norm_pow]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ n
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  refine mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le
  calc ‖(t : ℂ) + c‖ ≤ ‖(t : ℂ)‖ + ‖c‖ := norm_add_le _ _
    _ ≤ t + 1 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]; linarith

/-- The real weight `|g(t)| (π(t + 1))ⁿ`, as a complex function. -/
def weightFn (g : ℝ → ℂ) (n : ℕ) (t : ℝ) : ℂ := ((‖g t‖ * (π * (t + 1)) ^ n : ℝ) : ℂ)

theorem continuousOn_weightFn {g : ℝ → ℂ} (hg : ContinuousOn g (Ioi 0)) (n : ℕ) :
    ContinuousOn (weightFn g n) (Ioi 0) :=
  Complex.continuous_ofReal.comp_continuousOn (hg.norm.mul
    (by fun_prop : Continuous fun t : ℝ => (π * (t + 1)) ^ n).continuousOn)

theorem isBigO_weightFn_zero {g : ℝ → ℂ} {c : ℝ}
    (hg0 : g =O[𝓝[>] (0 : ℝ)] fun t => Real.exp (c / t)) (n : ℕ) :
    weightFn g n =O[𝓝[>] (0 : ℝ)] fun t => Real.exp (c / t) := by
  have hp : (fun t : ℝ => (π * (t + 1)) ^ n) =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) :=
    ((Continuous.tendsto (by fun_prop : Continuous fun t : ℝ => (π * (t + 1)) ^ n) 0)
      |>.mono_left nhdsWithin_le_nhds).isBigO_one ℝ
  rw [← isBigO_norm_left]
  refine ((hg0.norm_left.mul hp).congr_right fun _ => mul_one _).congr' ?_
    (Eventually.of_forall fun _ => rfl)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (0 : ℝ) < t := ht
  rw [weightFn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem isBigO_weightFn_atTop {g : ℝ → ℂ} {a : ℝ}
    (hginf : g =O[atTop] fun t => t * Real.exp (a * t)) (n : ℕ) :
    weightFn g n =O[atTop] fun t => t * Real.exp ((a + 1) * t) := by
  have hp : (fun t : ℝ => (π * (t + 1)) ^ n) =O[atTop] fun t : ℝ => t ^ n := by
    refine IsBigO.of_bound ((2 * π) ^ n) ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity), ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [Real.pi_pos]) n
  rw [← isBigO_norm_left]
  refine ((hginf.norm_left.mul hp).trans ((isBigO_pow_mul_exp_shift (n + 1) (c := a)
    one_pos).congr_left fun t => by ring)).congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [weightFn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

theorem hasDerivAt_claplaceFamily {g : ℝ → ℂ} {a : ℝ} (hg : ContinuousOn g (Ioi 0))
    (hg0 : g =O[𝓝[>] (0 : ℝ)] fun t => Real.exp (-π / t))
    (hginf : g =O[atTop] fun t => t * Real.exp (a * t)) {c : ℂ} (hc : c.re = 0)
    (hc1 : ‖c‖ ≤ 1) (n : ℕ) {s₀ : ℝ} (hs₀ : a + 1 < π * s₀) :
    HasDerivAt (claplaceFamily g c n) (claplaceFamily g c (n + 1) s₀) s₀ := by
  set δ := (π * s₀ - (a + 1)) / (2 * π) with hδ
  have hπ := Real.pi_pos
  have hδ0 : 0 < δ := by rw [hδ]; apply div_pos <;> linarith
  have hb : a + 1 < π * (s₀ - δ) := by
    have : π * δ = (π * s₀ - (a + 1)) / 2 := by rw [hδ]; field_simp
    nlinarith
  have hint : IntegrableOn (fun t => weightFn g (n + 1) t *
      (Real.exp (-(π * (s₀ - δ)) * t) : ℂ)) (Ioi 0) :=
    integrableOn_Ioi_mul_exp_of_isBigO hb (continuousOn_weightFn hg (n + 1))
      ((isBigO_weightFn_zero hg0 (n + 1)).trans (IsBigO.of_bound 1 (by
        filter_upwards [self_mem_nhdsWithin] with t ht
        have ht0 : (0 : ℝ) < t := ht
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one, one_mul]
        exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) ht0.le))))
      (isBigO_weightFn_atTop hginf (n + 1))
  have hcontF : ∀ m : ℕ, ∀ s : ℝ, ContinuousOn (fun t => g t *
      (-(π : ℂ) * ((t : ℂ) + c)) ^ m * cexp (-(π : ℂ) * ((t : ℂ) + c) * s)) (Ioi 0) :=
    fun m s => (hg.mul (by fun_prop : Continuous fun t : ℝ =>
      (-(π : ℂ) * ((t : ℂ) + c)) ^ m).continuousOn).mul
      (by fun_prop : Continuous fun t : ℝ => cexp (-(π : ℂ) * ((t : ℂ) + c) * s)).continuousOn
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (s : ℝ) t => g t * (-(π : ℂ) * ((t : ℂ) + c)) ^ n *
      cexp (-(π : ℂ) * ((t : ℂ) + c) * (s : ℂ)))
    (F' := fun (s : ℝ) t => g t * (-(π : ℂ) * ((t : ℂ) + c)) ^ (n + 1) *
      cexp (-(π : ℂ) * ((t : ℂ) + c) * (s : ℂ)))
    (bound := fun t => ‖weightFn g (n + 1) t * (Real.exp (-(π * (s₀ - δ)) * t) : ℂ)‖)
    (ball_mem_nhds s₀ hδ0) ?_ ?_ ?_ ?_ hint.norm ?_
  · exact key.2
  · exact Eventually.of_forall fun s => (hcontF n s).aestronglyMeasurable measurableSet_Ioi
  · -- integrability at `s₀`: dominated by the weight at the smaller exponent
    refine Integrable.mono' (integrableOn_Ioi_mul_exp_of_isBigO (b := π * s₀) hs₀
      (continuousOn_weightFn hg n) ((isBigO_weightFn_zero hg0 n).trans (IsBigO.of_bound 1 (by
        filter_upwards [self_mem_nhdsWithin] with t ht
        have ht0 : (0 : ℝ) < t := ht
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one, one_mul]
        exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) ht0.le))))
      (isBigO_weightFn_atTop hginf n)).norm ((hcontF n s₀).aestronglyMeasurable measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
    have ht0 : (0 : ℝ) < t := ht
    rw [norm_mul, norm_mul, norm_cexp_shift hc, weightFn, norm_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (norm_shift_pow_le hc1 ht0.le n) (norm_nonneg _)) (Real.exp_pos _).le
  · exact (hcontF (n + 1) s₀).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht s hs => ?_)
    have ht0 : (0 : ℝ) < t := ht
    have hs' : s₀ - δ ≤ s := by
      have := mem_ball.mp hs
      rw [Real.dist_eq] at this
      linarith [neg_abs_le (s - s₀)]
    rw [norm_mul, norm_mul, norm_cexp_shift hc, weightFn, norm_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (by positivity)]
    refine mul_le_mul (mul_le_mul_of_nonneg_left (norm_shift_pow_le hc1 ht0.le (n + 1))
      (norm_nonneg _)) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right hs' ht0.le]
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t _ s _ => ?_)
    have hd : HasDerivAt (fun s : ℝ => cexp (-(π : ℂ) * ((t : ℂ) + c) * s))
        (cexp (-(π : ℂ) * ((t : ℂ) + c) * s) * (-(π : ℂ) * ((t : ℂ) + c))) s := by
      have h1 : HasDerivAt (fun s : ℝ => -(π : ℂ) * ((t : ℂ) + c) * (s : ℂ))
          (-(π : ℂ) * ((t : ℂ) + c) * 1) s :=
        (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul _
      simpa using h1.cexp
    have hd' := hd.const_mul (g t * (-(π : ℂ) * ((t : ℂ) + c)) ^ n)
    refine hd'.congr_deriv ?_
    ring

theorem exists_bound_claplaceFamily_decay {g : ℝ → ℂ} {a : ℝ} (hg : ContinuousOn g (Ioi 0))
    (hg0 : g =O[𝓝[>] (0 : ℝ)] fun t => Real.exp (-π / t))
    (hginf : g =O[atTop] fun t => t * Real.exp (a * t)) {c : ℂ} (hc : c.re = 0)
    (hc1 : ‖c‖ ≤ 1) (n k : ℕ) :
    ∃ C S₀ : ℝ, ∀ s : ℝ, S₀ ≤ s → s ^ k * ‖claplaceFamily g c n s‖ ≤ C := by
  obtain ⟨C, S₀, hC⟩ := exists_bound_laplace_decay (continuousOn_weightFn hg n)
    (isBigO_weightFn_zero hg0 n) (isBigO_weightFn_atTop hginf n) k
  refine ⟨C, max S₀ ((|a| + 2) / π), fun s hs => ?_⟩
  have hs0 : S₀ ≤ s := le_trans (le_max_left _ _) hs
  have hπ := Real.pi_pos
  have hsa : (|a| + 2) / π ≤ s := le_trans (le_max_right _ _) hs
  have hspos : 0 ≤ s := le_trans (div_nonneg (by positivity) hπ.le) hsa
  have hb : a + 1 < π * s := by
    have := (div_le_iff₀ hπ).mp hsa
    linarith [le_abs_self a]
  have hint : IntegrableOn (fun t => weightFn g n t * (Real.exp (-(π * s) * t) : ℂ)) (Ioi 0) :=
    integrableOn_Ioi_mul_exp_of_isBigO hb (continuousOn_weightFn hg n)
      ((isBigO_weightFn_zero hg0 n).trans (IsBigO.of_bound 1 (by
        filter_upwards [self_mem_nhdsWithin] with t ht
        have ht0 : (0 : ℝ) < t := ht
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one, one_mul]
        exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith) ht0.le))))
      (isBigO_weightFn_atTop hginf n)
  have hle : ‖claplaceFamily g c n s‖ ≤
      ‖∫ t in Ioi 0, weightFn g n t * (Real.exp (-(π * s) * t) : ℂ)‖ := by
    have hreal : ∫ t in Ioi 0, weightFn g n t * (Real.exp (-(π * s) * t) : ℂ) =
        ((∫ t in Ioi 0, ‖g t‖ * (π * (t + 1)) ^ n * Real.exp (-(π * s) * t) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      simp [weightFn]
    rw [hreal, Complex.norm_real, Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans (le_trans ?_ (le_abs_self _))
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioi fun t ht => ?_
    · exact Integrable.mono' hint.norm ((((hg.mul (by fun_prop : Continuous fun t : ℝ =>
        (-(π : ℂ) * ((t : ℂ) + c)) ^ n).continuousOn).mul (by fun_prop : Continuous fun t : ℝ =>
          cexp (-(π : ℂ) * ((t : ℂ) + c) * s)).continuousOn).norm).aestronglyMeasurable
          measurableSet_Ioi) ((ae_restrict_iff' measurableSet_Ioi).mpr
          (Eventually.of_forall fun t ht => by
            have ht0 : (0 : ℝ) < t := ht
            rw [norm_norm, norm_mul, norm_mul, norm_cexp_shift hc, weightFn, norm_mul,
              Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_pos (Real.exp_pos _), abs_of_nonneg (by positivity)]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
              (norm_shift_pow_le hc1 ht0.le n) (norm_nonneg _)) (Real.exp_pos _).le))
    · refine IntegrableOn.congr_fun hint.norm (fun t ht => ?_) measurableSet_Ioi
      have ht0 : (0 : ℝ) < t := ht
      rw [weightFn, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_nonneg (by positivity)]
    · have ht0 : (0 : ℝ) < t := ht
      rw [norm_mul, norm_mul, norm_cexp_shift hc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (norm_shift_pow_le hc1 ht0.le n) (norm_nonneg _)) (Real.exp_pos _).le
  exact (mul_le_mul_of_nonneg_left hle (pow_nonneg hspos k)).trans (hC s hs0)

end E8Leech
