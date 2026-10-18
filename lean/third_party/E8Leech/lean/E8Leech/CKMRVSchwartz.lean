import E8Leech.CKMRVLaplaceAxisFull
import Riesz.RadialSchwartz
import SpherePacking.ForMathlib.IteratedDeriv

/-!
# The CKMRV kernel transforms on the imaginary axis are Schwartz (P4d-5g)

For `τ = iβ` (`β > 0`, `β ≠ 1`) and each of the four kernels `K = K₋⁽⁸⁾, K₊⁽⁸⁾, K₋⁽²⁴⁾, K₊⁽²⁴⁾`
the radial function `x ↦ 4 sin²(π|x|²/2) ∫₀^∞ K(iβ, it) e^{−π|x|²t} dt` (for `|x|² > 0`, resp.
`|x|² > 2` for Leech), continued to small `|x|` by (5.3)/(5.4), is a Schwartz function on every
real inner product space (in particular `ℝ⁸`, `ℝ²⁴`).

Assembly (Sphere-Packing-Lean `RadialSchwartz`): a profile `f` in the variable `s = |x|²` that is
`C^∞` on `s > −1` and whose derivatives decay rapidly on `s ≥ 0` gives `x ↦ f(|x|²)` Schwartz.
* Smoothness: the `sinc` form of the profile (`CKMRVRadialProfile`) on the axis
  (`CKMRVLaplaceAxisFull`). The `RadialSchwartz` cutoff vanishes on `s ≤ −1/2`, so smoothness on
  `s > a` for some `a < −1/2` suffices (Leech plus: `s > −3/4`).
* Decay: for large `s`, `f = 2C₀ − C₋ᵢ − Cᵢ` (`CKMRVSchwartzProfile`), whose derivative families
  decay; on `[0, S]` the derivatives are bounded by compactness.
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Asymptotics MeasureTheory Set
open UpperHalfPlane hiding I
open scoped Real ContDiff

/-! ## Generic assembly -/

/-- Rapid decay of `iteratedDeriv` for large `s` plus smoothness on `s > −1` give the one-sided
Schwartz bounds required by `RadialSchwartz`. -/
theorem schwartz_bounds_of_decay {f : ℝ → ℂ} {a : ℝ} (ha : a < 0) (hf : ContDiffOn ℝ ∞ f (Ioi a))
    (hdecay : ∀ n k : ℕ, ∃ C S₀ : ℝ, ∀ x : ℝ, S₀ ≤ x → x ^ k * ‖iteratedDeriv n f x‖ ≤ C) :
    ∀ k n : ℕ, ∃ C, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  intro k n
  obtain ⟨C, S₀, hC⟩ := hdecay n k
  set S := max S₀ 0
  have hcont : ContinuousOn (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) (Icc 0 S) := by
    have h1 : ContinuousOn (iteratedFDeriv ℝ n f) (Ioi a) := by
      have h := hf.continuousOn_iteratedFDerivWithin (m := n) (by exact_mod_cast le_top)
        (isOpen_Ioi.uniqueDiffOn)
      exact h.congr fun x hx => (iteratedFDerivWithin_of_isOpen n isOpen_Ioi hx).symm
    exact (continuous_norm.pow k).continuousOn.mul
      ((h1.mono fun x hx => lt_of_lt_of_le ha hx.1).norm)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max M C, fun x hx => ?_⟩
  by_cases hxS : x ≤ S
  · have h := hM x ⟨hx, hxS⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
    exact h.trans (le_max_left _ _)
  · have hx0 : S₀ ≤ x := le_trans (le_max_left _ _) (le_of_lt (not_le.mp hxS))
    rw [Real.norm_eq_abs, abs_of_nonneg hx, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact (hC x hx0).trans (le_max_right _ _)

/-- The `RadialSchwartz` cutoff vanishes on `r ≤ −1/2`, so smoothness on `Ioi a` with `a < −1/2`
suffices (`RadialSchwartz.contDiff_cutoffC_mul_of_contDiffOn_Ioi_neg1` is the case `a = −1`). -/
theorem contDiff_cutoffC_mul_of_contDiffOn_Ioi {f : ℝ → ℂ} {a : ℝ} (ha : a < -1 / 2)
    (hf : ContDiffOn ℝ ∞ f (Ioi a)) :
    ContDiff ℝ ∞ (fun r => RadialSchwartz.cutoffC r * f r) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x < (-1 / 2 : ℝ)
  · refine (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ => (0 : ℂ)) x).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    simp [RadialSchwartz.cutoffC_eq_zero_of_le_neg_half (r := y) (le_of_lt hy)]
  · have hx' : a < x := by linarith [le_of_not_gt hx]
    exact (RadialSchwartz.cutoffC_contDiff.contDiffAt (x := x)).mul
      (hf.contDiffAt (isOpen_Ioi.mem_nhds hx'))

/-- `2 − e^{iπs} − e^{−iπs} = 4 sin²(πs/2)`. -/
theorem two_sub_cexp_sub_cexp (s : ℝ) :
    (2 : ℂ) - cexp (((π * s : ℝ) : ℂ) * I) - cexp (-((π * s : ℝ) : ℂ) * I) =
      ((4 * Real.sin (π * s / 2) ^ 2 : ℝ) : ℂ) := by
  have h := Complex.two_cos ((π * s : ℝ) : ℂ)
  have hc : Real.cos (π * s) = 1 - 2 * Real.sin (π * s / 2) ^ 2 := by
    have h2 := Real.cos_two_mul (π * s / 2)
    have h3 := Real.sin_sq_add_cos_sq (π * s / 2)
    rw [show 2 * (π * s / 2) = π * s by ring] at h2
    linarith
  rw [← Complex.ofReal_cos] at h
  rw [sub_sub, ← h, hc]
  push_cast
  ring

/-- The `sin²`-weighted transform as a combination of shifted transforms. -/
theorem four_sin_sq_mul_integral_eq (g : ℝ → ℂ) (s : ℝ) :
    ((4 * Real.sin (π * s / 2) ^ 2 : ℝ) : ℂ) *
        ∫ t in Ioi 0, g t * (Real.exp (-(π * s) * t) : ℂ) =
      2 * claplaceFamily g 0 0 s - claplaceFamily g (-I) 0 s - claplaceFamily g I 0 s := by
  have hc : ∀ c : ℂ, claplaceFamily g c 0 s =
      cexp (-(π : ℂ) * c * s) * ∫ t in Ioi 0, g t * (Real.exp (-(π * s) * t) : ℂ) := by
    intro c
    rw [claplaceFamily, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [pow_zero, mul_one, Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hc, hc, hc, ← two_sub_cexp_sub_cexp]
  have e1 : cexp (-(π : ℂ) * 0 * s) = 1 := by simp
  have e2 : cexp (-(π : ℂ) * -I * s) = cexp (((π * s : ℝ) : ℂ) * I) := by
    congr 1; push_cast; ring
  have e3 : cexp (-(π : ℂ) * I * s) = cexp (-((π * s : ℝ) : ℂ) * I) := by
    congr 1; push_cast; ring
  rw [e1, e2, e3]
  ring

/-- The shifted combination `H n = 2 C₀ⁿ − C₋ᵢⁿ − Cᵢⁿ`. -/
def shiftedCombo (g : ℝ → ℂ) (n : ℕ) (s : ℝ) : ℂ :=
  2 * claplaceFamily g 0 n s - claplaceFamily g (-I) n s - claplaceFamily g I n s

theorem hasDerivAt_shiftedCombo {g : ℝ → ℂ} {a : ℝ} (hg : ContinuousOn g (Ioi 0))
    (hg0 : g =O[𝓝[>] (0 : ℝ)] fun t => Real.exp (-π / t))
    (hginf : g =O[atTop] fun t => t * Real.exp (a * t)) (n : ℕ) {s₀ : ℝ}
    (hs₀ : a + 1 < π * s₀) :
    HasDerivAt (shiftedCombo g n) (shiftedCombo g (n + 1) s₀) s₀ := by
  have h0 := hasDerivAt_claplaceFamily hg hg0 hginf (c := 0) (by simp) (by simp) n hs₀
  have h1 := hasDerivAt_claplaceFamily hg hg0 hginf (c := -I) (by simp) (by simp) n hs₀
  have h2 := hasDerivAt_claplaceFamily hg hg0 hginf (c := I) (by simp) (by simp) n hs₀
  exact ((h0.const_mul 2).sub h1).sub h2

theorem exists_bound_shiftedCombo {g : ℝ → ℂ} {a : ℝ} (hg : ContinuousOn g (Ioi 0))
    (hg0 : g =O[𝓝[>] (0 : ℝ)] fun t => Real.exp (-π / t))
    (hginf : g =O[atTop] fun t => t * Real.exp (a * t)) (n k : ℕ) :
    ∃ C S₀ : ℝ, ∀ s : ℝ, S₀ ≤ s → s ^ k * ‖shiftedCombo g n s‖ ≤ C := by
  obtain ⟨C₀, S₀, h0⟩ := exists_bound_claplaceFamily_decay hg hg0 hginf (c := 0) (by simp)
    (by simp) n k
  obtain ⟨C₁, S₁, h1⟩ := exists_bound_claplaceFamily_decay hg hg0 hginf (c := -I) (by simp)
    (by simp) n k
  obtain ⟨C₂, S₂, h2⟩ := exists_bound_claplaceFamily_decay hg hg0 hginf (c := I) (by simp)
    (by simp) n k
  refine ⟨2 * C₀ + C₁ + C₂, max (max S₀ S₁) (max S₂ 0), fun s hs => ?_⟩
  have hs0 : S₀ ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
  have hs1 : S₁ ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs
  have hs2 : S₂ ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hspos : 0 ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hs
  have hk := pow_nonneg hspos k
  have hn2 : ‖2 * claplaceFamily g 0 n s‖ = 2 * ‖claplaceFamily g 0 n s‖ := by
    rw [norm_mul]
    norm_num
  have hsum : ‖shiftedCombo g n s‖ ≤ 2 * ‖claplaceFamily g 0 n s‖ +
      ‖claplaceFamily g (-I) n s‖ + ‖claplaceFamily g I n s‖ := by
    rw [shiftedCombo, ← hn2]
    calc ‖2 * claplaceFamily g 0 n s - claplaceFamily g (-I) n s - claplaceFamily g I n s‖
        ≤ ‖2 * claplaceFamily g 0 n s - claplaceFamily g (-I) n s‖ +
            ‖claplaceFamily g I n s‖ := norm_sub_le _ _
      _ ≤ ‖2 * claplaceFamily g 0 n s‖ + ‖claplaceFamily g (-I) n s‖ +
            ‖claplaceFamily g I n s‖ := by
          gcongr
          exact norm_sub_le _ _
  calc s ^ k * ‖shiftedCombo g n s‖
      ≤ s ^ k * (2 * ‖claplaceFamily g 0 n s‖ + ‖claplaceFamily g (-I) n s‖ +
          ‖claplaceFamily g I n s‖) := mul_le_mul_of_nonneg_left hsum hk
    _ = 2 * (s ^ k * ‖claplaceFamily g 0 n s‖) + s ^ k * ‖claplaceFamily g (-I) n s‖ +
          s ^ k * ‖claplaceFamily g I n s‖ := by ring
    _ ≤ 2 * C₀ + C₁ + C₂ := by
        gcongr
        exacts [h0 s hs0, h1 s hs1, h2 s hs2]

/-- A profile which equals `4 sin²(πs/2) ∫ g e^{−πst}` for large `s` has rapidly decaying
derivatives. -/
theorem decay_of_eventually_eq_sin_sq {f g : ℝ → ℂ} {a S₁ : ℝ} (hg : ContinuousOn g (Ioi 0))
    (hg0 : g =O[𝓝[>] (0 : ℝ)] fun t => Real.exp (-π / t))
    (hginf : g =O[atTop] fun t => t * Real.exp (a * t))
    (heq : ∀ s : ℝ, S₁ < s → f s = ((4 * Real.sin (π * s / 2) ^ 2 : ℝ) : ℂ) *
      ∫ t in Ioi 0, g t * (Real.exp (-(π * s) * t) : ℂ)) :
    ∀ n k : ℕ, ∃ C S₀ : ℝ, ∀ x : ℝ, S₀ ≤ x → x ^ k * ‖iteratedDeriv n f x‖ ≤ C := by
  intro n k
  set S₂ := max S₁ ((|a| + 2) / π) with hS₂
  have hπ := Real.pi_pos
  have hS₂a : ∀ s : ℝ, S₂ < s → a + 1 < π * s := fun s hs => by
    have h1 : (|a| + 2) / π < s := lt_of_le_of_lt (le_max_right _ _) hs
    have := (div_lt_iff₀ hπ).mp h1
    linarith [le_abs_self a]
  have hderiv : ∀ m : ℕ, ∀ x ∈ Ioi S₂, deriv (shiftedCombo g m) x = shiftedCombo g (m + 1) x :=
    fun m x hx => (hasDerivAt_shiftedCombo hg hg0 hginf m (hS₂a x hx)).deriv
  have hEqOn := SpherePacking.ForMathlib.eqOn_iteratedDeriv_eq_of_deriv_eq isOpen_Ioi
    (shiftedCombo g) hderiv n 0
  obtain ⟨C, S₀, hC⟩ := exists_bound_shiftedCombo hg hg0 hginf n k
  refine ⟨C, max S₀ (S₂ + 1), fun x hx => ?_⟩
  have hxS₂ : S₂ < x := lt_of_lt_of_le (lt_add_one S₂) (le_trans (le_max_right _ _) hx)
  have hfeq : f =ᶠ[𝓝 x] shiftedCombo g 0 := by
    filter_upwards [Ioi_mem_nhds hxS₂] with s hs
    rw [heq s (lt_of_le_of_lt (le_max_left _ _) hs), four_sin_sq_mul_integral_eq]
    rfl
  rw [hfeq.iteratedDeriv_eq n, hEqOn hxS₂, add_zero]
  exact hC x (le_trans (le_max_left _ _) hx)

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Generic assembly.** A kernel `g` on the axis with the (5.3)/(5.4) split by a cusp profile,
`e^{−π/t}` decay at `0`, growth `t e^{at}` at `∞`, and subtracted transform `C^∞` on `b > a'`
(`a' < −π/2`) gives a Schwartz function equal to `4 sin²(π|x|²/2) ∫ g e^{−π|x|²t}` for
`|x|² > S₁`. -/
theorem exists_schwartz_of_cusp_split {g : ℝ → ℂ} {A B C D : ℂ} {a c a' S₁ : ℝ}
    (hg : ContinuousOn g (Ioi 0))
    (hg0 : g =O[𝓝[>] (0 : ℝ)] fun t => Real.exp (-π / t))
    (hginf : g =O[atTop] fun t => t * Real.exp (a * t)) (ha' : a' < -(π / 2))
    (hsmooth : ContDiffOn ℝ ∞ (fun b => ∫ t in Ioi 0, (g t - cuspProfile A B C D c t) *
      (Real.exp (-b * t) : ℂ)) (Ioi a'))
    (hc : Real.sin (c / 2) = 0) (hS₁ : 0 ≤ S₁) (hcS : c ≤ π * S₁)
    (hsplit : ∀ b : ℝ, π * S₁ < b → ∫ t in Ioi 0, g t * (Real.exp (-b * t) : ℂ) =
      (∫ t in Ioi 0, (g t - cuspProfile A B C D c t) * (Real.exp (-b * t) : ℂ)) +
        cuspProfileLaplace A B C D c b) :
    ∃ φ : SchwartzMap F ℂ, ∀ x : F, S₁ < ‖x‖ ^ 2 →
      φ x = ((4 * Real.sin (π * ‖x‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
        ∫ t in Ioi 0, g t * (Real.exp (-(π * ‖x‖ ^ 2) * t) : ℂ) := by
  have hπ := Real.pi_pos
  set prof : ℝ → ℂ := fun s => radialProfile (fun t => g t - cuspProfile A B C D c t) A B C D c
    (π * s) with hprof
  have hsmooth' : ContDiffOn ℝ ∞ prof (Ioi (a' / π)) := by
    refine (contDiffOn_radialProfile hsmooth).comp (contDiff_const.mul contDiff_id).contDiffOn
      fun s hs => ?_
    show a' < π * s
    have h : a' / π < s := hs
    rw [div_lt_iff₀ hπ] at h
    linarith
  have ha'' : a' / π < -1 / 2 := by
    rw [div_lt_iff₀ hπ]
    linarith
  have heq : ∀ s : ℝ, S₁ < s → prof s = ((4 * Real.sin (π * s / 2) ^ 2 : ℝ) : ℂ) *
      ∫ t in Ioi 0, g t * (Real.exp (-(π * s) * t) : ℂ) := by
    intro s hs
    have hb : π * S₁ < π * s := mul_lt_mul_of_pos_left hs hπ
    have hb0 : 0 < π * s := lt_of_le_of_lt (mul_nonneg hπ.le hS₁) hb
    have hbc : 0 < π * s - c := by linarith
    exact radialProfile_eq (hsplit _ hb) hc hb0.ne' hbc.ne'
  have hdecay := decay_of_eventually_eq_sin_sq hg hg0 hginf heq
  refine ⟨RadialSchwartz.Bridge.schwartzMap_norm_sq_of_cutoffMul_contDiff_decay_nonneg (F := F)
    prof (contDiff_cutoffC_mul_of_contDiffOn_Ioi ha'' hsmooth')
    (schwartz_bounds_of_decay (by linarith) hsmooth' hdecay), fun x hx => ?_⟩
  rw [RadialSchwartz.Bridge.schwartzMap_norm_sq_of_cutoffMul_contDiff_decay_nonneg_apply,
    heq _ hx]

/-! ## The four kernels on the axis -/

/-- **The `d = 8` minus-kernel transform on the imaginary axis is Schwartz.** For `β ≠ 1` there is
a Schwartz function `φ` with `φ(x) = 4 sin²(π|x|²/2) ∫₀^∞ K₋(iβ, it) e^{−π|x|²t} dt` for
`x ≠ 0` (and the (5.3) continuation at `x = 0`). -/
theorem exists_schwartz_ckmrvEightMinus_axis {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1) :
    ∃ φ : SchwartzMap F ℂ, ∀ x : F, x ≠ 0 →
      φ x = ((4 * Real.sin (π * ‖x‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
        ∫ t in Ioi 0, ckmrvEightMinusKernel (imagPt β) (imagPt t) *
          (Real.exp (-(π * ‖x‖ ^ 2) * t) : ℂ) := by
  obtain ⟨g, hg, hgK⟩ := exists_ckmrvEightMinus_axis hβ hβ1
  obtain ⟨φ, hφ⟩ := exists_schwartz_of_cusp_split F hg (isBigO_eightMinusAxis_zero hβ hgK)
    (isBigO_eightMinusAxis_atTop hgK) (by linarith [Real.pi_pos] : -π < -(π / 2))
    (contDiffOn_eightMinusAxis_sub_G_laplace hβ hg hgK) (by simp) le_rfl (by simp)
    (fun b hb => by
      rw [setIntegral_eq_of_eq_off_two (w := fun t => (Real.exp (-b * t) : ℂ)) hgK]
      exact integral_ckmrvEightMinusKernel_axis_eq hβ hg hgK (by simpa using hb))
  exact ⟨φ, fun x hx => by rw [hφ x (by positivity), setIntegral_eq_of_eq_off_two hgK]⟩

/-- **The `d = 8` plus-kernel transform on the imaginary axis is Schwartz.** -/
theorem exists_schwartz_ckmrvEightPlus_axis {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1) :
    ∃ φ : SchwartzMap F ℂ, ∀ x : F, x ≠ 0 →
      φ x = ((4 * Real.sin (π * ‖x‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
        ∫ t in Ioi 0, ckmrvEightPlusKernel (imagPt β) (imagPt t) *
          (Real.exp (-(π * ‖x‖ ^ 2) * t) : ℂ) := by
  obtain ⟨g, hg, hgK⟩ := exists_ckmrvEightPlus_axis hβ hβ1
  obtain ⟨φ, hφ⟩ := exists_schwartz_of_cusp_split F hg (isBigO_eightPlusAxis_zero hβ hgK)
    (isBigO_eightPlusAxis_atTop hgK) (by linarith [Real.pi_pos] : -π < -(π / 2))
    (contDiffOn_eightPlusAxis_sub_G_laplace hβ hg hgK) (by simp) le_rfl (by simp)
    (fun b hb => by
      rw [setIntegral_eq_of_eq_off_two (w := fun t => (Real.exp (-b * t) : ℂ)) hgK]
      exact integral_ckmrvEightPlusKernel_axis_eq hβ hg hgK (by simpa using hb))
  exact ⟨φ, fun x hx => by rw [hφ x (by positivity), setIntegral_eq_of_eq_off_two hgK]⟩

/-- **The `d = 24` minus-kernel transform on the imaginary axis is Schwartz** (equal to the
(5.1) transform for `|x|² > 2`). -/
theorem exists_schwartz_ckmrvLeechMinus_axis {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1) :
    ∃ φ : SchwartzMap F ℂ, ∀ x : F, 2 < ‖x‖ ^ 2 →
      φ x = ((4 * Real.sin (π * ‖x‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
        ∫ t in Ioi 0, ckmrvLeechMinusKernel (imagPt β) (imagPt t) *
          (Real.exp (-(π * ‖x‖ ^ 2) * t) : ℂ) := by
  obtain ⟨g, hg, hgK⟩ := exists_ckmrvLeechMinus_axis hβ hβ1
  obtain ⟨φ, hφ⟩ := exists_schwartz_of_cusp_split F hg (isBigO_leechMinusAxis_zero hβ hgK)
    (isBigO_leechMinusAxis_atTop hgK) (by linarith [Real.pi_pos] : -π < -(π / 2))
    (contDiffOn_leechMinusAxis_sub_G_laplace hβ hg hgK) sin_two_pi_div_two zero_le_two
    (by linarith [Real.pi_pos] : 2 * π ≤ π * 2)
    (fun b hb => by
      rw [setIntegral_eq_of_eq_off_two (w := fun t => (Real.exp (-b * t) : ℂ)) hgK]
      exact integral_ckmrvLeechMinusKernel_axis_eq hβ hg hgK (by linarith))
  exact ⟨φ, fun x hx => by rw [hφ x hx, setIntegral_eq_of_eq_off_two hgK]⟩

/-- **The `d = 24` plus-kernel transform on the imaginary axis is Schwartz** (equal to the
(5.1) transform for `|x|² > 2`). -/
theorem exists_schwartz_ckmrvLeechPlus_axis {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1) :
    ∃ φ : SchwartzMap F ℂ, ∀ x : F, 2 < ‖x‖ ^ 2 →
      φ x = ((4 * Real.sin (π * ‖x‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
        ∫ t in Ioi 0, ckmrvLeechPlusKernel (imagPt β) (imagPt t) *
          (Real.exp (-(π * ‖x‖ ^ 2) * t) : ℂ) := by
  obtain ⟨g, hg, hgK⟩ := exists_ckmrvLeechPlus_axis hβ hβ1
  obtain ⟨φ, hφ⟩ := exists_schwartz_of_cusp_split F hg (isBigO_leechPlusAxis_zero hβ hgK)
    (isBigO_leechPlusAxis_atTop hgK) (by linarith [Real.pi_pos] : -π + π / 4 < -(π / 2))
    (contDiffOn_leechPlusAxis_sub_G_laplace hβ hg hgK) sin_two_pi_div_two zero_le_two
    (by linarith [Real.pi_pos] : 2 * π ≤ π * 2)
    (fun b hb => by
      rw [setIntegral_eq_of_eq_off_two (w := fun t => (Real.exp (-b * t) : ℂ)) hgK]
      exact integral_ckmrvLeechPlusKernel_axis_eq hβ hg hgK (by linarith))
  exact ⟨φ, fun x hx => by rw [hφ x hx, setIntegral_eq_of_eq_off_two hgK]⟩

end E8Leech
