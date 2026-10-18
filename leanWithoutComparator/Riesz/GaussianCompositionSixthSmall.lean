import Riesz.GaussianCompositionSixth

/-! Sixth derivative of a Gaussian composition for small `τ` (stage NEG, τ-linear patch defect).

For `0 ≤ τ ≤ 1` the sixth derivative of `exp(-τ‖F‖²)` carries a factor `√τ`:
`‖D⁶ exp(-τ‖F‖²)(x)‖ ≤ 720·1568·(64 L²)⁶ √τ e^(-τ r²/2)`, `r = ‖F x‖`. The Faà di Bruno bound is
applied with `D = τ^(1/12) M (1 + √τ r)`, `M = 64 L²`: every derivative of `-τ‖F‖²` is at most
`τ·64(rL + L²) ≤ M √τ (1 + √τ r) ≤ D^i` (`i ≤ 6`), and `(1+u)⁶ e^(-u²) ≤ 1568 e^(-u²/2)`.
Since the patch Gaussian defect is quadratic in the bump quadrature error, this gives a defect
linear in `τ` at macroscopic scales, which is what the negative-exponent macroscopic end needs. -/

set_option autoImplicit false
noncomputable section
open Set
namespace SphericalRiesz

theorem one_add_pow_six_mul_exp_le {u : ℝ} (hu : 0 ≤ u) :
    (1+u)^6*Real.exp (-(u^2)) ≤ 1568*Real.exp (-(u^2/2)) := by
  have h1 : (1+u)^6 ≤ 32*(1+u^6) := by
    nlinarith [sq_nonneg (u-1), sq_nonneg (u^2-1), sq_nonneg (u^3-1), mul_nonneg hu (sq_nonneg (u-1)),
      pow_nonneg hu 3, pow_nonneg hu 4, pow_nonneg hu 5, mul_nonneg (pow_nonneg hu 2) (sq_nonneg (u-1)),
      mul_nonneg (pow_nonneg hu 3) (sq_nonneg (u-1)), mul_nonneg (pow_nonneg hu 4) (sq_nonneg (u-1))]
  have h2 : (u^2)^3*Real.exp (-(u^2)) ≤ 48*Real.exp (-(u^2/2)) := cube_mul_exp_neg_le (sq_nonneg u)
  have he : Real.exp (-(u^2)) ≤ Real.exp (-(u^2/2)) := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg u])
  have hE := Real.exp_pos (-(u^2))
  have hu6 : u^6 = (u^2)^3 := by ring
  calc (1+u)^6*Real.exp (-(u^2)) ≤ 32*(1+u^6)*Real.exp (-(u^2)) :=
        mul_le_mul_of_nonneg_right h1 hE.le
    _ = 32*(Real.exp (-(u^2))+(u^2)^3*Real.exp (-(u^2))) := by rw [hu6]; ring
    _ ≤ 32*(Real.exp (-(u^2/2))+48*Real.exp (-(u^2/2))) := by linarith
    _ = 1568*Real.exp (-(u^2/2)) := by ring

section
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Sixth derivative of `exp(-τ‖F‖²)` with a factor `√τ`, for `0 ≤ τ ≤ 1`. -/
theorem norm_iteratedFDeriv_six_exp_neg_mul_norm_sq_le_sqrt {F : E → H} {x : E}
    (hF : ContDiffAt ℝ 6 F x) {L : ℝ} (hL : 1 ≤ L)
    (hFL : ∀ j, 1 ≤ j → j ≤ 6 → ‖iteratedFDeriv ℝ j F x‖ ≤ L) {τ : ℝ} (hτ : 0 ≤ τ)
    (hτ1 : τ ≤ 1) :
    ‖iteratedFDeriv ℝ 6 (fun y => Real.exp (-(τ*‖F y‖^2))) x‖ ≤
      (720*1568*(64*L^2)^6)*Real.sqrt τ*Real.exp (-(τ*‖F x‖^2/2)) := by
  obtain ⟨U, hU, hxU, hFU⟩ := hF.contDiffOn' le_rfl (by simp)
  have hFU' : ContDiffOn ℝ 6 F U := by simpa using hFU
  set r := ‖F x‖ with hrdef
  have hr : 0 ≤ r := norm_nonneg _
  set f : E → ℝ := fun y => -(τ*‖F y‖^2) with hfdef
  have hf : ContDiffOn ℝ 6 f U := ((hFU'.norm_sq ℝ).const_smul τ).neg
  have hwithin : ∀ j, iteratedFDerivWithin ℝ j F U x = iteratedFDeriv ℝ j F x :=
    fun j => iteratedFDerivWithin_of_isOpen j hU hxU
  set a : ℕ → ℝ := fun i => ‖iteratedFDerivWithin ℝ i F U x‖ with hadef
  have ha : ∀ i, 0 ≤ a i := fun i => norm_nonneg _
  have ha0 : a 0 = r := by simp [hadef, hrdef]
  have haL : ∀ i, 1 ≤ i → i ≤ 6 → a i ≤ L := by
    intro i h1 h6
    simp only [hadef, hwithin]
    exact hFL i h1 h6
  have hL0 : 0 ≤ L := by linarith
  set M := 64*L^2 with hMdef
  have hM1 : 1 ≤ M := by nlinarith
  set s := Real.sqrt τ with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg τ
  have hs2 : s^2 = τ := Real.sq_sqrt hτ
  have hs1 : s ≤ 1 := by rw [hsdef]; exact Real.sqrt_le_one.mpr hτ1
  have hτs : τ ≤ s := by nlinarith
  set u := s*r with hudef
  have hu : 0 ≤ u := mul_nonneg hs0 hr
  set q := τ^((1:ℝ)/12) with hqdef
  have hq0 : 0 ≤ q := Real.rpow_nonneg hτ _
  set D := q*M*(1+u) with hDdef
  have hD0 : 0 ≤ D := by positivity
  -- each derivative of `f` is at most `M s (1+u) ≤ D^i`
  have hfi : ∀ i, 1 ≤ i → i ≤ 6 → ‖iteratedFDerivWithin ℝ i f U x‖ ≤ M*s*(1+u) := by
    intro i h1 h6
    have hl := norm_iteratedFDerivWithin_neg_mul_norm_sq_le hU hxU hFU' hτ h6
    have hsum : ∑ j ∈ Finset.range (i+1), (i.choose j : ℝ)*a j*a (i-j) ≤ 2^i*(r*L+L^2) := by
      rcases Nat.lt_or_ge i 2 with hi | hi
      · have hi1 : i = 1 := by omega
        subst hi1
        rw [leibniz_sum_one a, ha0]
        have := haL 1 le_rfl (by norm_num)
        nlinarith [mul_nonneg hL0 hL0, mul_nonneg hr hL0]
      · exact leibniz_sum_le i h1 a ha ha0 (fun j hj hji => haL j hj (hji.trans h6))
    have h2i : (2:ℝ)^i ≤ 64 := by
      calc (2:ℝ)^i ≤ 2^6 := pow_le_pow_right₀ (by norm_num) h6
        _ = 64 := by norm_num
    have hrL : r*L+L^2 ≤ L^2*(1+r) := by
      nlinarith [mul_nonneg (mul_nonneg hr hL0) (sub_nonneg.mpr hL)]
    have hτr : τ*(1+r) ≤ s*(1+u) := by
      rw [hudef, ← hs2]
      nlinarith [mul_nonneg hs0 hr, mul_nonneg (mul_nonneg hs0 hs0) hr]
    calc ‖iteratedFDerivWithin ℝ i f U x‖ ≤ τ*(2^i*(r*L+L^2)) :=
          hl.trans (mul_le_mul_of_nonneg_left hsum hτ)
      _ ≤ τ*(64*(L^2*(1+r))) := by
          apply mul_le_mul_of_nonneg_left _ hτ
          exact mul_le_mul h2i hrL (by positivity) (by norm_num)
      _ = M*(τ*(1+r)) := by rw [hMdef]; ring
      _ ≤ M*(s*(1+u)) := mul_le_mul_of_nonneg_left hτr (by positivity)
      _ = M*s*(1+u) := by ring
  have hDbound : ∀ i, 1 ≤ i → i ≤ 6 → ‖iteratedFDerivWithin ℝ i f U x‖ ≤ D^i := by
    intro i h1 h6
    refine (hfi i h1 h6).trans ?_
    have hqi : s ≤ q^i := by
      rcases hτ.eq_or_lt with h0 | hpos
      · rw [hsdef, ← h0, Real.sqrt_zero]
        exact pow_nonneg hq0 i
      · rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hτ, hsdef, Real.sqrt_eq_rpow]
        apply Real.rpow_le_rpow_of_exponent_ge hpos hτ1
        have : (i:ℝ) ≤ 6 := by exact_mod_cast h6
        linarith
    have hMi : M ≤ M^i := le_self_pow₀ hM1 (by omega)
    have hui : 1+u ≤ (1+u)^i := le_self_pow₀ (by linarith) (by omega)
    calc M*s*(1+u) = s*M*(1+u) := by ring
      _ ≤ q^i*M^i*(1+u)^i := by
          apply mul_le_mul (mul_le_mul hqi hMi (by linarith) (by positivity)) hui (by linarith)
            (by positivity)
      _ = D^i := by rw [hDdef, mul_pow (q*M) (1+u) i, mul_pow q M i]
  have hC : ∀ i, i ≤ 6 → ‖iteratedFDerivWithin ℝ i Real.exp univ (f x)‖ ≤ Real.exp (f x) := by
    intro i _
    rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hcomp := norm_iteratedFDerivWithin_comp_le (g := Real.exp) (f := f) (s := U) (t := univ)
    (n := 6) (N := 6) Real.contDiff_exp.contDiffOn hf le_rfl uniqueDiffOn_univ hU.uniqueDiffOn
    (mapsTo_univ _ _) hxU hC hDbound
  have hlhs : iteratedFDerivWithin ℝ 6 (Real.exp ∘ f) U x =
      iteratedFDeriv ℝ 6 (fun y => Real.exp (-(τ*‖F y‖^2))) x :=
    iteratedFDerivWithin_of_isOpen 6 hU hxU
  rw [hlhs] at hcomp
  refine hcomp.trans ?_
  have hfx : f x = -(τ*r^2) := by simp [hfdef, hrdef]
  rw [hfx]
  have h720 : ((6:ℕ).factorial : ℝ) = 720 := by norm_num [Nat.factorial]
  rw [h720]
  -- `q^6 = √τ` and the polynomial factor is absorbed
  have hq6 : q^6 = s := by
    rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hτ, hsdef, Real.sqrt_eq_rpow]
    norm_num
  have hu2 : u^2 = τ*r^2 := by rw [hudef, mul_pow, hs2]
  have hexp : (1+u)^6*Real.exp (-(τ*r^2)) ≤ 1568*Real.exp (-(τ*r^2/2)) := by
    have := one_add_pow_six_mul_exp_le hu
    rwa [hu2] at this
  have hD6 : D^6 = s*M^6*(1+u)^6 := by rw [hDdef, mul_pow, mul_pow, hq6]
  rw [hD6]
  have hM6 : 0 ≤ M^6 := by positivity
  calc 720*Real.exp (-(τ*r^2))*(s*M^6*(1+u)^6)
      = 720*s*M^6*((1+u)^6*Real.exp (-(τ*r^2))) := by ring
    _ ≤ 720*s*M^6*(1568*Real.exp (-(τ*r^2/2))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (720*1568*(64*L^2)^6)*s*Real.exp (-(τ*r^2/2)) := by rw [hMdef]; ring

end

#print axioms one_add_pow_six_mul_exp_le
#print axioms norm_iteratedFDeriv_six_exp_neg_mul_norm_sq_le_sqrt

end SphericalRiesz
