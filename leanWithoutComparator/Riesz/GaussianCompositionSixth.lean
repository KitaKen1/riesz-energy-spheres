import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Sixth derivative of a Gaussian composed with a smooth map.

If `‖Dʲ F(x)‖ ≤ L` for `1 ≤ j ≤ 6` (with `L ≥ 1`) and `r = ‖F x‖`, then
`‖D⁶ exp(-τ‖F‖²)(x)‖ ≤ C L⁶ (1+τ³) e^{-τr²/2}` with an absolute constant `C`.  Only the bilinear
Leibniz bound and the Faà di Bruno bound `n!·C·Dⁿ` of Mathlib are used; the polynomial factors
`(τ r²)³` are absorbed by `u³ ≤ 48 e^{u/2}`. -/

set_option autoImplicit false
noncomputable section
open Set
namespace SphericalRiesz

theorem cube_le_exp_half {u : ℝ} (hu : 0 ≤ u) : u^3 ≤ 48*Real.exp (u/2) := by
  have h := Real.pow_div_factorial_le_exp (x := u/2) (by positivity) 3
  norm_num [Nat.factorial] at h
  nlinarith

theorem cube_mul_exp_neg_le {u : ℝ} (hu : 0 ≤ u) : u^3*Real.exp (-u) ≤ 48*Real.exp (-(u/2)) := by
  have h := cube_le_exp_half hu
  have hsplit : Real.exp (-u) = Real.exp (-(u/2))*Real.exp (-(u/2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hinv : Real.exp (u/2)*Real.exp (-(u/2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hq : 0 < Real.exp (-(u/2)) := Real.exp_pos _
  have h2 : u^3*Real.exp (-(u/2)) ≤ 48 := by
    calc u^3*Real.exp (-(u/2)) ≤ 48*Real.exp (u/2)*Real.exp (-(u/2)) :=
          mul_le_mul_of_nonneg_right h hq.le
      _ = 48 := by rw [mul_assoc, hinv, mul_one]
  rw [hsplit]
  calc u^3*(Real.exp (-(u/2))*Real.exp (-(u/2))) = (u^3*Real.exp (-(u/2)))*Real.exp (-(u/2)) := by
        ring
    _ ≤ 48*Real.exp (-(u/2)) := mul_le_mul_of_nonneg_right h2 hq.le

theorem sixth_pow_three_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a+b+c)^6 ≤ 729*(a^6+b^6+c^6) := by
  set M := max a (max b c) with hM
  have h1 : a+b+c ≤ 3*M := by
    have := le_max_left a (max b c)
    have := le_max_left b c
    have := le_max_right b c
    have := le_max_right a (max b c)
    linarith
  have h2 : (a+b+c)^6 ≤ (3*M)^6 := pow_le_pow_left₀ (by positivity) h1 6
  have h3 : M^6 ≤ a^6+b^6+c^6 := by
    rcases max_choice a (max b c) with h | h <;> rw [hM, h]
    · nlinarith [pow_nonneg hb 6, pow_nonneg hc 6]
    · rcases max_choice b c with h' | h' <;> rw [h']
      · nlinarith [pow_nonneg ha 6, pow_nonneg hc 6]
      · nlinarith [pow_nonneg ha 6, pow_nonneg hb 6]
  calc (a+b+c)^6 ≤ (3*M)^6 := h2
    _ = 729*M^6 := by ring
    _ ≤ 729*(a^6+b^6+c^6) := by linarith

/-- The scalar part of the sixth derivative bound. -/
theorem sixth_scalar_bound {τ r L T D : ℝ} (hτ : 0 ≤ τ) (hr : 0 ≤ r) (hL : 1 ≤ L)
    (hTdef : T = τ*(64*(r*L+L^2))) (hDdef : D = 1+2*τ*r*L+Real.sqrt T) :
    720*Real.exp (-(τ*r^2))*D^6 ≤ (720*729*26000000*L^6)*(1+τ^3)*Real.exp (-(τ*r^2/2)) := by
  have hL0 : 0 ≤ L := by linarith
  have hT : 0 ≤ T := by rw [hTdef]; positivity
  have hu : 0 ≤ τ*r^2 := by positivity
  have hP := sixth_pow_three_le (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0 ≤ 2*τ*r*L)
    (Real.sqrt_nonneg T)
  have hsqrt6 : Real.sqrt T^6 = T^3 := by
    rw [show (6:ℕ) = 2*3 from rfl, pow_mul, Real.sq_sqrt hT]
  rw [hsqrt6, ← hDdef] at hP
  have hcube' : (τ*r^2)^3*Real.exp (-(τ*r^2)) ≤ 48*Real.exp (-(τ*r^2/2)) := by
    simpa only [neg_div] using cube_mul_exp_neg_le hu
  obtain ⟨e, he_def⟩ : ∃ e, e = Real.exp (-(τ*r^2)) := ⟨_, rfl⟩
  obtain ⟨e2, he2_def⟩ : ∃ e2, e2 = Real.exp (-(τ*r^2/2)) := ⟨_, rfl⟩
  rw [← he_def, ← he2_def] at hcube' ⊢
  have he : 0 ≤ e := he_def ▸ (Real.exp_pos _).le
  have he2 : 0 ≤ e2 := he2_def ▸ (Real.exp_pos _).le
  have hE1 : e ≤ e2 := by
    rw [he_def, he2_def]
    exact Real.exp_le_exp.mpr (by linarith)
  have hτ3 : 0 ≤ τ^3 := by positivity
  have hA : (2*τ*r*L)^6*e ≤ 3072*L^6*τ^3*e2 := by
    have h1 : (2*τ*r*L)^6*e = 64*L^6*τ^3*((τ*r^2)^3*e) := by ring
    rw [h1]
    have hc : 0 ≤ 64*L^6*τ^3 := by positivity
    have h2 := mul_le_mul_of_nonneg_left hcube' hc
    linarith
  have hrL : r*L+L^2 ≤ L^2*(1+r) := by
    nlinarith [mul_nonneg (mul_nonneg hr hL0) (sub_nonneg.mpr hL)]
  have hT3 : T^3 ≤ 262144*L^6*(τ^3*(1+r)^3) := by
    have h0 : 0 ≤ r*L+L^2 := by positivity
    calc T^3 = 262144*τ^3*(r*L+L^2)^3 := by rw [hTdef]; ring
      _ ≤ 262144*τ^3*(L^2*(1+r))^3 := by
          apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hrL 3) (by positivity)
      _ = 262144*L^6*(τ^3*(1+r)^3) := by ring
  have hpoly : τ^3*(1+r)^3 ≤ 6*τ^3+2*(τ*r^2)^3 := by
    have h1 : (1+r)^3 ≤ 4*(1+r^3) := by nlinarith [sq_nonneg (r-1), sq_nonneg r]
    have h2 : r^3 ≤ (1+r^6)/2 := by nlinarith [sq_nonneg (r^3-1)]
    calc τ^3*(1+r)^3 ≤ τ^3*(4*(1+r^3)) := mul_le_mul_of_nonneg_left h1 hτ3
      _ ≤ τ^3*(4*(1+(1+r^6)/2)) := by
          apply mul_le_mul_of_nonneg_left _ hτ3
          linarith
      _ = 6*τ^3+2*(τ*r^2)^3 := by ring
  have hL6 : 0 ≤ 262144*L^6 := by positivity
  have hB : T^3*e ≤ 262144*L^6*(6*τ^3+96)*e2 := by
    have h1 : T^3*e ≤ 262144*L^6*(τ^3*(1+r)^3)*e := mul_le_mul_of_nonneg_right hT3 he
    have h2 : 262144*L^6*(τ^3*(1+r)^3)*e ≤ 262144*L^6*(6*τ^3+2*(τ*r^2)^3)*e := by
      apply mul_le_mul_of_nonneg_right _ he
      exact mul_le_mul_of_nonneg_left hpoly hL6
    have h3 : 6*τ^3*e ≤ 6*τ^3*e2 := mul_le_mul_of_nonneg_left hE1 (by positivity)
    have h4 : 262144*L^6*(6*τ^3*e+2*((τ*r^2)^3*e)) ≤ 262144*L^6*(6*τ^3*e2+2*(48*e2)) := by
      apply mul_le_mul_of_nonneg_left _ hL6
      linarith
    calc T^3*e ≤ 262144*L^6*(6*τ^3+2*(τ*r^2)^3)*e := h1.trans h2
      _ = 262144*L^6*(6*τ^3*e+2*((τ*r^2)^3*e)) := by ring
      _ ≤ 262144*L^6*(6*τ^3*e2+2*(48*e2)) := h4
      _ = 262144*L^6*(6*τ^3+96)*e2 := by ring
  have hL6' : 1 ≤ L^6 := one_le_pow₀ hL
  have hD6 : D^6*e ≤ 729*(e2+3072*L^6*τ^3*e2+262144*L^6*(6*τ^3+96)*e2) := by
    have h1 : D^6*e ≤ 729*(1^6+(2*τ*r*L)^6+T^3)*e := mul_le_mul_of_nonneg_right hP he
    have h2 : 729*(1^6+(2*τ*r*L)^6+T^3)*e = 729*(e+(2*τ*r*L)^6*e+T^3*e) := by ring
    linarith
  have hfinal : 729*(e2+3072*L^6*τ^3*e2+262144*L^6*(6*τ^3+96)*e2) ≤
      729*26000000*L^6*(1+τ^3)*e2 := by
    have h1 : e2 ≤ L^6*e2 := le_mul_of_one_le_left he2 hL6'
    have h2 : 0 ≤ L^6*τ^3*e2 := by positivity
    have h3 : 0 ≤ L^6*e2 := by positivity
    nlinarith
  have hfin := hD6.trans hfinal
  calc 720*e*D^6 = 720*(D^6*e) := by ring
    _ ≤ 720*(729*26000000*L^6*(1+τ^3)*e2) := mul_le_mul_of_nonneg_left hfin (by norm_num)
    _ = 720*729*26000000*L^6*(1+τ^3)*e2 := by ring

section
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Leibniz bound for `-τ‖F‖²`. -/
theorem norm_iteratedFDerivWithin_neg_mul_norm_sq_le {F : E → H} {U : Set E} (hU : IsOpen U)
    {x : E} (hx : x ∈ U) (hF : ContDiffOn ℝ 6 F U) {τ : ℝ} (hτ : 0 ≤ τ) {n : ℕ} (hn : n ≤ 6) :
    ‖iteratedFDerivWithin ℝ n (fun y => -(τ*‖F y‖^2)) U x‖ ≤
      τ*∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*‖iteratedFDerivWithin ℝ i F U x‖*
        ‖iteratedFDerivWithin ℝ (n-i) F U x‖ := by
  have hq : ContDiffOn ℝ 6 (fun y => inner ℝ (F y) (F y)) U := hF.inner ℝ hF
  have heq : (fun y => -(τ*‖F y‖^2)) = (-τ) • (fun y => inner ℝ (F y) (F y)) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, real_inner_self_eq_norm_sq]
    ring
  have hn' : (n : WithTop ℕ∞) ≤ 6 := by exact_mod_cast hn
  rw [heq, iteratedFDerivWithin_const_smul_apply ((hq.of_le hn').contDiffWithinAt hx)
    hU.uniqueDiffOn hx, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hτ]
  apply mul_le_mul_of_nonneg_left _ hτ
  have h := (innerSL ℝ (E := H)).norm_iteratedFDerivWithin_le_of_bilinear_of_le_one hF hF
    hU.uniqueDiffOn hx (n := n) hn' (norm_innerSL_le ℝ)
  exact h

/-- The Leibniz sum for `n = 1`. -/
theorem leibniz_sum_one (a : ℕ → ℝ) :
    ∑ i ∈ Finset.range (1+1), ((1:ℕ).choose i : ℝ)*a i*a (1-i) = 2*a 0*a 1 := by
  simp [Finset.sum_range_succ]
  ring

/-- The Leibniz sum for `2 ≤ n ≤ 6`, with `a 0 = r` and `a i ≤ L` for `1 ≤ i ≤ n`. -/
theorem leibniz_sum_le (n : ℕ) (hn : 1 ≤ n) (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) {r L : ℝ}
    (h0 : a 0 = r) (hL : ∀ i, 1 ≤ i → i ≤ n → a i ≤ L) :
    ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*a i*a (n-i) ≤ 2^n*(r*L+L^2) := by
  have hr : 0 ≤ r := h0 ▸ ha 0
  have hL0 : 0 ≤ L := (ha n).trans (hL n hn le_rfl)
  have hterm : ∀ i ∈ Finset.range (n+1), (n.choose i : ℝ)*a i*a (n-i) ≤
      (n.choose i : ℝ)*(r*L+L^2) := by
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      rw [h0, Nat.sub_zero]
      nlinarith [hL n hn le_rfl, mul_nonneg hL0 hL0]
    · by_cases hin : i = n
      · subst hin
        rw [Nat.sub_self, h0]
        nlinarith [hL i h le_rfl, mul_nonneg hL0 hL0]
      · have h1 := hL i h hi'
        have h2 := hL (n-i) (by omega) (by omega)
        have : a i*a (n-i) ≤ L*L := mul_le_mul h1 h2 (ha _) hL0
        nlinarith [mul_nonneg hr hL0]
  calc ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*a i*a (n-i)
      ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*(r*L+L^2) := Finset.sum_le_sum hterm
    _ = 2^n*(r*L+L^2) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose n

/-- Sixth derivative of `exp(-τ‖F‖²)` at a point where `F` is `C⁶`. -/
theorem norm_iteratedFDeriv_six_exp_neg_mul_norm_sq_le {F : E → H} {x : E}
    (hF : ContDiffAt ℝ 6 F x) {L : ℝ} (hL : 1 ≤ L)
    (hFL : ∀ j, 1 ≤ j → j ≤ 6 → ‖iteratedFDeriv ℝ j F x‖ ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖iteratedFDeriv ℝ 6 (fun y => Real.exp (-(τ*‖F y‖^2))) x‖ ≤
      (720*729*26000000*L^6)*(1+τ^3)*Real.exp (-(τ*‖F x‖^2/2)) := by
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
  set T := τ*(64*(r*L+L^2)) with hTdef
  have hT : 0 ≤ T := by positivity
  set D := 1+2*τ*r*L+Real.sqrt T with hDdef
  have hD1 : 1 ≤ D := by
    have : 0 ≤ 2*τ*r*L := by positivity
    have := Real.sqrt_nonneg T
    linarith
  have hDT : T ≤ D^2 := by
    have hs : Real.sqrt T ≤ D := by
      have : 0 ≤ 2*τ*r*L := by positivity
      linarith
    calc T = Real.sqrt T^2 := (Real.sq_sqrt hT).symm
      _ ≤ D^2 := pow_le_pow_left₀ (Real.sqrt_nonneg T) hs 2
  have hDbound : ∀ i, 1 ≤ i → i ≤ 6 → ‖iteratedFDerivWithin ℝ i f U x‖ ≤ D^i := by
    intro i h1 h6
    have hl := norm_iteratedFDerivWithin_neg_mul_norm_sq_le hU hxU hFU' hτ h6
    rcases Nat.lt_or_ge i 2 with hi | hi
    · have hi1 : i = 1 := by omega
      subst hi1
      rw [leibniz_sum_one a] at hl
      have hb : 2*a 0*a 1 ≤ 2*r*L := by
        rw [ha0]
        have := haL 1 le_rfl (by norm_num)
        nlinarith
      calc ‖iteratedFDerivWithin ℝ 1 f U x‖ ≤ τ*(2*a 0*a 1) := hl
        _ ≤ τ*(2*r*L) := mul_le_mul_of_nonneg_left hb hτ
        _ ≤ D^1 := by
            have := Real.sqrt_nonneg T
            nlinarith
    · have hs := leibniz_sum_le i h1 a ha ha0 (fun j hj hji => haL j hj (hji.trans h6))
      have h2i : (2:ℝ)^i ≤ 64 := by
        calc (2:ℝ)^i ≤ 2^6 := pow_le_pow_right₀ (by norm_num) h6
          _ = 64 := by norm_num
      have hmono : D^2 ≤ D^i := pow_le_pow_right₀ hD1 hi
      calc ‖iteratedFDerivWithin ℝ i f U x‖ ≤ τ*(2^i*(r*L+L^2)) :=
            hl.trans (mul_le_mul_of_nonneg_left hs hτ)
        _ ≤ T := by
            rw [hTdef]
            apply mul_le_mul_of_nonneg_left _ hτ
            exact mul_le_mul_of_nonneg_right h2i (by positivity)
        _ ≤ D^2 := hDT
        _ ≤ D^i := hmono
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
  exact sixth_scalar_bound hτ hr hL rfl rfl

end

end SphericalRiesz
