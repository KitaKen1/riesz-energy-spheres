import Riesz.GaussianCompositionSixth

/-! Twelfth derivative envelope for a Gaussian on a smooth chart.  The
constant is explicit and independent of the Gaussian scale.  This supplies
the order needed to pair the actual n^-12 rule error with n^24 density. -/
set_option autoImplicit false
noncomputable section
open Set
namespace SphericalRiesz

theorem sixth_le_exp_half {u : ℝ} (hu : 0 ≤ u) : u^6 ≤ 46080*Real.exp (u/2) := by
  have h := Real.pow_div_factorial_le_exp (x := u/2) (by positivity) 6
  norm_num [Nat.factorial] at h
  nlinarith

theorem sixth_mul_exp_neg_le {u : ℝ} (hu : 0 ≤ u) : u^6*Real.exp (-u) ≤ 46080*Real.exp (-(u/2)) := by
  have h := sixth_le_exp_half hu
  have hsplit : Real.exp (-u) = Real.exp (-(u/2))*Real.exp (-(u/2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hinv : Real.exp (u/2)*Real.exp (-(u/2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hq : 0 < Real.exp (-(u/2)) := Real.exp_pos _
  have h2 : u^6*Real.exp (-(u/2)) ≤ 46080 := by
    calc u^6*Real.exp (-(u/2)) ≤ 46080*Real.exp (u/2)*Real.exp (-(u/2)) :=
          mul_le_mul_of_nonneg_right h hq.le
      _ = 46080 := by rw [mul_assoc, hinv, mul_one]
  rw [hsplit]
  calc u^6*(Real.exp (-(u/2))*Real.exp (-(u/2))) = (u^6*Real.exp (-(u/2)))*Real.exp (-(u/2)) := by
        ring
    _ ≤ 46080*Real.exp (-(u/2)) := mul_le_mul_of_nonneg_right h2 hq.le

theorem twelfth_pow_three_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a+b+c)^12 ≤ 531441*(a^12+b^12+c^12) := by
  set M := max a (max b c) with hM
  have h1 : a+b+c ≤ 3*M := by
    have := le_max_left a (max b c)
    have := le_max_left b c
    have := le_max_right b c
    have := le_max_right a (max b c)
    linarith
  have h2 : (a+b+c)^12 ≤ (3*M)^12 := pow_le_pow_left₀ (by positivity) h1 12
  have h3 : M^12 ≤ a^12+b^12+c^12 := by
    rcases max_choice a (max b c) with h | h <;> rw [hM, h]
    · nlinarith [pow_nonneg hb 12, pow_nonneg hc 12]
    · rcases max_choice b c with h' | h' <;> rw [h']
      · nlinarith [pow_nonneg ha 12, pow_nonneg hc 12]
      · nlinarith [pow_nonneg ha 12, pow_nonneg hb 12]
  calc (a+b+c)^12 ≤ (3*M)^12 := h2
    _ = 531441*M^12 := by ring
    _ ≤ 531441*(a^12+b^12+c^12) := by linarith

/-- The scale-dependent scalar factors in Faà di Bruno are absorbed into the Gaussian. -/
theorem twelfth_scalar_bound {τ r L T D : ℝ} (hτ : 0 ≤ τ) (hr : 0 ≤ r) (hL : 1 ≤ L)
    (hTdef : T = τ*(4096*(r*L+L^2))) (hDdef : D = 1+2*τ*r*L+Real.sqrt T) :
    479001600*Real.exp (-(τ*r^2))*D^12 ≤
      (479001600*531441*(10:ℝ)^30*L^12)*(1+τ^6)*Real.exp (-(τ*r^2/2)) := by
  have hL0 : 0 ≤ L := by linarith
  have hT : 0 ≤ T := by rw [hTdef]; positivity
  have hu : 0 ≤ τ*r^2 := by positivity
  have hP := twelfth_pow_three_le (by norm_num : (0:ℝ) ≤ 1)
    (by positivity : 0 ≤ 2*τ*r*L) (Real.sqrt_nonneg T)
  have hsqrt : Real.sqrt T^12 = T^6 := by
    rw [show (12:ℕ) = 2*6 from rfl, pow_mul, Real.sq_sqrt hT]
  rw [hsqrt, ← hDdef] at hP
  have hgauss : (τ*r^2)^6*Real.exp (-(τ*r^2)) ≤ 46080*Real.exp (-(τ*r^2/2)) := by
    simpa only [neg_div] using sixth_mul_exp_neg_le hu
  obtain ⟨e, he_def⟩ : ∃ e, e = Real.exp (-(τ*r^2)) := ⟨_,rfl⟩
  obtain ⟨e2, he2_def⟩ : ∃ e2, e2 = Real.exp (-(τ*r^2/2)) := ⟨_,rfl⟩
  rw [← he_def, ← he2_def] at hgauss ⊢
  have he : 0 ≤ e := he_def ▸ (Real.exp_pos _).le
  have he2 : 0 ≤ e2 := he2_def ▸ (Real.exp_pos _).le
  have hE : e ≤ e2 := by rw [he_def,he2_def]; exact Real.exp_le_exp.mpr (by linarith)
  have hτ6 : 0 ≤ τ^6 := by positivity
  have hA : (2*τ*r*L)^12*e ≤ 188743680*L^12*τ^6*e2 := by
    have h1 : (2*τ*r*L)^12*e = 4096*L^12*τ^6*((τ*r^2)^6*e) := by ring
    rw [h1]
    have h2 := mul_le_mul_of_nonneg_left hgauss (by positivity : 0 ≤ 4096*L^12*τ^6)
    linarith
  have hrL : r*L+L^2 ≤ L^2*(1+r) := by
    nlinarith [mul_nonneg (mul_nonneg hr hL0) (sub_nonneg.mpr hL)]
  have hT6 : T^6 ≤ 4096^6*L^12*(τ^6*(1+r)^6) := by
    calc
      T^6 = 4096^6*τ^6*(r*L+L^2)^6 := by rw [hTdef]; ring
      _ ≤ 4096^6*τ^6*(L^2*(1+r))^6 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hrL 6) (by positivity)
      _ = _ := by ring
  have hpoly : τ^6*(1+r)^6 ≤ 1094*τ^6+365*(τ*r^2)^6 := by
    have h1 : (1+r)^6 ≤ 729*(1+r^6) := by
      simpa using sixth_pow_three_le (a:=1) (b:=r) (c:=0) (by norm_num) hr (by norm_num)
    have h2 : r^6 ≤ (1+r^12)/2 := by nlinarith [sq_nonneg (r^6-1)]
    have h3 : 0 ≤ τ^6*r^12 := by positivity
    calc
      _ ≤ τ^6*(729*(1+r^6)) := mul_le_mul_of_nonneg_left h1 hτ6
      _ ≤ τ^6*(729*(1+(1+r^12)/2)) := by
        apply mul_le_mul_of_nonneg_left _ hτ6
        linarith
      _ ≤ _ := by nlinarith
  have hB : T^6*e ≤ 4096^6*L^12*(1094*τ^6+16819200)*e2 := by
    have h1 := mul_le_mul_of_nonneg_right hT6 he
    have h2 : 4096^6*L^12*(τ^6*(1+r)^6)*e ≤
        4096^6*L^12*(1094*τ^6+365*(τ*r^2)^6)*e :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly (by positivity)) he
    have h3 := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ 1094*τ^6)
    have h4 : 4096^6*L^12*(1094*τ^6*e+365*((τ*r^2)^6*e)) ≤
        4096^6*L^12*(1094*τ^6*e2+365*(46080*e2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    calc
      _ ≤ 4096^6*L^12*(1094*τ^6+365*(τ*r^2)^6)*e := h1.trans h2
      _ = 4096^6*L^12*(1094*τ^6*e+365*((τ*r^2)^6*e)) := by ring
      _ ≤ 4096^6*L^12*(1094*τ^6*e2+365*(46080*e2)) := h4
      _ = _ := by ring
  have hL12 : 1 ≤ L^12 := one_le_pow₀ hL
  have hD : D^12*e ≤ 531441*(e2+188743680*L^12*τ^6*e2+
      4096^6*L^12*(1094*τ^6+16819200)*e2) := by
    have h1 := mul_le_mul_of_nonneg_right hP he
    have h2 : 531441*(1^12+(2*τ*r*L)^12+T^6)*e =
      531441*(e+(2*τ*r*L)^12*e+T^6*e) := by ring
    rw [h2] at h1
    linarith
  have hfinal : 531441*(e2+188743680*L^12*τ^6*e2+
      4096^6*L^12*(1094*τ^6+16819200)*e2) ≤
      531441*(10:ℝ)^30*L^12*(1+τ^6)*e2 := by
    have h1 : e2 ≤ L^12*e2 := le_mul_of_one_le_left he2 hL12
    have h2 : 0 ≤ L^12*τ^6*e2 := by positivity
    have h3 : 0 ≤ L^12*e2 := by positivity
    nlinarith
  have hfin := hD.trans hfinal
  calc
    479001600*e*D^12 = 479001600*(D^12*e) := by ring
    _ ≤ 479001600*(531441*10^30*L^12*(1+τ^6)*e2) :=
      mul_le_mul_of_nonneg_left hfin (by norm_num)
    _ = _ := by ring

section
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Leibniz bound for `-τ‖F‖²`. -/
theorem norm_iteratedFDerivWithin_neg_mul_norm_sq_le_twelve {F : E → H} {U : Set E} (hU : IsOpen U)
    {x : E} (hx : x ∈ U) (hF : ContDiffOn ℝ 12 F U) {τ : ℝ} (hτ : 0 ≤ τ) {n : ℕ} (hn : n ≤ 12) :
    ‖iteratedFDerivWithin ℝ n (fun y => -(τ*‖F y‖^2)) U x‖ ≤
      τ*∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*‖iteratedFDerivWithin ℝ i F U x‖*
        ‖iteratedFDerivWithin ℝ (n-i) F U x‖ := by
  have hq : ContDiffOn ℝ 12 (fun y => inner ℝ (F y) (F y)) U := hF.inner ℝ hF
  have heq : (fun y => -(τ*‖F y‖^2)) = (-τ) • (fun y => inner ℝ (F y) (F y)) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, real_inner_self_eq_norm_sq]
    ring
  have hn' : (n : WithTop ℕ∞) ≤ 12 := by exact_mod_cast hn
  rw [heq, iteratedFDerivWithin_const_smul_apply ((hq.of_le hn').contDiffWithinAt hx)
    hU.uniqueDiffOn hx, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hτ]
  apply mul_le_mul_of_nonneg_left _ hτ
  have h := (innerSL ℝ (E := H)).norm_iteratedFDerivWithin_le_of_bilinear_of_le_one hF hF
    hU.uniqueDiffOn hx (n := n) hn' (norm_innerSL_le ℝ)
  exact h

/-- Twelfth derivative of `exp(-τ‖F‖²)` at a point where `F` is `C¹²`. -/
theorem norm_iteratedFDeriv_twelve_exp_neg_mul_norm_sq_le {F : E → H} {x : E}
    (hF : ContDiffAt ℝ 12 F x) {L : ℝ} (hL : 1 ≤ L)
    (hFL : ∀ j, 1 ≤ j → j ≤ 12 → ‖iteratedFDeriv ℝ j F x‖ ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖iteratedFDeriv ℝ 12 (fun y => Real.exp (-(τ*‖F y‖^2))) x‖ ≤
      (479001600*531441*(10:ℝ)^30*L^12)*(1+τ^6)*Real.exp (-(τ*‖F x‖^2/2)) := by
  obtain ⟨U, hU, hxU, hFU⟩ := hF.contDiffOn' le_rfl (by simp)
  have hFU' : ContDiffOn ℝ 12 F U := by simpa using hFU
  set r := ‖F x‖ with hrdef
  have hr : 0 ≤ r := norm_nonneg _
  set f : E → ℝ := fun y => -(τ*‖F y‖^2) with hfdef
  have hf : ContDiffOn ℝ 12 f U := ((hFU'.norm_sq ℝ).const_smul τ).neg
  have hwithin : ∀ j, iteratedFDerivWithin ℝ j F U x = iteratedFDeriv ℝ j F x :=
    fun j => iteratedFDerivWithin_of_isOpen j hU hxU
  set a : ℕ → ℝ := fun i => ‖iteratedFDerivWithin ℝ i F U x‖ with hadef
  have ha : ∀ i, 0 ≤ a i := fun i => norm_nonneg _
  have ha0 : a 0 = r := by simp [hadef, hrdef]
  have haL : ∀ i, 1 ≤ i → i ≤ 12 → a i ≤ L := by
    intro i h1 h6
    simp only [hadef, hwithin]
    exact hFL i h1 h6
  set T := τ*(4096*(r*L+L^2)) with hTdef
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
  have hDbound : ∀ i, 1 ≤ i → i ≤ 12 → ‖iteratedFDerivWithin ℝ i f U x‖ ≤ D^i := by
    intro i h1 h6
    have hl := norm_iteratedFDerivWithin_neg_mul_norm_sq_le_twelve hU hxU hFU' hτ h6
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
      have h2i : (2:ℝ)^i ≤ 4096 := by
        calc (2:ℝ)^i ≤ 2^12 := pow_le_pow_right₀ (by norm_num) h6
          _ = 4096 := by norm_num
      have hmono : D^2 ≤ D^i := pow_le_pow_right₀ hD1 hi
      calc ‖iteratedFDerivWithin ℝ i f U x‖ ≤ τ*(2^i*(r*L+L^2)) :=
            hl.trans (mul_le_mul_of_nonneg_left hs hτ)
        _ ≤ T := by
            rw [hTdef]
            apply mul_le_mul_of_nonneg_left _ hτ
            exact mul_le_mul_of_nonneg_right h2i (by positivity)
        _ ≤ D^2 := hDT
        _ ≤ D^i := hmono
  have hC : ∀ i, i ≤ 12 → ‖iteratedFDerivWithin ℝ i Real.exp univ (f x)‖ ≤ Real.exp (f x) := by
    intro i _
    rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hcomp := norm_iteratedFDerivWithin_comp_le (g := Real.exp) (f := f) (s := U) (t := univ)
    (n := 12) (N := 12) Real.contDiff_exp.contDiffOn hf le_rfl uniqueDiffOn_univ hU.uniqueDiffOn
    (mapsTo_univ _ _) hxU hC hDbound
  have hlhs : iteratedFDerivWithin ℝ 12 (Real.exp ∘ f) U x =
      iteratedFDeriv ℝ 12 (fun y => Real.exp (-(τ*‖F y‖^2))) x :=
    iteratedFDerivWithin_of_isOpen 12 hU hxU
  rw [hlhs] at hcomp
  refine hcomp.trans ?_
  have hfx : f x = -(τ*r^2) := by simp [hfdef, hrdef]
  rw [hfx]
  have h720 : ((12:ℕ).factorial : ℝ) = 479001600 := by norm_num [Nat.factorial]
  rw [h720]
  exact twelfth_scalar_bound hτ hr hL rfl rfl

end

end SphericalRiesz
