import Riesz.GaussianCompositionSixth

/-! Fourteenth derivative envelope for a Gaussian on a smooth chart.

Two forms.  For every `τ ≥ 0`:
`‖D¹⁴ exp(-τ‖F‖²)(x)‖ ≤ 14!·3¹⁴·10³⁸ L¹⁴ (1+τ⁷) e^(-τ r²/2)`, `r = ‖F x‖`.
For `0 ≤ τ ≤ 1` the same derivative carries a factor `√τ`:
`‖D¹⁴ exp(-τ‖F‖²)(x)‖ ≤ 14!·16384·645121·(16384 L²)¹⁴ √τ e^(-τ r²/2)`.
Order fourteen is what the negative exponents on `S²⁴` need: the patch Gaussian defect is
quadratic in the bump quadrature error, so `n⁻¹⁴ (√τ + τ⁷)` gives a defect of size
`α²` at mesoscopic scales and linear in `τ` at macroscopic scales. -/
set_option autoImplicit false
noncomputable section
open Set
namespace SphericalRiesz

theorem one_add_pow_le_two_pow_mul (n : ℕ) {u : ℝ} (hu : 0 ≤ u) : (1+u)^n ≤ 2^n*(1+u^n) := by
  have h2 : (0:ℝ) ≤ 2^n := by positivity
  have hun : 0 ≤ u^n := pow_nonneg hu n
  rcases le_total u 1 with h | h
  · calc (1+u)^n ≤ 2^n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ ≤ 2^n*(1+u^n) := le_mul_of_one_le_right h2 (by linarith)
  · calc (1+u)^n ≤ (2*u)^n := pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = 2^n*u^n := mul_pow _ _ _
      _ ≤ 2^n*(1+u^n) := mul_le_mul_of_nonneg_left (by linarith) h2

theorem seventh_le_exp_half {u : ℝ} (hu : 0 ≤ u) : u^7 ≤ 645120*Real.exp (u/2) := by
  have h := Real.pow_div_factorial_le_exp (x := u/2) (by positivity) 7
  norm_num [Nat.factorial] at h
  nlinarith

theorem seventh_mul_exp_neg_le {u : ℝ} (hu : 0 ≤ u) :
    u^7*Real.exp (-u) ≤ 645120*Real.exp (-(u/2)) := by
  have h := seventh_le_exp_half hu
  have hsplit : Real.exp (-u) = Real.exp (-(u/2))*Real.exp (-(u/2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hinv : Real.exp (u/2)*Real.exp (-(u/2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hq : 0 < Real.exp (-(u/2)) := Real.exp_pos _
  have h2 : u^7*Real.exp (-(u/2)) ≤ 645120 := by
    calc u^7*Real.exp (-(u/2)) ≤ 645120*Real.exp (u/2)*Real.exp (-(u/2)) :=
          mul_le_mul_of_nonneg_right h hq.le
      _ = 645120 := by rw [mul_assoc, hinv, mul_one]
  rw [hsplit]
  calc u^7*(Real.exp (-(u/2))*Real.exp (-(u/2))) = (u^7*Real.exp (-(u/2)))*Real.exp (-(u/2)) := by
        ring
    _ ≤ 645120*Real.exp (-(u/2)) := mul_le_mul_of_nonneg_right h2 hq.le

theorem fourteenth_pow_three_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a+b+c)^14 ≤ 4782969*(a^14+b^14+c^14) := by
  set M := max a (max b c) with hM
  have h1 : a+b+c ≤ 3*M := by
    have := le_max_left a (max b c)
    have := le_max_left b c
    have := le_max_right b c
    have := le_max_right a (max b c)
    linarith
  have h2 : (a+b+c)^14 ≤ (3*M)^14 := pow_le_pow_left₀ (by positivity) h1 14
  have h3 : M^14 ≤ a^14+b^14+c^14 := by
    rcases max_choice a (max b c) with h | h <;> rw [hM, h]
    · nlinarith [pow_nonneg hb 14, pow_nonneg hc 14]
    · rcases max_choice b c with h' | h' <;> rw [h']
      · nlinarith [pow_nonneg ha 14, pow_nonneg hc 14]
      · nlinarith [pow_nonneg ha 14, pow_nonneg hb 14]
  calc (a+b+c)^14 ≤ (3*M)^14 := h2
    _ = 4782969*M^14 := by ring
    _ ≤ 4782969*(a^14+b^14+c^14) := by linarith

/-- The scale-dependent scalar factors in Faà di Bruno are absorbed into the Gaussian. -/
theorem fourteenth_scalar_bound {τ r L T D : ℝ} (hτ : 0 ≤ τ) (hr : 0 ≤ r) (hL : 1 ≤ L)
    (hTdef : T = τ*(16384*(r*L+L^2))) (hDdef : D = 1+2*τ*r*L+Real.sqrt T) :
    87178291200*Real.exp (-(τ*r^2))*D^14 ≤
      (87178291200*4782969*(10:ℝ)^38*L^14)*(1+τ^7)*Real.exp (-(τ*r^2/2)) := by
  have hL0 : 0 ≤ L := by linarith
  have hT : 0 ≤ T := by rw [hTdef]; positivity
  have hu : 0 ≤ τ*r^2 := by positivity
  have hP := fourteenth_pow_three_le (by norm_num : (0:ℝ) ≤ 1)
    (by positivity : 0 ≤ 2*τ*r*L) (Real.sqrt_nonneg T)
  have hsqrt : Real.sqrt T^14 = T^7 := by
    rw [show (14:ℕ) = 2*7 from rfl, pow_mul, Real.sq_sqrt hT]
  rw [hsqrt, ← hDdef] at hP
  have hgauss : (τ*r^2)^7*Real.exp (-(τ*r^2)) ≤ 645120*Real.exp (-(τ*r^2/2)) := by
    simpa only [neg_div] using seventh_mul_exp_neg_le hu
  obtain ⟨e, he_def⟩ : ∃ e, e = Real.exp (-(τ*r^2)) := ⟨_,rfl⟩
  obtain ⟨e2, he2_def⟩ : ∃ e2, e2 = Real.exp (-(τ*r^2/2)) := ⟨_,rfl⟩
  rw [← he_def, ← he2_def] at hgauss ⊢
  have he : 0 ≤ e := he_def ▸ (Real.exp_pos _).le
  have he2 : 0 ≤ e2 := he2_def ▸ (Real.exp_pos _).le
  have hE : e ≤ e2 := by rw [he_def,he2_def]; exact Real.exp_le_exp.mpr (by linarith)
  have hτ7 : 0 ≤ τ^7 := by positivity
  have hA : (2*τ*r*L)^14*e ≤ 10569646080*L^14*τ^7*e2 := by
    have h1 : (2*τ*r*L)^14*e = 16384*L^14*τ^7*((τ*r^2)^7*e) := by ring
    rw [h1]
    have h2 := mul_le_mul_of_nonneg_left hgauss (by positivity : 0 ≤ 16384*L^14*τ^7)
    linarith
  have hrL : r*L+L^2 ≤ L^2*(1+r) := by
    nlinarith [mul_nonneg (mul_nonneg hr hL0) (sub_nonneg.mpr hL)]
  have hT7 : T^7 ≤ 16384^7*L^14*(τ^7*(1+r)^7) := by
    calc
      T^7 = 16384^7*τ^7*(r*L+L^2)^7 := by rw [hTdef]; ring
      _ ≤ 16384^7*τ^7*(L^2*(1+r))^7 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hrL 7) (by positivity)
      _ = _ := by ring
  have hpoly : τ^7*(1+r)^7 ≤ 192*τ^7+64*(τ*r^2)^7 := by
    have h1 : (1+r)^7 ≤ 128*(1+r^7) := by
      have := one_add_pow_le_two_pow_mul 7 hr
      norm_num at this
      linarith
    have h2 : r^7 ≤ (1+r^14)/2 := by nlinarith [sq_nonneg (r^7-1)]
    have h3 : 0 ≤ τ^7*r^14 := by positivity
    calc
      _ ≤ τ^7*(128*(1+r^7)) := mul_le_mul_of_nonneg_left h1 hτ7
      _ ≤ τ^7*(128*(1+(1+r^14)/2)) := by
        apply mul_le_mul_of_nonneg_left _ hτ7
        linarith
      _ = 192*τ^7+64*(τ*r^2)^7 := by ring
  have hB : T^7*e ≤ 16384^7*L^14*(192*τ^7+41287680)*e2 := by
    have h1 := mul_le_mul_of_nonneg_right hT7 he
    have h2 : 16384^7*L^14*(τ^7*(1+r)^7)*e ≤
        16384^7*L^14*(192*τ^7+64*(τ*r^2)^7)*e :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly (by positivity)) he
    have h3 := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ 192*τ^7)
    have h4 : 16384^7*L^14*(192*τ^7*e+64*((τ*r^2)^7*e)) ≤
        16384^7*L^14*(192*τ^7*e2+64*(645120*e2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    calc
      _ ≤ 16384^7*L^14*(192*τ^7+64*(τ*r^2)^7)*e := h1.trans h2
      _ = 16384^7*L^14*(192*τ^7*e+64*((τ*r^2)^7*e)) := by ring
      _ ≤ 16384^7*L^14*(192*τ^7*e2+64*(645120*e2)) := h4
      _ = _ := by ring
  have hL14 : 1 ≤ L^14 := one_le_pow₀ hL
  have hD : D^14*e ≤ 4782969*(e2+10569646080*L^14*τ^7*e2+
      16384^7*L^14*(192*τ^7+41287680)*e2) := by
    have h1 := mul_le_mul_of_nonneg_right hP he
    have h2 : 4782969*(1^14+(2*τ*r*L)^14+T^7)*e =
      4782969*(e+(2*τ*r*L)^14*e+T^7*e) := by ring
    rw [h2] at h1
    linarith
  have hfinal : 4782969*(e2+10569646080*L^14*τ^7*e2+
      16384^7*L^14*(192*τ^7+41287680)*e2) ≤
      4782969*(10:ℝ)^38*L^14*(1+τ^7)*e2 := by
    have h1 : e2 ≤ L^14*e2 := le_mul_of_one_le_left he2 hL14
    have h2 : 0 ≤ L^14*τ^7*e2 := by positivity
    have h3 : 0 ≤ L^14*e2 := by positivity
    have hk1 : (16384:ℝ)^7*192+10569646080 ≤ 10^38 := by norm_num
    have hk2 : (16384:ℝ)^7*41287680+1 ≤ 10^38 := by norm_num
    have e1 : 4782969*(e2+10569646080*L^14*τ^7*e2+16384^7*L^14*(192*τ^7+41287680)*e2) =
        4782969*(e2+((16384:ℝ)^7*192+10569646080)*(L^14*τ^7*e2)+
          ((16384:ℝ)^7*41287680)*(L^14*e2)) := by ring
    have e3 : 4782969*(10:ℝ)^38*L^14*(1+τ^7)*e2 =
        4782969*((10:ℝ)^38*(L^14*τ^7*e2)+(10:ℝ)^38*(L^14*e2)) := by ring
    rw [e1, e3]
    have hY := mul_le_mul_of_nonneg_right hk1 h2
    have hZ := mul_le_mul_of_nonneg_right hk2 h3
    nlinarith
  have hfin := hD.trans hfinal
  calc
    87178291200*e*D^14 = 87178291200*(D^14*e) := by ring
    _ ≤ 87178291200*(4782969*10^38*L^14*(1+τ^7)*e2) :=
      mul_le_mul_of_nonneg_left hfin (by norm_num)
    _ = _ := by ring

theorem one_add_pow_fourteen_mul_exp_le {u : ℝ} (hu : 0 ≤ u) :
    (1+u)^14*Real.exp (-(u^2)) ≤ 10569662464*Real.exp (-(u^2/2)) := by
  have h1 : (1+u)^14 ≤ 16384*(1+u^14) := by
    have := one_add_pow_le_two_pow_mul 14 hu
    norm_num at this
    linarith
  have h2 : (u^2)^7*Real.exp (-(u^2)) ≤ 645120*Real.exp (-(u^2/2)) :=
    seventh_mul_exp_neg_le (sq_nonneg u)
  have he : Real.exp (-(u^2)) ≤ Real.exp (-(u^2/2)) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg u])
  have hE := Real.exp_pos (-(u^2))
  have hu14 : u^14 = (u^2)^7 := by ring
  calc (1+u)^14*Real.exp (-(u^2)) ≤ 16384*(1+u^14)*Real.exp (-(u^2)) :=
        mul_le_mul_of_nonneg_right h1 hE.le
    _ = 16384*(Real.exp (-(u^2))+(u^2)^7*Real.exp (-(u^2))) := by rw [hu14]; ring
    _ ≤ 16384*(Real.exp (-(u^2/2))+645120*Real.exp (-(u^2/2))) := by linarith
    _ = 10569662464*Real.exp (-(u^2/2)) := by ring

section
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Leibniz bound for `-τ‖F‖²`. -/
theorem norm_iteratedFDerivWithin_neg_mul_norm_sq_le_fourteen {F : E → H} {U : Set E}
    (hU : IsOpen U) {x : E} (hx : x ∈ U) (hF : ContDiffOn ℝ 14 F U) {τ : ℝ} (hτ : 0 ≤ τ)
    {n : ℕ} (hn : n ≤ 14) :
    ‖iteratedFDerivWithin ℝ n (fun y => -(τ*‖F y‖^2)) U x‖ ≤
      τ*∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*‖iteratedFDerivWithin ℝ i F U x‖*
        ‖iteratedFDerivWithin ℝ (n-i) F U x‖ := by
  have hq : ContDiffOn ℝ 14 (fun y => inner ℝ (F y) (F y)) U := hF.inner ℝ hF
  have heq : (fun y => -(τ*‖F y‖^2)) = (-τ) • (fun y => inner ℝ (F y) (F y)) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, real_inner_self_eq_norm_sq]
    ring
  have hn' : (n : WithTop ℕ∞) ≤ 14 := by exact_mod_cast hn
  rw [heq, iteratedFDerivWithin_const_smul_apply ((hq.of_le hn').contDiffWithinAt hx)
    hU.uniqueDiffOn hx, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hτ]
  apply mul_le_mul_of_nonneg_left _ hτ
  have h := (innerSL ℝ (E := H)).norm_iteratedFDerivWithin_le_of_bilinear_of_le_one hF hF
    hU.uniqueDiffOn hx (n := n) hn' (norm_innerSL_le ℝ)
  exact h

/-- Fourteenth derivative of `exp(-τ‖F‖²)` at a point where `F` is `C¹⁴`. -/
theorem norm_iteratedFDeriv_fourteen_exp_neg_mul_norm_sq_le {F : E → H} {x : E}
    (hF : ContDiffAt ℝ 14 F x) {L : ℝ} (hL : 1 ≤ L)
    (hFL : ∀ j, 1 ≤ j → j ≤ 14 → ‖iteratedFDeriv ℝ j F x‖ ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖iteratedFDeriv ℝ 14 (fun y => Real.exp (-(τ*‖F y‖^2))) x‖ ≤
      (87178291200*4782969*(10:ℝ)^38*L^14)*(1+τ^7)*Real.exp (-(τ*‖F x‖^2/2)) := by
  obtain ⟨U, hU, hxU, hFU⟩ := hF.contDiffOn' le_rfl (by simp)
  have hFU' : ContDiffOn ℝ 14 F U := by simpa using hFU
  set r := ‖F x‖ with hrdef
  have hr : 0 ≤ r := norm_nonneg _
  set f : E → ℝ := fun y => -(τ*‖F y‖^2) with hfdef
  have hf : ContDiffOn ℝ 14 f U := ((hFU'.norm_sq ℝ).const_smul τ).neg
  have hwithin : ∀ j, iteratedFDerivWithin ℝ j F U x = iteratedFDeriv ℝ j F x :=
    fun j => iteratedFDerivWithin_of_isOpen j hU hxU
  set a : ℕ → ℝ := fun i => ‖iteratedFDerivWithin ℝ i F U x‖ with hadef
  have ha : ∀ i, 0 ≤ a i := fun i => norm_nonneg _
  have ha0 : a 0 = r := by simp [hadef, hrdef]
  have haL : ∀ i, 1 ≤ i → i ≤ 14 → a i ≤ L := by
    intro i h1 h6
    simp only [hadef, hwithin]
    exact hFL i h1 h6
  set T := τ*(16384*(r*L+L^2)) with hTdef
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
  have hDbound : ∀ i, 1 ≤ i → i ≤ 14 → ‖iteratedFDerivWithin ℝ i f U x‖ ≤ D^i := by
    intro i h1 h6
    have hl := norm_iteratedFDerivWithin_neg_mul_norm_sq_le_fourteen hU hxU hFU' hτ h6
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
      have h2i : (2:ℝ)^i ≤ 16384 := by
        calc (2:ℝ)^i ≤ 2^14 := pow_le_pow_right₀ (by norm_num) h6
          _ = 16384 := by norm_num
      have hmono : D^2 ≤ D^i := pow_le_pow_right₀ hD1 hi
      calc ‖iteratedFDerivWithin ℝ i f U x‖ ≤ τ*(2^i*(r*L+L^2)) :=
            hl.trans (mul_le_mul_of_nonneg_left hs hτ)
        _ ≤ T := by
            rw [hTdef]
            apply mul_le_mul_of_nonneg_left _ hτ
            exact mul_le_mul_of_nonneg_right h2i (by positivity)
        _ ≤ D^2 := hDT
        _ ≤ D^i := hmono
  have hC : ∀ i, i ≤ 14 → ‖iteratedFDerivWithin ℝ i Real.exp univ (f x)‖ ≤ Real.exp (f x) := by
    intro i _
    rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hcomp := norm_iteratedFDerivWithin_comp_le (g := Real.exp) (f := f) (s := U) (t := univ)
    (n := 14) (N := 14) Real.contDiff_exp.contDiffOn hf le_rfl uniqueDiffOn_univ hU.uniqueDiffOn
    (mapsTo_univ _ _) hxU hC hDbound
  have hlhs : iteratedFDerivWithin ℝ 14 (Real.exp ∘ f) U x =
      iteratedFDeriv ℝ 14 (fun y => Real.exp (-(τ*‖F y‖^2))) x :=
    iteratedFDerivWithin_of_isOpen 14 hU hxU
  rw [hlhs] at hcomp
  refine hcomp.trans ?_
  have hfx : f x = -(τ*r^2) := by simp [hfdef, hrdef]
  rw [hfx]
  have h720 : ((14:ℕ).factorial : ℝ) = 87178291200 := by norm_num [Nat.factorial]
  rw [h720]
  exact fourteenth_scalar_bound hτ hr hL rfl rfl

/-- Fourteenth derivative of `exp(-τ‖F‖²)` with a factor `√τ`, for `0 ≤ τ ≤ 1`. -/
theorem norm_iteratedFDeriv_fourteen_exp_neg_mul_norm_sq_le_sqrt {F : E → H} {x : E}
    (hF : ContDiffAt ℝ 14 F x) {L : ℝ} (hL : 1 ≤ L)
    (hFL : ∀ j, 1 ≤ j → j ≤ 14 → ‖iteratedFDeriv ℝ j F x‖ ≤ L) {τ : ℝ} (hτ : 0 ≤ τ)
    (hτ1 : τ ≤ 1) :
    ‖iteratedFDeriv ℝ 14 (fun y => Real.exp (-(τ*‖F y‖^2))) x‖ ≤
      (87178291200*10569662464*(16384*L^2)^14)*Real.sqrt τ*Real.exp (-(τ*‖F x‖^2/2)) := by
  obtain ⟨U, hU, hxU, hFU⟩ := hF.contDiffOn' le_rfl (by simp)
  have hFU' : ContDiffOn ℝ 14 F U := by simpa using hFU
  set r := ‖F x‖ with hrdef
  have hr : 0 ≤ r := norm_nonneg _
  set f : E → ℝ := fun y => -(τ*‖F y‖^2) with hfdef
  have hf : ContDiffOn ℝ 14 f U := ((hFU'.norm_sq ℝ).const_smul τ).neg
  have hwithin : ∀ j, iteratedFDerivWithin ℝ j F U x = iteratedFDeriv ℝ j F x :=
    fun j => iteratedFDerivWithin_of_isOpen j hU hxU
  set a : ℕ → ℝ := fun i => ‖iteratedFDerivWithin ℝ i F U x‖ with hadef
  have ha : ∀ i, 0 ≤ a i := fun i => norm_nonneg _
  have ha0 : a 0 = r := by simp [hadef, hrdef]
  have haL : ∀ i, 1 ≤ i → i ≤ 14 → a i ≤ L := by
    intro i h1 h6
    simp only [hadef, hwithin]
    exact hFL i h1 h6
  have hL0 : 0 ≤ L := by linarith
  set M := 16384*L^2 with hMdef
  have hM1 : 1 ≤ M := by nlinarith
  set s := Real.sqrt τ with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg τ
  have hs2 : s^2 = τ := Real.sq_sqrt hτ
  have hs1 : s ≤ 1 := by rw [hsdef]; exact Real.sqrt_le_one.mpr hτ1
  have hτs : τ ≤ s := by nlinarith
  set u := s*r with hudef
  have hu : 0 ≤ u := mul_nonneg hs0 hr
  set q := τ^((1:ℝ)/28) with hqdef
  have hq0 : 0 ≤ q := Real.rpow_nonneg hτ _
  set D := q*M*(1+u) with hDdef
  have hD0 : 0 ≤ D := by positivity
  -- each derivative of `f` is at most `M s (1+u) ≤ D^i`
  have hfi : ∀ i, 1 ≤ i → i ≤ 14 → ‖iteratedFDerivWithin ℝ i f U x‖ ≤ M*s*(1+u) := by
    intro i h1 h6
    have hl := norm_iteratedFDerivWithin_neg_mul_norm_sq_le_fourteen hU hxU hFU' hτ h6
    have hsum : ∑ j ∈ Finset.range (i+1), (i.choose j : ℝ)*a j*a (i-j) ≤ 2^i*(r*L+L^2) := by
      rcases Nat.lt_or_ge i 2 with hi | hi
      · have hi1 : i = 1 := by omega
        subst hi1
        rw [leibniz_sum_one a, ha0]
        have := haL 1 le_rfl (by norm_num)
        nlinarith [mul_nonneg hL0 hL0, mul_nonneg hr hL0]
      · exact leibniz_sum_le i h1 a ha ha0 (fun j hj hji => haL j hj (hji.trans h6))
    have h2i : (2:ℝ)^i ≤ 16384 := by
      calc (2:ℝ)^i ≤ 2^14 := pow_le_pow_right₀ (by norm_num) h6
        _ = 16384 := by norm_num
    have hrL : r*L+L^2 ≤ L^2*(1+r) := by
      nlinarith [mul_nonneg (mul_nonneg hr hL0) (sub_nonneg.mpr hL)]
    have hτr : τ*(1+r) ≤ s*(1+u) := by
      rw [hudef, ← hs2]
      nlinarith [mul_nonneg hs0 hr, mul_nonneg (mul_nonneg hs0 hs0) hr]
    calc ‖iteratedFDerivWithin ℝ i f U x‖ ≤ τ*(2^i*(r*L+L^2)) :=
          hl.trans (mul_le_mul_of_nonneg_left hsum hτ)
      _ ≤ τ*(16384*(L^2*(1+r))) := by
          apply mul_le_mul_of_nonneg_left _ hτ
          exact mul_le_mul h2i hrL (by positivity) (by norm_num)
      _ = M*(τ*(1+r)) := by rw [hMdef]; ring
      _ ≤ M*(s*(1+u)) := mul_le_mul_of_nonneg_left hτr (by positivity)
      _ = M*s*(1+u) := by ring
  have hDbound : ∀ i, 1 ≤ i → i ≤ 14 → ‖iteratedFDerivWithin ℝ i f U x‖ ≤ D^i := by
    intro i h1 h6
    refine (hfi i h1 h6).trans ?_
    have hqi : s ≤ q^i := by
      rcases hτ.eq_or_lt with h0 | hpos
      · rw [hsdef, ← h0, Real.sqrt_zero]
        exact pow_nonneg hq0 i
      · rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hτ, hsdef, Real.sqrt_eq_rpow]
        apply Real.rpow_le_rpow_of_exponent_ge hpos hτ1
        have : (i:ℝ) ≤ 14 := by exact_mod_cast h6
        linarith
    have hMi : M ≤ M^i := le_self_pow₀ hM1 (by omega)
    have hui : 1+u ≤ (1+u)^i := le_self_pow₀ (by linarith) (by omega)
    calc M*s*(1+u) = s*M*(1+u) := by ring
      _ ≤ q^i*M^i*(1+u)^i := by
          apply mul_le_mul (mul_le_mul hqi hMi (by linarith) (by positivity)) hui (by linarith)
            (by positivity)
      _ = D^i := by rw [hDdef, mul_pow (q*M) (1+u) i, mul_pow q M i]
  have hC : ∀ i, i ≤ 14 → ‖iteratedFDerivWithin ℝ i Real.exp univ (f x)‖ ≤ Real.exp (f x) := by
    intro i _
    rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_eq_iterate, Real.iter_deriv_exp, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  have hcomp := norm_iteratedFDerivWithin_comp_le (g := Real.exp) (f := f) (s := U) (t := univ)
    (n := 14) (N := 14) Real.contDiff_exp.contDiffOn hf le_rfl uniqueDiffOn_univ hU.uniqueDiffOn
    (mapsTo_univ _ _) hxU hC hDbound
  have hlhs : iteratedFDerivWithin ℝ 14 (Real.exp ∘ f) U x =
      iteratedFDeriv ℝ 14 (fun y => Real.exp (-(τ*‖F y‖^2))) x :=
    iteratedFDerivWithin_of_isOpen 14 hU hxU
  rw [hlhs] at hcomp
  refine hcomp.trans ?_
  have hfx : f x = -(τ*r^2) := by simp [hfdef, hrdef]
  rw [hfx]
  have h720 : ((14:ℕ).factorial : ℝ) = 87178291200 := by norm_num [Nat.factorial]
  rw [h720]
  -- `q^14 = √τ` and the polynomial factor is absorbed
  have hq14 : q^14 = s := by
    rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hτ, hsdef, Real.sqrt_eq_rpow]
    norm_num
  have hu2 : u^2 = τ*r^2 := by rw [hudef, mul_pow, hs2]
  have hexp : (1+u)^14*Real.exp (-(τ*r^2)) ≤ 10569662464*Real.exp (-(τ*r^2/2)) := by
    have := one_add_pow_fourteen_mul_exp_le hu
    rwa [hu2] at this
  have hD14 : D^14 = s*M^14*(1+u)^14 := by rw [hDdef, mul_pow, mul_pow, hq14]
  rw [hD14]
  have hM14 : 0 ≤ M^14 := by positivity
  calc 87178291200*Real.exp (-(τ*r^2))*(s*M^14*(1+u)^14)
      = 87178291200*s*M^14*((1+u)^14*Real.exp (-(τ*r^2))) := by ring
    _ ≤ 87178291200*s*M^14*(10569662464*Real.exp (-(τ*r^2/2))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (87178291200*10569662464*(16384*L^2)^14)*s*Real.exp (-(τ*r^2/2)) := by rw [hMdef]; ring

end

end SphericalRiesz
