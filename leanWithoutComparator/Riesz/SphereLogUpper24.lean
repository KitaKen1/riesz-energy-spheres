import Riesz.SphereLog24
import Riesz.LeechLogBlock24
import Riesz.RationalSizeCeiling24
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Riesz.LeechNegSharp24

/-! The logarithmic energy on S²⁴: sharp upper bound at every large `N` and the two-sided
asymptotics (stage LOG of the S²⁴ chain).

The module has three parts.

* `SphereLogBridge24`: the Gaussian-only bridge.  A macroscopic budget at a negative exponent, a
  bound of the full Gaussian profile at `α = 1/2`, a short-range cost and the pointwise window
  give an explicit integrable majorant of `α⁻¹ (F_N(α) + 1_{(0,1)}(α))`, and the reverse Fatou
  lemma bounds the normalized logarithmic energy by `C_log + η`.
* `RationalSizeLogGap24`: the gap of the rational size ceiling beats the logarithm,
  `(1 - (N-1)/(M-1))(1 + log M) → 0`, and the arithmetic of the normalized logarithmic energy of
  a subconfiguration.
* `SphereLogUpper24`: configurations of every large size with normalized logarithmic energy at
  most `C_log + η` (a block of the least rational size above `N` and a subconfiguration whose
  pair average does not increase), the form of the conjecture, and the two-sided statement.

The upper half uses no hypothesis.  The two-sided statement assumes all-scale Leech contact
certificates (stage G24, not proved in this project) for its lower half. -/

section

/-! The Gaussian-only upper bridge for the logarithmic energy on S²⁴ (stage LOG).

With `J_N = ∫ α⁻¹ (F_N(α) + 1_{(0,1)}(α)) dα` the normalized logarithmic energy is
`½ (J_N + κ - log π + (1/12) log A₂₄)`.  Three Gaussian controls of a sequence of configurations
give an integrable majorant of the integrand:

* a macroscopic budget `∫_{(0,1]} α^(s/2-1) (F+1) ≤ B` at a negative exponent `-2 < s < 0` gives
  `F(α)+1 ≤ C B α^(-s/2)` for `α ≤ 1/2` by the doubling of the positive semidefinite profile, so
  the integrand is at most `C B α^(-s/2-1)`, integrable at `0`;
* a bound `Full_{1/2} ≤ W` gives `F(α)+1 ≤ W` for `α ≥ 1/2`;
* a short-range cost `Σ T_p/N ≤ D`, `p ≥ 0`, gives `F(α) ≤ 2^(p+1) D α^(-(p+1))` for `α ≥ 2`, so
  the integrand is at most `2^(p+1) D α^(-(p+2))`, integrable at infinity.

With the pointwise window `limsup Full_α ≤ Θ_Λ(α)` the reverse Fatou lemma gives
`limsup J_N ≤ ∫ α⁻¹ (Θ_Λ(α) - α⁻¹² - 1 + 1_{(0,1)}(α)) dα`, i.e. the normalized logarithmic
energy is eventually at most `C_log + η`.  No Gaussian certificate is used. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalRiesz

/-- Doubling of the positive semidefinite profile turns a macroscopic Gaussian budget at a
negative exponent into a pointwise bound which decays at `0`. -/
theorem sphereGaussianCenteredScaled24_macro_budget_bound {N : ℕ} (hN : 0 < N) {s B : ℝ}
    (hs : -2 < s) (hs0 : s < 0) (X : ConfigurationD 24 N)
    (hB : (∫ β in Ioc (0:ℝ) 1, β^(s/2-1)*(sphereGaussianCenteredScaled24 β X+1)) ≤ B)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1/2) :
    sphereGaussianCenteredScaled24 α X+1 ≤
      (Real.sqrt 2^25*(s/2)/(2^(s/2)-1))*B*α^(-(s/2)) := by
  have hκ : 0 < Real.sqrt 2^25 := by positivity
  have hi : IntegrableOn (fun β : ℝ => β^(s/2-1)*(sphereGaussianCenteredScaled24 β X+1))
      (Ioc 0 1) :=
    (sphereGaussianCenteredScaled24_neg_integrable hs hs0 hN X).mono_set Ioc_subset_Ioi_self
  have hsub : Ioc α (2*α) ⊆ Ioc (0:ℝ) 1 := fun β hβ => ⟨hα.trans hβ.1, by linarith [hβ.2]⟩
  have h0 : (0:ℝ) ∉ Set.uIcc α (2*α) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  have hw : IntegrableOn (fun β : ℝ => β^(s/2-1)) (Ioc α (2*α)) :=
    (intervalIntegral.intervalIntegrable_rpow (Or.inr h0)).1
  have hq1 : s/2-1 ≠ -1 := ne_of_lt (by linarith)
  have hid : (∫ β in Ioc α (2*α), β^(s/2-1)) = α^(s/2)*(2^(s/2)-1)/(s/2) := by
    rw [← intervalIntegral.integral_of_le (by linarith), integral_rpow (Or.inr ⟨hq1, h0⟩),
      show s/2-1+1 = s/2 by ring, Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hα.le]
    ring
  have hl : (sphereGaussianCenteredScaled24 α X+1)/Real.sqrt 2^25*
      (α^(s/2)*(2^(s/2)-1)/(s/2)) ≤ B := by
    calc (sphereGaussianCenteredScaled24 α X+1)/Real.sqrt 2^25*(α^(s/2)*(2^(s/2)-1)/(s/2))
        = ∫ β in Ioc α (2*α),
            ((sphereGaussianCenteredScaled24 α X+1)/Real.sqrt 2^25)*β^(s/2-1) := by
          rw [integral_const_mul, hid]
      _ ≤ ∫ β in Ioc α (2*α), β^(s/2-1)*(sphereGaussianCenteredScaled24 β X+1) := by
          apply setIntegral_mono_on (hw.const_mul _) (hi.mono_set hsub) measurableSet_Ioc
          intro β hβ
          have hd := sphereGaussianCenteredScaled24_doubling hN X hα hβ.1.le hβ.2
          have hd' : (sphereGaussianCenteredScaled24 α X+1)/Real.sqrt 2^25 ≤
              sphereGaussianCenteredScaled24 β X+1 := by
            rw [div_le_iff₀ hκ]
            linarith
          exact (mul_le_mul_of_nonneg_right hd'
            (Real.rpow_nonneg (hα.le.trans hβ.1.le) _)).trans_eq (mul_comm _ _)
      _ ≤ ∫ β in Ioc (0:ℝ) 1, β^(s/2-1)*(sphereGaussianCenteredScaled24 β X+1) := by
          apply setIntegral_mono_set hi
          · filter_upwards [ae_restrict_mem measurableSet_Ioc] with β hβ
            exact mul_nonneg (Real.rpow_nonneg hβ.1.le _)
              (sphereGaussianCenteredScaled24_add_one_nonneg hN hβ.1.le X)
          · exact hsub.eventuallyLE
      _ ≤ B := hB
  have hq : s/2 < 0 := by linarith
  have hqne : s/2 ≠ 0 := hq.ne
  have h2 : (2:ℝ)^(s/2)-1 < 0 := by
    have := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ) < 2) hq
    linarith
  have h2ne : (2:ℝ)^(s/2)-1 ≠ 0 := h2.ne
  have ha : 0 < α^(s/2) := Real.rpow_pos_of_pos hα _
  have hane : α^(s/2) ≠ 0 := ha.ne'
  have hκne : Real.sqrt 2^25 ≠ 0 := hκ.ne'
  have hcoef : 0 < Real.sqrt 2^25*(s/2)/(2^(s/2)-1) := by
    rw [mul_div_assoc]
    exact mul_pos hκ (div_pos_of_neg_of_neg hq h2)
  have hm := mul_le_mul_of_nonneg_right hl
    (mul_nonneg hcoef.le (inv_nonneg.mpr ha.le) :
      0 ≤ Real.sqrt 2^25*(s/2)/(2^(s/2)-1)*(α^(s/2))⁻¹)
  have he : (sphereGaussianCenteredScaled24 α X+1)/Real.sqrt 2^25*
      (α^(s/2)*(2^(s/2)-1)/(s/2))*(Real.sqrt 2^25*(s/2)/(2^(s/2)-1)*(α^(s/2))⁻¹) =
      sphereGaussianCenteredScaled24 α X+1 := by
    calc (sphereGaussianCenteredScaled24 α X+1)/Real.sqrt 2^25*
          (α^(s/2)*(2^(s/2)-1)/(s/2))*(Real.sqrt 2^25*(s/2)/(2^(s/2)-1)*(α^(s/2))⁻¹)
        = (sphereGaussianCenteredScaled24 α X+1)*((Real.sqrt 2^25*(Real.sqrt 2^25)⁻¹)*
            (α^(s/2)*(α^(s/2))⁻¹)*(((2:ℝ)^(s/2)-1)*((2:ℝ)^(s/2)-1)⁻¹)*(s/2*(s/2)⁻¹)) := by
          ring
      _ = sphereGaussianCenteredScaled24 α X+1 := by
          rw [mul_inv_cancel₀ hκne, mul_inv_cancel₀ hane, mul_inv_cancel₀ h2ne,
            mul_inv_cancel₀ hqne]
          ring
  rw [he] at hm
  rw [Real.rpow_neg hα.le]
  calc sphereGaussianCenteredScaled24 α X+1
      ≤ B*(Real.sqrt 2^25*(s/2)/(2^(s/2)-1)*(α^(s/2))⁻¹) := hm
    _ = Real.sqrt 2^25*(s/2)/(2^(s/2)-1)*B*(α^(s/2))⁻¹ := by ring

/-- The short-range cost controls the centered profile at large scales. -/
theorem sphereGaussianCenteredScaled24_le_shortRange {N : ℕ} (hN : 0 < N) {p D : ℝ}
    (hp : 0 ≤ p) (X : ConfigurationD 24 N)
    (hD : cellPairSum (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) X/(N:ℝ) ≤ D)
    {α : ℝ} (hα : 2 ≤ α) :
    sphereGaussianCenteredScaled24 α X ≤ 2^(p+1)*α^(-(p+1))*D := by
  classical
  have hα0 : 0 < α := by linarith
  have hA : 0 ≤ (2:ℝ)^(p+1)*α^(-(p+1)) := by positivity
  have hNR : 0 < (N:ℝ) := by exact_mod_cast hN
  have hrow : (∑ i, ∑ j ∈ Finset.univ.erase i,
      sphereGaussianKernel24 (sphereGaussianScale24 N α) (X i) (X j)) ≤
      (2:ℝ)^(p+1)*α^(-(p+1))*
        cellPairSum (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) X := by
    unfold cellPairSum
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    calc
      _ ≤ (∑ j ∈ Finset.univ.erase i, (2:ℝ)^(p+1)*α^(-(p+1))*shortRangeKernel24
        (sphereGaussianDensityFactor24 N) p (X i) (X j)) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [sphereGaussianScale24_eq_factor]
        exact gaussian24_le_shortRange_pointwise (sphereGaussianDensityFactor24_pos hN) hp hα
          (X.injective.ne (Finset.mem_erase.mp hj).1.symm)
      _ ≤ (∑ j : Fin N, (2:ℝ)^(p+1)*α^(-(p+1))*shortRangeKernel24
          (sphereGaussianDensityFactor24 N) p (X i) (X j)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun _ _ _ =>
          mul_nonneg hA (shortRangeKernel24_nonneg _ _ _ _))
  have hcenter : sphereGaussianCenteredScaled24 α X ≤
      (2:ℝ)^(p+1)*α^(-(p+1))*
        (cellPairSum (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) X/(N:ℝ)) := by
    have hoff := sphereGaussianOffDiagonal24_eq_full_sub (sphereGaussianScale24 N α) X
    have hbg := sphereGaussianBackground24_nonneg (sphereGaussianScale24 N α)
    have he : sphereGaussianOffDiagonal24 (sphereGaussianScale24 N α) X/(N:ℝ) =
        (∑ i, ∑ j, sphereGaussianKernel24 (sphereGaussianScale24 N α) (X i) (X j))/(N:ℝ)-1 := by
      rw [hoff, sub_div, div_self hNR.ne']
    calc
      _ ≤ sphereGaussianOffDiagonal24 (sphereGaussianScale24 N α) X/(N:ℝ) := by
        rw [he]
        unfold sphereGaussianCenteredScaled24
        nlinarith [mul_nonneg hNR.le hbg]
      _ ≤ ((2:ℝ)^(p+1)*α^(-(p+1))*
          cellPairSum (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) X)/(N:ℝ) :=
        div_le_div_of_nonneg_right hrow hNR.le
      _ = _ := by ring
  exact hcenter.trans (mul_le_mul_of_nonneg_left hD hA)

/-- An explicit majorant of the logarithmic profile integrand, with actual Gaussian budgets as
its constants. -/
def sphereGaussianLogMajorant24 (s p B W D α : ℝ) : ℝ :=
  if α ≤ 1/2 then (Real.sqrt 2^25*(s/2)/(2^(s/2)-1))*|B| *α^(-(s/2)-1)
  else if α ≤ 2 then 2*|W|
  else 2^(p+1)*|D| *α^(-(p+2))

theorem sphereGaussianLogMajorant24_coef_pos {s : ℝ} (hs0 : s < 0) :
    0 < Real.sqrt 2^25*(s/2)/(2^(s/2)-1) := by
  have hκ : 0 < Real.sqrt 2^25 := by positivity
  have hq : s/2 < 0 := by linarith
  have h2 : (2:ℝ)^(s/2)-1 < 0 := by
    have := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ) < 2) hq
    linarith
  rw [mul_div_assoc]
  exact mul_pos hκ (div_pos_of_neg_of_neg hq h2)

theorem sphereGaussianLogMajorant24_nonneg {s : ℝ} (hs0 : s < 0) (p B W D : ℝ) {α : ℝ}
    (hα : 0 < α) : 0 ≤ sphereGaussianLogMajorant24 s p B W D α := by
  have hc := sphereGaussianLogMajorant24_coef_pos hs0
  unfold sphereGaussianLogMajorant24
  split_ifs
  · exact mul_nonneg (mul_nonneg hc.le (abs_nonneg B)) (Real.rpow_nonneg hα.le _)
  · exact mul_nonneg (by norm_num) (abs_nonneg W)
  · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (abs_nonneg D))
      (Real.rpow_nonneg hα.le _)

theorem sphereGaussianLogMajorant24_integrable {s p : ℝ} (hs0 : s < 0) (hp : 0 ≤ p)
    (B W D : ℝ) : IntegrableOn (sphereGaussianLogMajorant24 s p B W D) (Ioi 0) := by
  have hi0 : IntegrableOn (fun α : ℝ => α^(-(s/2)-1)) (Ioc 0 (1/2)) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < -(s/2)-1)
      (a := 0) (b := 1/2)).1
  have hj0 : IntegrableOn (fun α : ℝ => α^(-(p+2))) (Ioi 2) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hi1 : IntegrableOn (fun α : ℝ =>
      (Real.sqrt 2^25*(s/2)/(2^(s/2)-1))*|B| *α^(-(s/2)-1)) (Ioc 0 (1/2)) := hi0.const_mul _
  have hm1 : IntegrableOn (fun _ : ℝ => 2*|W|) (Ioc (1/2) 2) :=
    integrableOn_const (by simp)
  have hj1 : IntegrableOn (fun α : ℝ => 2^(p+1)*|D| *α^(-(p+2))) (Ioi 2) := hj0.const_mul _
  have hi := hi1.integrable_indicator measurableSet_Ioc
  have hm := hm1.integrable_indicator measurableSet_Ioc
  have hj := hj1.integrable_indicator measurableSet_Ioi
  refine ((hi.add hm).add hj).integrableOn.congr_fun (fun α hα => ?_) measurableSet_Ioi
  have hα0 : (0:ℝ) < α := hα
  dsimp only [sphereGaussianLogMajorant24, Pi.add_apply]
  by_cases h1 : α ≤ 1/2
  · rw [ite_eq_left h1, indicator_of_mem (show α ∈ Ioc (0:ℝ) (1/2) from ⟨hα0, h1⟩),
      indicator_of_notMem (show α ∉ Ioc (1/2:ℝ) 2 from fun h => absurd h.1 (not_lt.mpr h1)),
      indicator_of_notMem (show α ∉ Ioi (2:ℝ) from fun h => by
        have : (2:ℝ) < α := h
        linarith), add_zero, add_zero]
  · have h1' : 1/2 < α := lt_of_not_ge h1
    by_cases h2 : α ≤ 2
    · rw [ite_eq_right h1, ite_eq_left h2,
        indicator_of_notMem (show α ∉ Ioc (0:ℝ) (1/2) from fun h => h1 h.2),
        indicator_of_mem (show α ∈ Ioc (1/2:ℝ) 2 from ⟨h1', h2⟩),
        indicator_of_notMem (show α ∉ Ioi (2:ℝ) from fun h => absurd h (not_lt.mpr h2)),
        zero_add, add_zero]
    · have h2' : 2 < α := lt_of_not_ge h2
      rw [ite_eq_right h1, ite_eq_right h2,
        indicator_of_notMem (show α ∉ Ioc (0:ℝ) (1/2) from fun h => h1 h.2),
        indicator_of_notMem (show α ∉ Ioc (1/2:ℝ) 2 from fun h => h2 h.2),
        indicator_of_mem (show α ∈ Ioi (2:ℝ) from h2'), zero_add, zero_add]

/-- The three Gaussian budgets bound the logarithmic profile integrand by the majorant. -/
theorem sphereGaussianCenteredScaled24_log_le_majorant {N : ℕ} (hN : 0 < N) {s p B W D : ℝ}
    (hs : -2 < s) (hs0 : s < 0) (hp : 0 ≤ p) (X : ConfigurationD 24 N)
    (hB : (∫ β in Ioc (0:ℝ) 1, β^(s/2-1)*(sphereGaussianCenteredScaled24 β X+1)) ≤ B)
    (hW : sphereGaussianFullScaled24 (1/2) X ≤ W)
    (hD : cellPairSum (shortRangeKernel24 (sphereGaussianDensityFactor24 N) p) X/(N:ℝ) ≤ D)
    {α : ℝ} (hα : 0 < α) :
    α⁻¹*(sphereGaussianCenteredScaled24 α X+(Ioo (0:ℝ) 1).indicator 1 α) ≤
      sphereGaussianLogMajorant24 s p B W D α := by
  have hinv : 0 < α⁻¹ := inv_pos.mpr hα
  have hc := sphereGaussianLogMajorant24_coef_pos hs0
  unfold sphereGaussianLogMajorant24
  by_cases h1 : α ≤ 1/2
  · rw [ite_eq_left h1, indicator_of_mem (show α ∈ Ioo (0:ℝ) 1 from ⟨hα, by linarith⟩),
      Pi.one_apply]
    have hb := sphereGaussianCenteredScaled24_macro_budget_bound hN hs hs0 X hB hα h1
    have hpow : 0 ≤ α^(-(s/2)) := Real.rpow_nonneg hα.le _
    have hb' : sphereGaussianCenteredScaled24 α X+1 ≤
        (Real.sqrt 2^25*(s/2)/(2^(s/2)-1))*|B| *α^(-(s/2)) :=
      hb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_abs_self B) hc.le) hpow)
    have hsplit : α^(-(s/2)-1) = α^(-(s/2))*α⁻¹ := by
      rw [Real.rpow_sub_one hα.ne', div_eq_mul_inv]
    rw [hsplit]
    calc α⁻¹*(sphereGaussianCenteredScaled24 α X+1)
        ≤ α⁻¹*((Real.sqrt 2^25*(s/2)/(2^(s/2)-1))*|B| *α^(-(s/2))) :=
          mul_le_mul_of_nonneg_left hb' hinv.le
      _ = (Real.sqrt 2^25*(s/2)/(2^(s/2)-1))*|B| *(α^(-(s/2))*α⁻¹) := by ring
  · have h1' : 1/2 < α := lt_of_not_ge h1
    rw [ite_eq_right h1]
    have hind : (Ioo (0:ℝ) 1).indicator (1 : ℝ → ℝ) α ≤ 1 := by
      by_cases hm : α ∈ Ioo (0:ℝ) 1
      · rw [indicator_of_mem hm, Pi.one_apply]
      · rw [indicator_of_notMem hm]
        exact zero_le_one
    by_cases h2 : α ≤ 2
    · rw [ite_eq_left h2]
      have hfull := (sphereGaussianCenteredScaled24_add_one_le_full α X).trans
        ((sphereGaussianFullScaled24_anti hN X h1'.le).trans hW)
      have hval : sphereGaussianCenteredScaled24 α X+(Ioo (0:ℝ) 1).indicator 1 α ≤ |W| := by
        have := le_abs_self W
        linarith
      have hinv2 : α⁻¹ ≤ 2 :=
        inv_le_of_inv_le₀ (by norm_num) (by rw [inv_eq_one_div]; exact h1'.le)
      calc α⁻¹*(sphereGaussianCenteredScaled24 α X+(Ioo (0:ℝ) 1).indicator 1 α)
          ≤ α⁻¹*|W| := mul_le_mul_of_nonneg_left hval hinv.le
        _ ≤ 2*|W| := mul_le_mul_of_nonneg_right hinv2 (abs_nonneg W)
    · have h2' : 2 < α := lt_of_not_ge h2
      rw [ite_eq_right h2, indicator_of_notMem (show α ∉ Ioo (0:ℝ) 1 from fun h => by
        have : α < 1 := h.2
        linarith), add_zero]
      have hb := sphereGaussianCenteredScaled24_le_shortRange hN hp X hD h2'.le
      have hA : 0 ≤ (2:ℝ)^(p+1)*α^(-(p+1)) := by positivity
      have hb' : sphereGaussianCenteredScaled24 α X ≤ 2^(p+1)*α^(-(p+1))*|D| :=
        hb.trans (mul_le_mul_of_nonneg_left (le_abs_self D) hA)
      have hsplit : α^(-(p+2)) = α^(-(p+1))*α⁻¹ := by
        rw [show -(p+2) = -(p+1)-1 by ring, Real.rpow_sub_one hα.ne', div_eq_mul_inv]
      rw [hsplit]
      calc α⁻¹*sphereGaussianCenteredScaled24 α X
          ≤ α⁻¹*(2^(p+1)*α^(-(p+1))*|D|) := mul_le_mul_of_nonneg_left hb' hinv.le
        _ = 2^(p+1)*|D| *(α^(-(p+1))*α⁻¹) := by ring

/-- The pointwise window gives the pointwise upper limit of the logarithmic profile integrand. -/
theorem sphereGaussianCenteredScaled24_log_profile_upper_eventually
    {N : ℕ → ℕ} (hNt : Tendsto N atTop atTop) (hN : ∀ k, 0 < N k)
    (X : ∀ k, ConfigurationD 24 (N k)) {α : ℝ} (hα : 0 < α)
    (hp : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      sphereGaussianFullScaled24 α (X k) ≤ leechGaussianThetaReal24 α+ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      α⁻¹*(sphereGaussianCenteredScaled24 α (X k)+(Ioo (0:ℝ) 1).indicator 1 α) ≤
        leechGaussianLogProfile24 α+ε := by
  intro ε hε
  have he : α^((0:ℝ)/2-1) = α⁻¹ := by
    rw [show (0:ℝ)/2-1 = -1 by norm_num, Real.rpow_neg_one]
  filter_upwards [sphereGaussianCenteredScaled24_weighted_profile_upper_eventually 0 hNt hN X hα
    hp ε hε] with k hk
  unfold leechGaussianRieszProfileRpow24 at hk
  rw [he] at hk
  unfold leechGaussianLogProfile24
  linarith [mul_add α⁻¹ (sphereGaussianCenteredScaled24 α (X k)) ((Ioo (0:ℝ) 1).indicator 1 α),
    mul_add α⁻¹ (leechGaussianThetaReal24 α-(α^12)⁻¹-1) ((Ioo (0:ℝ) 1).indicator 1 α)]

/-- The Gaussian-only upper bridge for the logarithmic energy: a macroscopic budget at a
negative exponent, a bound of the full profile at `α = 1/2`, a short-range cost and the
pointwise window give `limsup normalizedEnergyLog24 ≤ C_log`. -/
theorem sphere24_log_upper_of_gaussian_budgets {s p : ℝ} (hs : -2 < s) (hs0 : s < 0)
    (hp : 0 ≤ p) {N : ℕ → ℕ} (hNt : Tendsto N atTop atTop) (hN : ∀ k, 0 < N k)
    (X : ∀ k, ConfigurationD 24 (N k)) (B W D : ℝ)
    (hB : ∀ k, (∫ β in Ioc (0:ℝ) 1,
      β^(s/2-1)*(sphereGaussianCenteredScaled24 β (X k)+1)) ≤ B)
    (hW : ∀ k, sphereGaussianFullScaled24 (1/2) (X k) ≤ W)
    (hD : ∀ k, cellPairSum (shortRangeKernel24 (sphereGaussianDensityFactor24 (N k)) p)
      (X k)/(N k:ℝ) ≤ D)
    (hprof : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      sphereGaussianFullScaled24 α (X k) ≤ leechGaussianThetaReal24 α+ε) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
      normalizedEnergyLog24 (X k) ≤ sphereLogCoefficient24+η := by
  intro η hη
  by_contra hcon
  rw [not_eventually] at hcon
  obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hcon
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hJ : ∀ n, (∫ α : ℝ in Ioi 0, leechGaussianLogProfile24 α)+2*η ≤
      ∫ α : ℝ in Ioi 0, α⁻¹*(sphereGaussianCenteredScaled24 α (X (φ n))+
        (Ioo (0:ℝ) 1).indicator 1 α) := by
    intro n
    have h1 := normalizedEnergyLog24_gaussian_mellin (hN (φ n)) (X (φ n))
    have h2 := lt_of_not_ge (hbad n)
    unfold sphereLogCoefficient24 at h2
    rw [h1] at h2
    unfold sphereLogProfileIntegral24 at h2
    linarith
  have h := integral_ge_of_eventual_upper_profile24
    (μ := volume.restrict (Ioi (0:ℝ))) (g := leechGaussianLogProfile24)
    (G := sphereGaussianLogMajorant24 s p B W D)
    (f := fun n α => α⁻¹*(sphereGaussianCenteredScaled24 α (X (φ n))+
      (Ioo (0:ℝ) 1).indicator 1 α))
    leechGaussianLogProfile24_integrable
    (fun n => sphereGaussianCenteredScaled24_log_integrable (hN (φ n)) (X (φ n)))
    (sphereGaussianLogMajorant24_integrable hs0 hp B W D)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact sphereGaussianLogMajorant24_nonneg hs0 p B W D hα)
    (fun n => by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact sphereGaussianCenteredScaled24_log_le_majorant (hN (φ n)) hs hs0 hp (X (φ n))
        (hB (φ n)) (hW (φ n)) (hD (φ n)) hα)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact fun ε hε => hφt.eventually
        (sphereGaussianCenteredScaled24_log_profile_upper_eventually hNt hN X hα
          (hprof α hα) ε hε))
    hJ
  linarith

end SphericalRiesz
end
end

section

/-! The gap of the rational size ceiling with a logarithmic factor, and the arithmetic of the
normalized logarithmic energy of a subconfiguration.

For `M = (d m)²⁴`, the least rational size above `N`, the relative gap satisfies
`(M - N) N^(1/24) ≤ 24 d M` (Bernoulli's inequality), hence
`(1 - (N-1)/(M-1)) (1 + log M) → 0`: the gap beats the logarithm.  This is the size condition
under which the normalized logarithmic energy `(E_log - W N² + (N/24) log N)/N` passes from a
configuration of `M` points to a subconfiguration of `N` points: if the pair average does not
increase, then

`nE(Y) ≤ θ nE(X) + (1-θ)(-W) + (1/24)(log N - θ log M)`,  `θ = (N-1)/(M-1)`,

and the right side is at most `c + (|c|+|W|+1)(1-θ)(1+log M)` when `nE(X) ≤ c`.  Only real
arithmetic and the size ceiling are used; no sphere, energy or configuration appears. -/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace SphericalRiesz

/-- Arithmetic of the normalized logarithmic energy of a subconfiguration: `a`, `b` are the
energies of the configurations of `M` and `N` points. -/
theorem logSubconfiguration_arith {a b W lN lM N M : ℝ} (hN : 1 < N) (hNM : N ≤ M)
    (he : b/(N*(N-1)) ≤ a/(M*(M-1))) :
    (b-W*N^2+N/24*lN)/N ≤
      (N-1)/(M-1)*((a-W*M^2+M/24*lM)/M)+(1-(N-1)/(M-1))*(-W)+
        (1/24)*(lN-(N-1)/(M-1)*lM) := by
  have hN0 : 0 < N := by linarith
  have hM0 : 0 < M := by linarith
  have hN1 : 0 < N-1 := by linarith
  have hM1 : 0 < M-1 := by linarith
  have hM0' : M ≠ 0 := hM0.ne'
  have hM1' : M-1 ≠ 0 := hM1.ne'
  have hb : b ≤ a/(M*(M-1))*(N*(N-1)) := (div_le_iff₀ (mul_pos hN0 hN1)).mp he
  rw [div_le_iff₀ hN0]
  have hθ : (N-1)/(M-1)*(M-1) = N-1 := div_mul_cancel₀ _ hM1'
  have hA : a/(M*(M-1))*(M*(M-1)) = a := div_mul_cancel₀ _ (mul_ne_zero hM0' hM1')
  have hE : (a-W*M^2+M/24*lM)/M*M = a-W*M^2+M/24*lM := div_mul_cancel₀ _ hM0'
  have key : ((N-1)/(M-1)*((a-W*M^2+M/24*lM)/M)+(1-(N-1)/(M-1))*(-W)+
      (1/24)*(lN-(N-1)/(M-1)*lM))*N = a/(M*(M-1))*(N*(N-1))-W*N^2+N/24*lN := by
    apply mul_right_cancel₀ hM0'
    linear_combination ((N-1)/(M-1)*N)*hE-((N-1)/(M-1)*N)*hA+
      (a/(M*(M-1))*N*M-W*N*M)*hθ
  rw [key]
  linarith

/-- From the three-term bound of a subconfiguration to a bound with one error term. -/
theorem logSubconfiguration_bound {x y c W lN lM θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hl : lN ≤ lM) (hlM : 0 ≤ lM) (hx : x ≤ c)
    (hy : y ≤ θ*x+(1-θ)*(-W)+(1/24)*(lN-θ*lM)) :
    y ≤ c+(|c|+|W|+1)*((1-θ)*(1+lM)) := by
  have h1θ : 0 ≤ 1-θ := sub_nonneg.mpr hθ1
  have h1 : θ*x ≤ θ*c := mul_le_mul_of_nonneg_left hx hθ0
  have h2 : θ*c ≤ c+(1-θ)*|c| := by
    have h := mul_nonneg h1θ (by linarith [neg_abs_le c] : 0 ≤ c+|c|)
    nlinarith [h]
  have h3 : (1-θ)*(-W) ≤ (1-θ)*|W| := mul_le_mul_of_nonneg_left (neg_le_abs W) h1θ
  have h4 : (1/24)*(lN-θ*lM) ≤ (1-θ)*lM := by
    have h := mul_nonneg h1θ hlM
    nlinarith [h]
  have h5 : 0 ≤ (|c|+|W|)*((1-θ)*lM) :=
    mul_nonneg (add_nonneg (abs_nonneg c) (abs_nonneg W)) (mul_nonneg h1θ hlM)
  nlinarith [h1, h2, h3, h4, h5, h1θ]

/-- The gap of the rational size ceiling: `(M - N) N^(1/24) ≤ 24 d M`. -/
theorem rationalSizeCeiling24_gap_le (d N : ℕ) (hd : 0 < d) (hN : 0 < N) :
    ((rationalSizeCeiling24 d N:ℝ)-(N:ℝ))*(N:ℝ)^(1/24:ℝ) ≤
      24*(d:ℝ)*(rationalSizeCeiling24 d N:ℝ) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = (N:ℝ)^(1/24:ℝ) := ⟨_, rfl⟩
  have ha : 0 < a := by
    rw [hadef]
    exact Real.rpow_pos_of_pos hNR _
  have hNa : (N:ℝ) = a^24 := by
    rw [hadef]
    exact (real_twentyFourth_root_pow N).symm
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = (d:ℝ)*(rationalSizeIndex24 d N:ℝ) := ⟨_, rfl⟩
  have hceil1 : a/(d:ℝ) ≤ (rationalSizeIndex24 d N:ℝ) := by
    rw [hadef]
    exact Nat.le_ceil _
  have hceil2 : (rationalSizeIndex24 d N:ℝ) < a/(d:ℝ)+1 := by
    rw [hadef]
    exact Nat.ceil_lt_add_one (div_nonneg (Real.rpow_nonneg hNR.le _) hdR.le)
  have hab : a ≤ b := by
    rw [hbdef]
    have h := (div_le_iff₀ hdR).mp hceil1
    linarith [mul_comm (d:ℝ) (rationalSizeIndex24 d N:ℝ)]
  have hbd : b ≤ a+d := by
    rw [hbdef]
    have h := mul_lt_mul_of_pos_left hceil2 hdR
    have e : (d:ℝ)*(a/(d:ℝ)+1) = a+d := by
      rw [mul_add, mul_div_cancel₀ _ hdR.ne', mul_one]
    linarith
  have hb : 0 < b := ha.trans_le hab
  have hMb : (rationalSizeCeiling24 d N:ℝ) = b^24 := by
    rw [hbdef]
    unfold rationalSizeCeiling24
    rw [Nat.cast_pow, Nat.cast_mul]
  have hb24 : 0 < b^24 := pow_pos hb 24
  have hB := one_add_mul_sub_le_pow (a := a/b) (by linarith [div_nonneg ha.le hb.le]) 24
  have h1 : b^24-a^24 ≤ 24*(1-a/b)*b^24 := by
    have h := mul_le_mul_of_nonneg_right hB hb24.le
    rw [div_pow, div_mul_cancel₀ _ hb24.ne'] at h
    push_cast at h
    nlinarith [h]
  have hr : 1-a/b ≤ (d:ℝ)/b := by
    rw [one_sub_div hb.ne']
    exact div_le_div_of_nonneg_right (by linarith) hb.le
  have hab1 : a/b ≤ 1 := (div_le_one hb).mpr hab
  rw [← hadef, hMb, hNa]
  calc (b^24-a^24)*a ≤ (24*(1-a/b)*b^24)*a := mul_le_mul_of_nonneg_right h1 ha.le
    _ ≤ (24*((d:ℝ)/b)*b^24)*a :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hr (by norm_num)) hb24.le) ha.le
    _ = 24*(d:ℝ)*b^24*(a/b) := by ring
    _ ≤ 24*(d:ℝ)*b^24*1 := mul_le_mul_of_nonneg_left hab1 (by positivity)
    _ = 24*(d:ℝ)*b^24 := mul_one _

/-- The relative gap of the rational size ceiling beats the logarithm:
`(1 - (N-1)/(M-1)) (1 + log M) → 0` for `M = rationalSizeCeiling24 d N`. -/
theorem rationalSizeCeiling24_log_gap_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => (1-((N:ℝ)-1)/((rationalSizeCeiling24 d N:ℝ)-1))*
      (1+Real.log (rationalSizeCeiling24 d N:ℝ))) atTop (𝓝 0) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hcast : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun N : ℕ => (N:ℝ)^(-(1/24:ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1/24)).comp hcast
  have h2 : Tendsto (fun N : ℕ => Real.log (N:ℝ)/(N:ℝ)^(1/24:ℝ)) atTop (𝓝 0) :=
    ((isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/24)).tendsto_div_nhds_zero).comp hcast
  have hU : Tendsto (fun N : ℕ => 48*(d:ℝ)*((1+Real.log 2)*(N:ℝ)^(-(1/24:ℝ))+
      Real.log (N:ℝ)/(N:ℝ)^(1/24:ℝ))) atTop (𝓝 0) := by
    have h := ((h1.const_mul (1+Real.log 2)).add h2).const_mul (48*(d:ℝ))
    simpa only [mul_zero, add_zero] using h
  have hratio := (tendsto_order.mp (rationalSizeCeiling24_ratio_tendsto d hd)).2 2 (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hNR : (2:ℝ) ≤ N := by exact_mod_cast hN
    have hMN : (N:ℝ) ≤ (rationalSizeCeiling24 d N:ℝ) := by
      exact_mod_cast rationalSizeCeiling24_ge d N hd
    have hM1 : 0 < (rationalSizeCeiling24 d N:ℝ)-1 := by linarith
    have hθ : ((N:ℝ)-1)/((rationalSizeCeiling24 d N:ℝ)-1) ≤ 1 :=
      (div_le_one hM1).mpr (by linarith)
    have hlog : 0 ≤ Real.log (rationalSizeCeiling24 d N:ℝ) := Real.log_nonneg (by linarith)
    exact mul_nonneg (by linarith) (by linarith)
  · filter_upwards [eventually_ge_atTop 2, hratio] with N hN hr
    have hNR : (2:ℝ) ≤ N := by exact_mod_cast hN
    have hN0 : (0:ℝ) < N := by linarith
    have hMN : (N:ℝ) ≤ (rationalSizeCeiling24 d N:ℝ) := by
      exact_mod_cast rationalSizeCeiling24_ge d N hd
    have hM0 : (0:ℝ) < (rationalSizeCeiling24 d N:ℝ) := by linarith
    have hM1 : 0 < (rationalSizeCeiling24 d N:ℝ)-1 := by linarith
    have hM2N : (rationalSizeCeiling24 d N:ℝ) < 2*(N:ℝ) := (div_lt_iff₀ hN0).mp hr
    have ha : 0 < (N:ℝ)^(1/24:ℝ) := Real.rpow_pos_of_pos hN0 _
    have hgap := rationalSizeCeiling24_gap_le d N hd (by omega)
    have ht : 1-((N:ℝ)-1)/((rationalSizeCeiling24 d N:ℝ)-1) =
        ((rationalSizeCeiling24 d N:ℝ)-(N:ℝ))/((rationalSizeCeiling24 d N:ℝ)-1) := by
      rw [one_sub_div hM1.ne']
      congr 1
      ring
    have ht0 : 0 ≤ ((rationalSizeCeiling24 d N:ℝ)-(N:ℝ))/((rationalSizeCeiling24 d N:ℝ)-1) :=
      div_nonneg (by linarith) hM1.le
    have ht' : ((rationalSizeCeiling24 d N:ℝ)-(N:ℝ))/((rationalSizeCeiling24 d N:ℝ)-1) ≤
        48*(d:ℝ)/(N:ℝ)^(1/24:ℝ) := by
      rw [div_le_div_iff₀ hM1 ha]
      have h48 : 24*(d:ℝ)*(rationalSizeCeiling24 d N:ℝ) ≤
          48*(d:ℝ)*((rationalSizeCeiling24 d N:ℝ)-1) := by
        nlinarith [mul_nonneg hdR.le (by linarith : (0:ℝ) ≤ (rationalSizeCeiling24 d N:ℝ)-2)]
      linarith
    have hlogM : Real.log (rationalSizeCeiling24 d N:ℝ) ≤ Real.log 2+Real.log (N:ℝ) := by
      rw [← Real.log_mul (by norm_num) hN0.ne']
      exact Real.log_le_log hM0 hM2N.le
    have hlog0 : 0 ≤ Real.log (rationalSizeCeiling24 d N:ℝ) := Real.log_nonneg (by linarith)
    have hc0 : 0 ≤ 48*(d:ℝ)/(N:ℝ)^(1/24:ℝ) := by positivity
    rw [ht, Real.rpow_neg hN0.le]
    calc ((rationalSizeCeiling24 d N:ℝ)-(N:ℝ))/((rationalSizeCeiling24 d N:ℝ)-1)*
          (1+Real.log (rationalSizeCeiling24 d N:ℝ))
        ≤ 48*(d:ℝ)/(N:ℝ)^(1/24:ℝ)*(1+Real.log 2+Real.log (N:ℝ)) :=
          mul_le_mul ht' (by linarith) (by linarith) hc0
      _ = 48*(d:ℝ)*((1+Real.log 2)*((N:ℝ)^(1/24:ℝ))⁻¹+
          Real.log (N:ℝ)/(N:ℝ)^(1/24:ℝ)) := by ring

end SphericalRiesz
end
end

section

/-! The logarithmic energy on S²⁴: sharp upper bound at every large `N` and the two-sided
asymptotics (stage LOG).

For every tolerance index the block construction gives configurations at all rational sizes
`(d m)²⁴` with a Gaussian window, a macroscopic budget at the exponent `s = -1` and a bounded
short-range cost.  A diagonal choice over the tolerance index gives one configuration of size
`M(N) ≥ N` for every large `N`, with `(1 - (N-1)/(M-1))(1 + log M) → 0`; the Gaussian-only
bridge bounds its normalized logarithmic energy by `C_log + η/2`.  A subconfiguration of `N`
points whose pair average of `-log |x_i - x_j|` does not exceed that of the whole configuration
(no sign condition is needed) has normalized logarithmic energy at most

`θ nE(X) + (1-θ)(-W) + (1/24)(log N - θ log M)`,  `θ = (N-1)/(M-1)`,

which is at most `C_log + η` for large `N`.  The upper half uses no Gaussian certificate; the
stratification of the residual regions is proved in `Riesz.SphereStratification24`.  The
two-sided statement assumes all-scale Leech contact certificates (stage G24) for its lower
half. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalRiesz

/-- The ordered off-diagonal logarithmic energy as a full pair sum with zero diagonal. -/
theorem energyLogD_eq_orderedPair {d N : ℕ} (X : ConfigurationD d N) :
    energyLogD X = finiteOrderedPair
      (fun i j : Fin N => if i = j then (0:ℝ) else -Real.log (dist (X i) (X j))) := by
  unfold energyLogD finiteOrderedPair
  refine Finset.sum_congr rfl fun i _ => ?_
  show (∑ j ∈ Finset.univ.erase i, -Real.log (dist (X i) (X j))) =
    ∑ j : Fin N, (if i = j then (0:ℝ) else -Real.log (dist (X i) (X j)))
  rw [← Finset.add_sum_erase Finset.univ
    (fun j : Fin N => if i = j then (0:ℝ) else -Real.log (dist (X i) (X j)))
    (Finset.mem_univ i), ite_eq_left rfl, zero_add]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [ite_eq_right (Finset.ne_of_mem_erase hj).symm]

/-- A subconfiguration of `N` points whose pair average of the logarithmic energy is at most
that of the whole configuration. -/
theorem energyLogD_exists_subconfiguration {d : ℕ} (N M : ℕ) (hN : 2 ≤ N) (hNM : N ≤ M)
    (X : ConfigurationD d M) :
    ∃ e : Fin N ↪ Fin M,
      energyLogD (e.trans X)/((N:ℝ)*(N-1)) ≤ energyLogD X/((M:ℝ)*(M-1)) := by
  obtain ⟨e, he⟩ := finiteOrderedPair_exists_subembedding N M hN hNM
    (fun i j : Fin M => if i = j then (0:ℝ) else -Real.log (dist (X i) (X j)))
    (fun i j => by
      show (if i = j then (0:ℝ) else -Real.log (dist (X i) (X j))) =
        if j = i then (0:ℝ) else -Real.log (dist (X j) (X i))
      by_cases h : i = j
      · subst h
        rfl
      · rw [ite_eq_right h, ite_eq_right (Ne.symm h), dist_comm])
    (fun i => ite_eq_left rfl)
  refine ⟨e, ?_⟩
  have hX := energyLogD_eq_orderedPair X
  have hY : energyLogD (e.trans X) = finiteOrderedPair (fun i j : Fin N =>
      if e i = e j then (0:ℝ) else -Real.log (dist (X (e i)) (X (e j)))) := by
    rw [energyLogD_eq_orderedPair]
    unfold finiteOrderedPair
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    show (if i = j then (0:ℝ) else -Real.log (dist ((e.trans X) i) ((e.trans X) j))) =
      if e i = e j then (0:ℝ) else -Real.log (dist (X (e i)) (X (e j)))
    by_cases h : i = j
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl]
    · have h' : e i ≠ e j := fun he' => h (e.injective he')
      rw [ite_eq_right h, ite_eq_right h']
      rfl
  rw [hY, hX]
  exact he

/-- A subconfiguration of `N` points keeps the normalized logarithmic energy on S²⁴ up to the
gap terms, `θ = (N-1)/(M-1)`. -/
theorem normalizedEnergyLog24_exists_subconfiguration (N M : ℕ) (hN : 2 ≤ N) (hNM : N ≤ M)
    (X : ConfigurationD 24 M) :
    ∃ Y : ConfigurationD 24 N, normalizedEnergyLog24 Y ≤
      ((N:ℝ)-1)/((M:ℝ)-1)*normalizedEnergyLog24 X+
        (1-((N:ℝ)-1)/((M:ℝ)-1))*(-sphereLogConst24)+
        (1/24)*(Real.log N-((N:ℝ)-1)/((M:ℝ)-1)*Real.log M) := by
  obtain ⟨e, he⟩ := energyLogD_exists_subconfiguration N M hN hNM X
  refine ⟨e.trans X, ?_⟩
  have hNR : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNM' : (N:ℝ) ≤ M := by exact_mod_cast hNM
  unfold normalizedEnergyLog24
  exact logSubconfiguration_arith hNR hNM' he

/-- The residual constant of the logarithmic blocks is nonnegative. -/
theorem leechLogBlockConst24_nonneg {s p Bst : ℝ} (hs : -2 < s) (hp11 : p < 11)
    (hBst : 0 ≤ Bst) : 0 ≤ leechLogBlockConst24 s p Bst := by
  have hp2 : 0 < s/2+1 := by linarith
  have h11 : 0 < 11-p := by linarith
  unfold leechLogBlockConst24 leechNegBlockConst24
  positivity

/-- The macroscopic budget of a block at the cutoff `w = 1` is bounded uniformly in the
tolerance index. -/
theorem leechLogBlock_macro_uniform {s A C L : ℝ} (hs : -2 < s) (hC : 0 ≤ C) (hL : 1 ≤ L) :
    2*(A*((1:ℝ)^(s/2+2)/(s/2+2))+1/L*((1:ℝ)^(s/2+1)/(s/2+1)))+2*(C/L^2) ≤
      2*(A/(s/2+2)+1/(s/2+1))+2*C := by
  have hp2 : 0 < s/2+1 := by linarith
  have hL0 : 0 < L := by linarith
  have h1L : 1/L ≤ 1 := (div_le_one hL0).mpr hL
  have h2 : 1/L*(1/(s/2+1)) ≤ 1/(s/2+1) := by
    calc 1/L*(1/(s/2+1)) ≤ 1*(1/(s/2+1)) :=
          mul_le_mul_of_nonneg_right h1L (one_div_pos.mpr hp2).le
      _ = 1/(s/2+1) := one_mul _
  have h3 : C/L^2 ≤ C := div_le_self hC (one_le_pow₀ hL)
  have e1 : A*(1/(s/2+2)) = A/(s/2+2) := mul_one_div _ _
  rw [Real.one_rpow, Real.one_rpow]
  linarith

/-- The window of a block at `α = 1/2` is bounded uniformly in the tolerance index. -/
theorem leechLogBlock_window_uniform {C L : ℝ} (hC : 0 ≤ C) (hL : 2 ≤ L) :
    (1+1/L)*(leechGaussianThetaReal24 (1/2*(1-1/L)^2)+2/L)+(1+L)*(C/L^2) ≤
      2*(leechGaussianThetaReal24 (1/8)+1)+C := by
  have hL0 : 0 < L := by linarith
  have h1L : 1/L ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hL
  have h1L0 : 0 < 1/L := one_div_pos.mpr hL0
  have h2L : 2/L ≤ 1 := (div_le_one hL0).mpr hL
  have h2L0 : 0 ≤ 2/L := div_nonneg (by norm_num) hL0.le
  have hge : (1/2:ℝ) ≤ 1-1/L := by linarith
  have hsq : (1/2:ℝ)^2 ≤ (1-1/L)^2 := pow_le_pow_left₀ (by norm_num) hge 2
  have harg : (1/8:ℝ) ≤ 1/2*(1-1/L)^2 := by nlinarith [hsq]
  have hθ := leechGaussianThetaReal24_anti (by norm_num : (0:ℝ) < 1/8) harg
  have hθ1 := leechGaussianThetaReal24_ge_one (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/8) harg)
  have hfirst : (1+1/L)*(leechGaussianThetaReal24 (1/2*(1-1/L)^2)+2/L) ≤
      2*(leechGaussianThetaReal24 (1/8)+1) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  have hL2 : 0 < L^2 := pow_pos hL0 2
  have hpoly : 1+L ≤ L^2 := by nlinarith [sq_nonneg (L-2)]
  have hsecond : (1+L)*(C/L^2) ≤ C := by
    calc (1+L)*(C/L^2) = C*((1+L)/L^2) := by ring
      _ ≤ C*1 := mul_le_mul_of_nonneg_left ((div_le_one hL2).mpr hpoly) hC
      _ = C := mul_one C
  linarith

/-- Configurations of every large size with normalized logarithmic energy at most `C_log + η`,
for one choice of the auxiliary exponents and given the stratification of the residual
regions. -/
theorem sphere24_log_upper_allN_of_block {s p : ℝ} (hs : -2 < s) (hs0 : s < 0) (hp0 : 0 ≤ p)
    (hp11 : p < 11) {Bst : ℝ} (hBst : 0 ≤ Bst) (hstrat : LeechResidualStratifiable24 Bst) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 24 N,
      normalizedEnergyLog24 Y ≤ sphereLogCoefficient24+η := by
  intro η hη
  have hC0 := leechLogBlockConst24_nonneg (p := p) hs hp11 hBst
  -- blocks for every tolerance index
  have hblocks : ∀ j : ℕ, ∃ d : ℕ, 0 < d ∧ ∀ᶠ m : ℕ in atTop,
      ∃ X : ConfigurationD 24 ((d*m)^24),
        (∀ α : ℝ, 1/((j+2:ℕ):ℝ) ≤ α → sphereGaussianFullScaled24 α X ≤
          (1+1/((j+2:ℕ):ℝ))*(leechGaussianThetaReal24 (α*(1-1/((j+2:ℕ):ℝ))^2)+2/((j+2:ℕ):ℝ))+
            (1+((j+2:ℕ):ℝ))*(leechLogBlockConst24 s p Bst/((j+2:ℕ):ℝ)^2)) ∧
        (∀ w : ℝ, 0 < w → w ≤ 1 →
          (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled24 α X+1)) ≤
            2*(leechMacroConstA24*(w^(s/2+2)/(s/2+2))+
              1/((j+2:ℕ):ℝ)*(w^(s/2+1)/(s/2+1)))+
              2*(leechLogBlockConst24 s p Bst/((j+2:ℕ):ℝ)^2)) ∧
        cellPairSum (shortRangeKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) p) X/
          (((d*m)^24:ℕ):ℝ) ≤ leechLogBlockTailConst24 s p Bst :=
    fun j => exists_leech_log_block24 hs hs0 hp0 hp11 hBst hstrat (L := j+2) (by omega)
  choose d hd hev using hblocks
  -- every tolerance index reaches every large N
  have hP : ∀ j : ℕ, ∀ᶠ N : ℕ in atTop,
      (1-((N:ℝ)-1)/((rationalSizeCeiling24 (d j) N:ℝ)-1))*
        (1+Real.log (rationalSizeCeiling24 (d j) N:ℝ)) ≤ 1/((j:ℝ)+1) ∧
      ∃ X : ConfigurationD 24 (rationalSizeCeiling24 (d j) N),
        (∀ α : ℝ, 1/((j+2:ℕ):ℝ) ≤ α → sphereGaussianFullScaled24 α X ≤
          (1+1/((j+2:ℕ):ℝ))*(leechGaussianThetaReal24 (α*(1-1/((j+2:ℕ):ℝ))^2)+2/((j+2:ℕ):ℝ))+
            (1+((j+2:ℕ):ℝ))*(leechLogBlockConst24 s p Bst/((j+2:ℕ):ℝ)^2)) ∧
        (∀ w : ℝ, 0 < w → w ≤ 1 →
          (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled24 α X+1)) ≤
            2*(leechMacroConstA24*(w^(s/2+2)/(s/2+2))+
              1/((j+2:ℕ):ℝ)*(w^(s/2+1)/(s/2+1)))+
              2*(leechLogBlockConst24 s p Bst/((j+2:ℕ):ℝ)^2)) ∧
        cellPairSum (shortRangeKernel24
          (sphereGaussianDensityFactor24 (rationalSizeCeiling24 (d j) N)) p) X/
          ((rationalSizeCeiling24 (d j) N:ℕ):ℝ) ≤ leechLogBlockTailConst24 s p Bst := by
    intro j
    have h1 := (rationalSizeIndex24_tendsto (d j) (hd j)).eventually (hev j)
    have hgap : (0:ℝ) < 1/((j:ℝ)+1) := by positivity
    have h2 := (tendsto_order.mp (rationalSizeCeiling24_log_gap_tendsto (d j) (hd j))).2 _ hgap
    filter_upwards [h1, h2] with N hN1 hN2
    exact ⟨hN2.le, hN1⟩
  obtain ⟨J, hJt, hJ⟩ := exists_diagonal_eventually hP
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hJ
  obtain ⟨N₂, hN₂1, hN₂2⟩ : ∃ N₂ : ℕ, N₁ ≤ N₂ ∧ 2 ≤ N₂ :=
    ⟨max N₁ 2, le_max_left _ _, le_max_right _ _⟩
  -- one configuration for every index k, of size M k ≥ N₂ + k
  have hQ := fun k : ℕ => hN₁ (N₂+k) (hN₂1.trans (Nat.le_add_right N₂ k))
  choose hgapk Z hZW hZM hZT using hQ
  have hge : ∀ k : ℕ, N₂+k ≤ rationalSizeCeiling24 (d (J (N₂+k))) (N₂+k) := fun k =>
    rationalSizeCeiling24_ge _ _ (hd _)
  have hMt : Tendsto (fun k : ℕ => rationalSizeCeiling24 (d (J (N₂+k))) (N₂+k)) atTop atTop :=
    tendsto_atTop_mono (fun k => (Nat.le_add_left k N₂).trans (hge k)) tendsto_id
  have hMpos : ∀ k : ℕ, 0 < rationalSizeCeiling24 (d (J (N₂+k))) (N₂+k) := fun k =>
    lt_of_lt_of_le (by omega) (hge k)
  have hidx : Tendsto (fun k : ℕ => N₂+k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_add_left k N₂) tendsto_id
  have hLt : Tendsto (fun k : ℕ => J (N₂+k)+2) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_add_right (J (N₂+k)) 2) (hJt.comp hidx)
  have hL2 : ∀ k : ℕ, (2:ℝ) ≤ ((J (N₂+k)+2:ℕ):ℝ) := fun k => by
    exact_mod_cast Nat.le_add_left 2 (J (N₂+k))
  -- the pointwise window
  have hprofile : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      sphereGaussianFullScaled24 α (Z k) ≤ leechGaussianThetaReal24 α+ε := by
    intro α hα ε hε
    have hΦ := leechBlockWindowBound_tendsto (B := leechLogBlockConst24 s p Bst) hα hLt
    have e1 := (tendsto_order.mp hΦ).2 (leechGaussianThetaReal24 α+ε) (by linarith)
    have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hu : Tendsto (fun k : ℕ => 1/((J (N₂+k)+2:ℕ):ℝ)) atTop (𝓝 0) :=
      hone.div_atTop (tendsto_natCast_atTop_atTop.comp hLt)
    have e2 := (tendsto_order.mp hu).2 α hα
    filter_upwards [e1, e2] with k hk1 hk2
    exact (hZW k α hk2.le).trans hk1.le
  -- the three uniform budgets
  have hBk : ∀ k : ℕ, (∫ β in Ioc (0:ℝ) 1,
      β^(s/2-1)*(sphereGaussianCenteredScaled24 β (Z k)+1)) ≤
      2*(leechMacroConstA24/(s/2+2)+1/(s/2+1))+2*leechLogBlockConst24 s p Bst := fun k =>
    (hZM k 1 one_pos le_rfl).trans
      (leechLogBlock_macro_uniform hs hC0 (by linarith [hL2 k]))
  have hWk : ∀ k : ℕ, sphereGaussianFullScaled24 (1/2) (Z k) ≤
      2*(leechGaussianThetaReal24 (1/8)+1)+leechLogBlockConst24 s p Bst := fun k =>
    (hZW k (1/2) (one_div_le_one_div_of_le (by norm_num) (hL2 k))).trans
      (leechLogBlock_window_uniform hC0 (hL2 k))
  have hfin := sphere24_log_upper_of_gaussian_budgets hs hs0 hp0 hMt hMpos Z
    (2*(leechMacroConstA24/(s/2+2)+1/(s/2+1))+2*leechLogBlockConst24 s p Bst)
    (2*(leechGaussianThetaReal24 (1/8)+1)+leechLogBlockConst24 s p Bst)
    (leechLogBlockTailConst24 s p Bst) hBk hWk hZT hprofile (η/2) (half_pos hη)
  -- the gap terms tend to zero
  obtain ⟨Kc, hKcdef⟩ : ∃ Kc : ℝ,
      Kc = |sphereLogCoefficient24+η/2|+|sphereLogConst24|+1 := ⟨_, rfl⟩
  have hKc0 : 0 ≤ Kc := by
    rw [hKcdef]
    positivity
  have hJR : Tendsto (fun k : ℕ => (J (N₂+k):ℝ)+1) atTop atTop :=
    tendsto_atTop_mono
      (fun k => (le_add_of_nonneg_right zero_le_one : (J (N₂+k):ℝ) ≤ (J (N₂+k):ℝ)+1))
      (tendsto_natCast_atTop_atTop.comp (hJt.comp hidx))
  have hsmall : Tendsto (fun k : ℕ => Kc*(1/((J (N₂+k):ℝ)+1))) atTop (𝓝 0) := by
    have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h := (hone.div_atTop hJR).const_mul Kc
    rw [mul_zero] at h
    exact h
  have e3 := (tendsto_order.mp hsmall).2 (η/2) (half_pos hη)
  -- subconfigurations of every large size
  have hall : ∀ᶠ k : ℕ in atTop, ∃ Y : ConfigurationD 24 (N₂+k),
      normalizedEnergyLog24 Y ≤ sphereLogCoefficient24+η := by
    filter_upwards [hfin, e3] with k hk1 hk3
    obtain ⟨Y, hY⟩ := normalizedEnergyLog24_exists_subconfiguration (N₂+k)
      (rationalSizeCeiling24 (d (J (N₂+k))) (N₂+k)) (by omega) (hge k) (Z k)
    refine ⟨Y, ?_⟩
    have hNk : (2:ℝ) ≤ ((N₂+k:ℕ):ℝ) := by exact_mod_cast (show 2 ≤ N₂+k by omega)
    have hNM : ((N₂+k:ℕ):ℝ) ≤ (rationalSizeCeiling24 (d (J (N₂+k))) (N₂+k):ℝ) := by
      exact_mod_cast hge k
    have hM1 : 0 < (rationalSizeCeiling24 (d (J (N₂+k))) (N₂+k):ℝ)-1 := by linarith
    have hθ0 : 0 ≤ (((N₂+k:ℕ):ℝ)-1)/((rationalSizeCeiling24 (d (J (N₂+k))) (N₂+k):ℝ)-1) :=
      div_nonneg (by linarith) hM1.le
    have hθ1 : (((N₂+k:ℕ):ℝ)-1)/((rationalSizeCeiling24 (d (J (N₂+k))) (N₂+k):ℝ)-1) ≤ 1 :=
      (div_le_one hM1).mpr (by linarith)
    have hl : Real.log ((N₂+k:ℕ):ℝ) ≤
        Real.log (rationalSizeCeiling24 (d (J (N₂+k))) (N₂+k):ℝ) :=
      Real.log_le_log (by linarith) hNM
    have hlM : 0 ≤ Real.log (rationalSizeCeiling24 (d (J (N₂+k))) (N₂+k):ℝ) :=
      Real.log_nonneg (by linarith)
    have hb := logSubconfiguration_bound hθ0 hθ1 hl hlM hk1 hY
    rw [← hKcdef] at hb
    have hg := mul_le_mul_of_nonneg_left (hgapk k) hKc0
    linarith
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hall
  refine ⟨N₂+k₀, fun N hN => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, N = N₂+k := Nat.exists_eq_add_of_le (by omega)
  exact hk₀ k (by omega)

/-- Sharp upper bound for the logarithmic energy on S²⁴ at every large `N`: configurations with
normalized logarithmic energy at most `C_log + η`.  No hypothesis is used. -/
theorem sphere24_log_upper_allN :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 24 N,
      normalizedEnergyLog24 Y ≤ sphereLogCoefficient24+η := by
  obtain ⟨B, hB, hneg, _⟩ := sphere24_stratification_hypotheses
  exact sphere24_log_upper_allN_of_block (s := -1) (p := 0) (by norm_num) (by norm_num)
    le_rfl (by norm_num) hB (leechResidualStratifiable24_of_neg hneg)

/-- The sharp upper bound for the logarithmic energy on S²⁴ in the form of the conjecture:
actual double integral of `-log |x - y|`, the `-(N/24) log N` term and the coefficient
`½ Re Z'(0) + (1/24) log A₂₄` (`Z(u) = ζ_Λ(2u)` the continued Leech Epstein zeta function).  No
hypothesis is used. -/
theorem sphere24_log_upper_conjecture_form :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 24 N,
      (energyLogD Y-(∫ p : SphereD 24 × SphereD 24, -Real.log (dist p.1 p.2)
          ∂((sphereProbabilityD 24).prod (sphereProbabilityD 24)))*(N:ℝ)^2+
            (N:ℝ)/24*Real.log N)/(N:ℝ) ≤
        (1/2)*(deriv leechEpsteinZetaCont 0).re+
          (1/24)*Real.log ((sphereAreaD 24).real univ)+η := by
  intro η hη
  obtain ⟨N₀, h⟩ := sphere24_log_upper_allN η hη
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨Y, hY⟩ := h N hN
  refine ⟨Y, ?_⟩
  rw [← sphereLogConst24_eq_pair_integral, ← sphereLogCoefficient24_eq_epstein]
  exact hY

/-- The two-sided logarithmic asymptotics on S²⁴ in the form of the conjecture:
`(E_log - W N² + (N/24) log N)/N → ½ Re Z'(0) + (1/24) log A₂₄` (all configurations above, some
configuration below, every large `N`).  The lower half assumes all-scale Leech contact
certificates (stage G24); the upper half is unconditional. -/
theorem sphere24_log_sharp_asymptotic
    (hG24 : ∀ β : ℝ, 0 < β → ∃ f, LeechGaussianContactCertificate24 β f) :
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 24 N,
      (1/2)*(deriv leechEpsteinZetaCont 0).re+
          (1/24)*Real.log ((sphereAreaD 24).real univ)-η ≤
        (energyLogD X-(∫ p : SphereD 24 × SphereD 24, -Real.log (dist p.1 p.2)
          ∂((sphereProbabilityD 24).prod (sphereProbabilityD 24)))*(N:ℝ)^2+
            (N:ℝ)/24*Real.log N)/(N:ℝ)) ∧
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 24 N,
      (energyLogD Y-(∫ p : SphereD 24 × SphereD 24, -Real.log (dist p.1 p.2)
          ∂((sphereProbabilityD 24).prod (sphereProbabilityD 24)))*(N:ℝ)^2+
            (N:ℝ)/24*Real.log N)/(N:ℝ) ≤
        (1/2)*(deriv leechEpsteinZetaCont 0).re+
          (1/24)*Real.log ((sphereAreaD 24).real univ)+η) :=
  ⟨sphere24_log_lower_conjecture_form hG24, sphere24_log_upper_conjecture_form⟩

end SphericalRiesz
end
end
