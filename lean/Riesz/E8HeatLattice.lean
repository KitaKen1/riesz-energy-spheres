import Riesz.GaussianTailMoment

/-! The actual Gaussian-damped inverse-fourth sum on the unchanged E8 basis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace SphericalRiesz

def e8HeatTerm (ε : ℝ) (z : Fin 8 → ℤ) : ℝ :=
  if z = 0 then 0 else Real.exp (-Real.pi*ε*‖e8EuclideanPoint z‖^2)/‖e8EuclideanPoint z‖^4

def e8HeatEnergy (ε : ℝ) : ℝ := ∑' z : Fin 8 → ℤ, e8HeatTerm ε z

def e8HeatTailTerm (ε : ℝ) (z : Fin 8 → ℤ) (t : ℝ) : ℝ :=
  if z = 0 then 0 else (t-ε)*Real.exp (-Real.pi*‖e8EuclideanPoint z‖^2*t)

theorem e8HeatTerm_nonneg (ε : ℝ) (z : Fin 8 → ℤ) : 0 ≤ e8HeatTerm ε z := by
  unfold e8HeatTerm
  split_ifs <;> positivity

theorem e8ThetaTail_real_gaussian_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun z : Fin 8 → ℤ => if z = 0 then (0 : ℝ)
      else Real.exp (-Real.pi*‖e8EuclideanPoint z‖^2*t)) (e8ThetaTail t).re := by
  have h := Complex.hasSum_re (e8ThetaTail_gaussian_hasSum ht)
  apply h.congr_fun
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · have hp : 0 < ‖e8EuclideanPoint z‖^2 :=
      lt_of_lt_of_le (by norm_num) (e8EuclideanPoint_norm_sq_ge_two hz)
    simp only [if_neg hz, if_neg hp.ne', Complex.ofReal_re]

theorem e8ThetaTail_eq_ofReal_re {t : ℝ} (ht : 0 < t) :
    e8ThetaTail t = ((e8ThetaTail t).re : ℂ) := by
  have h := Complex.hasSum_im (e8ThetaTail_gaussian_hasSum ht)
  have hi : (e8ThetaTail t).im = 0 := by
    have h' : HasSum (fun _ : Fin 8 → ℤ => (0 : ℝ)) (e8ThetaTail t).im := by
      have hz (z : Fin 8 → ℤ) :
          (if ‖e8EuclideanPoint z‖^2 = 0 then (0 : ℂ) else
            (Real.exp (-Real.pi*‖e8EuclideanPoint z‖^2*t) : ℂ)).im = 0 := by
        split_ifs <;> simp only [Complex.zero_im, Complex.ofReal_im]
      simpa only [hz] using h
    exact h'.unique hasSum_zero
  apply Complex.ext
  · simp
  · simpa using hi

theorem e8HeatTerm_summable {ε : ℝ} (hε : 0 < ε) : Summable (e8HeatTerm ε) := by
  apply Summable.of_nonneg_of_le (e8HeatTerm_nonneg ε) _
    (e8ThetaTail_real_gaussian_hasSum hε).summable
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · simp [e8HeatTerm]
  · have h2 := e8EuclideanPoint_norm_sq_ge_two hz
    have h4 : 1 ≤ ‖e8EuclideanPoint z‖^4 := by nlinarith [sq_nonneg (‖e8EuclideanPoint z‖^2-1)]
    simp only [e8HeatTerm, if_neg hz]
    convert div_le_self (Real.exp_pos _).le h4 using 1 <;>
      congr 1 <;> ring

theorem e8HeatTailTerm_integrable (ε : ℝ) (z : Fin 8 → ℤ) :
    IntegrableOn (e8HeatTailTerm ε z) (Ioi ε) := by
  unfold e8HeatTailTerm
  rcases eq_or_ne z 0 with rfl | hz
  · simp only [ite_true]
    exact integrableOn_zero
  · have hp : 0 < Real.pi*‖e8EuclideanPoint z‖^2 :=
      mul_pos Real.pi_pos (lt_of_lt_of_le (by norm_num) (e8EuclideanPoint_norm_sq_ge_two hz))
    simpa only [if_neg hz, neg_mul] using gaussianTailMoment_integrable hp ε

theorem e8HeatTailTerm_integral (ε : ℝ) (z : Fin 8 → ℤ) :
    (∫ t : ℝ in Ioi ε, e8HeatTailTerm ε z t) = e8HeatTerm ε z / Real.pi^2 := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [e8HeatTailTerm, e8HeatTerm]
  · have hp : 0 < Real.pi*‖e8EuclideanPoint z‖^2 :=
      mul_pos Real.pi_pos (lt_of_lt_of_le (by norm_num) (e8EuclideanPoint_norm_sq_ge_two hz))
    unfold e8HeatTailTerm e8HeatTerm
    simp only [if_neg hz]
    have h := gaussianTailMoment_integral hp ε
    rw [show (fun t : ℝ => (t-ε)*Real.exp (-Real.pi*‖e8EuclideanPoint z‖^2*t)) =
      (fun t : ℝ => (t-ε)*Real.exp (-(Real.pi*‖e8EuclideanPoint z‖^2)*t)) by
        funext t; congr 2; ring, h]
    rw [show -(Real.pi*‖e8EuclideanPoint z‖^2)*ε =
      -Real.pi*ε*‖e8EuclideanPoint z‖^2 by ring]
    have hn : ‖e8EuclideanPoint z‖ ≠ 0 := by intro h; simpa [h] using hp
    field_simp [hn, Real.pi_ne_zero]

theorem e8HeatEnergy_eq_tail_integral {ε : ℝ} (hε : 0 < ε) :
    e8HeatEnergy ε = Real.pi^2 *
      ∫ t : ℝ in Ioi ε, (t-ε)*(e8ThetaTail t).re := by
  have hn (z : Fin 8 → ℤ) : (∫ t : ℝ in Ioi ε, ‖e8HeatTailTerm ε z t‖) =
      e8HeatTerm ε z / Real.pi^2 := by
    rw [← e8HeatTailTerm_integral]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    apply Real.norm_of_nonneg
    unfold e8HeatTailTerm
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (sub_nonneg.mpr (show ε < t from ht).le) (Real.exp_pos _).le
  have hs := hasSum_integral_of_summable_integral_norm
    (fun z => e8HeatTailTerm_integrable ε z)
    ((e8HeatTerm_summable hε).div_const (Real.pi^2) |>.congr (fun z => (hn z).symm))
  have hs' : HasSum (fun z => e8HeatTerm ε z / Real.pi^2)
      (∫ t : ℝ in Ioi ε, (t-ε)*(e8ThetaTail t).re) := by
    convert hs using 1
    · funext z
      exact (e8HeatTailTerm_integral ε z).symm
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := hε.trans ht
      have h := (e8ThetaTail_real_gaussian_hasSum ht0).mul_left (t-ε)
      change (t-ε)*(e8ThetaTail t).re = ∑' z : Fin 8 → ℤ, e8HeatTailTerm ε z t
      rw [← h.tsum_eq]
      apply tsum_congr
      intro z
      simp [e8HeatTailTerm, mul_ite]
  have he := hs'.unique ((e8HeatTerm_summable hε).hasSum.div_const (Real.pi^2))
  unfold e8HeatEnergy
  rw [he]
  field_simp [Real.pi_ne_zero]

theorem e8HeatEnergy_cast_eq_tail_integral {ε : ℝ} (hε : 0 < ε) :
    (e8HeatEnergy ε : ℂ) = (Real.pi : ℂ)^2 *
      ∫ t : ℝ in Ioi ε, ((t-ε : ℝ) : ℂ)*e8ThetaTail t := by
  rw [e8HeatEnergy_eq_tail_integral hε, Complex.ofReal_mul, Complex.ofReal_pow,
    ← integral_complex_ofReal]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  change (((t-ε)*(e8ThetaTail t).re : ℝ) : ℂ) = ((t-ε : ℝ) : ℂ)*e8ThetaTail t
  rw [Complex.ofReal_mul]
  congr 1
  exact (e8ThetaTail_eq_ofReal_re (hε.trans ht)).symm

#print axioms e8HeatTerm_nonneg
#print axioms e8ThetaTail_real_gaussian_hasSum
#print axioms e8ThetaTail_eq_ofReal_re
#print axioms e8HeatTerm_summable
#print axioms e8HeatTailTerm_integrable
#print axioms e8HeatTailTerm_integral
#print axioms e8HeatEnergy_eq_tail_integral
#print axioms e8HeatEnergy_cast_eq_tail_integral

end SphericalRiesz
