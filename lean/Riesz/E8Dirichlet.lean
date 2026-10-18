import Riesz.E8ThetaModular
import Riesz.ZetaValue
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Dirichlet series of the actual E8 theta coefficients

The coefficient sequence comes from the actual lattice theta function.
Dirichlet convolution, rather than a crude divisor-count bound, gives the
sharp half-plane Re(u) > 4. The explicit zeta product below agrees with this
series there. Its value at u = 2 is a candidate for the regularized lattice
value; identifying a cutoff sum-minus-integral limit is a separate theorem.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped LSeries.notation ArithmeticFunction.zeta
namespace SphericalRiesz

theorem lSeries_pow_term_shift (k n : ℕ) (u : ℂ) :
    LSeries.term (fun m => (ArithmeticFunction.pow k m : ℂ)) u n =
      LSeries.term (fun m => (ArithmeticFunction.zeta m : ℂ)) (u-k) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  simp only [LSeries.term_of_ne_zero hn, ArithmeticFunction.pow_apply,
    hn, and_false, ite_false, Nat.cast_pow, ArithmeticFunction.zeta_apply,
    Nat.cast_one, Complex.cpow_sub _ _ hnC, Complex.cpow_natCast]
  field_simp

theorem lSeries_pow_hasSum (k : ℕ) {u : ℂ} (hu : 1 < (u-k).re) :
    LSeriesHasSum (fun n => (ArithmeticFunction.pow k n : ℂ)) u (riemannZeta (u-k)) := by
  exact (ArithmeticFunction.LSeriesHasSum_zeta hu).congr_fun
    (fun n => lSeries_pow_term_shift k n u)

theorem lSeries_pow_summable_iff (k : ℕ) (u : ℂ) :
    LSeriesSummable (fun n => (ArithmeticFunction.pow k n : ℂ)) u ↔ 1 < (u-k).re := by
  have ht : LSeries.term (fun n => (ArithmeticFunction.pow k n : ℂ)) u =
      LSeries.term (fun n => (ArithmeticFunction.zeta n : ℂ)) (u-k) :=
    funext (fun n => lSeries_pow_term_shift k n u)
  rw [LSeriesSummable, ht]
  exact ArithmeticFunction.LSeriesSummable_zeta_iff

theorem sigma_three_hasSum {u : ℂ} (hu : 4 < u.re) :
    LSeriesHasSum (fun n => (ArithmeticFunction.sigma 3 n : ℂ)) u
      (riemannZeta u * riemannZeta (u-3)) := by
  have h₁ : 1 < u.re := by linarith
  have h₂ : 1 < (u-3).re := by simpa using (by linarith : 1 < u.re-3)
  have h := (ArithmeticFunction.LSeriesHasSum_zeta h₁).convolution (lSeries_pow_hasSum 3 h₂)
  have hc : (fun n => (ArithmeticFunction.zeta n : ℂ)) ⍟
      (fun n => (ArithmeticFunction.pow 3 n : ℂ)) =
      (fun n => (ArithmeticFunction.sigma 3 n : ℂ)) := by
    change ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) ⍟
      ((ArithmeticFunction.pow 3 : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) = _
    rw [ArithmeticFunction.coe_mul, ← ArithmeticFunction.natCoe_mul,
      ArithmeticFunction.zeta_mul_pow_eq_sigma]
    rfl
  rw [hc] at h
  exact h

theorem pow_three_le_sigma_three (n : ℕ) : n^3 ≤ ArithmeticFunction.sigma 3 n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  exact Finset.single_le_sum (fun d _ => Nat.zero_le (d^3)) (Nat.mem_divisors_self n hn)

theorem sigma_three_summable_iff (u : ℂ) :
    LSeriesSummable (fun n => (ArithmeticFunction.sigma 3 n : ℂ)) u ↔ 4 < u.re := by
  refine ⟨fun h => ?_, fun h => (sigma_three_hasSum h).LSeriesSummable⟩
  have hp : LSeriesSummable (fun n => (ArithmeticFunction.pow 3 n : ℂ)) u := by
    apply Summable.of_norm
    apply h.norm.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => LSeries.norm_term_le u ?_)
    simp only [Complex.norm_natCast, ArithmeticFunction.pow_apply]
    simpa using (Nat.cast_le (α := ℝ)).mpr (pow_three_le_sigma_three n)
  have hs := (lSeries_pow_summable_iff 3 u).mp hp
  norm_num at hs
  linarith

/-- Positive coefficients of the actual lattice theta; the constant term is removed. -/
def e8ThetaPositiveCoeff (n : ℕ) : ℂ :=
  if n = 0 then 0 else (UpperHalfPlane.qExpansion 1 e8ThetaUpper).coeff n

theorem e8ThetaPositiveCoeff_eq (n : ℕ) :
    e8ThetaPositiveCoeff n = 240 * (ArithmeticFunction.sigma 3 n : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [e8ThetaPositiveCoeff]
  · simpa [e8ThetaPositiveCoeff, hn] using e8ThetaUpper_positive_coeff n hn

def e8ThetaDirichlet (u : ℂ) : ℂ := LSeries e8ThetaPositiveCoeff u

theorem e8ThetaDirichlet_hasSum {u : ℂ} (hu : 4 < u.re) :
    LSeriesHasSum e8ThetaPositiveCoeff u (240 * (riemannZeta u * riemannZeta (u-3))) := by
  have h := (sigma_three_hasSum hu).mul_left (240 : ℂ)
  apply h.congr_fun
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [LSeries.term_of_ne_zero hn, e8ThetaPositiveCoeff_eq, mul_div_assoc]

theorem e8ThetaDirichlet_eq {u : ℂ} (hu : 4 < u.re) :
    e8ThetaDirichlet u = 240 * riemannZeta u * riemannZeta (u-3) := by
  simpa only [e8ThetaDirichlet, mul_assoc] using (e8ThetaDirichlet_hasSum hu).LSeries_eq

theorem e8ThetaPositiveCoeff_summable_iff (u : ℂ) :
    LSeriesSummable e8ThetaPositiveCoeff u ↔ 4 < u.re := by
  have ht : LSeries.term e8ThetaPositiveCoeff u =
      fun n => (240 : ℂ) * LSeries.term (fun m => (ArithmeticFunction.sigma 3 m : ℂ)) u n := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [LSeries.term_of_ne_zero hn, e8ThetaPositiveCoeff_eq, mul_div_assoc]
  change Summable _ ↔ _
  rw [ht, summable_mul_left_iff (by norm_num : (240 : ℂ) ≠ 0)]
  exact sigma_three_summable_iff u

theorem e8ThetaDirichlet_not_summable_at_two : ¬ LSeriesSummable e8ThetaPositiveCoeff 2 := by
  rw [e8ThetaPositiveCoeff_summable_iff]
  norm_num

/-- Explicit continuation candidate with the norm-squared factor 2 restored. -/
def e8EpsteinCandidate (u : ℂ) : ℂ :=
  (2 : ℂ)^(-u) * (240 * riemannZeta u * riemannZeta (u-3))

theorem e8EpsteinCandidate_eq_thetaDirichlet {u : ℂ} (hu : 4 < u.re) :
    e8EpsteinCandidate u = (2 : ℂ)^(-u) * e8ThetaDirichlet u := by
  rw [e8ThetaDirichlet_eq hu]
  rfl

theorem e8EpsteinCandidate_at_two : e8EpsteinCandidate 2 = -(5*(Real.pi : ℂ)^2/6) := by
  have hpow : (2 : ℂ)^(-(2 : ℂ)) = (1/4 : ℂ) := by
    rw [Complex.cpow_neg, show (2 : ℂ) = (2 : ℕ) by norm_num, Complex.cpow_natCast]
    norm_num
  have hsub : (2 : ℂ)-3 = -1 := by norm_num
  rw [e8EpsteinCandidate, hpow, hsub]
  convert e8_zeta_product_at_two using 1 <;> ring

#print axioms lSeries_pow_term_shift
#print axioms lSeries_pow_hasSum
#print axioms lSeries_pow_summable_iff
#print axioms sigma_three_hasSum
#print axioms pow_three_le_sigma_three
#print axioms sigma_three_summable_iff
#print axioms e8ThetaPositiveCoeff_eq
#print axioms e8ThetaDirichlet_hasSum
#print axioms e8ThetaDirichlet_eq
#print axioms e8ThetaPositiveCoeff_summable_iff
#print axioms e8ThetaDirichlet_not_summable_at_two
#print axioms e8EpsteinCandidate_eq_thetaDirichlet
#print axioms e8EpsteinCandidate_at_two
end SphericalRiesz
