import E8Leech.CKMRVAxisNumerator
import E8Leech.EisensteinTwoAxis

/-!
# The generators on the imaginary axis as power series in the nome `x = e^{−πu}`

On the axis `τ = iu` every generator of the axis numerator `axPhi` is an explicit function of
the nome `x = e^{−πu}`:

* `θ₃(iu) = 1 + 2 Σ_{n ≥ 1} xⁿ²`, `θ₄(iu) = 1 + 2 Σ_{n ≥ 1} (−1)ⁿ xⁿ²`,
* `θ₂(iu) = 2 x^{1/4} η₁(x)` with `η₁(x) = Σ_{n ≥ 0} x^{n(n+1)}`, so `V = θ₂⁴ = 16 x η₁(x)⁴`,
* `W = θ₄⁴`, `U = θ₃⁴ = V + W`, `E₂(iu) = 1 − 24 Σ σ₁(n) x^{2n}`,
* `L = log λ = 4 log 2 − πu + 4 log η₁(x) − 4 log θ₃(x)`, `L_S = 4 log θ₄(x) − 4 log θ₃(x)`.

Together with explicit tail bounds these are the inputs of the Taylor-model certificate for (6.4)(1).
-/

noncomputable section

namespace E8Leech

open scoped Real
open UpperHalfPlane hiding I

/-! ## The nome series -/

/-- `θ₃` in the nome: `1 + 2 Σ_{n ≥ 1} xⁿ²`. -/
def nomeTheta3 (x : ℝ) : ℝ := 1 + 2 * ∑' n : ℕ, x ^ ((n + 1) ^ 2)

/-- `θ₄` in the nome: `1 + 2 Σ_{n ≥ 1} (−1)ⁿ xⁿ²`. -/
def nomeTheta4 (x : ℝ) : ℝ := 1 + 2 * ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * x ^ ((n + 1) ^ 2)

/-- `η₁(x) = Σ_{n ≥ 0} x^{n(n+1)}`, so that `θ₂ = 2 x^{1/4} η₁`. -/
def nomeEta1 (x : ℝ) : ℝ := ∑' n : ℕ, x ^ (n * (n + 1))

/-- `E₂` in the nome `x` (`q = x²`). -/
def nomeE2 (x : ℝ) : ℝ := eisensteinTwoQ (x ^ 2)

theorem le_pow_succ_sq (n : ℕ) : n + 1 ≤ (n + 1) ^ 2 := by nlinarith

theorem pow_sq_le_pow {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    x ^ ((n + 1) ^ 2) ≤ x ^ (n + 1) :=
  pow_le_pow_of_le_one hx0 hx1 (le_pow_succ_sq n)

theorem summable_pow_sq {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable fun n : ℕ => x ^ ((n + 1) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun n => pow_nonneg hx0 _) (pow_sq_le_pow hx0 hx1.le) ?_
  exact (summable_geometric_of_lt_one hx0 hx1).comp_injective (add_left_injective 1)

theorem summable_signed_pow_sq {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable fun n : ℕ => (-1 : ℝ) ^ (n + 1) * x ^ ((n + 1) ^ 2) := by
  refine (summable_pow_sq hx0 hx1).of_norm_bounded ?_
  intro n
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hx0 _)]

theorem le_mul_succ (n : ℕ) : n ≤ n * (n + 1) := Nat.le_mul_of_pos_right n (Nat.succ_pos n)

theorem summable_pow_triangular {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable fun n : ℕ => x ^ (n * (n + 1)) := by
  refine Summable.of_nonneg_of_le (fun n => pow_nonneg hx0 _)
    (fun n => pow_le_pow_of_le_one hx0 hx1.le (le_mul_succ n)) ?_
  exact summable_geometric_of_lt_one hx0 hx1

/-! ## Integer theta sums on the axis -/

theorem exp_neg_pi_sq_eq {t : ℝ} (n : ℕ) :
    Real.exp (-π * ((n + 1 : ℕ) : ℝ) ^ 2 * t) = Real.exp (-π * t) ^ ((n + 1) ^ 2) := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem summable_exp_neg_pi_int_sq {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℤ => Real.exp (-π * (n : ℝ) ^ 2 * t) := by
  have hx0 : 0 ≤ Real.exp (-π * t) := (Real.exp_pos _).le
  have hx1 : Real.exp (-π * t) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  refine Summable.of_add_one_of_neg_add_one ?_ ?_
  · refine (summable_pow_sq hx0 hx1).congr fun n => ?_
    rw [← exp_neg_pi_sq_eq n]
    push_cast
    ring_nf
  · refine (summable_pow_sq hx0 hx1).congr fun n => ?_
    rw [← exp_neg_pi_sq_eq n]
    push_cast
    ring_nf

theorem exp_int_succ_sq_eq {t : ℝ} (n : ℕ) :
    Real.exp (-π * (((n : ℤ) + 1 : ℤ) : ℝ) ^ 2 * t) = Real.exp (-π * t) ^ ((n + 1) ^ 2) := by
  rw [← exp_neg_pi_sq_eq n]
  push_cast
  ring_nf

theorem exp_int_neg_succ_sq_eq {t : ℝ} (n : ℕ) :
    Real.exp (-π * ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2 * t) = Real.exp (-π * t) ^ ((n + 1) ^ 2) := by
  rw [← exp_neg_pi_sq_eq n]
  push_cast
  ring_nf

/-- `Σ_{n ∈ ℤ} e^{−πn²t} = θ₃(e^{−πt})`. -/
theorem tsum_exp_neg_pi_int_sq {t : ℝ} (ht : 0 < t) :
    ∑' n : ℤ, Real.exp (-π * (n : ℝ) ^ 2 * t) = nomeTheta3 (Real.exp (-π * t)) := by
  have hx0 : 0 ≤ Real.exp (-π * t) := (Real.exp_pos _).le
  have hx1 : Real.exp (-π * t) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hs := summable_pow_sq hx0 hx1
  rw [tsum_of_add_one_of_neg_add_one (hs.congr fun n => (exp_int_succ_sq_eq n).symm)
    (hs.congr fun n => (exp_int_neg_succ_sq_eq n).symm), tsum_congr exp_int_succ_sq_eq,
    tsum_congr exp_int_neg_succ_sq_eq, nomeTheta3]
  simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_mul, Real.exp_zero]
  ring

/-! ## `θ₂` and `θ₄` on the axis -/

theorem exp_neg_pi_half_sq_eq {t : ℝ} (n : ℕ) :
    Real.exp (-π * ((n : ℝ) + 1 / 2) ^ 2 * t) =
      Real.exp (-π * t / 4) * Real.exp (-π * t) ^ (n * (n + 1)) := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring

theorem tsum_exp_neg_pi_int_half_sq {t : ℝ} (ht : 0 < t) :
    ∑' n : ℤ, Real.exp (-π * ((n : ℝ) + 1 / 2) ^ 2 * t) =
      2 * Real.exp (-π * t / 4) * nomeEta1 (Real.exp (-π * t)) := by
  have hx0 : 0 ≤ Real.exp (-π * t) := (Real.exp_pos _).le
  have hx1 : Real.exp (-π * t) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hs := (summable_pow_triangular hx0 hx1).mul_left (Real.exp (-π * t / 4))
  have hpos : ∀ n : ℕ, Real.exp (-π * ((((n : ℤ) + 1 : ℤ) : ℝ) + 1 / 2) ^ 2 * t) =
      Real.exp (-π * t / 4) * Real.exp (-π * t) ^ ((n + 1) * (n + 1 + 1)) := by
    intro n
    rw [← exp_neg_pi_half_sq_eq (n + 1)]
    push_cast
    ring_nf
  have hneg : ∀ n : ℕ, Real.exp (-π * (((-((n : ℤ) + 1) : ℤ) : ℝ) + 1 / 2) ^ 2 * t) =
      Real.exp (-π * t / 4) * Real.exp (-π * t) ^ (n * (n + 1)) := by
    intro n
    rw [← exp_neg_pi_half_sq_eq n]
    push_cast
    ring_nf
  have hs1 : Summable fun n : ℕ =>
      Real.exp (-π * t / 4) * Real.exp (-π * t) ^ ((n + 1) * (n + 1 + 1)) :=
    (summable_nat_add_iff 1).mpr hs
  rw [tsum_of_add_one_of_neg_add_one (hs1.congr fun n => (hpos n).symm)
    (hs.congr fun n => (hneg n).symm), tsum_congr hpos, tsum_congr hneg]
  have h0 : Real.exp (-π * (((0 : ℤ) : ℝ) + 1 / 2) ^ 2 * t) =
      Real.exp (-π * t / 4) * Real.exp (-π * t) ^ (0 * (0 + 1)) := by
    rw [← exp_neg_pi_half_sq_eq 0]
    push_cast
    ring_nf
  have hsplit := hs.tsum_eq_zero_add
  have hB : ∑' n : ℕ, Real.exp (-π * t / 4) * Real.exp (-π * t) ^ (n * (n + 1)) =
      Real.exp (-π * t / 4) * nomeEta1 (Real.exp (-π * t)) := by
    rw [nomeEta1, tsum_mul_left]
  rw [h0]
  linarith [hsplit, hB]

theorem exp_int_succ_sq_signed_eq {t : ℝ} (n : ℕ) :
    (-1 : ℝ) ^ (((n : ℤ) + 1 : ℤ)) * Real.exp (-π * (((n : ℤ) + 1 : ℤ) : ℝ) ^ 2 * t) =
      (-1 : ℝ) ^ (n + 1) * Real.exp (-π * t) ^ ((n + 1) ^ 2) := by
  rw [exp_int_succ_sq_eq n, show (((n : ℤ) + 1 : ℤ)) = ((n + 1 : ℕ) : ℤ) by push_cast; ring,
    zpow_natCast]

theorem exp_int_neg_succ_sq_signed_eq {t : ℝ} (n : ℕ) :
    (-1 : ℝ) ^ ((-((n : ℤ) + 1) : ℤ)) * Real.exp (-π * ((-((n : ℤ) + 1) : ℤ) : ℝ) ^ 2 * t) =
      (-1 : ℝ) ^ (n + 1) * Real.exp (-π * t) ^ ((n + 1) ^ 2) := by
  rw [exp_int_neg_succ_sq_eq n]
  congr 1
  rw [show (-((n : ℤ) + 1) : ℤ) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  rcases neg_one_pow_eq_or ℝ (n + 1) with h | h <;> rw [h] <;> norm_num

/-- `Σ_{n ∈ ℤ} (−1)ⁿ e^{−πn²t} = θ₄(e^{−πt})`. -/
theorem tsum_signed_exp_neg_pi_int_sq {t : ℝ} (ht : 0 < t) :
    ∑' n : ℤ, (-1 : ℝ) ^ n * Real.exp (-π * (n : ℝ) ^ 2 * t) =
      nomeTheta4 (Real.exp (-π * t)) := by
  have hx0 : 0 ≤ Real.exp (-π * t) := (Real.exp_pos _).le
  have hx1 : Real.exp (-π * t) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hs := summable_signed_pow_sq hx0 hx1
  rw [tsum_of_add_one_of_neg_add_one (hs.congr fun n => (exp_int_succ_sq_signed_eq n).symm)
    (hs.congr fun n => (exp_int_neg_succ_sq_signed_eq n).symm),
    tsum_congr exp_int_succ_sq_signed_eq, tsum_congr exp_int_neg_succ_sq_signed_eq, nomeTheta4]
  simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    zero_mul, Real.exp_zero, zpow_zero, one_mul]
  ring

/-! ## The generators of `axPhi` in the nome -/

theorem thetaTwo_I_mul_real (t : ℝ) :
    thetaTwo (Complex.I * t) =
      ((∑' n : ℤ, Real.exp (-π * ((n : ℝ) + 1 / 2) ^ 2 * t) : ℝ) : ℂ) := by
  rw [thetaTwo_eq_tsum, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem thetaThree_I_mul_real (t : ℝ) :
    thetaThree (Complex.I * t) = ((∑' n : ℤ, Real.exp (-π * (n : ℝ) ^ 2 * t) : ℝ) : ℂ) := by
  rw [thetaThree_eq_tsum, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem thetaFour_I_mul_real (t : ℝ) :
    thetaFour (Complex.I * t) =
      ((∑' n : ℤ, (-1 : ℝ) ^ n * Real.exp (-π * (n : ℝ) ^ 2 * t) : ℝ) : ℂ) := by
  rw [thetaFour_eq_tsum, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_zpow, Complex.ofReal_neg,
    Complex.ofReal_one]
  congr 2
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem nomeEta1_pos {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) : 0 < nomeEta1 x :=
  (summable_pow_triangular hx0 hx1).tsum_pos (fun n => pow_nonneg hx0 _) 0 (by simp)

theorem one_le_nomeTheta3 {x : ℝ} (hx0 : 0 ≤ x) : 1 ≤ nomeTheta3 x := by
  unfold nomeTheta3
  have h : (0 : ℝ) ≤ ∑' n : ℕ, x ^ ((n + 1) ^ 2) := tsum_nonneg fun n => pow_nonneg hx0 _
  linarith

section Axis

variable {u : ℝ} (hu : 0 < u)
include hu

theorem exp_neg_pi_mem : 0 ≤ Real.exp (-π * u) ∧ Real.exp (-π * u) < 1 :=
  ⟨(Real.exp_pos _).le, Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])⟩

theorem thetaV_imagPt_eq_nome :
    thetaV (imagPt u) =
      ((16 * Real.exp (-π * u) * nomeEta1 (Real.exp (-π * u)) ^ 4 : ℝ) : ℂ) := by
  show thetaTwo ((imagPt u : ℍ) : ℂ) ^ 4 = _
  rw [coe_imagPt hu, thetaTwo_I_mul_real, tsum_exp_neg_pi_int_half_sq hu]
  have h4 : Real.exp (-π * u / 4) ^ 4 = Real.exp (-π * u) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [← Complex.ofReal_pow]
  congr 1
  rw [mul_pow, mul_pow, h4]
  ring

theorem thetaW_imagPt_eq_nome :
    thetaW (imagPt u) = ((nomeTheta4 (Real.exp (-π * u)) ^ 4 : ℝ) : ℂ) := by
  show thetaFour ((imagPt u : ℍ) : ℂ) ^ 4 = _
  rw [coe_imagPt hu, thetaFour_I_mul_real, tsum_signed_exp_neg_pi_int_sq hu,
    ← Complex.ofReal_pow]

theorem thetaU_imagPt_eq_nome :
    thetaU (imagPt u) = ((nomeTheta3 (Real.exp (-π * u)) ^ 4 : ℝ) : ℂ) := by
  show thetaThree ((imagPt u : ℍ) : ℂ) ^ 4 = _
  rw [coe_imagPt hu, thetaThree_I_mul_real, tsum_exp_neg_pi_int_sq hu, ← Complex.ofReal_pow]

theorem axV_eq_nome : axV u = 16 * Real.exp (-π * u) * nomeEta1 (Real.exp (-π * u)) ^ 4 := by
  rw [axV, thetaV_imagPt_eq_nome hu, Complex.ofReal_re]

theorem axW_eq_nome : axW u = nomeTheta4 (Real.exp (-π * u)) ^ 4 := by
  rw [axW, thetaW_imagPt_eq_nome hu, Complex.ofReal_re]

theorem axV_add_axW_eq_nome : axV u + axW u = nomeTheta3 (Real.exp (-π * u)) ^ 4 := by
  have h := thetaU_imagPt_eq_ax hu
  rw [thetaU_imagPt_eq_nome hu] at h
  exact_mod_cast h.symm

theorem axE2_eq_nome : axE2 u = nomeE2 (Real.exp (-π * u)) := by
  have h := eisensteinTwo_imaginary_eq_q hu
  rw [axE2, show imagPt u = UpperHalfPlane.ofComplex (Complex.I * u) from rfl, h,
    Complex.ofReal_re, nomeE2]
  congr 1
  rw [imaginaryNome, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem axL_eq_nome :
    axL u = 4 * Real.log 2 - π * u + 4 * Real.log (nomeEta1 (Real.exp (-π * u))) -
      4 * Real.log (nomeTheta3 (Real.exp (-π * u))) := by
  obtain ⟨hx0, hx1⟩ := exp_neg_pi_mem hu
  have hη := nomeEta1_pos hx0 hx1
  have hθ := lt_of_lt_of_le one_pos (one_le_nomeTheta3 hx0)
  have hL := ckmrvL_imagAxis hu
  rw [← imagPt_eq_imagAxisPoint hu] at hL
  have hlam : (modularLambda (imagPt u)).re =
      16 * Real.exp (-π * u) * nomeEta1 (Real.exp (-π * u)) ^ 4 /
        nomeTheta3 (Real.exp (-π * u)) ^ 4 := by
    rw [modularLambda, thetaV_imagPt_eq_nome hu, thetaU_imagPt_eq_nome hu, ← Complex.ofReal_div,
      Complex.ofReal_re]
  rw [axL, hL, Complex.ofReal_re, hlam, Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_exp, show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
  push_cast
  ring

theorem axLS_eq_nome :
    axLS u = 4 * Real.log (nomeTheta4 (Real.exp (-π * u))) -
      4 * Real.log (nomeTheta3 (Real.exp (-π * u))) := by
  obtain ⟨hx0, _⟩ := exp_neg_pi_mem hu
  have hθ := lt_of_lt_of_le one_pos (one_le_nomeTheta3 hx0)
  have hW : 0 < nomeTheta4 (Real.exp (-π * u)) ^ 4 := by
    obtain ⟨w, hw, hWw⟩ := thetaW_imagAxis_pos hu
    rw [← imagPt_eq_imagAxisPoint hu, thetaW_imagPt_eq_nome hu] at hWw
    have := congrArg Complex.re hWw
    simp only [Complex.ofReal_re] at this
    rw [this]
    exact hw
  have hLS := ckmrvLS_imagAxis hu
  rw [← imagPt_eq_imagAxisPoint hu] at hLS
  have hlam : (1 - modularLambda (imagPt u)).re =
      nomeTheta4 (Real.exp (-π * u)) ^ 4 / nomeTheta3 (Real.exp (-π * u)) ^ 4 := by
    rw [one_sub_modularLambda, thetaW_imagPt_eq_nome hu, thetaU_imagPt_eq_nome hu,
      ← Complex.ofReal_div, Complex.ofReal_re]
  rw [axLS, hLS, Complex.ofReal_re, hlam, Real.log_div hW.ne' (by positivity), Real.log_pow,
    Real.log_pow]
  push_cast
  ring

end Axis

end E8Leech
