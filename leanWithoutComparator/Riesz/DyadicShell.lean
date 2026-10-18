import Riesz.LocalCellQuadrature
import Riesz.TensorQuadrature

/-!
# Fixed-exponent dyadic shell algebra for d=8, s=4

A cell error h^(8+6) r^(-4-6), multiplied by O((r/h)^8)
cells in a shell of radius r=2^k h, has scale h^4 4^(-k).
We check this scaling and its finite geometric sum directly. The Riesz
derivative estimate, shell cell count, and near/boundary cells are still
separate mathematical obligations; this file does not prove them.
-/

set_option autoImplicit false
noncomputable section

namespace SphericalRiesz

theorem dyadic_eight_four_scale (h : ℝ) (hh : 0 < h) (k : ℕ) :
    ((2 : ℝ)^k)^8 * h^14 / ((2 : ℝ)^k*h)^10 = h^4*(1/4 : ℝ)^k := by
  have h2 : (2 : ℝ)^k ≠ 0 := pow_ne_zero k (by norm_num)
  have hp : (4 : ℝ)^k = ((2 : ℝ)^k)^2 := by
    rw [← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  rw [div_pow, one_pow, hp]
  field_simp [h2, hh.ne']

theorem dyadic_quarter_sum (n : ℕ) :
    (∑ k ∈ Finset.range n, (1/4 : ℝ)^k) = (4/3 : ℝ)*(1-(1/4 : ℝ)^n) := by
  induction n with
  | zero => norm_num
  | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

theorem dyadic_quarter_sum_le (n : ℕ) :
    (∑ k ∈ Finset.range n, (1/4 : ℝ)^k) ≤ 4/3 := by
  rw [dyadic_quarter_sum]
  have h : 0 ≤ (1/4 : ℝ)^n := by positivity
  linarith

/-- A concrete summation bound once each actual far shell has been estimated. -/
theorem dyadic_shell_error_bound (n : ℕ) (e : ℕ → ℝ) (C h : ℝ) (hC : 0 ≤ C)
    (he : ∀ k ∈ Finset.range n, |e k| ≤ C*h^4*(1/4 : ℝ)^k) :
    |∑ k ∈ Finset.range n, e k| ≤ (4/3 : ℝ)*C*h^4 := by
  calc
    _ ≤ ∑ k ∈ Finset.range n, |e k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, C*h^4*(1/4 : ℝ)^k := Finset.sum_le_sum he
    _ = C*h^4*(∑ k ∈ Finset.range n, (1/4 : ℝ)^k) := (Finset.mul_sum _ _ _).symm
    _ ≤ C*h^4*(4/3 : ℝ) :=
      mul_le_mul_of_nonneg_left (dyadic_quarter_sum_le n) (by positivity)
    _ = (4/3 : ℝ)*C*h^4 := by ring

#print axioms dyadic_eight_four_scale
#print axioms dyadic_quarter_sum
#print axioms dyadic_shell_error_bound

end SphericalRiesz
