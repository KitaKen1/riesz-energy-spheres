import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Uniform derivatives of Schwartz dilations away from zero

The n-th derivative gains a^n; the Schwartz seminorm with weight n
cancels it. No compactness in the unbounded dilation parameter is used.
-/
set_option autoImplicit false
set_option maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped SchwartzMap
namespace SphericalRiesz

theorem schwartzDilation_derivative_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : 𝓢(E, ℝ)) (n : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (a : ℝ) (ha : 0 ≤ a) (v : E) (hv : δ ≤ ‖v‖) :
    ‖iteratedFDeriv ℝ n (fun y => f (a • y)) v‖ ≤
      SchwartzMap.seminorm ℝ n n f / δ^n := by
  rw [iteratedFDeriv_comp_const_smul a (f.smooth n), norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ha n)]
  apply (le_div_iff₀ (pow_pos hδ n)).mpr
  calc
    _ = (a^n*δ^n)*‖iteratedFDeriv ℝ n f (a • v)‖ := by ring
    _ ≤ (a^n*‖v‖^n)*‖iteratedFDeriv ℝ n f (a • v)‖ := by
      gcongr
    _ = ‖a • v‖^n*‖iteratedFDeriv ℝ n f (a • v)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, mul_pow]
    _ ≤ _ := f.le_seminorm ℝ n n (a • v)

def schwartzDilationBound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : 𝓢(E, ℝ)) (N : ℕ) (δ : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N+1), SchwartzMap.seminorm ℝ j j f / δ^j

theorem schwartzDilationBound_nonneg {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : 𝓢(E, ℝ)) (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    0 ≤ schwartzDilationBound f N δ := by
  apply Finset.sum_nonneg
  intro j _
  exact div_nonneg (apply_nonneg _ _) (pow_pos hδ j).le

theorem schwartzDilation_derivatives_uniform {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : 𝓢(E, ℝ)) (N : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (a : ℝ) (ha : 0 ≤ a) (v : E) (hv : δ ≤ ‖v‖) (n : ℕ) (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (fun y => f (a • y)) v‖ ≤ schwartzDilationBound f N δ := by
  have hsum : SchwartzMap.seminorm ℝ n n f / δ^n ≤ schwartzDilationBound f N δ := by
    unfold schwartzDilationBound
    exact Finset.single_le_sum (s := Finset.range (N+1)) (a := n)
      (f := fun j => SchwartzMap.seminorm ℝ j j f / δ^j)
      (fun j _ => div_nonneg (apply_nonneg _ _) (pow_pos hδ j).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  exact (schwartzDilation_derivative_bound f n hδ a ha v hv).trans hsum

#print axioms schwartzDilation_derivative_bound
#print axioms schwartzDilationBound_nonneg
#print axioms schwartzDilation_derivatives_uniform
end SphericalRiesz
