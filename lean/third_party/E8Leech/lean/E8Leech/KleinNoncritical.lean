import E8Leech.CKMRVDerivativeBridge
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# An actual noncritical imaginary point without the explicit j derivative

If j' vanished at every iy with 1<y<4, the differentiable imaginary-axis
restriction would be constant. The certified gap j(3i)-j(2i)>=2000000
contradicts this. This constructs a genuine noncritical point existentially;
it does not identify j' explicitly or classify all critical points.
-/

noncomputable section
namespace E8Leech
open Set
open scoped Topology

theorem hasDerivAt_kleinImaginaryJ {y : ℝ} (hy : 0 < y) :
    HasDerivAt kleinImaginaryJ
      (kleinModularJDerivative (UpperHalfPlane.ofComplex (Complex.I * y)) * Complex.I) y := by
  let z := UpperHalfPlane.ofComplex (Complex.I * y)
  have him : 0 < (Complex.I * (y : ℂ)).im := by simpa using hy
  have hz : (z : ℂ) = Complex.I * y := by
    change (UpperHalfPlane.ofComplex (Complex.I * y) : ℂ) = Complex.I * y
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos him]
  have hj := hasDerivAt_kleinModularJ z
  rw [hz] at hj
  have h := hj.comp (y : ℂ) ((hasDerivAt_id (y : ℂ)).const_mul Complex.I)
  convert! h.comp_ofReal using 1
  simp only [mul_one, z]

theorem exists_imaginary_kleinModularJDerivative_ne_zero :
    ∃ y : ℝ, y ∈ Ioo 1 4 ∧
      kleinModularJDerivative (UpperHalfPlane.ofComplex (Complex.I * y)) ≠ 0 := by
  by_contra h
  push Not at h
  have hf : DifferentiableOn ℝ kleinImaginaryJ (Ioo 1 4) := by
    intro y hy
    exact (hasDerivAt_kleinImaginaryJ (by linarith only [hy.1])).differentiableAt.differentiableWithinAt
  have hd : (Ioo (1 : ℝ) 4).EqOn (deriv kleinImaginaryJ) 0 := by
    intro y hy
    rw [(hasDerivAt_kleinImaginaryJ (by linarith only [hy.1])).deriv, h y hy, zero_mul]
    rfl
  have heq : kleinImaginaryJ 2 = kleinImaginaryJ 3 :=
    isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (1 : ℝ) 4).isPreconnected hf hd
      (by norm_num) (by norm_num)
  have hg := kleinImaginaryJ_rectangle_real_gap (by norm_num : (3 : ℝ) ∈ Icc 3 4)
    (by norm_num : (2 : ℝ) ∈ Icc 1 2)
  rw [heq, sub_self, Complex.zero_re] at hg
  norm_num at hg

end E8Leech
