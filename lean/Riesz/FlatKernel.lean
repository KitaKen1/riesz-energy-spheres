import Riesz.QuadraticKernel
import Riesz.BoxQuadrature
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The actual inverse-fourth Euclidean kernel on flat boxes

Squared distance splits into the varying coordinate and a nonnegative
sum of the remaining coordinate squares. The distance separation of a
box will supply the denominator bound for the derivative certificate.
-/

set_option autoImplicit false
noncomputable section

namespace SphericalRiesz
open Boundary

def squaredDistance (d : ℕ) (x v : Fin d → ℝ) : ℝ := ∑ i, (v i-x i)^2

def flatRieszFour (d : ℕ) (x v : Fin d → ℝ) : ℝ := 1/(squaredDistance d x v)^2

def perpendicularSquare (d : ℕ) (x v : Fin d → ℝ) (i : Fin d) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, (v j-x j)^2

theorem squaredDistance_nonneg (d : ℕ) (x v : Fin d → ℝ) : 0 ≤ squaredDistance d x v :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (v i-x i))

theorem perpendicularSquare_nonneg (d : ℕ) (x v : Fin d → ℝ) (i : Fin d) :
    0 ≤ perpendicularSquare d x v i :=
  Finset.sum_nonneg (fun j _ => sq_nonneg (v j-x j))

theorem squaredDistance_update (d : ℕ) (x v : Fin d → ℝ) (i : Fin d) (t : ℝ) :
    squaredDistance d x (Function.update v i t) = (t-x i)^2+perpendicularSquare d x v i := by
  unfold squaredDistance perpendicularSquare
  rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin d))
    (fun j => (Function.update v i t j-x j)^2) (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem flatRieszFour_slice (d : ℕ) (x v : Fin d → ℝ) (i : Fin d) :
    (fun t => flatRieszFour d x (Function.update v i t)) =
      quadraticKernel (perpendicularSquare d x v i) (x i) := by
  funext t
  simp only [flatRieszFour, squaredDistance_update, quadraticKernel]

/-- This is the Euclidean distance kernel, with its actual normalization. -/
theorem flatRieszFour_eq_dist (d : ℕ) (x v : EuclideanSpace ℝ (Fin d)) :
    flatRieszFour d (fun i => x i) (fun i => v i) = (dist x v)⁻¹^4 := by
  have hs : squaredDistance d (fun i => x i) (fun i => v i) = (dist x v)^2 := by
    rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
    unfold squaredDistance
    apply Finset.sum_congr rfl
    intro i _
    simp only [PiLp.sub_apply]
    ring
  rw [flatRieszFour, hs, one_div, inv_pow, ← pow_mul]

theorem update_mem_boxCell {d : ℕ} {a w v : Fin d → ℝ} (hv : v ∈ BoxCell d a w)
    (i : Fin d) {t : ℝ} (ht : t ∈ Set.Icc (a i) (a i+w i)) :
    Function.update v i t ∈ BoxCell d a w := by
  intro j
  by_cases hji : j = i
  · subst j; simpa using ht
  · simpa [Function.update_of_ne hji] using hv j

end SphericalRiesz
