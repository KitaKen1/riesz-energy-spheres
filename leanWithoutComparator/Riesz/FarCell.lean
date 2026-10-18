import Riesz.FlatKernel

/-!
# Actual inverse-fourth kernel error on a separated flat box

The only geometric input is a positive lower bound for the squared
Euclidean distance on the whole box. All continuity and sixth-derivative
inputs of the quadrature rule are proved here for the actual kernel.
No construction of a lattice recovery sequence is claimed by this file.
-/

set_option autoImplicit false
noncomputable section

namespace SphericalRiesz
open Boundary

theorem flatRieszFour_contDiffOn_box (d : ℕ) (a w x : Fin d → ℝ)
    (r : ℝ) (hr : 0 < r)
    (hsep : ∀ v ∈ BoxCell d a w, r^2 ≤ squaredDistance d x v) :
    ContDiffOn ℝ 6 (flatRieszFour d x) (BoxCell d a w) := by
  unfold flatRieszFour
  apply ContDiffOn.div contDiffOn_const
  · unfold squaredDistance
    fun_prop
  · intro v hv
    exact pow_ne_zero 2 ((sq_pos_of_pos hr).trans_le (hsep v hv)).ne'

theorem flatRieszFour_contDiffOn_slice_box (d : ℕ) (a w x : Fin d → ℝ)
    (r : ℝ) (hr : 0 < r)
    (hsep : ∀ v ∈ BoxCell d a w, r^2 ≤ squaredDistance d x v)
    (i : Fin d) (v : Fin d → ℝ) (hv : v ∈ BoxCell d a w) :
    ContDiffOn ℝ 6 (fun t => flatRieszFour d x (Function.update v i t))
      (Set.Icc (a i) (a i+w i)) := by
  rw [flatRieszFour_slice]
  apply quadraticKernel_contDiffOn
  intro t ht
  have h := ((sq_pos_of_pos hr).trans_le (hsep _ (update_mem_boxCell hv i ht))).ne'
  rwa [squaredDistance_update] at h

theorem flatRieszFour_sixth_derivative_bound_box (d : ℕ) (a w x : Fin d → ℝ)
    (hw : ∀ i, 0 < w i) (r : ℝ) (hr : 0 < r)
    (hsep : ∀ v ∈ BoxCell d a w, r^2 ≤ squaredDistance d x v)
    (i : Fin d) (v : Fin d → ℝ) (hv : v ∈ BoxCell d a w)
    (t : ℝ) (ht : t ∈ Set.Icc (a i) (a i+w i)) :
    |iteratedDerivWithin 6 (fun u => flatRieszFour d x (Function.update v i u))
      (Set.Icc (a i) (a i+w i)) t| ≤ 322560/r^10 := by
  have hq : ∀ u ∈ Set.Icc (a i) (a i+w i),
      (u-x i)^2+perpendicularSquare d x v i ≠ 0 := by
    intro u hu
    have h := ((sq_pos_of_pos hr).trans_le (hsep _ (update_mem_boxCell hv i hu))).ne'
    rwa [squaredDistance_update] at h
  rw [flatRieszFour_slice, iteratedDerivWithin_quadraticKernel 6 (by omega)
    _ _ (uniqueDiffOn_Icc (by linarith [hw i])) hq ht]
  apply quadraticKernelDerivative_six_bound_radius _ _ _ r (perpendicularSquare_nonneg d x v i) hr
  simpa only [squaredDistance_update] using hsep _ (update_mem_boxCell hv i ht)

/-- No derivative estimate is an assumption: only actual distance separation. -/
theorem flatRieszFour_box_error (d : ℕ) {m : ℕ} (hm : 8 ≤ m) (a w x : Fin d → ℝ)
    (hw : ∀ i, 0 < w i) (r : ℝ) (hr : 0 < r)
    (hsep : ∀ v ∈ BoxCell d a w, r^2 ≤ squaredDistance d x v) :
    |boxQuadrature d m a w (flatRieszFour d x)-boxIntegral d a w (flatRieszFour d x)| ≤
      (64/(m : ℝ)^6)*(∏ i, w i)*(∑ i, (w i)^6*(322560/r^10)) := by
  apply boxQuadrature_sixth_order_bound_on d hm a w hw
    (flatRieszFour_contDiffOn_box d a w x r hr hsep).continuousOn
    (flatRieszFour_contDiffOn_slice_box d a w x r hr hsep) (fun _ => 322560/r^10)
  exact flatRieszFour_sixth_derivative_bound_box d a w x hw r hr hsep

theorem flatRieszFour_uniform_box_error (d : ℕ) {m : ℕ} (hm : 8 ≤ m)
    (a x : Fin d → ℝ) (w : ℝ) (hw : 0 < w) (r : ℝ) (hr : 0 < r)
    (hsep : ∀ v ∈ BoxCell d a (fun _ => w), r^2 ≤ squaredDistance d x v) :
    |boxQuadrature d m a (fun _ => w) (flatRieszFour d x)-
      boxIntegral d a (fun _ => w) (flatRieszFour d x)| ≤
        (64/(m : ℝ)^6)*w^(d+6)*((d : ℝ)*(322560/r^10)) := by
  have h := boxQuadrature_uniform_sixth_order_bound_on d hm a w hw
    (flatRieszFour_contDiffOn_box d a (fun _ => w) x r hr hsep).continuousOn
    (flatRieszFour_contDiffOn_slice_box d a (fun _ => w) x r hr hsep) (fun _ => 322560/r^10)
    (flatRieszFour_sixth_derivative_bound_box d a (fun _ => w) x (fun _ => hw) r hr hsep)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h

#print axioms flatRieszFour_sixth_derivative_bound_box
#print axioms flatRieszFour_box_error
#print axioms flatRieszFour_uniform_box_error

end SphericalRiesz
