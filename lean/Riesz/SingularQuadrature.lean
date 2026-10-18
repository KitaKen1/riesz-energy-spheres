import Riesz.L1Quadrature
import Riesz.PeanoSingularWeight
import Riesz.CubeLebesgue

/-!
# Tensor quadrature from singular endpoint derivative bounds

The original corrected rule is retained. A one-dimensional Peano bound
with endpoint growth t⁻² + (1-t)⁻² gives m⁻⁵. Telescoping finite averages
and integrals lifts this bound to any finite dimension, using only pure
slice derivatives. No mixed derivative or differentiation of an integral
is needed. The smoothness assumptions apply to a regularized potential;
they are not asserted here for the actual singular E8 potential.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace SphericalRiesz.Boundary

theorem quadrature_singular_sixth_order_bound_on {m : ℕ} (hm : 8 ≤ m)
    {f : ℝ → ℝ} (hf : ContDiffOn ℝ 6 f (Set.Icc (0:ℝ) 1))
    (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ t ∈ Set.Ioo (0:ℝ) 1,
      |iteratedDerivWithin 6 f (Set.Icc (0:ℝ) 1) t| ≤ A*(t⁻¹^2+(1-t)⁻¹^2)) :
    |quadrature m f-∫ t in (0:ℝ)..1, f t| ≤ 2097152*A/(m:ℝ)^5 := by
  let g : ℝ → ℝ := fun t => iteratedDerivWithin 6 f (Set.Icc (0:ℝ) 1) (unitClamp t)
  have hg : Continuous g := continuous_unit_extension
    (hf.continuousOn_iteratedDerivWithin (by norm_num) (uniqueDiffOn_Icc (by norm_num)))
  have heq : (∫ t in (0:ℝ)..1, unitPeanoKernel m t*
      iteratedDerivWithin 6 f (Set.Icc (0:ℝ) 1) t) =
      ∫ t in (0:ℝ)..1, unitPeanoKernel m t*g t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    dsimp only [g]
    rw [unitClamp_eq ht]
  rw [quadrature_sixth_order_error_on hm hf, heq]
  apply unitPeanoKernel_singular_integral_bound hm g hg.measurable A hA
  intro t ht
  dsimp only [g]
  rw [unitClamp_eq (Set.Ioo_subset_Icc_self ht)]
  exact hb t ht

theorem quadrature_quadrature_comm (m : ℕ) (F : ℝ → ℝ → ℝ) :
    quadrature m (fun x => quadrature m (F x)) =
      quadrature m (fun y => quadrature m (fun x => F x y)) := by
  simp only [quadrature_as_node_sum]
  rw [← Finset.sum_div, ← Finset.sum_div, Finset.sum_comm]

/-- Tensor stability uses the errors of the actual one-coordinate rules. -/
theorem cubeQuadrature_error_of_slice_bound (d : ℕ) {m : ℕ} (hm : 8 ≤ m)
    {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) (C : Fin d → ℝ)
    (hb : ∀ i v, v ∈ UnitCube d →
      |quadrature m (fun t => f (Function.update v i t))-
        ∫ t in (0:ℝ)..1, f (Function.update v i t)| ≤ C i) :
    |cubeQuadrature d m f-cubeIntegral d f| ≤ ∑ i, C i := by
  induction d with
  | zero => simp [cubeQuadrature, cubeIntegral]
  | succ d ih =>
    let q : (Fin d → ℝ) → ℝ := fun v => quadrature m (fun t => f (Fin.cons t v))
    let a : (Fin d → ℝ) → ℝ := fun v => ∫ t in (0:ℝ)..1, f (Fin.cons t v)
    have hq : Continuous q := continuous_quadrature_param m (hf.comp (by fun_prop))
    have ha : Continuous a := continuous_unitIntegral_param (hf.comp (by fun_prop))
    have hqb : ∀ i v, v ∈ UnitCube d →
        |quadrature m (fun t => q (Function.update v i t))-
          ∫ t in (0:ℝ)..1, q (Function.update v i t)| ≤ C i.succ := by
      intro i v hv
      dsimp only [q]
      rw [quadrature_quadrature_comm m (fun t z => f (Fin.cons z (Function.update v i t)))]
      have hi : ∀ j : NodeIndex m, IntervalIntegrable
          (fun t => f (Fin.cons (ruleNode m j) (Function.update v i t))) volume 0 1 := by
        intro j
        exact (hf.comp (by fun_prop)).intervalIntegrable _ _
      rw [← quadrature_intervalIntegral m (fun z t => f (Fin.cons z (Function.update v i t))) hi,
        ← quadrature_sub]
      apply quadrature_abs_le hm
      intro z hz
      simpa only [← Fin.cons_update] using
        hb i.succ (Fin.cons z v) (cons_mem_unitCube hz hv)
    have hfirst := ih hq (fun i => C i.succ) hqb
    have hhead : ∀ v ∈ UnitCube d, |q v-a v| ≤ C 0 := by
      intro v hv
      simpa only [q, a, Fin.update_cons_zero] using
        hb 0 (Fin.cons 0 v) (cons_mem_unitCube (by norm_num) hv)
    have hsecond : |cubeIntegral d q-cubeIntegral d a| ≤ C 0 := by
      rw [← cubeIntegral_sub d q a hq ha]
      exact cubeIntegral_abs_le d _ _ hhead
    change |cubeQuadrature d m q-cubeIntegral d a| ≤ _
    calc
      _ ≤ |cubeQuadrature d m q-cubeIntegral d q|+|cubeIntegral d q-cubeIntegral d a| := by
        rw [show cubeQuadrature d m q-cubeIntegral d a =
          (cubeQuadrature d m q-cubeIntegral d q)+(cubeIntegral d q-cubeIntegral d a) by ring]
        exact abs_add_le _ _
      _ ≤ (∑ i : Fin d, C i.succ)+C 0 := add_le_add hfirst hsecond
      _ = _ := by rw [Fin.sum_univ_succ]; ring

theorem cubeQuadrature_error_of_slice_bound_on (d : ℕ) {m : ℕ} (hm : 8 ≤ m)
    {f : (Fin d → ℝ) → ℝ} (hf : ContinuousOn f (UnitCube d)) (C : Fin d → ℝ)
    (hb : ∀ i v, v ∈ UnitCube d →
      |quadrature m (fun t => f (Function.update v i t))-
        ∫ t in (0:ℝ)..1, f (Function.update v i t)| ≤ C i) :
    |cubeQuadrature d m f-cubeIntegral d f| ≤ ∑ i, C i := by
  let g : (Fin d → ℝ) → ℝ := fun v => f (cubeClamp d v)
  have hgf : Set.EqOn g f (UnitCube d) := fun v hv => by
    dsimp only [g]
    rw [cubeClamp_eq hv]
  have hgb : ∀ i v, v ∈ UnitCube d →
      |quadrature m (fun t => g (Function.update v i t))-
        ∫ t in (0:ℝ)..1, g (Function.update v i t)| ≤ C i := by
    intro i v hv
    have hslice : Set.EqOn (fun t => g (Function.update v i t))
        (fun t => f (Function.update v i t)) (Set.Icc (0:ℝ) 1) :=
      fun t ht => hgf (update_mem_unitCube hv i ht)
    have hq : quadrature m (fun t => g (Function.update v i t)) =
        quadrature m (fun t => f (Function.update v i t)) := by
      rw [quadrature_as_node_sum, quadrature_as_node_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact hslice (Set.Ioo_subset_Icc_self (ruleNode_mem_unit hm j))
    have hi : (∫ t in (0:ℝ)..1, g (Function.update v i t)) =
        ∫ t in (0:ℝ)..1, f (Function.update v i t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      exact hslice ht
    rw [hq, hi]
    exact hb i v hv
  have h := cubeQuadrature_error_of_slice_bound d hm (continuous_cube_extension hf) C hgb
  rw [cubeQuadrature_congr d m hm hgf, cubeIntegral_congr d hgf] at h
  exact h

theorem cubeQuadrature_singular_sixth_order_bound_on (d : ℕ) {m : ℕ} (hm : 8 ≤ m)
    {f : (Fin d → ℝ) → ℝ} (hf : ContinuousOn f (UnitCube d))
    (hs : ∀ i v, v ∈ UnitCube d →
      ContDiffOn ℝ 6 (fun t => f (Function.update v i t)) (Set.Icc (0:ℝ) 1))
    (A : Fin d → ℝ) (hA : ∀ i, 0 ≤ A i)
    (hb : ∀ i v, v ∈ UnitCube d → ∀ t ∈ Set.Ioo (0:ℝ) 1,
      |iteratedDerivWithin 6 (fun u => f (Function.update v i u))
        (Set.Icc (0:ℝ) 1) t| ≤ A i*(t⁻¹^2+(1-t)⁻¹^2)) :
    |cubeQuadrature d m f-∫ x in UnitCube d, f x| ≤
      (2097152/(m:ℝ)^5)*(∑ i, A i) := by
  rw [← cubeIntegral_eq_setIntegral_on d f hf]
  have h := cubeQuadrature_error_of_slice_bound_on d hm hf
    (fun i => 2097152*A i/(m:ℝ)^5) (fun i v hv =>
      quadrature_singular_sixth_order_bound_on hm (hs i v hv) (A i) (hA i) (hb i v hv))
  convert h using 1
  simp only [div_eq_mul_inv]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

#print axioms quadrature_singular_sixth_order_bound_on
#print axioms quadrature_quadrature_comm
#print axioms cubeQuadrature_error_of_slice_bound
#print axioms cubeQuadrature_error_of_slice_bound_on
#print axioms cubeQuadrature_singular_sixth_order_bound_on

end SphericalRiesz.Boundary
