import Riesz.E8NearQuadrature

/-! Boundary-uniform full singular flat E8 rows; sharp coefficients and sphere recovery remain open. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace SphericalRiesz
open Boundary

theorem e8Kernel_integrableOn_cube (x : Fin 8 → ℝ) :
    IntegrableOn (obliqueRieszFour 8 e8Map x) (UnitCube 8) := by
  have hf : IntegrableOn (farObliqueRieszFour 8 e8Map 2 x) (UnitCube 8) :=
    (farObliqueRieszFour_contDiffOn_cube 8 e8Map e8Map_injective 2 (by norm_num) x).continuousOn.integrableOn_compact
      (unitCube_isCompact 8)
  have hn := (e8Near_integrable (2/2) (by norm_num) x).integrableOn (s := UnitCube 8)
  exact (hf.add hn).congr_fun
    (fun y _ => oblique_far_near_kernel_partition 8 e8Map 2 x y) (unitCube_measurableSet 8)

theorem e8Kernel_integral_partition (r : ℝ) (hr : 0 < r) (x : Fin 8 → ℝ) :
    (∫ y in UnitCube 8, obliqueRieszFour 8 e8Map x y) =
      (∫ y in UnitCube 8, farObliqueRieszFour 8 e8Map r x y)+
        ∫ y in UnitCube 8, nearObliqueRieszFour 8 e8Map (r/2) x y := by
  have hf : IntegrableOn (farObliqueRieszFour 8 e8Map r x) (UnitCube 8) :=
    (farObliqueRieszFour_contDiffOn_cube 8 e8Map e8Map_injective r hr x).continuousOn.integrableOn_compact
      (unitCube_isCompact 8)
  have hn := (e8Near_integrable (r/2) (by positivity) x).integrableOn (s := UnitCube 8)
  rw [← integral_add hf hn]
  apply setIntegral_congr_fun (unitCube_measurableSet 8)
  intro y _
  exact (oblique_far_near_kernel_partition 8 e8Map r x y).symm

theorem e8Kernel_quadrature_partition (m : ℕ) (r : ℝ) (x : Fin 8 → ℝ) :
    cubeQuadrature 8 m (obliqueRieszFour 8 e8Map x) =
      cubeQuadrature 8 m (farObliqueRieszFour 8 e8Map r x)+
        cubeQuadrature 8 m (nearObliqueRieszFour 8 e8Map (r/2) x) := by
  have h := cubeQuadrature_sub 8 m (obliqueRieszFour 8 e8Map x)
    (nearObliqueRieszFour 8 e8Map (r/2) x)
  change cubeQuadrature 8 m (farObliqueRieszFour 8 e8Map r x) = _ at h
  linarith

/-- A full singular flat row, uniform over every original center index. -/
theorem e8FlatRow_error_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 8 ≤ m → ∀ v : Fin 8 → NodeIndex m,
      |cubeQuadrature 8 m (obliqueRieszFour 8 e8Map (cubeNode 8 m v))-
        ∫ y in UnitCube 8, obliqueRieszFour 8 e8Map (cubeNode 8 m v) y| ≤ C/(m:ℝ)^4 := by
  obtain ⟨Cf, hCf, hfar⟩ := farObliqueRieszFour_quadrature_bound e8Map e8Map_injective
  let Cq := (4:ℝ)^8/e8SeparationConstant^4
  have hnC := e8NearIntegralConstant_nonneg
  refine ⟨Cf+Cq+e8NearIntegralConstant/16, by
    dsimp only [Cq]
    positivity, ?_⟩
  intro m hm v
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  let x := cubeNode 8 m v
  let r := 1/(m:ℝ)
  have hr : 0 < r := div_pos one_pos hm0
  have hf := hfar m hm r hr le_rfl x
  rw [cubeIntegral_eq_setIntegral_on 8 _
    (farObliqueRieszFour_contDiffOn_cube 8 e8Map e8Map_injective r hr x).continuousOn] at hf
  have hfarScale : Cf/((m:ℝ)^6*r^2) = Cf/(m:ℝ)^4 := by
    dsimp only [r]
    field_simp
  rw [hfarScale] at hf
  have hq := e8Near_quadrature_bound hm (1/2) (by norm_num) v
  have hrad : (1/2:ℝ)/(m:ℝ) = r/2 := by dsimp only [r]; ring
  rw [hrad] at hq
  have hq' : |cubeQuadrature 8 m (nearObliqueRieszFour 8 e8Map (r/2) x)| ≤ Cq/(m:ℝ)^4 := by
    dsimp only [Cq, x]
    convert hq using 1; norm_num; ring
  have hi := e8Near_cubeIntegral_bound (r/2) (by positivity) x
  have hnearScale : e8NearIntegralConstant*(r/2)^4 = (e8NearIntegralConstant/16)/(m:ℝ)^4 := by
    dsimp only [r]
    field_simp
    norm_num
  rw [hnearScale] at hi
  have heq : cubeQuadrature 8 m (obliqueRieszFour 8 e8Map x)-
      (∫ y in UnitCube 8, obliqueRieszFour 8 e8Map x y) =
      (cubeQuadrature 8 m (farObliqueRieszFour 8 e8Map r x)-
        ∫ y in UnitCube 8, farObliqueRieszFour 8 e8Map r x y)+
      (cubeQuadrature 8 m (nearObliqueRieszFour 8 e8Map (r/2) x)-
        ∫ y in UnitCube 8, nearObliqueRieszFour 8 e8Map (r/2) x y) := by
    rw [e8Kernel_quadrature_partition m r x, e8Kernel_integral_partition r hr x]
    ring
  change |cubeQuadrature 8 m (obliqueRieszFour 8 e8Map x)-
    ∫ y in UnitCube 8, obliqueRieszFour 8 e8Map x y| ≤ _
  rw [heq]
  calc
    _ ≤ |cubeQuadrature 8 m (farObliqueRieszFour 8 e8Map r x)-
          ∫ y in UnitCube 8, farObliqueRieszFour 8 e8Map r x y|+
        (|cubeQuadrature 8 m (nearObliqueRieszFour 8 e8Map (r/2) x)|+
          |∫ y in UnitCube 8, nearObliqueRieszFour 8 e8Map (r/2) x y|) :=
      (abs_add_le _ _).trans (add_le_add le_rfl (abs_sub _ _))
    _ ≤ Cf/(m:ℝ)^4+(Cq/(m:ℝ)^4+(e8NearIntegralConstant/16)/(m:ℝ)^4) :=
      add_le_add hf (add_le_add hq' hi)
    _ = _ := by ring

#print axioms e8Kernel_integrableOn_cube
#print axioms e8Kernel_integral_partition
#print axioms e8Kernel_quadrature_partition
#print axioms e8FlatRow_error_bound

end SphericalRiesz
