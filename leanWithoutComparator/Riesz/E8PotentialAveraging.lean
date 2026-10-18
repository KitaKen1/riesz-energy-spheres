import Riesz.E8PotentialRegularity

/-!
# Averaging the actual far row error

Symmetry and a finite-sum/integral interchange turn the far-potential
quadrature error into the integral of the already bounded actual row
errors. No derivative of the potential is taken. At r=R/m the scaled
error is at most C/R². The near-potential average still has to be
handled before this proves the flat background limit.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace SphericalRiesz
open Boundary

theorem e8Kernel_symm (x y : Fin 8 → ℝ) :
    obliqueRieszFour 8 e8Map x y = obliqueRieszFour 8 e8Map y x := by
  simp only [obliqueRieszFour_eq_dist, dist_comm]

theorem e8Near_symm (r : ℝ) (x y : Fin 8 → ℝ) :
    nearObliqueRieszFour 8 e8Map r x y = nearObliqueRieszFour 8 e8Map r y x := by
  unfold nearObliqueRieszFour
  rw [e8Kernel_symm]
  congr 1
  rw [show r⁻¹ • (y-x) = -(r⁻¹ • (x-y)) by rw [← smul_neg, neg_sub]]
  exact (outerUnitBump 8).neg _

theorem e8Far_symm (r : ℝ) (x y : Fin 8 → ℝ) :
    farObliqueRieszFour 8 e8Map r x y = farObliqueRieszFour 8 e8Map r y x := by
  unfold farObliqueRieszFour
  rw [e8Kernel_symm, e8Near_symm]

theorem cubeQuadrature_continuous_parameter (d m : ℕ)
    {F : (Fin d → ℝ) × (Fin d → ℝ) → ℝ} (hF : Continuous F) :
    Continuous (fun y => cubeQuadrature d m (fun x => F (x,y))) := by
  simp_rw [cubeQuadrature_as_node_sum]
  exact (continuous_finsetSum _ (fun v _ =>
    hF.comp (continuous_const.prodMk continuous_id))).div_const _

theorem cubeQuadrature_setIntegral_comm (d m : ℕ)
    {F : (Fin d → ℝ) × (Fin d → ℝ) → ℝ} (hF : Continuous F) :
    cubeQuadrature d m (fun x => ∫ y in UnitCube d, F (x,y)) =
      ∫ y in UnitCube d, cubeQuadrature d m (fun x => F (x,y)) := by
  simp_rw [cubeQuadrature_as_node_sum]
  rw [integral_div, integral_finsetSum]
  intro v _
  exact (hF.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
    (unitCube_isCompact d)

theorem e8FarPotential_quadrature_integral_identity (r : ℝ) (hr : 0 < r) (m : ℕ) :
    cubeQuadrature 8 m (e8FarPotential r)-∫ y in UnitCube 8, e8FarPotential r y =
      ∫ y in UnitCube 8,
        (cubeQuadrature 8 m (farObliqueRieszFour 8 e8Map r y)-e8FarPotential r y) := by
  have hF := (e8Far_joint_contDiff r hr).continuous
  have hQ := cubeQuadrature_continuous_parameter 8 m hF
  have heq : cubeQuadrature 8 m (e8FarPotential r) =
      ∫ y in UnitCube 8, cubeQuadrature 8 m (farObliqueRieszFour 8 e8Map r y) := by
    change cubeQuadrature 8 m (fun x => ∫ y in UnitCube 8,
      farObliqueRieszFour 8 e8Map r x y) = _
    rw [cubeQuadrature_setIntegral_comm 8 m hF]
    simp_rw [e8Far_symm r]
  rw [heq, integral_sub]
  · have heqQ : (fun y => cubeQuadrature 8 m (fun x =>
        farObliqueRieszFour 8 e8Map r x y)) =
      (fun y => cubeQuadrature 8 m (farObliqueRieszFour 8 e8Map r y)) := by
      funext y
      simp_rw [e8Far_symm r]
    rw [heqQ] at hQ
    exact hQ.continuousOn.integrableOn_compact (unitCube_isCompact 8)
  · exact (e8FarPotential_continuous r hr).continuousOn.integrableOn_compact
      (unitCube_isCompact 8)

theorem e8FarPotential_quadrature_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 8 ≤ m → ∀ r : ℝ, 0 < r → 1/(m:ℝ) ≤ r →
      |cubeQuadrature 8 m (e8FarPotential r)-∫ x in UnitCube 8, e8FarPotential r x|
        ≤ C/((m:ℝ)^6*r^2) := by
  obtain ⟨C,hC,hb⟩ := farObliqueRieszFour_quadrature_bound e8Map e8Map_injective
  refine ⟨C,hC,fun m hm r hr hmesh => ?_⟩
  rw [e8FarPotential_quadrature_integral_identity r hr m]
  have hF := (e8Far_joint_contDiff r hr).continuous
  have hQ : Continuous (fun y => cubeQuadrature 8 m (farObliqueRieszFour 8 e8Map r y)) := by
    have h := cubeQuadrature_continuous_parameter 8 m hF
    simpa only [e8Far_symm r] using h
  have hdiff : Continuous (fun y =>
      cubeQuadrature 8 m (farObliqueRieszFour 8 e8Map r y)-e8FarPotential r y) :=
    hQ.sub (e8FarPotential_continuous r hr)
  rw [← cubeIntegral_eq_setIntegral 8 _ hdiff]
  apply cubeIntegral_abs_le
  intro x _
  have h := hb m hm r hr hmesh x
  rw [cubeIntegral_eq_setIntegral_on 8 _
    (farObliqueRieszFour_contDiffOn_cube 8 e8Map e8Map_injective r hr x).continuousOn] at h
  exact h

theorem e8FarPotential_scaled_quadrature_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 8 ≤ m → ∀ R : ℝ, 1 ≤ R →
      |(m:ℝ)^4*(cubeQuadrature 8 m (e8FarPotential (R/(m:ℝ)))-
        ∫ x in UnitCube 8, e8FarPotential (R/(m:ℝ)) x)| ≤ C/R^2 := by
  obtain ⟨C,hC,hb⟩ := e8FarPotential_quadrature_bound
  refine ⟨C,hC,fun m hm R hR => ?_⟩
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hR0 : 0 < R := by linarith
  have hmesh : 1/(m:ℝ) ≤ R/(m:ℝ) := div_le_div_of_nonneg_right hR hm0.le
  rw [abs_mul, abs_of_nonneg (pow_nonneg hm0.le 4)]
  calc
    _ ≤ (m:ℝ)^4*(C/((m:ℝ)^6*(R/(m:ℝ))^2)) :=
      mul_le_mul_of_nonneg_left (hb m hm _ (div_pos hR0 hm0) hmesh) (by positivity)
    _ = C/R^2 := by field_simp [hm0.ne',hR0.ne']

#print axioms e8Kernel_symm
#print axioms e8Near_symm
#print axioms e8Far_symm
#print axioms cubeQuadrature_continuous_parameter
#print axioms cubeQuadrature_setIntegral_comm
#print axioms e8FarPotential_quadrature_integral_identity
#print axioms e8FarPotential_quadrature_bound
#print axioms e8FarPotential_scaled_quadrature_bound

end SphericalRiesz
