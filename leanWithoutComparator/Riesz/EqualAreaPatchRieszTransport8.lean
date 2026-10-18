import Riesz.EqualAreaPatchTransport8
import Riesz.EqualAreaPatchEnergy8

/-! Actual spherical Riesz row and double-background integrals on a physical
patch, including their exact scaling to the normalized local chart. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace SphericalRiesz
open Boundary

theorem equalAreaE8SpherePatch8_kernel_integrable (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 8)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8) (p : Sphere8) :
    IntegrableOn (fun x => (dist (p : Ambient9) (equalAreaE8Patch g v c ε x))⁻¹ ^ 4)
      (UnitCube 8) := by
  apply (equalAreaE8SpherePatch8_integrable_iff g v c ε hε hc hsmall
    (fun y => (dist (p : Ambient9) y)⁻¹ ^ 4)).mp
  exact (sphereKernel4_integrable p).integrableOn

theorem equalAreaE8Patch_kernel_integrable (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 8)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8) (x : UnitCube 8) :
    IntegrableOn (curvedRieszFour (equalAreaE8Patch g v c ε) x) (UnitCube 8) :=
  equalAreaE8SpherePatch8_kernel_integrable g v c ε hε hc hsmall
    (equalAreaE8CubeEmbedding8 g v c ε hε hc hsmall x)

theorem equalAreaNormalizedE8Patch_kernel_integrable (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 8)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8) (x : UnitCube 8) :
    IntegrableOn (curvedRieszFour (equalAreaNormalizedE8Patch g v c ε) x) (UnitCube 8) := by
  have he : curvedRieszFour (equalAreaNormalizedE8Patch g v c ε) x =
      (fun y => ε^4 * curvedRieszFour (equalAreaE8Patch g v c ε) x y) := by
    funext y
    exact (equalAreaE8Patch_kernel_scaling g v c ε hε x y).symm
  rw [he]
  exact (equalAreaE8Patch_kernel_integrable g v c ε hε hc hsmall x).const_mul _

theorem equalAreaE8SpherePatch8_doubleIntegral (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 8)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8) (f : Ambient9 → Ambient9 → ℝ) :
    (∫ y in equalAreaE8SpherePatch8 g v c ε (UnitCube 8),
      ∫ z in equalAreaE8SpherePatch8 g v c ε (UnitCube 8), f y z ∂sphereProbability8
        ∂sphereProbability8) = equalAreaE8PatchProbabilityDensity8 ε ^ 2 *
      ∫ x in UnitCube 8, ∫ w in UnitCube 8,
        f (equalAreaE8Patch g v c ε x) (equalAreaE8Patch g v c ε w) := by
  rw [equalAreaE8SpherePatch8_integral g v c ε hε hc hsmall
    (fun y => ∫ z in equalAreaE8SpherePatch8 g v c ε (UnitCube 8), f y z ∂sphereProbability8)]
  simp_rw [equalAreaE8SpherePatch8_integral g v c ε hε hc hsmall,
    integral_const_mul]
  ring

theorem equalAreaE8SpherePatch8_potential (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 8)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8) (x : UnitCube 8) :
    (∫ y in equalAreaE8SpherePatch8 g v c ε (UnitCube 8),
      sphereKernel4 (equalAreaE8CubeEmbedding8 g v c ε hε hc hsmall x) y
        ∂sphereProbability8) = equalAreaE8PatchProbabilityDensity8 ε *
      curvedPotential8 (equalAreaE8Patch g v c ε) x := by
  exact equalAreaE8SpherePatch8_integral g v c ε hε hc hsmall
    (fun y => (dist (equalAreaE8Patch g v c ε x) y)⁻¹ ^ 4)

theorem equalAreaE8SpherePatch8_scaled_potential (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 8)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8) (x : UnitCube 8) :
    ε^4 * (∫ y in equalAreaE8SpherePatch8 g v c ε (UnitCube 8),
      sphereKernel4 (equalAreaE8CubeEmbedding8 g v c ε hε hc hsmall x) y
        ∂sphereProbability8) = equalAreaE8PatchProbabilityDensity8 ε *
      curvedPotential8 (equalAreaNormalizedE8Patch g v c ε) x := by
  rw [equalAreaE8SpherePatch8_potential g v c ε hε hc hsmall]
  unfold curvedPotential8
  rw [mul_left_comm,← integral_const_mul]
  simp_rw [equalAreaE8Patch_kernel_scaling g v c ε hε]

theorem equalAreaE8SpherePatch8_background (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 8)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8) :
    (∫ y in equalAreaE8SpherePatch8 g v c ε (UnitCube 8),
      ∫ z in equalAreaE8SpherePatch8 g v c ε (UnitCube 8), sphereKernel4 y z
        ∂sphereProbability8 ∂sphereProbability8) =
      equalAreaE8PatchProbabilityDensity8 ε ^ 2 *
        ∫ x in UnitCube 8, curvedPotential8 (equalAreaE8Patch g v c ε) x := by
  exact equalAreaE8SpherePatch8_doubleIntegral g v c ε hε hc hsmall
    (fun y z => (dist y z)⁻¹ ^ 4)

theorem equalAreaE8SpherePatch8_scaled_background (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 8)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius ≤ 1/8) :
    ε^4 * (∫ y in equalAreaE8SpherePatch8 g v c ε (UnitCube 8),
      ∫ z in equalAreaE8SpherePatch8 g v c ε (UnitCube 8), sphereKernel4 y z
        ∂sphereProbability8 ∂sphereProbability8) =
      equalAreaE8PatchProbabilityDensity8 ε ^ 2 *
        ∫ x in UnitCube 8, curvedPotential8 (equalAreaNormalizedE8Patch g v c ε) x := by
  rw [equalAreaE8SpherePatch8_background g v c ε hε hc hsmall]
  unfold curvedPotential8
  rw [mul_left_comm,← integral_const_mul]
  simp_rw [← integral_const_mul,equalAreaE8Patch_kernel_scaling g v c ε hε]

end SphericalRiesz
