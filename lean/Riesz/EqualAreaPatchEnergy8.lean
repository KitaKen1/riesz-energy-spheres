import Riesz.EqualAreaPatchNeutralized8

/-! Physical sphere points, separation and scaling of the actual ordered
off-diagonal energy. These connect the normalized local stability result
to a concrete sphere patch; probability density and global gluing remain
separate. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalRiesz
open Boundary

theorem curvedAnnularData8_injOn (F : (Fin 8 → ℝ) → Ambient9)
    (hF : CurvedAnnularData8 F) : InjOn F (UnitCube 8) := by
  intro x hx y hy hxy
  have hb := (hF.distances x hx y hy).1
  rw [hxy,dist_self] at hb
  have hn : ‖y-x‖ = 0 := by
    nlinarith [equalAreaPatchLowerDistance8_pos,norm_nonneg (y-x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

theorem curvedAnnularData8_original_nodes_injective (F : (Fin 8 → ℝ) → Ambient9)
    (hF : CurvedAnnularData8 F) (m : ℕ) (hm : 8 ≤ m) :
    Function.Injective (fun v : Fin 8 → NodeIndex m => F (cubeNode 8 m v)) := by
  intro v w hvw
  exact cubeNode_injective 8 m hm (curvedAnnularData8_injOn F hF
    (originalNode8_mem_cube m hm v) (originalNode8_mem_cube m hm w) hvw)

theorem equalAreaNormalizedE8Patch_smul_sub (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : ε ≠ 0) (x y : Fin 8 → ℝ) :
    ε • (equalAreaNormalizedE8Patch g v c ε x-equalAreaNormalizedE8Patch g v c ε y) =
      equalAreaE8Patch g v c ε x-equalAreaE8Patch g v c ε y := by
  rw [equalAreaNormalizedE8Patch_eq,equalAreaNormalizedE8Patch_eq,← smul_sub,
    smul_smul,mul_inv_cancel₀ hε,one_smul,sub_sub_sub_cancel_right]

theorem equalAreaE8Patch_scaled_distance (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (x y : Fin 8 → ℝ) :
    dist (equalAreaE8Patch g v c ε x) (equalAreaE8Patch g v c ε y) =
      ε*dist (equalAreaNormalizedE8Patch g v c ε x) (equalAreaNormalizedE8Patch g v c ε y) := by
  simp only [dist_eq_norm]
  rw [← equalAreaNormalizedE8Patch_smul_sub g v c ε hε.ne' x y,norm_smul,
    Real.norm_eq_abs,abs_of_pos hε]

theorem equalAreaE8Patch_kernel_scaling (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (x y : Fin 8 → ℝ) :
    ε^4*curvedRieszFour (equalAreaE8Patch g v c ε) x y =
      curvedRieszFour (equalAreaNormalizedE8Patch g v c ε) x y := by
  unfold curvedRieszFour
  rw [equalAreaE8Patch_scaled_distance g v c ε hε,mul_inv,mul_pow]
  field_simp

theorem equalAreaE8Patch_pair_energy_scaling (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (v c : Fin 8 → ℝ) (ε : ℝ) (hε : 0 < ε) (m : ℕ) :
    ε^4*curvedOriginalPairEnergy8 (equalAreaE8Patch g v c ε) m =
      curvedOriginalPairEnergy8 (equalAreaNormalizedE8Patch g v c ε) m := by
  classical
  unfold curvedOriginalPairEnergy8
  simp_rw [Finset.mul_sum,equalAreaE8Patch_kernel_scaling g v c ε hε]

theorem equalAreaE8Patch_original_sphere_nodes_uniform :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ v : Fin 8 → ℝ, ‖v‖ ≤ ρ →
      ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius ≤ ρ →
      ∀ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9, ∀ c ∈ UnitCube 8,
      ∀ m : ℕ, 8 ≤ m →
        (∀ w : Fin 8 → NodeIndex m, ‖equalAreaE8Patch g v c ε (cubeNode 8 m w)‖ = 1) ∧
        Function.Injective (fun w : Fin 8 → NodeIndex m =>
          equalAreaE8Patch g v c ε (cubeNode 8 m w)) := by
  obtain ⟨ρ,hρ,hρb,hdata⟩ := equalAreaNormalizedE8Patch_annular_data_uniform
  refine ⟨ρ,hρ,hρb,?_⟩
  intro v hv ε hε hs g c hc m hm
  constructor
  · intro w
    apply equalAreaE8Patch_norm
    apply equalArea_small_norm_domain
    apply (equalAreaMovingScaledE8_norm v ε _
      (unitCube8_sub_norm _ c (originalNode8_mem_cube m hm w) hc)).trans
    rw [abs_of_pos hε]
    linarith
  · intro w z hwz
    apply curvedAnnularData8_original_nodes_injective _ (hdata v hv ε hε hs g c hc) m hm
    simp only [equalAreaNormalizedE8Patch_eq,hwz]

end SphericalRiesz
