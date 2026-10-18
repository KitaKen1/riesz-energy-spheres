import Riesz.NormalizedBumpError
import Riesz.CrossPatchPhysical8
import Riesz.AmbientBumpSquare9

/-! Localized bump errors on the actual small E8 sphere patches.

The normalized patch charts have uniform `C⁶` bounds (`equalAreaNormalizedE8Patch_C7_uniform`)
and uniform lower and upper Lipschitz constants on the cube, so the abstract localized bump error
applies to every small patch with one constant.  In physical coordinates, for the ambient bump
`e^{-2t|Φx-z|²}` with `τ = 2tε²`,

  `|Q_n - I| ≤ K n⁻⁶ (1+τ³) ∫_cube e^{-(t/4)|Φx-z|²} dx`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
open Boundary

/-- Upper derivative and Lipschitz constant of the normalized patch charts. -/
def patchChartUpper8 : ℝ := ‖equalAreaFlatDerivative8‖+1

/-- Lower Lipschitz constant of the normalized patch charts. -/
def patchChartLower8 : ℝ := 1/(2*(1+‖e8InverseMap‖))

theorem one_le_patchChartUpper8 : 1 ≤ patchChartUpper8 := by
  unfold patchChartUpper8
  linarith [norm_nonneg equalAreaFlatDerivative8]

theorem patchChartLower8_pos : 0 < patchChartLower8 := by
  unfold patchChartLower8
  positivity

theorem smallPatch_normalized_chart_bounds :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ p : SmallE8CubePatch8, ‖p.v‖ ≤ ρ → p.ε*equalAreaScaleRadius ≤ ρ →
      (∀ x ∈ UnitCube 8, ContDiffAt ℝ 6 (equalAreaNormalizedE8Patch p.g p.v p.c p.ε) x) ∧
      (∀ x ∈ UnitCube 8, ∀ j, 1 ≤ j → j ≤ 6 →
        ‖iteratedFDeriv ℝ j (equalAreaNormalizedE8Patch p.g p.v p.c p.ε) x‖ ≤ patchChartUpper8) ∧
      (∀ x ∈ UnitCube 8, ∀ y ∈ UnitCube 8, patchChartLower8*‖x-y‖ ≤
        ‖equalAreaNormalizedE8Patch p.g p.v p.c p.ε x-equalAreaNormalizedE8Patch p.g p.v p.c p.ε y‖) ∧
      (∀ x ∈ UnitCube 8, ∀ y ∈ UnitCube 8,
        ‖equalAreaNormalizedE8Patch p.g p.v p.c p.ε x-equalAreaNormalizedE8Patch p.g p.v p.c p.ε y‖ ≤
          patchChartUpper8*‖x-y‖) := by
  obtain ⟨ρ₁, hρ₁, hρ₁', h₁⟩ := equalAreaNormalizedE8Patch_C7_uniform 1 one_pos
  obtain ⟨ρ₂, hρ₂, -, h₂⟩ := equalAreaNormalizedE8Patch_lower_distance_uniform
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, (min_le_left _ _).trans hρ₁', ?_⟩
  intro p hv hε
  have hv₁ : ‖p.v‖ ≤ ρ₁ := hv.trans (min_le_left _ _)
  have hv₂ : ‖p.v‖ ≤ ρ₂ := hv.trans (min_le_right _ _)
  have hε₁ : p.ε*equalAreaScaleRadius ≤ ρ₁ := hε.trans (min_le_left _ _)
  have hε₂ : p.ε*equalAreaScaleRadius ≤ ρ₂ := hε.trans (min_le_right _ _)
  have hb := fun x hx => h₁ p.v hv₁ p.ε p.ε_pos hε₁ p.g p.c p.c_mem x hx
  have hflat : ‖equalAreaRotatedFlatDerivative8 p.g‖ ≤ ‖equalAreaFlatDerivative8‖ :=
    equalAreaRotation_comp_norm_le p.g equalAreaFlatDerivative8
  have hfd : ∀ x ∈ UnitCube 8,
      ‖fderiv ℝ (equalAreaNormalizedE8Patch p.g p.v p.c p.ε) x‖ ≤ patchChartUpper8 := by
    intro x hx
    have h := (hb x hx).2.2.1
    calc ‖fderiv ℝ (equalAreaNormalizedE8Patch p.g p.v p.c p.ε) x‖
        = ‖(fderiv ℝ (equalAreaNormalizedE8Patch p.g p.v p.c p.ε) x-
            equalAreaRotatedFlatDerivative8 p.g)+equalAreaRotatedFlatDerivative8 p.g‖ := by
          congr 1; abel
      _ ≤ ‖fderiv ℝ (equalAreaNormalizedE8Patch p.g p.v p.c p.ε) x-
            equalAreaRotatedFlatDerivative8 p.g‖+‖equalAreaRotatedFlatDerivative8 p.g‖ :=
          norm_add_le _ _
      _ ≤ 1+‖equalAreaFlatDerivative8‖ := add_le_add h hflat
      _ = patchChartUpper8 := by rw [patchChartUpper8]; ring
  refine ⟨fun x hx => (hb x hx).1.of_le (by simp), ?_, ?_, ?_⟩
  · intro x hx j hj hj6
    rcases Nat.lt_or_ge j 2 with h | h
    · have : j = 1 := by omega
      subst this
      rw [norm_iteratedFDeriv_one]
      exact hfd x hx
    · exact ((hb x hx).2.2.2 j h (by omega)).trans one_le_patchChartUpper8
  · intro x hx y hy
    have h := h₂ p.v hv₂ p.ε p.ε_pos hε₂ p.g p.c p.c_mem x hx y hy
    rw [dist_eq_norm] at h
    simpa only [patchChartLower8] using h
  · intro x hx y hy
    exact unitCube8_convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => ((hb z hz).1.differentiableAt (by simp))) hfd hy hx

/-- The patch map in normalized form. -/
theorem smallE8CubeMap8_sub_eq (p : SmallE8CubePatch8) (z : Ambient9) (x : Fin 8 → ℝ) :
    smallE8CubeMap8 p x-z = p.ε • (equalAreaNormalizedE8Patch p.g p.v p.c p.ε x-
      p.ε⁻¹ • (z-smallE8CubeMap8 p p.c)) := by
  have hε := p.ε_pos.ne'
  rw [equalAreaNormalizedE8Patch_eq, smul_sub, smul_smul, smul_smul, mul_inv_cancel₀ hε, one_smul,
    one_smul]
  change equalAreaE8Patch p.g p.v p.c p.ε x-z = _
  unfold smallE8CubeMap8
  abel

theorem smallE8CubeMap8_sub_norm_sq (p : SmallE8CubePatch8) (z : Ambient9) (x : Fin 8 → ℝ) :
    ‖smallE8CubeMap8 p x-z‖^2 = p.ε^2*‖equalAreaNormalizedE8Patch p.g p.v p.c p.ε x-
      p.ε⁻¹ • (z-smallE8CubeMap8 p p.c)‖^2 := by
  rw [smallE8CubeMap8_sub_eq, norm_smul, Real.norm_eq_abs, abs_of_pos p.ε_pos, mul_pow]

/-- Localized sixth-order error of an ambient Gaussian bump on one small patch. -/
theorem smallPatch_bump_quadrature :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ p : SmallE8CubePatch8, ‖p.v‖ ≤ ρ → p.ε*equalAreaScaleRadius ≤ ρ →
      ∀ n : ℕ, 8 ≤ n → ∀ t : ℝ, 0 < t → 2*t*p.ε^2*patchChartLower8^2/128 ≤ (n:ℝ)^2 →
      ∀ z : Ambient9,
      |cubeQuadrature 8 n (fun x => ambientBump9 t (smallE8CubeMap8 p x) z)-
        cubeIntegral 8 (fun x => ambientBump9 t (smallE8CubeMap8 p x) z)| ≤
        bumpErrorConst patchChartUpper8 patchChartLower8/(n:ℝ)^6*(1+(2*t*p.ε^2)^3)*
          cubeIntegral 8 (fun x => Real.exp (-(t/4*‖smallE8CubeMap8 p x-z‖^2))) := by
  obtain ⟨ρ, hρ, hρ1, hb⟩ := smallPatch_normalized_chart_bounds
  refine ⟨ρ, hρ, hρ1, ?_⟩
  intro p hv hε n hn t ht hτn z
  obtain ⟨hcd, hder, hlow, hup⟩ := hb p hv hε
  set w := p.ε⁻¹ • (z-smallE8CubeMap8 p p.c) with hw
  set τ := 2*t*p.ε^2 with hτdef
  have hτ : 0 < τ := by have := p.ε_pos; positivity
  have hf1 : (fun x => ambientBump9 t (smallE8CubeMap8 p x) z) =
      fun x => Real.exp (-(τ*‖equalAreaNormalizedE8Patch p.g p.v p.c p.ε x-w‖^2)) := by
    funext x
    unfold ambientBump9
    rw [smallE8CubeMap8_sub_norm_sq, ← hw, hτdef]
    ring_nf
  have hf2 : (fun x => Real.exp (-(t/4*‖smallE8CubeMap8 p x-z‖^2))) =
      fun x => Real.exp (-(τ/8*‖equalAreaNormalizedE8Patch p.g p.v p.c p.ε x-w‖^2)) := by
    funext x
    rw [smallE8CubeMap8_sub_norm_sq, ← hw, hτdef]
    ring_nf
  rw [hf1, hf2]
  exact normalized_bump_quadrature_error one_le_patchChartUpper8 patchChartLower8_pos hcd hder
    hlow hup hn hτ (by rw [hτdef]; exact hτn) w

end SphericalRiesz
