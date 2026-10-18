import Riesz.SmallPatchBumpError8
import Riesz.NormalizedBumpErrorSmall

/-! Localized sixth-order error of an ambient Gaussian bump on one small patch, for small
`τ = 2 t ε²` (stage NEG): the factor `1+τ³` becomes `√τ` when `τ ≤ 1`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
open Boundary

/-- Localized sixth-order error of an ambient Gaussian bump on one small patch, `2tε² ≤ 1`. -/
theorem smallPatch_bump_quadrature_small :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ p : SmallE8CubePatch8, ‖p.v‖ ≤ ρ → p.ε*equalAreaScaleRadius ≤ ρ →
      ∀ n : ℕ, 8 ≤ n → ∀ t : ℝ, 0 < t → 2*t*p.ε^2 ≤ 1 →
      2*t*p.ε^2*patchChartLower8^2/128 ≤ (n:ℝ)^2 →
      ∀ z : Ambient9,
      |cubeQuadrature 8 n (fun x => ambientBump9 t (smallE8CubeMap8 p x) z)-
        cubeIntegral 8 (fun x => ambientBump9 t (smallE8CubeMap8 p x) z)| ≤
        bumpErrorConstSmall patchChartUpper8 patchChartLower8/(n:ℝ)^6*Real.sqrt (2*t*p.ε^2)*
          cubeIntegral 8 (fun x => Real.exp (-(t/4*‖smallE8CubeMap8 p x-z‖^2))) := by
  obtain ⟨ρ, hρ, hρ1, hb⟩ := smallPatch_normalized_chart_bounds
  refine ⟨ρ, hρ, hρ1, ?_⟩
  intro p hv hε n hn t ht hτ1 hτn z
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
  exact normalized_bump_quadrature_error_small one_le_patchChartUpper8 patchChartLower8_pos hcd
    hder hlow hup hn hτ hτ1 (by rw [hτdef]; exact hτn) w

#print axioms smallPatch_bump_quadrature_small

end SphericalRiesz
