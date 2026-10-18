import Riesz.PatchGaussianDefect8
import Riesz.SmallPatchBumpErrorSmall8

/-! The patch Gaussian defect at macroscopic scales (stage NEG, τ-linear patch defect).

With the small-`τ` bump error, for `2tε² ≤ 1` the rational patch defect is bounded by
`8^(9/2) (K'_b n² √(2tε²)/δ)² B(t/8) = 8^(9/2) K'_b² n⁴ 2tε² B(t/8)/δ²`, linear in `t`; this is
what the negative-exponent macroscopic end needs for the patch part (the earlier bound with
`1+τ³` does not decay as `t → 0`). -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
open Boundary

/-- One patch: the scaled localized error with a general factor `κ`. -/
theorem patch_bump_error_le_gen (p : SmallE8CubePatch8) (n : ℕ) (hn : 8 ≤ n) {N δ Kb κ t : ℝ}
    (hNδ : N*smallE8CubeDensity8 p = (n:ℝ)^8) (hδ : smallE8CubeDensity8 p = δ) (hδ0 : 0 < δ)
    (z : Ambient9)
    (h : |cubeQuadrature 8 n (fun x => ambientBump9 t (smallE8CubeMap8 p x) z)-
        cubeIntegral 8 (fun x => ambientBump9 t (smallE8CubeMap8 p x) z)| ≤
        Kb/(n:ℝ)^6*κ*cubeIntegral 8 (fun x => Real.exp (-(t/4*‖smallE8CubeMap8 p x-z‖^2)))) :
    |(∑ u : Fin 8 → NodeIndex n, ambientBump9 t (smallE8CubeMap8 p (cubeNode 8 n u)) z)-
      N*∫ y in smallE8CubeSet8 p, ambientBump9 t (y:Ambient9) z ∂sphereProbability8| ≤
      (Kb*(n:ℝ)^2*κ/δ)*∫ y in smallE8CubeSet8 p, ambientBump9 (t/8) (y:Ambient9) z
        ∂sphereProbability8 := by
  rw [patch_bump_error_eq p n hn hNδ t z, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)^8)]
  rw [patch_majorant_eq, hδ] at h
  have hn0 : (0:ℝ) < (n:ℝ)^6 := by
    have : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity
  calc (n:ℝ)^8*|cubeQuadrature 8 n (fun x => ambientBump9 t (smallE8CubeMap8 p x) z)-
        cubeIntegral 8 (fun x => ambientBump9 t (smallE8CubeMap8 p x) z)|
      ≤ (n:ℝ)^8*(Kb/(n:ℝ)^6*κ*((∫ y in smallE8CubeSet8 p,
          ambientBump9 (t/8) (y:Ambient9) z ∂sphereProbability8)/δ)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = (Kb*(n:ℝ)^2*κ/δ)*∫ y in smallE8CubeSet8 p, ambientBump9 (t/8) (y:Ambient9) z
          ∂sphereProbability8 := by
        field_simp

/-- The Gaussian defect of the rational patch nodes for `2tε² ≤ 1`: linear in `t`. -/
theorem rationalPatchDefect_le_small :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ {K : ℕ} (P : Fin K → SmallE8CubePatch8),
      Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i)) (smallE8CubeSet8 (P j))) →
      (∀ i, ‖(P i).v‖ ≤ ρ ∧ (P i).ε*equalAreaScaleRadius ≤ ρ) →
      ∀ (a d m : ℕ) (ha : 0 < a) (hd : 0 < d) (hm : 8 ≤ m) {ε : ℝ},
      (∀ i, (P i).ε = ε) → (∀ i, smallE8CubeDensity8 (P i) = ((a:ℝ)/d)^8) →
      ∀ t : ℝ, 0 < t → 2*t*ε^2 ≤ 1 → 2*t*ε^2*patchChartLower8^2/128 ≤ ((a*m:ℕ):ℝ)^2 →
      diffuseGaussianDefect t (((d*m)^8:ℕ):ℝ)
          (fun u => (rationalCubePatchNodes8 P a m ha hm u : Ambient9))
          (patchBackground8 (⋃ i, smallE8CubeSet8 (P i))) ≤
        (8:ℝ)^((9:ℝ)/2)*(bumpErrorConstSmall patchChartUpper8 patchChartLower8*((a*m:ℕ):ℝ)^2*
          Real.sqrt (2*t*ε^2)/((a:ℝ)/d)^8)^2*sphereGaussianBackground8 (t/8) := by
  obtain ⟨ρ, hρ, hρ1, hbump⟩ := smallPatch_bump_quadrature_small
  refine ⟨ρ, hρ, hρ1, ?_⟩
  intro K P hdis hsmall a d m ha hd hm ε hε hdens t ht hτ1 htn
  have hn : 8 ≤ a*m := hm.trans (Nat.le_mul_of_pos_left m ha)
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have haR : (0:ℝ) < a := by exact_mod_cast ha
  have hδ : (0:ℝ) < ((a:ℝ)/d)^8 := by positivity
  have hKb : 0 ≤ bumpErrorConstSmall patchChartUpper8 patchChartLower8 := by
    rw [bumpErrorConstSmall, sixthConstSmall]
    positivity
  have hK' : 0 ≤ bumpErrorConstSmall patchChartUpper8 patchChartLower8*((a*m:ℕ):ℝ)^2*
      Real.sqrt (2*t*ε^2)/((a:ℝ)/d)^8 := by
    have := Real.sqrt_nonneg (2*t*ε^2)
    positivity
  have hNdens : ∀ i, (((d*m)^8:ℕ):ℝ)*smallE8CubeDensity8 (P i) = ((a*m:ℕ):ℝ)^8 := by
    intro i
    rw [hdens i]
    push_cast
    field_simp
  rw [diffuseGaussianDefect_eq_measureDefect ht.le]
  apply gaussianMeasureDefect_le_sphere_bump ht
  intro z
  rw [rationalPatchNodes_bumpField, patchBackground8_bumpField_union P hdis]
  apply family_bump_error_le P hdis (a*m) hK' z
  intro i
  have hβ : 2*t*(P i).ε^2*patchChartLower8^2/128 ≤ ((a*m:ℕ):ℝ)^2 := by
    rw [hε i]; exact htn
  have hτ1' : 2*t*(P i).ε^2 ≤ 1 := by rw [hε i]; exact hτ1
  have h := hbump (P i) (hsmall i).1 (hsmall i).2 (a*m) hn t ht hτ1' hβ z
  rw [hε i] at h
  exact patch_bump_error_le_gen (P i) (a*m) hn (hNdens i) (hdens i) hδ z h


#print axioms patch_bump_error_le_gen
#print axioms rationalPatchDefect_le_small

end SphericalRiesz
