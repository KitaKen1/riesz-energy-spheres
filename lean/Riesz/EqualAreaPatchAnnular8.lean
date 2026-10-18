import Riesz.CurvedAnnularQuadrature8
import Riesz.EqualAreaPatchNear8

/-! The auxiliary kernel equals the actual inverse-fourth curved kernel on
the cube. The supplied derivative bounds are discharged by the checked
moving-center/rotation patch class. Thus one constant works for every
actual small sphere patch and every resolved coordinate annulus. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped ContDiff
namespace SphericalRiesz
open Boundary

def curvedAnnularRieszFour8 (F : (Fin 8 → ℝ) → Ambient9) (r : ℝ)
    (x y : Fin 8 → ℝ) : ℝ :=
  curvedRieszFour F x y*unitAnnularCutoff 8 (r⁻¹ • (y-x))

theorem ambientInverseFourth8_scaled (r : ℝ) (hr : 0 < r) (z : Ambient9) :
    ambientInverseFourth8 (r⁻¹ • z) = r^4*ambientInverseFourth8 z := by
  unfold ambientInverseFourth8
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),mul_inv,inv_inv,mul_pow]

theorem regularizedCurvedAnnular8_eq_actual (F : (Fin 8 → ℝ) → Ambient9)
    (κ B r : ℝ) (hκ : 0 < κ) (hB : 1 ≤ B) (hr : 0 < r)
    (x y : Fin 8 → ℝ)
    (hlo : κ*‖y-x‖ ≤ dist (F x) (F y)) (hhi : dist (F x) (F y) ≤ B*‖y-x‖) :
    regularizedCurvedAnnular8 F r (κ/4) (4*B) (by positivity) (by linarith) x y =
      curvedAnnularRieszFour8 F r x y := by
  let w := r⁻¹ • (y-x)
  let z := r⁻¹ • (F y-F x)
  by_cases hcut : unitAnnularCutoff 8 w = 0
  · simp [regularizedCurvedAnnular8,curvedAnnularAuxiliary8,curvedAnnularPair8,
      curvedAnnularRieszFour8,w] at hcut ⊢
    simp [hcut]
  have hwl : 1/2 < ‖w‖ := lt_of_not_ge (fun h => hcut (unitAnnularCutoff_zero_inside 8 w h))
  have hwu : ‖w‖ < 2 := lt_of_not_ge (fun h => hcut (unitAnnularCutoff_zero_outside 8 w h))
  have hnw : ‖w‖ = r⁻¹*‖y-x‖ := by
    dsimp only [w]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
  have hnz : ‖z‖ = r⁻¹*dist (F x) (F y) := by
    simp only [z,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    rw [dist_eq_norm,norm_sub_rev]
  have hzl : κ/4 ≤ ‖z‖ := by
    rw [hnz]
    have h := mul_le_mul_of_nonneg_left hlo (inv_nonneg.mpr hr.le)
    rw [hnw] at hwl
    nlinarith
  have hzu : ‖z‖ ≤ 4*B := by
    rw [hnz]
    have h := mul_le_mul_of_nonneg_left hhi (inv_nonneg.mpr hr.le)
    nlinarith [show 0 < B by linarith]
  change (r⁻¹)^4*(ambientRegularizedInverseFourth8 (κ/4) (4*B) _ _ z*
    unitAnnularCutoff 8 w) = _
  rw [ambientRegularizedInverseFourth8_eq _ _ _ _ z hzl hzu]
  dsimp only [z]
  rw [ambientInverseFourth8_scaled r hr]
  have hc : (r⁻¹)^4*r^4 = 1 := by rw [← mul_pow,inv_mul_cancel₀ hr.ne',one_pow]
  have hd : ambientInverseFourth8 (F y-F x) = curvedRieszFour F x y := by
    rw [ambientInverseFourth8,curvedRieszFour,dist_eq_norm,norm_sub_rev]
  rw [hd]
  change _ = curvedRieszFour F x y*unitAnnularCutoff 8 w
  calc
    _ = ((r⁻¹)^4*r^4)*(curvedRieszFour F x y*unitAnnularCutoff 8 w) := by ring
    _ = _ := by rw [hc,one_mul]

def equalAreaPatchLowerDistance8 : ℝ := 1/(2*(1+‖e8InverseMap‖))

theorem equalAreaPatchLowerDistance8_pos : 0 < equalAreaPatchLowerDistance8 := by
  unfold equalAreaPatchLowerDistance8
  positivity

theorem equalAreaNormalizedE8Patch_annular_class :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ v : Fin 8 → ℝ, ‖v‖ ≤ ρ →
      ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius ≤ ρ →
      ∀ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9, ∀ c ∈ UnitCube 8,
      (∀ y ∈ UnitCube 8, ContDiffAt ℝ ∞ (equalAreaNormalizedE8Patch g v c ε) y ∧
        ∀ k : ℕ, 1 ≤ k → k ≤ 6 →
          ‖iteratedFDeriv ℝ k (equalAreaNormalizedE8Patch g v c ε) y‖ ≤
            equalAreaPatchDerivativeBound8) ∧
      ∀ x ∈ UnitCube 8, ∀ y ∈ UnitCube 8,
        equalAreaPatchLowerDistance8*‖y-x‖ ≤
          dist (equalAreaNormalizedE8Patch g v c ε x) (equalAreaNormalizedE8Patch g v c ε y) ∧
        dist (equalAreaNormalizedE8Patch g v c ε x) (equalAreaNormalizedE8Patch g v c ε y) ≤
          equalAreaPatchDerivativeBound8*‖y-x‖ := by
  obtain ⟨ρ₁,hρ₁,hρ₁b,hder⟩ := equalAreaNormalizedE8Patch_derivatives_uniform
  obtain ⟨ρ₂,hρ₂,hρ₂b,hlo⟩ := equalAreaNormalizedE8Patch_lower_distance_uniform
  refine ⟨min ρ₁ ρ₂,lt_min hρ₁ hρ₂,(min_le_left _ _).trans hρ₁b,?_⟩
  intro v hv ε hε hs g c hc
  have hD := hder v (hv.trans (min_le_left _ _)) ε hε
    (hs.trans (min_le_left _ _)) g c hc
  refine ⟨hD,?_⟩
  intro x hx y hy
  refine ⟨?_,?_⟩
  · simpa only [equalAreaPatchLowerDistance8,norm_sub_rev] using
      hlo v (hv.trans (min_le_right _ _)) ε hε (hs.trans (min_le_right _ _)) g c hc x hx y hy
  · rw [dist_eq_norm,norm_sub_rev]
    apply unitCube8_convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f' := fun z => fderiv ℝ (equalAreaNormalizedE8Patch g v c ε) z)
      (fun z hz => ((hD z hz).1.differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt)
      _ hx hy
    intro z hz
    simpa only [norm_iteratedFDeriv_one] using (hD z hz).2 1 le_rfl (by norm_num)

/-- The constant and chart radius are independent of all patch parameters,
all original nodes, and all resolved annuli. -/
theorem equalAreaPatchAnnular8_resolved_bound :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ v : Fin 8 → ℝ, ‖v‖ ≤ ρ → ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius ≤ ρ →
      ∀ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9, ∀ c ∈ UnitCube 8,
      ∀ m : ℕ, 8 ≤ m → ∀ r : ℝ, 0 < r → r ≤ 2 → 1/(m:ℝ) ≤ r → ∀ x ∈ UnitCube 8,
      |cubeQuadrature 8 m (curvedAnnularRieszFour8 (equalAreaNormalizedE8Patch g v c ε) r x)-
        cubeIntegral 8 (curvedAnnularRieszFour8 (equalAreaNormalizedE8Patch g v c ε) r x)| ≤
          C/((m:ℝ)^6*r^2) := by
  let κ := equalAreaPatchLowerDistance8
  let B := equalAreaPatchDerivativeBound8
  have hκ : 0 < κ := equalAreaPatchLowerDistance8_pos
  have hB : 1 ≤ B := equalAreaPatchDerivativeBound8_ge_one
  obtain ⟨ρ,hρ,hρb,hclass⟩ := equalAreaNormalizedE8Patch_annular_class
  obtain ⟨C,hC,hquad⟩ := regularizedCurvedAnnular8_resolved_bound (κ/4) (4*B) B
    (by positivity) (by linarith) hB
  refine ⟨ρ,hρ,hρb,C,hC,?_⟩
  intro v hv ε hε hs g c hc m hm r hr hr1 hmesh x hx
  have hcl := hclass v hv ε hε hs g c hc
  have heq : EqOn
      (regularizedCurvedAnnular8 (equalAreaNormalizedE8Patch g v c ε) r
        (κ/4) (4*B) (by positivity) (by linarith) x)
      (curvedAnnularRieszFour8 (equalAreaNormalizedE8Patch g v c ε) r x) (UnitCube 8) := by
    intro y hy
    exact regularizedCurvedAnnular8_eq_actual _ κ B r hκ hB hr x y
      (hcl.2 x hx y hy).1 (hcl.2 x hx y hy).2
  have h := hquad _ (equalAreaNormalizedE8Patch_continuous g v c ε) hcl.1 m hm r hr hr1 hmesh x
  rw [cubeQuadrature_congr 8 m hm heq,cubeIntegral_congr 8 heq] at h
  exact h

end SphericalRiesz
