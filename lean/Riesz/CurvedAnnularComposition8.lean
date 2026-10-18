import Riesz.CurvedAnnularRegularization8

/-! Rescale before composition. Derivatives of the pair of actual ambient
and coordinate increments have a uniform B/r bound. The fixed product
kernel then gives the sixth derivative bound C/r^10. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped ContDiff
namespace SphericalRiesz
open Boundary

def curvedAnnularPair8 (F : (Fin 8 → ℝ) → Ambient9) (r : ℝ)
    (x y : Fin 8 → ℝ) : Ambient9 × (Fin 8 → ℝ) :=
  (r⁻¹ • (F y-F x),r⁻¹ • (y-x))

def regularizedCurvedAnnular8 (F : (Fin 8 → ℝ) → Ambient9) (r : ℝ)
    (δ R : ℝ) (hδ : 0 < δ) (hR : 0 < R) (x y : Fin 8 → ℝ) : ℝ :=
  (r⁻¹)^4*curvedAnnularAuxiliary8 δ R hδ hR (curvedAnnularPair8 F r x y)

theorem norm_iteratedFDeriv_scaled_increment8
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (r : ℝ) (hr : 0 < r) (x y : E) (k : ℕ) (hk : k ≠ 0)
    (hf : ContDiffAt ℝ k f y) :
    ‖iteratedFDeriv ℝ k (fun z => r⁻¹ • (f z-f x)) y‖ =
      r⁻¹*‖iteratedFDeriv ℝ k f y‖ := by
  rw [iteratedFDeriv_const_smul_apply' (hf.sub contDiffAt_const)]
  change ‖r⁻¹ • iteratedFDeriv ℝ k (f-(fun _ => f x)) y‖ = _
  rw [iteratedFDeriv_sub_apply hf contDiffAt_const,
    iteratedFDeriv_const_of_ne hk,Pi.zero_apply,sub_zero,norm_smul,
    Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]

theorem norm_iteratedFDeriv_id_le_one8 (y : Fin 8 → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    ‖iteratedFDeriv ℝ k (id : (Fin 8 → ℝ) → (Fin 8 → ℝ)) y‖ ≤ 1 := by
  by_cases hk1 : k = 1
  · subst k
    simp
  · obtain ⟨j,hj⟩ : ∃ j, k = j+2 := ⟨k-2,by omega⟩
    subst k
    rw [← norm_iteratedFDeriv_fderiv]
    rw [show fderiv ℝ (id : (Fin 8 → ℝ) → (Fin 8 → ℝ)) =
      (fun _ => ContinuousLinearMap.id ℝ (Fin 8 → ℝ)) from funext (fun _ => fderiv_id)]
    change ‖iteratedFDeriv ℝ (j+1) (fun _ : Fin 8 → ℝ =>
      ContinuousLinearMap.id ℝ (Fin 8 → ℝ)) y‖ ≤ 1
    simp only [iteratedFDeriv_const_of_ne (by omega : j+1 ≠ 0),
      Pi.zero_apply,norm_zero]
    norm_num

theorem curvedAnnularPair8_contDiffAt (F : (Fin 8 → ℝ) → Ambient9)
    (r : ℝ) (x y : Fin 8 → ℝ) (hf : ContDiffAt ℝ ∞ F y) :
    ContDiffAt ℝ ∞ (curvedAnnularPair8 F r x) y :=
  ((hf.sub contDiffAt_const).const_smul r⁻¹).prodMk
    ((contDiffAt_id.sub contDiffAt_const).const_smul r⁻¹)

theorem curvedAnnularPair8_derivative_bound (F : (Fin 8 → ℝ) → Ambient9)
    (r B : ℝ) (hr : 0 < r) (hr1 : r ≤ 2) (hB : 1 ≤ B)
    (x y : Fin 8 → ℝ) (hf : ContDiffAt ℝ ∞ F y)
    (hb : ∀ k : ℕ, 1 ≤ k → k ≤ 6 → ‖iteratedFDeriv ℝ k F y‖ ≤ B) :
    ∀ k : ℕ, 1 ≤ k → k ≤ 6 →
      ‖iteratedFDeriv ℝ k (curvedAnnularPair8 F r x) y‖ ≤ (2*B/r)^k := by
  intro k hk hk6
  have hf' : ContDiffAt ℝ k F y := hf.of_le (by simp)
  have hi : ContDiffAt ℝ k (id : (Fin 8 → ℝ) → (Fin 8 → ℝ)) y := contDiffAt_id
  have hk0 : k ≠ 0 := by omega
  have h1 : ContDiffAt ℝ k (fun z => r⁻¹ • (F z-F x)) y :=
    (hf'.sub (contDiffAt_const (c := F x))).const_smul r⁻¹
  have h2 : ContDiffAt ℝ k (fun z : Fin 8 → ℝ => r⁻¹ • (z-x)) y :=
    (contDiffAt_id.sub (contDiffAt_const (c := x))).const_smul r⁻¹
  have heq : ‖iteratedFDeriv ℝ k (curvedAnnularPair8 F r x) y‖ =
      max (r⁻¹*‖iteratedFDeriv ℝ k F y‖)
        (r⁻¹*‖iteratedFDeriv ℝ k (id : (Fin 8 → ℝ) → (Fin 8 → ℝ)) y‖) := by
    change ‖iteratedFDeriv ℝ k (fun z => (r⁻¹ • (F z-F x),r⁻¹ • (z-x))) y‖ = _
    rw [iteratedFDeriv_prodMk h1 h2 le_rfl,
      ContinuousMultilinearMap.opNorm_prod]
    rw [norm_iteratedFDeriv_scaled_increment8 F r hr x y k hk0 hf']
    congr 1
    simpa only [id_eq] using norm_iteratedFDeriv_scaled_increment8 id r hr x y k hk0 hi
  rw [heq]
  have hBr : 1 ≤ 2*B/r := (le_div_iff₀ hr).mpr (by linarith)
  have hmax : max (r⁻¹*‖iteratedFDeriv ℝ k F y‖)
      (r⁻¹*‖iteratedFDeriv ℝ k (id : (Fin 8 → ℝ) → (Fin 8 → ℝ)) y‖) ≤ B/r := by
    rw [div_eq_inv_mul]
    apply max_le
    · exact mul_le_mul_of_nonneg_left (hb k hk hk6) (inv_nonneg.mpr hr.le)
    · exact mul_le_mul_of_nonneg_left
        ((norm_iteratedFDeriv_id_le_one8 y k hk).trans hB) (inv_nonneg.mpr hr.le)
  have hmax' : max (r⁻¹*‖iteratedFDeriv ℝ k F y‖)
      (r⁻¹*‖iteratedFDeriv ℝ k (id : (Fin 8 → ℝ) → (Fin 8 → ℝ)) y‖) ≤ 2*B/r :=
    hmax.trans (div_le_div_of_nonneg_right (by linarith) hr.le)
  exact hmax'.trans (by simpa only [pow_one] using pow_le_pow_right₀ hBr hk)

theorem regularizedCurvedAnnular8_contDiffAt (F : (Fin 8 → ℝ) → Ambient9)
    (r δ R : ℝ) (hδ : 0 < δ) (hR : 0 < R) (x y : Fin 8 → ℝ)
    (hf : ContDiffAt ℝ ∞ F y) :
    ContDiffAt ℝ ∞ (regularizedCurvedAnnular8 F r δ R hδ hR x) y := by
  exact contDiffAt_const.mul ((curvedAnnularAuxiliary8_contDiff δ R hδ hR).contDiffAt.comp y
    (curvedAnnularPair8_contDiffAt F r x y hf))

theorem regularizedCurvedAnnular8_sixth_bounded (δ R B : ℝ)
    (hδ : 0 < δ) (hR : 0 < R) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : (Fin 8 → ℝ) → Ambient9,
      ∀ r : ℝ, 0 < r → r ≤ 2 → ∀ x y : Fin 8 → ℝ,
      ContDiffAt ℝ ∞ F y →
      (∀ k : ℕ, 1 ≤ k → k ≤ 6 → ‖iteratedFDeriv ℝ k F y‖ ≤ B) →
      ‖iteratedFDeriv ℝ 6 (regularizedCurvedAnnular8 F r δ R hδ hR x) y‖ ≤ C/r^10 := by
  obtain ⟨C,hC,hb⟩ := curvedAnnularAuxiliary8_derivatives_bounded δ R hδ hR
  refine ⟨720*C*(2*B)^6,by positivity,?_⟩
  intro F r hr hr1 x y hf hF
  have hp := curvedAnnularPair8_contDiffAt F r x y hf
  have hc := (curvedAnnularAuxiliary8_contDiff δ R hδ hR).contDiffAt.comp y hp
  have hn := norm_iteratedFDeriv_comp_le_of_contDiffAt (hp.of_le (by simp))
    ((curvedAnnularAuxiliary8_contDiff δ R hδ hR).of_le (by simp))
    (fun k hk => hb k hk _) (curvedAnnularPair8_derivative_bound F r B hr hr1 hB x y hf hF)
  change ‖iteratedFDeriv ℝ 6 (fun z => (r⁻¹)^4 •
    (curvedAnnularAuxiliary8 δ R hδ hR ∘ curvedAnnularPair8 F r x) z) y‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (hc.of_le (by simp)),norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (r⁻¹)^4)]
  calc
    _ ≤ (r⁻¹)^4*((6:ℕ).factorial*C*(2*B/r)^6) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = (720*C*(2*B)^6)/r^10 := by norm_num [div_pow,inv_pow]; field_simp

def equalAreaPatchDerivativeBound8 : ℝ := 2+‖equalAreaFlatDerivative8‖

theorem equalAreaPatchDerivativeBound8_ge_one : 1 ≤ equalAreaPatchDerivativeBound8 := by
  unfold equalAreaPatchDerivativeBound8
  linarith [norm_nonneg equalAreaFlatDerivative8]

theorem equalAreaNormalizedE8Patch_derivatives_uniform :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ v : Fin 8 → ℝ, ‖v‖ ≤ ρ →
      ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius ≤ ρ →
      ∀ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9, ∀ c ∈ UnitCube 8, ∀ y ∈ UnitCube 8,
      ContDiffAt ℝ ∞ (equalAreaNormalizedE8Patch g v c ε) y ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ 6 →
        ‖iteratedFDeriv ℝ k (equalAreaNormalizedE8Patch g v c ε) y‖ ≤
          equalAreaPatchDerivativeBound8 := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := equalAreaNormalizedE8Patch_C7_uniform 1 (by norm_num)
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro v hv ε hε hs g c hc y hy
  have h := hb v hv ε hε hs g c hc y hy
  refine ⟨h.1,?_⟩
  intro k hk hk6
  by_cases hk1 : k = 1
  · subst k
    rw [norm_iteratedFDeriv_one]
    calc
      _ ≤ ‖fderiv ℝ (equalAreaNormalizedE8Patch g v c ε) y-
          equalAreaRotatedFlatDerivative8 g‖+‖equalAreaRotatedFlatDerivative8 g‖ :=
        norm_le_norm_sub_add _ _
      _ ≤ 1+‖equalAreaFlatDerivative8‖ := add_le_add h.2.2.1
        (equalAreaRotation_comp_norm_le g equalAreaFlatDerivative8)
      _ ≤ equalAreaPatchDerivativeBound8 := by unfold equalAreaPatchDerivativeBound8; linarith
  · exact (h.2.2.2 k (by omega) (by omega)).trans equalAreaPatchDerivativeBound8_ge_one

end SphericalRiesz
