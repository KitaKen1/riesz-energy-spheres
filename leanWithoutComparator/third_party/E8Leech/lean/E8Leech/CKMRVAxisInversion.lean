import E8Leech.CKMRVAxisNumerator

/-!
# The axis functions under `u ↦ 1/u`

The modular inversion `S` maps `iu` to `i/u`. From the transformation laws of `θ₂⁴, θ₄⁴, E₂` and
of the two logarithms:

`V(1/u) = u² W(u)`, `W(1/u) = u² V(u)`, `E₂(1/u) = −u² E₂(u) + 6u/π`,
`L(1/u) = L_S(u)`, `L_S(1/u) = L(u)`.

These are the arguments of the anti-diagonal identities `axPhi_anti`, `axPhiK_anti`, and they
reduce the kernel inequality for `t < 1` to series in the nome of `i/t`.
-/

noncomputable section

namespace E8Leech

open Complex
open UpperHalfPlane hiding I
open scoped Real

variable {s : ℝ}

theorem axV_inv (hs : 0 < s) : axV s⁻¹ = s ^ 2 * axW s := by
  have h := thetaV_S (imagPt s)
  rw [S_smul_imagPt hs, thetaV_imagPt_eq_axV (inv_pos.mpr hs), thetaW_imagPt_eq_axW hs,
    coe_imagPt hs] at h
  have h2 : ((axV s⁻¹ : ℝ) : ℂ) = ((s ^ 2 * axW s : ℝ) : ℂ) := by
    rw [h]
    push_cast
    linear_combination (-((s : ℂ) ^ 2 * (axW s : ℂ))) * I_sq
  exact_mod_cast h2

theorem axW_inv (hs : 0 < s) : axW s⁻¹ = s ^ 2 * axV s := by
  have h := thetaW_S (imagPt s)
  rw [S_smul_imagPt hs, thetaW_imagPt_eq_axW (inv_pos.mpr hs), thetaV_imagPt_eq_axV hs,
    coe_imagPt hs] at h
  have h2 : ((axW s⁻¹ : ℝ) : ℂ) = ((s ^ 2 * axV s : ℝ) : ℂ) := by
    rw [h]
    push_cast
    linear_combination (-((s : ℂ) ^ 2 * (axV s : ℂ))) * I_sq
  exact_mod_cast h2

theorem axE2_inv (hs : 0 < s) : axE2 s⁻¹ = -s ^ 2 * axE2 s + 6 * s / π := by
  have h := eisensteinTwo_S_explicit (imagPt s)
  rw [S_smul_imagPt hs, E2_imagPt_eq_axE2 (inv_pos.mpr hs), E2_imagPt_eq_axE2 hs,
    coe_imagPt hs] at h
  have h2 : ((axE2 s⁻¹ : ℝ) : ℂ) = ((-s ^ 2 * axE2 s + 6 * s / π : ℝ) : ℂ) := by
    rw [h]
    push_cast
    linear_combination ((s : ℂ) ^ 2 * (axE2 s : ℂ) - 6 * (s : ℂ) / (π : ℂ)) * I_sq
  exact_mod_cast h2

theorem axL_inv (hs : 0 < s) : axL s⁻¹ = axLS s := by
  have h := ckmrvL_S (imagPt s)
  rw [S_smul_imagPt hs, ckmrvL_imagPt_eq_axL (inv_pos.mpr hs), ckmrvLS_imagPt_eq_axLS hs] at h
  exact_mod_cast h

theorem axLS_inv (hs : 0 < s) : axLS s⁻¹ = axL s := by
  have h := ckmrvLS_S (imagPt s)
  rw [S_smul_imagPt hs, ckmrvLS_imagPt_eq_axLS (inv_pos.mpr hs), ckmrvL_imagPt_eq_axL hs] at h
  exact_mod_cast h

end E8Leech
