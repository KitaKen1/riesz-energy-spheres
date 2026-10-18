import E8Leech.LeechAxisNumerator
import E8Leech.LeechSchwartzProfile

/-!
# The growing cusp coefficients of the Leech kernel as explicit real expressions

For `τ = iu` the two coefficients of the growing part `e^{2πt}(a₁ t + a₀)` of the cusp profile of
`𝒦̂⁽²⁴⁾(iu, i·)` are real polynomials in `E₂, V, W, L, L_S` at `iu` and in `u`, `π`, `1/π`, `log 2`:

* `a₁ = (π u Y + Z) / 10368` with `Y = 6 (E₂E₄ − E₆)(E₄² − E₂E₆)` and
  `Z = 3 (12 E₂E₄E₆ − 5 E₄³ − 7 E₆²)` (`leechAxisCusp_zero_axis`);
* `a₀ = −(u (Y − 1728 E₂Δ) + Z/π)/3456 − α/(2304π) − (4 log 2 − 1) Δ/(2π)` with
  `α = ψ₂ E₄E₆ − ψ₄ E₄²` (`leechAxisCusp_one_axis`).

These are the forms in which the inequalities (6.4)(2), (3a) of Cohn–Kumar–Miller–Radchenko–
Viazovska are checked. Nothing about their signs is proved in this file.
-/

noncomputable section

namespace E8Leech

open Complex
open UpperHalfPlane hiding I
open scoped Real

/-! ## The real expressions -/

/-- `Y = 6 (E₂E₄ − E₆)(E₄² − E₂E₆)`. -/
def axCuspY (E2 V W : ℝ) : ℝ :=
  6 * (E2 * axE4 V W - axE6 V W) * (axE4 V W ^ 2 - E2 * axE6 V W)

/-- `Z = 3 (12 E₂E₄E₆ − 5 E₄³ − 7 E₆²)`. -/
def axCuspZ (E2 V W : ℝ) : ℝ :=
  3 * (12 * E2 * axE4 V W * axE6 V W - 5 * axE4 V W ^ 3 - 7 * axE6 V W ^ 2)

/-- `α = ψ₂ E₄E₆ − ψ₄ E₄²` (`leechMinusAlpha` on the axis). -/
def axCuspAlpha (V W L LS : ℝ) : ℝ :=
  axPsiTwo V W L LS * (axE4 V W * axE6 V W) - axPsiFour V W L LS * axE4 V W ^ 2

/-- `−i` times `leechPlusP2` on the axis. -/
def axCuspP2 (E2 V W u : ℝ) : ℝ :=
  -6 * (u * (axE4 V W ^ 2 * axE6 V W)) +
    (12 * axE4 V W ^ 3 - 7 * 1728 * axDelta V W) * (u * E2 - 3 / π) -
    6 * (E2 * (u * E2 - 6 / π) * (axE4 V W * axE6 V W))

/-- The coefficient `a₁` of `t e^{2πt}`. -/
def axCuspA1 (E2 V W u : ℝ) : ℝ := (π * u * axCuspY E2 V W + axCuspZ E2 V W) / 10368

/-- The coefficient `a₀` of `e^{2πt}`. -/
def axCuspA0 (E2 V W L LS u : ℝ) : ℝ :=
  -(u * (axCuspY E2 V W - 1728 * E2 * axDelta V W) + axCuspZ E2 V W / π) / 3456 -
    axCuspAlpha V W L LS / (2304 * π) - (4 * Real.log 2 - 1) * axDelta V W / (2 * π)

/-- `E₄³ − E₆² = 1728 Δ` for the polynomial models. -/
theorem axE4_cube_sub_axE6_sq (V W : ℝ) : axE4 V W ^ 3 - axE6 V W ^ 2 = 1728 * axDelta V W := by
  simp only [axE4, axE6, axDelta]
  ring

/-! ## The coefficients on the axis -/

section Axis

variable {u : ℝ}

theorem leechPlusA1_axis (hu : 0 < u) :
    leechPlusA1 (imagPt u) =
      I * (((u * axE2 u - 3 / π) * axDelta (axV u) (axW u) : ℝ) : ℂ) := by
  rw [leechPlusA1, phi1_axis hu, discriminant_imagPt_eq_ax hu]
  push_cast
  ring

theorem leechPlusP2_axis (hu : 0 < u) :
    leechPlusP2 (imagPt u) = I * ((axCuspP2 (axE2 u) (axV u) (axW u) u : ℝ) : ℂ) := by
  have hD : (axDelta (axV u) (axW u) : ℂ) ≠ 0 := by exact_mod_cast axDelta_ne_zero hu
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [leechPlusP2, leechPlusA0, leechPlusA1, leechPlusA2, coe_imagPt hu, phi1_axis hu,
    phi2_axis hu, kleinModularJ_imagPt_eq_ax hu, E4_imagPt_eq_ax hu, E6_imagPt_eq_ax hu,
    discriminant_imagPt_eq_ax hu, axCuspP2]
  push_cast
  field_simp
  ring

theorem leechMinusAlpha_axis (hu : 0 < u) :
    leechMinusAlpha (imagPt u) =
      ((axCuspAlpha (axV u) (axW u) (axL u) (axLS u) : ℝ) : ℂ) := by
  rw [leechMinusAlpha, psiBasis_one_axis hu, psiBasis_two_axis hu, E4_imagPt_eq_ax hu,
    E6_imagPt_eq_ax hu, axCuspAlpha]
  push_cast
  ring

/-- The leading coefficient of the plus kernel. -/
theorem leechPlusCusp_zero_axis (hu : 0 < u) :
    leechPlusCusp (imagPt u) 0 =
      ((π * (axCuspP2 (axE2 u) (axV u) (axW u) u +
        1728 * ((u * axE2 u - 3 / π) * axDelta (axV u) (axW u))) / 5184 : ℝ) : ℂ) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  show (1728 * ckmrvPlusScale)⁻¹ * (I * leechPlusM1a (imagPt u)) = _
  rw [leechPlusM1a, leechPlusP2_axis hu, leechPlusA1_axis hu, ckmrvPlusScale, zpow_neg, zpow_two]
  push_cast
  field_simp
  ring_nf
  simp only [I_sq]
  ring

/-- The second coefficient of the plus kernel. -/
theorem leechPlusCusp_one_axis (hu : 0 < u) :
    leechPlusCusp (imagPt u) 1 =
      ((-axCuspP2 (axE2 u) (axV u) (axW u) u / 1728 : ℝ) : ℂ) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  show (1728 * ckmrvPlusScale)⁻¹ * leechPlusM0a (imagPt u) = _
  rw [leechPlusM0a, leechPlusP2_axis hu, ckmrvPlusScale, zpow_neg, zpow_two]
  push_cast
  field_simp

/-- The leading coefficient of the minus kernel is `−Δ`. -/
theorem leechMinusCusp_zero_axis (hu : 0 < u) :
    leechMinusCusp (imagPt u) 0 = ((-axDelta (axV u) (axW u) : ℝ) : ℂ) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  show ckmrvMinusScale⁻¹ * (-π * (2 * 1728 * ModularForm.discriminant (imagPt u))) = _
  rw [ckmrvMinusScale, discriminant_imagPt_eq_ax hu]
  push_cast
  field_simp

/-- The second coefficient of the minus kernel. -/
theorem leechMinusCusp_one_axis (hu : 0 < u) :
    leechMinusCusp (imagPt u) 1 =
      (((4 * Real.log 2 - 1) * axDelta (axV u) (axW u) / π +
        axCuspAlpha (axV u) (axW u) (axL u) (axLS u) / (1152 * π) : ℝ) : ℂ) := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  show ckmrvMinusScale⁻¹ * (4 * Real.log 2 * (2 * 1728 * ModularForm.discriminant (imagPt u)) +
    (leechMinusBeta (imagPt u) + leechMinusAlpha (imagPt u))) = _
  rw [leechMinusBeta, leechMinusAlpha_axis hu, ckmrvMinusScale, discriminant_imagPt_eq_ax hu]
  push_cast
  field_simp
  ring

/-- **The coefficient `a₁` of `𝒦̂⁽²⁴⁾(iu, i·)` on the axis.** -/
theorem leechAxisCusp_zero_axis (hu : 0 < u) :
    leechAxisCusp (-1) u 0 = ((axCuspA1 (axE2 u) (axV u) (axW u) u : ℝ) : ℂ) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hreal : (π * (axCuspP2 (axE2 u) (axV u) (axW u) u +
      1728 * ((u * axE2 u - 3 / π) * axDelta (axV u) (axW u))) / 5184 +
        -1 * -axDelta (axV u) (axW u)) / 2 = axCuspA1 (axE2 u) (axV u) (axW u) u := by
    simp only [axCuspA1, axCuspP2, axCuspY, axCuspZ, axE4, axE6, axDelta]
    field_simp
    ring
  rw [leechAxisCusp, leechPlusCusp_zero_axis hu, leechMinusCusp_zero_axis hu, ← hreal]
  push_cast
  ring

/-- **The coefficient `a₀` of `𝒦̂⁽²⁴⁾(iu, i·)` on the axis.** -/
theorem leechAxisCusp_one_axis (hu : 0 < u) :
    leechAxisCusp (-1) u 1 =
      ((axCuspA0 (axE2 u) (axV u) (axW u) (axL u) (axLS u) u : ℝ) : ℂ) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hreal : (-axCuspP2 (axE2 u) (axV u) (axW u) u / 1728 +
      -1 * ((4 * Real.log 2 - 1) * axDelta (axV u) (axW u) / π +
        axCuspAlpha (axV u) (axW u) (axL u) (axLS u) / (1152 * π))) / 2 =
      axCuspA0 (axE2 u) (axV u) (axW u) (axL u) (axLS u) u := by
    simp only [axCuspA0, axCuspP2, axCuspY, axCuspZ, axE4, axE6, axDelta]
    field_simp
    ring
  rw [leechAxisCusp, leechPlusCusp_one_axis hu, leechMinusCusp_one_axis hu, ← hreal]
  push_cast
  ring

/-- The real parts, in the form used for the inequalities. -/
theorem leechAxisCusp_zero_re (hu : 0 < u) :
    (leechAxisCusp (-1) u 0).re = axCuspA1 (axE2 u) (axV u) (axW u) u := by
  rw [leechAxisCusp_zero_axis hu, ofReal_re]

theorem leechAxisCusp_one_re (hu : 0 < u) :
    (leechAxisCusp (-1) u 1).re = axCuspA0 (axE2 u) (axV u) (axW u) (axL u) (axLS u) u := by
  rw [leechAxisCusp_one_axis hu, ofReal_re]

end Axis

end E8Leech
