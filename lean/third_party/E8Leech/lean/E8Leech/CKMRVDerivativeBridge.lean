import E8Leech.CKMRVDiagonalCertificates
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Actual derivatives and a two-Eisenstein bridge

The actual derivative of the actual Klein j is defined using deriv and is
certified by existing holomorphy. A finite differential calculation reduces
its published formula to the E4 and E6 derivative identities with a common
quasimodular value. No E2 derivative or eta differentiation is needed.
Those two identities are explicit premises here, not imported as axioms or
asserted to have been proved for the actual pinned Eisenstein series.
-/

set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 3
noncomputable section
namespace E8Leech
open Filter
open scoped Topology Manifold

def kleinModularJDerivative (z : UpperHalfPlane) : ℂ :=
  deriv (fun w : ℂ => kleinModularJ (UpperHalfPlane.ofComplex w)) (z : ℂ)

theorem hasDerivAt_kleinModularJ (z : UpperHalfPlane) :
    HasDerivAt (fun w : ℂ => kleinModularJ (UpperHalfPlane.ofComplex w))
      (kleinModularJDerivative z) (z : ℂ) :=
  (UpperHalfPlane.mdifferentiableAt_iff.mp (mdifferentiable_kleinModularJ z)).hasDerivAt

theorem hasDerivAt_modularDiscriminant_of_eisenstein_derivatives
    (z : UpperHalfPlane) (c : ℂ)
    (hA : HasDerivAt (fun w : ℂ => ModularForm.E₄ (UpperHalfPlane.ofComplex w))
      ((2 * (Real.pi : ℂ) * Complex.I) / 3 *
        (c * ModularForm.E₄ z - ModularForm.E₆ z)) (z : ℂ))
    (hB : HasDerivAt (fun w : ℂ => ModularForm.E₆ (UpperHalfPlane.ofComplex w))
      ((2 * (Real.pi : ℂ) * Complex.I) / 2 *
        (c * ModularForm.E₆ z - ModularForm.E₄ z ^ 2)) (z : ℂ)) :
    HasDerivAt (fun w : ℂ => ModularForm.discriminant (UpperHalfPlane.ofComplex w))
      (2 * (Real.pi : ℂ) * Complex.I * c * ModularForm.discriminant z) (z : ℂ) := by
  have h := ((hA.pow 3).sub (hB.pow 2)).div_const 1728
  have hval := eisenstein_cubic_square_discriminant z
  have heq : (fun w : ℂ => ModularForm.discriminant (UpperHalfPlane.ofComplex w)) =
      (fun w : ℂ => (ModularForm.E₄ (UpperHalfPlane.ofComplex w) ^ 3 -
        ModularForm.E₆ (UpperHalfPlane.ofComplex w) ^ 2) / 1728) := by
    funext w
    rw [eisenstein_cubic_square_discriminant]
    ring
  rw [heq]
  apply h.congr_deriv
  simp only [UpperHalfPlane.ofComplex_apply]
  linear_combination (2 * (Real.pi : ℂ) * Complex.I * c / 1728) * hval

theorem hasDerivAt_kleinModularJ_of_eisenstein_derivatives
    (z : UpperHalfPlane) (c : ℂ)
    (hA : HasDerivAt (fun w : ℂ => ModularForm.E₄ (UpperHalfPlane.ofComplex w))
      ((2 * (Real.pi : ℂ) * Complex.I) / 3 *
        (c * ModularForm.E₄ z - ModularForm.E₆ z)) (z : ℂ))
    (hB : HasDerivAt (fun w : ℂ => ModularForm.E₆ (UpperHalfPlane.ofComplex w))
      ((2 * (Real.pi : ℂ) * Complex.I) / 2 *
        (c * ModularForm.E₆ z - ModularForm.E₄ z ^ 2)) (z : ℂ)) :
    HasDerivAt (fun w : ℂ => kleinModularJ (UpperHalfPlane.ofComplex w))
      (ckmrvKleinDerivativeCandidate z) (z : ℂ) := by
  have hD := hasDerivAt_modularDiscriminant_of_eisenstein_derivatives z c hA hB
  have h := (hA.pow 3).div hD (by
    simpa only [UpperHalfPlane.ofComplex_apply] using ModularForm.discriminant_ne_zero z)
  change HasDerivAt (fun w : ℂ => ModularForm.E₄ (UpperHalfPlane.ofComplex w) ^ 3 /
    ModularForm.discriminant (UpperHalfPlane.ofComplex w)) _ _
  apply h.congr_deriv
  simp only [UpperHalfPlane.ofComplex_apply, Pi.pow_apply]
  unfold ckmrvKleinDerivativeCandidate
  field_simp [ModularForm.discriminant_ne_zero z]
  ring

theorem kleinModularJDerivative_eq_candidate_of_eisenstein_derivatives
    (z : UpperHalfPlane) (c : ℂ)
    (hA : HasDerivAt (fun w : ℂ => ModularForm.E₄ (UpperHalfPlane.ofComplex w))
      ((2 * (Real.pi : ℂ) * Complex.I) / 3 *
        (c * ModularForm.E₄ z - ModularForm.E₆ z)) (z : ℂ))
    (hB : HasDerivAt (fun w : ℂ => ModularForm.E₆ (UpperHalfPlane.ofComplex w))
      ((2 * (Real.pi : ℂ) * Complex.I) / 2 *
        (c * ModularForm.E₆ z - ModularForm.E₄ z ^ 2)) (z : ℂ)) :
    kleinModularJDerivative z = ckmrvKleinDerivativeCandidate z :=
  (hasDerivAt_kleinModularJ_of_eisenstein_derivatives z c hA hB).deriv

theorem tendsto_kleinModularJ_inverse_slope (z : UpperHalfPlane)
    (hne : kleinModularJDerivative z ≠ 0) :
    Tendsto (fun w : ℂ => (w - (z : ℂ)) /
      (kleinModularJ (UpperHalfPlane.ofComplex w) - kleinModularJ z))
      (𝓝[≠] (z : ℂ)) (𝓝 ((kleinModularJDerivative z)⁻¹)) := by
  have h := (hasDerivAt_kleinModularJ z).tendsto_slope.inv₀ hne
  simpa only [slope_def_field, UpperHalfPlane.ofComplex_apply, inv_div] using h

theorem eventually_kleinModularJ_gap_ne_zero (z : UpperHalfPlane)
    (hne : kleinModularJDerivative z ≠ 0) :
    ∀ᶠ w : ℂ in 𝓝[≠] (z : ℂ),
      kleinModularJ (UpperHalfPlane.ofComplex w) - kleinModularJ z ≠ 0 := by
  have hs := (hasDerivAt_kleinModularJ z).tendsto_slope
  have he := hs.eventually (isOpen_ne.mem_nhds hne)
  filter_upwards [he] with w hw
  intro hz
  apply hw
  simp only [slope_def_field, UpperHalfPlane.ofComplex_apply, hz, zero_div]

end E8Leech
