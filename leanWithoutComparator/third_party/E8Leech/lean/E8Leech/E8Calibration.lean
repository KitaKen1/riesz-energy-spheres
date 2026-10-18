import E8Leech.E8Duality
import E8Leech.LatticeCalibration

/-!
# Calibration for E8 (P5c)

On `E8` every squared norm is even, also on the dual lattice. So a Schwartz function that equals the
Gaussian at nonzero even squared norms, and whose Fourier transform vanishes there, has
`f̂(0) − f(0)` equal to the Gaussian lattice energy of `E8`. The CKMRV functions satisfy both
conditions because of the factor `sin²(π|x|²/2)`.
-/

noncomputable section

namespace E8Leech

open MeasureTheory
open scoped FourierTransform Real

/-- `sin(π r²/2) = 0` when `r²` is even. -/
theorem sin_pi_mul_sq_div_two_eq_zero {r : ℝ} {n : ℤ} (h : r ^ 2 = 2 * n) :
    Real.sin (π * r ^ 2 / 2) = 0 := by
  rw [h, show π * (2 * (n : ℝ)) / 2 = (n : ℝ) * π by ring]
  exact Real.sin_int_mul_pi n

/-- **E8 calibration.** -/
theorem e8_calibration_of_even_vanishing (f : SchwartzMap (Ambient 8) ℂ) {α : ℝ} (hα : 0 < α)
    (hf : ∀ v : Ambient 8, v ≠ 0 → (∃ n : ℤ, ‖v‖ ^ 2 = 2 * n) →
      f v = (gaussianKernel α v : ℂ))
    (hfhat : ∀ m : Ambient 8, m ≠ 0 → (∃ n : ℤ, ‖m‖ ^ 2 = 2 * n) → 𝓕 (⇑f) m = 0) :
    (latticePotentialEnergy e8Set (gaussianPotential α)).toReal = (𝓕 (⇑f) 0).re - (f 0).re := by
  have hfin := e8_gaussian_lattice_energy_ne_top hα
  rw [← coe_e8Lattice] at hfin ⊢
  exact latticePotentialEnergy_gaussian_toReal_eq e8Lattice e8Lattice_covolume f α hfin
    (fun v hv hne => hf v hne (e8Set_norm_sq_even (by rw [← coe_e8Lattice]; exact hv)))
    (fun m hm hne => hfhat m hne (dualLattice_e8Lattice_norm_sq_even hm))

end E8Leech
