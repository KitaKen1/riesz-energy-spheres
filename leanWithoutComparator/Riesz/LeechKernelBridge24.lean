import E8Leech.LeechSlackProfile
import E8Leech.LeechKernelInequalitiesProof
import E8Leech.LeechFourierIdentityProof
import Riesz.LeechModelRelabel24
import Riesz.LeechInputFromCertificate24

/-! The Gaussian input of `S²⁴` from the kernel inequalities of the Leech lattice (stage G24).

The vendored development `E8Leech` (snapshot of the sibling project, `third_party/E8Leech`)
proves the kernel inequalities of Cohn–Kumar–Miller–Radchenko–Viazovska for the Leech lattice
(`E8Leech.leechKernelInequalities`) and the Fourier identities of the interpolation functions
(`E8Leech.leechFourierIdentities`), and from them, for every scale `α > 0` with `α ≠ π`, a
Schwartz function with the properties of a sharp Gaussian certificate for its Leech set
(`E8Leech.leechCertFamily_cert`).

Its Leech set is the image of the lattice `leechLattice` of this project under a relabelling of
the coordinates (`Riesz/LeechModelRelabel24.lean`), an isometry of `ℝ²⁴`.  The certificate
therefore gives the Gaussian input `LeechSharpGaussianSchwartzInputOff24` at the scales
`β = α/π ≠ 1`, hence the sharp lower Gaussian profile of `S²⁴` without hypotheses. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped FourierTransform SchwartzMap ENNReal
namespace SphericalRiesz

/-- The Gaussian input of `S²⁴` at every scale `β ≠ 1`: no hypothesis. -/
theorem leechSharpGaussianSchwartzInputOff24 : LeechSharpGaussianSchwartzInputOff24 := by
  intro β hβ hβ1
  have hα : 0 < Real.pi*β := mul_pos Real.pi_pos hβ
  have hαπ : Real.pi*β ≠ Real.pi := fun h =>
    hβ1 (mul_left_cancel₀ Real.pi_ne_zero (h.trans (mul_one Real.pi).symm))
  have hc := E8Leech.leechCertFamily_cert E8Leech.leechKernelInequalities
    E8Leech.leechFourierIdentities hα hαπ
  have hmin : ∀ v : LeechAmbient, v ≠ 0 →
      ((E8Leech.leechCertFamily (Real.pi*β)) v).re ≤
        Real.exp (-(Real.pi*β)*‖v‖^2) := fun v hv => hc.minorant v hv
  have hcal : (∑' y : E8Leech.leechSet, if (y : LeechAmbient) = 0 then (0 : ℝ≥0∞)
      else ENNReal.ofReal (Real.exp (-(Real.pi*β)*‖(0 : LeechAmbient)-y‖^2))).toReal =
        ((𝓕 (E8Leech.leechCertFamily (Real.pi*β))) (0 : LeechAmbient)).re-
          ((E8Leech.leechCertFamily (Real.pi*β)) 0).re := by
    rw [← hc.calibration]
    unfold E8Leech.latticePotentialEnergy E8Leech.gaussianPotential E8Leech.gaussianKernel
    congr 1
  have h := leechSchwartzInput_of_gaussian_certificate leechRelabelIsometry
    leechRelabelIsometry_image_leechLattice hα (E8Leech.leechCertFamily (Real.pi*β))
    hc.fourierReal hc.fourierNonneg hmin hcal
  have hβ' : Real.pi*β/Real.pi = β := by
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  rw [hβ'] at h
  exact ⟨_, h⟩

/-- The sharp lower Gaussian profile of `S²⁴`: no hypothesis. -/
theorem sphere24_gaussian_sharp_profile_lower : SphereGaussianSharpProfileLower24 :=
  sphereGaussianSharpProfileLower24_of_schwartz_input_off leechSharpGaussianSchwartzInputOff24

end SphericalRiesz
