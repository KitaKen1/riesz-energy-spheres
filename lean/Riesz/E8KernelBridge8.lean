import E8Leech.E8KernelPositivity
import Riesz.E8InputFromCertificate8

/-! The Gaussian input of `S⁸` from the kernel inequality of `E8` (stage G8).

The vendored development `E8Leech` (snapshot of the sibling project, `third_party/E8Leech`)
proves the inequality (6.4)(1) of Cohn–Kumar–Miller–Radchenko–Viazovska for `E8` on the whole
quadrant (`E8Leech.e8KernelNonneg`) and from it, for every scale `α > 0` with `α ≠ π`, a
Schwartz function with the properties of a sharp Gaussian certificate for the `E8` set
(`E8Leech.e8CertFamily_cert`).

Here its `E8` set is identified with the lattice `e8Lattice` of this project (the two
developments use the same triangular basis), and the certificate is turned into the Gaussian
input `E8SharpGaussianSchwartzInputOff8` at the scales `β = α/π ≠ 1`.  Hence the sharp lower
Gaussian profile of `S⁸` and the main target `S8s4Target` hold without hypotheses. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped FourierTransform SchwartzMap ENNReal
namespace SphericalRiesz

/-- The triangular basis matrix of the vendored development is the matrix `e8Matrix`. -/
theorem e8Leech_triangularMatrix_eq : E8Leech.e8TriangularMatrix = e8Matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [E8Leech.e8TriangularMatrix, E8Leech.e8TriangularNumerators, e8Matrix]

/-- The two Euclidean bases of `E8` are the same vectors. -/
theorem e8Leech_euclideanBasis_eq (i : Fin 8) :
    E8Leech.e8EuclideanBasis i = e8EuclideanBasis i := by
  rw [E8Leech.e8EuclideanBasis, e8EuclideanBasis, Module.Basis.map_apply, Module.Basis.map_apply,
    E8Leech.e8CoordinateBasis_apply, e8Basis_apply, e8Leech_triangularMatrix_eq]

/-- The `E8` lattice of the vendored development is the lattice of this project. -/
theorem e8Leech_e8Lattice_eq : E8Leech.e8Lattice = e8Lattice := by
  rw [E8Leech.e8Lattice, e8Lattice]
  congr 1
  ext x
  simp only [Set.mem_range, e8Leech_euclideanBasis_eq]

/-- The `E8` set of the vendored development (integer or half-integer coordinates with even
sum) is the lattice of this project. -/
theorem e8Leech_e8Set_eq : E8Leech.e8Set = (e8Lattice : Set E8Ambient) := by
  rw [← E8Leech.coe_e8Lattice, e8Leech_e8Lattice_eq]

/-- The Gaussian input of `S⁸` at every scale `β ≠ 1`: no hypothesis. -/
theorem e8SharpGaussianSchwartzInputOff8 : E8SharpGaussianSchwartzInputOff8 := by
  intro β hβ hβ1
  have hα : 0 < Real.pi*β := mul_pos Real.pi_pos hβ
  have hαπ : Real.pi*β ≠ Real.pi := fun h =>
    hβ1 (mul_left_cancel₀ Real.pi_ne_zero (h.trans (mul_one Real.pi).symm))
  have hc := E8Leech.e8CertFamily_cert E8Leech.e8KernelNonneg hα hαπ
  have hmin : ∀ v : E8Ambient, v ≠ 0 →
      ((E8Leech.e8CertFamily E8Leech.e8KernelNonneg (Real.pi*β)) v).re ≤
        Real.exp (-(Real.pi*β)*‖v‖^2) := fun v hv => hc.minorant v hv
  have hcal : (∑' y : E8Leech.e8Set, if (y : E8Ambient) = 0 then (0 : ℝ≥0∞)
      else ENNReal.ofReal (Real.exp (-(Real.pi*β)*‖(0 : E8Ambient)-y‖^2))).toReal =
        ((𝓕 (E8Leech.e8CertFamily E8Leech.e8KernelNonneg (Real.pi*β))) (0 : E8Ambient)).re-
          ((E8Leech.e8CertFamily E8Leech.e8KernelNonneg (Real.pi*β)) 0).re := by
    rw [← hc.calibration]
    unfold E8Leech.latticePotentialEnergy E8Leech.gaussianPotential E8Leech.gaussianKernel
    congr 1
  have h := e8SchwartzInput_of_gaussian_certificate e8Leech_e8Set_eq hα
    (E8Leech.e8CertFamily E8Leech.e8KernelNonneg (Real.pi*β)) hc.fourierReal hc.fourierNonneg
    hmin hcal
  have hβ' : Real.pi*β/Real.pi = β := by
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  rw [hβ'] at h
  exact ⟨_, h⟩

/-- The sharp lower Gaussian profile of `S⁸`: no hypothesis. -/
theorem sphere8_gaussian_sharp_profile_lower : SphereGaussianSharpProfileLower8 :=
  sphereGaussianSharpProfileLower8_of_schwartz_input_off e8SharpGaussianSchwartzInputOff8

/-- **The main target.**  The sharp second-order asymptotics of the Riesz energy with exponent
`s = 4` on `S⁸`, without hypotheses. -/
theorem S8s4Target_unconditional : S8s4Target :=
  S8s4Target_of_gaussian_profile sphere8_gaussian_sharp_profile_lower

end SphericalRiesz
