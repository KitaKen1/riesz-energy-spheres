import OAI.Analysis.Triangular.GaussianMinorants
import Riesz.HexLattice2

/-! Gaussian certificates of the triangular lattice at every scale (stage S2-6: the external
input of the S² chain).

The theorem `OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction` of the OpenAI
triangular-lattice development (vendored unmodified in `third_party/OpenAIMath`, Apache-2.0)
gives, for every `α > 0`, a real radial Schwartz function on the plane below the Gaussian
`exp(-π α |x|²)`, with real nonnegative Fourier transform, equal to the Gaussian at the nonzero
points of the density-one triangular lattice and with Fourier transform zero at the nonzero
points which pair integrally with the lattice.

Here its objects are identified with those of this project: the point map is
`hexTriangularPoint`, the lattice is `hexLattice`, the Gaussian is the same function, and the
dual condition is the hypothesis of `HexGaussianContactCertificate2.of_real`.  Hence
`HexGaussianContactCertificate2 β f` has a solution for every `β > 0`, without hypotheses. -/

set_option autoImplicit false
noncomputable section
open scoped FourierTransform SchwartzMap
namespace SphericalRiesz

/-- The constant `b = √3/2` of the external development. -/
theorem oaiTriangular_b_eq : OAI.AtomicTriangular.b = hexB := rfl

/-- The lattice points of the external development are the points `hexTriangularPoint`. -/
theorem oaiTriangularPoint_eq (p : ℤ × ℤ) :
    OAI.AtomicTriangular.triangularPoint p = hexTriangularPoint p.1 p.2 := by
  apply hexAmbient_ext
  · rw [hexTriangularPoint_apply_zero]
    simp [OAI.AtomicTriangular.triangularPoint, OAI.AtomicTriangular.b, hexB]
  · rw [hexTriangularPoint_apply_one]
    simp [OAI.AtomicTriangular.triangularPoint, OAI.AtomicTriangular.b, hexB]

/-- The lattice of the external development is the triangular lattice of this project. -/
theorem oaiTriangular_A_eq : OAI.AtomicTriangular.A = (hexLattice : Set HexAmbient) := by
  rw [hexLattice_coe_eq_range]
  exact congrArg Set.range (funext oaiTriangularPoint_eq)

/-- The Gaussian of the external development. -/
theorem oaiTriangular_gaussian_eq (α : ℝ) (x : HexAmbient) :
    OAI.AtomicTriangular.gaussian α x = Real.exp (-(Real.pi*α*‖x‖^2)) := by
  unfold OAI.AtomicTriangular.gaussian
  congr 1
  ring

/-- Gaussian contact certificates of the triangular lattice exist at every scale.  This is the
input of the S² chain; it is the OpenAI theorem in the form of this project. -/
theorem hexGaussianContact_all :
    ∀ β : ℝ, 0 < β → ∃ f, HexGaussianContactCertificate2 β f := by
  intro β hβ
  obtain ⟨g, _, hmin, hfour, hcontact, hzero, _⟩ :=
    OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction β hβ
  refine ⟨hexSchwartzOfReal g, HexGaussianContactCertificate2.of_real g ?_ hfour ?_ ?_⟩
  · intro x
    rw [← oaiTriangular_gaussian_eq]
    exact hmin x
  · intro a ha ha0
    rw [← oaiTriangular_gaussian_eq]
    exact hcontact a (by rw [oaiTriangular_A_eq]; exact ha) ha0
  · intro w hw hw0
    refine hzero w ?_ hw0
    show ∀ a ∈ OAI.AtomicTriangular.A, ∃ n : ℤ, inner ℝ a w = (n : ℝ)
    intro a ha
    rw [oaiTriangular_A_eq] at ha
    exact hw a ha

end SphericalRiesz
