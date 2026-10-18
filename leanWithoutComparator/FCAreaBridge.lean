import FCDefinitions
import Riesz.SphereMeasureD

noncomputable section
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace RieszSphereFC

theorem uniform_eq (d : ℕ) : uniform d = SphericalRiesz.sphereProbabilityD d := rfl

theorem area_eq (d : ℕ) : area d = (SphericalRiesz.sphereAreaD d).real univ := by
  rw [SphericalRiesz.sphereAreaD_univ_real]
  have hp : Real.sqrt Real.pi ^ (d + 1) = Real.pi ^ (((d : ℝ) + 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    congr 1
    push_cast
    ring
  rw [hp]
  unfold area
  push_cast
  rw [Real.Gamma_add_one (show ((d : ℝ) + 1) / 2 ≠ 0 by positivity)]
  field_simp
  <;> ring

end RieszSphereFC
