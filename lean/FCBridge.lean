import FCTargetDefinitions
import Riesz.SphereStatements8
import Riesz.OptimalSphereEnergy

/-! Checked correspondence between the Mathlib-only reference and the proof library.
The reference never imports this module or any part of the proof library. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RieszSphereFC

theorem triangular_eq : triangular = SphericalRiesz.hexLattice := by
  unfold triangular SphericalRiesz.hexLattice
  congr 1
  congr 1
  funext i
  exact (SphericalRiesz.hexEuclideanBasis_apply i).symm

theorem leech_eq : leech = SphericalRiesz.leechLattice := by
  unfold leech SphericalRiesz.leechLattice
  congr 1
  congr 1
  funext i
  exact (SphericalRiesz.leechEuclideanBasis_apply i).symm

theorem theta_triangular_eq : theta triangular = SphericalRiesz.hexThetaImag := by
  rw [triangular_eq]
  rfl

theorem theta_leech_eq : theta leech = SphericalRiesz.leechThetaImag := by
  rw [leech_eq]
  rfl

theorem hexZeta_eq : hexZeta = SphericalRiesz.hexEpsteinZeta := by
  unfold hexZeta
  rw [theta_triangular_eq]
  rfl

theorem leechZeta_eq : leechZeta = SphericalRiesz.leechEpsteinZeta := by
  unfold leechZeta
  rw [theta_leech_eq]
  rfl

theorem hexZetaCont_eq : hexZetaCont = SphericalRiesz.hexEpsteinZetaCont := by
  unfold hexZetaCont
  rw [theta_triangular_eq]
  rfl

theorem leechZetaCont_eq : leechZetaCont = SphericalRiesz.leechEpsteinZetaCont := by
  unfold leechZetaCont
  rw [theta_leech_eq]
  rfl

theorem e8Zeta_eq : e8Zeta = SphericalRiesz.e8EpsteinCandidate := rfl

theorem normalizedMin_eq (d : ℕ) (s : ℝ) :
    normalizedMin d s = SphericalRiesz.normalizedMinimumRieszEnergyD d s := rfl
theorem normalizedMax_eq (d : ℕ) (s : ℝ) :
    normalizedMax d s = SphericalRiesz.normalizedMaximumRieszEnergyD d s := rfl
theorem normalizedLogMin_eq (d : ℕ) :
    normalizedLogMin d = SphericalRiesz.normalizedMinimumLogEnergyD d := rfl
theorem area_eq (d : ℕ) : area d = (SphericalRiesz.sphereAreaD d).real univ := rfl
theorem area_two : area 2 = 4*Real.pi := SphericalRiesz.sphereArea2_univ_real
theorem area_eight : area 8 = 32*Real.pi^4/105 := SphericalRiesz.sphereArea8_mass_real

theorem minimumCap_two : minimumCap 2 = SphericalRiesz.minimumCapDiscrepancy2 := rfl
theorem minimumCap_eight : minimumCap 8 = SphericalRiesz.minimumCapDiscrepancy8 := rfl
theorem minimumCap_twentyfour : minimumCap 24 = SphericalRiesz.minimumCapDiscrepancy24 := rfl

end RieszSphereFC
