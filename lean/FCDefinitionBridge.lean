import FCAreaBridge
import Riesz.OptimalSphereEnergy

noncomputable section
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace RieszSphereFC

theorem rieszEnergy_eq_min {d N : ℕ} {s : ℝ} (hs : 0 ≤ s) :
    rieszEnergy d s N = SphericalRiesz.minimumRieszEnergyD d s N := by
  unfold rieszEnergy
  rw [if_neg (not_lt_of_ge hs)]
  rfl

theorem rieszEnergy_eq_max {d N : ℕ} {s : ℝ} (hs : s < 0) :
    rieszEnergy d s N = SphericalRiesz.maximumRieszEnergyD d s N := by
  unfold rieszEnergy
  rw [if_pos hs]
  rfl

theorem logEnergy_eq (d N : ℕ) :
    logEnergy d N = SphericalRiesz.minimumLogEnergyD d N := rfl

theorem capDiscrepancy_two_eq {N : ℕ} (X : Fin N ↪ Sphere 2) :
    capDiscrepancy 2 X = Real.sqrt (SphericalRiesz.capDiscrepancyL2Sq2 X) := rfl

theorem capDiscrepancy_eight_eq {N : ℕ} (X : Fin N ↪ Sphere 8) :
    capDiscrepancy 8 X = Real.sqrt (SphericalRiesz.capDiscrepancyL2Sq8 X) := rfl

theorem capDiscrepancy_twenty_four_eq {N : ℕ} (X : Fin N ↪ Sphere 24) :
    capDiscrepancy 24 X = Real.sqrt (SphericalRiesz.capDiscrepancyL2Sq24 X) := rfl

end RieszSphereFC
