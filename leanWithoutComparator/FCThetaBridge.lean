import FCDefinitions
import FCEisensteinBridge
import Riesz.FCLeechFormula24
import Riesz.LeechRegularized24
import Riesz.HexLattice2
import Riesz.E8ThetaModular

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RieszSphereFC

private def triangularIndex : ℤ × ℤ → SphericalRiesz.hexLattice := fun p =>
  ⟨SphericalRiesz.hexTriangularPoint p.1 p.2, SphericalRiesz.hexTriangularPoint_mem p.1 p.2⟩

private theorem triangularIndex_bijective : Function.Bijective triangularIndex := by
  constructor
  · rintro ⟨j, k⟩ ⟨j', k'⟩ h
    have he : SphericalRiesz.hexTriangularPoint j k = SphericalRiesz.hexTriangularPoint j' k' :=
      congrArg Subtype.val h
    rw [SphericalRiesz.hexTriangularPoint_eq_integerPoint,
      SphericalRiesz.hexTriangularPoint_eq_integerPoint] at he
    have hz := SphericalRiesz.hexMap_injective (congrArg WithLp.ofLp he)
    have h0 := congrFun hz 0
    have h1 := congrFun hz 1
    apply Prod.ext
    · exact_mod_cast h0
    · exact_mod_cast h1
  · intro x
    obtain ⟨j, k, h⟩ := (SphericalRiesz.hexLattice_mem_iff_triangular x).mp x.property
    exact ⟨(j, k), Subtype.ext h⟩

theorem triangularTheta_eq (t : ℝ) :
    triangularTheta t = SphericalRiesz.hexGaussianThetaReal2 t := by
  let e := Equiv.ofBijective triangularIndex triangularIndex_bijective
  unfold triangularTheta SphericalRiesz.hexGaussianThetaReal2
  rw [← e.tsum_eq]
  apply tsum_congr
  intro p
  change Real.exp _ = Real.exp (-(Real.pi * t *
    ‖SphericalRiesz.hexTriangularPoint p.1 p.2‖ ^ 2))
  rw [SphericalRiesz.hexTriangularPoint_norm_sq]
  push_cast
  congr 1
  ring

theorem triangularTheta_complex_eq {t : ℝ} (ht : 0 < t) :
    (triangularTheta t : ℂ) = SphericalRiesz.hexThetaImag t := by
  rw [triangularTheta_eq, SphericalRiesz.hexThetaImag_eq_real ht]

theorem latticeTheta_two_complex_eq {t : ℝ} (ht : 0 < t) :
    (latticeTheta 2 t : ℂ) = SphericalRiesz.hexThetaImag t := by
  change (triangularTheta t : ℂ) = _
  exact triangularTheta_complex_eq ht

theorem leechTheta_complex_eq {t : ℝ} (ht : 0 < t) :
    (leechTheta t : ℂ) = SphericalRiesz.leechThetaImag t := by
  rw [SphericalRiesz.leechThetaImag]
  have h := SphericalRiesz.leechTheta_eq_E4_E6 (imaginaryPoint t ht)
  change SphericalRiesz.leechTheta ((t : ℂ) * Complex.I) = _ at h
  rw [h, E4_imaginary ht, E6_imaginary ht]
  change (((7 * (1 + 240 * divisorSeries 3 t) ^ 3 +
      5 * (1 - 504 * divisorSeries 5 t) ^ 2) / 12 : ℝ) : ℂ) = _
  push_cast
  rfl

theorem latticeTheta_twenty_four_complex_eq {t : ℝ} (ht : 0 < t) :
    (latticeTheta 24 t : ℂ) = SphericalRiesz.leechThetaImag t := by
  change (leechTheta t : ℂ) = _
  exact leechTheta_complex_eq ht

end RieszSphereFC
