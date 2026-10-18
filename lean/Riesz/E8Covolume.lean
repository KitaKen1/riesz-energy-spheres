import Riesz.E8Lattice
import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# Covolume one of the actual Euclidean E8 lattice

Transport the actual basis fundamental domain through the existing
volume-preserving L2-coordinate equivalence. Its Pi-space volume is the
already checked determinant 1. This avoids reconstructing the arbitrary
integer basis chosen by the general Poisson infrastructure.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace SphericalRiesz

theorem e8EuclideanFundamentalDomain_volume :
    (volume : Measure E8Ambient).real (ZSpan.fundamentalDomain e8EuclideanBasis) = 1 := by
  have hp : (WithLp.ofLp : E8Ambient → (Fin 8 → ℝ)) ⁻¹'
      ZSpan.fundamentalDomain e8Basis = ZSpan.fundamentalDomain e8EuclideanBasis := by
    ext x
    simp only [Set.mem_preimage, ZSpan.mem_fundamentalDomain, e8EuclideanBasis,
      Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm]
    rfl
  have hm : (Matrix.of e8Basis : Matrix (Fin 8) (Fin 8) ℝ) = e8Matrix := by
    ext i j
    simp only [Matrix.of_apply, e8Basis_apply]
    rfl
  have hv : (volume : Measure (Fin 8 → ℝ)).real (ZSpan.fundamentalDomain e8Basis) = 1 := by
    rw [ZSpan.volume_real_fundamentalDomain, hm, e8Matrix_det, abs_one]
  have h := (PiLp.volume_preserving_ofLp (ι := Fin 8)).measureReal_preimage
    (ZSpan.fundamentalDomain_measurableSet (b := e8Basis)).nullMeasurableSet
  simpa only [hp, hv] using h

theorem e8Lattice_covolume : ZLattice.covolume e8Lattice = 1 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain e8Lattice volume
    (ZSpan.isAddFundamentalDomain e8EuclideanBasis volume)]
  exact e8EuclideanFundamentalDomain_volume

#print axioms e8EuclideanFundamentalDomain_volume
#print axioms e8Lattice_covolume

end SphericalRiesz
