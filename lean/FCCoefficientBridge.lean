import FCThetaBridge
import FCEpsteinBridge
import Riesz.SphereLog2
import Riesz.SphereLog24

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Set MeasureTheory
namespace RieszSphereFC

theorem epstein_two_eq (s : ℂ) :
    epstein 2 (latticeTheta 2) s = SphericalRiesz.hexEpsteinZetaCont (s / 2) := by
  have h := epstein_eq_weakFEPair 2 (latticeTheta 2) SphericalRiesz.hexThetaFEPair
    (by norm_num [SphericalRiesz.hexThetaFEPair]) rfl rfl rfl rfl
    (fun t ht => latticeTheta_two_complex_eq (lt_trans zero_lt_one ht)) s
  simpa [SphericalRiesz.hexEpsteinZetaCont] using h

theorem epstein_twenty_four_eq (s : ℂ) :
    epstein 24 (latticeTheta 24) s = SphericalRiesz.leechEpsteinZetaCont (s / 2) := by
  have h := epstein_eq_weakFEPair 24 (latticeTheta 24) SphericalRiesz.leechThetaFEPair
    (by norm_num [SphericalRiesz.leechThetaFEPair]) rfl rfl rfl rfl
    (fun t ht => latticeTheta_twenty_four_complex_eq (lt_trans zero_lt_one ht)) s
  simpa [SphericalRiesz.leechEpsteinZetaCont, show (24 : ℂ) / 2 = 12 by norm_num] using h

theorem epstein_two_eq_of_ne_zero {s : ℂ} (hs : s ≠ 0) :
    epstein 2 (latticeTheta 2) s = SphericalRiesz.hexEpsteinZeta (s / 2) := by
  rw [epstein_two_eq, SphericalRiesz.hexEpsteinZetaCont_eq (div_ne_zero hs (by norm_num))]

theorem epstein_twenty_four_eq_of_ne_zero {s : ℂ} (hs : s ≠ 0) :
    epstein 24 (latticeTheta 24) s = SphericalRiesz.leechEpsteinZeta (s / 2) := by
  rw [epstein_twenty_four_eq, SphericalRiesz.leechEpsteinZetaCont_eq (div_ne_zero hs (by norm_num))]

theorem deriv_comp_half_re {f : ℂ → ℂ} (hf : DifferentiableAt ℂ f 0) :
    (deriv (fun s : ℂ => f (s / 2)) 0).re = (1 / 2 : ℝ) * (deriv f 0).re := by
  have hg : HasDerivAt (fun s : ℂ => s / 2) (1 / 2 : ℂ) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).div_const 2
  have hf' : HasDerivAt f (deriv f 0) ((0 : ℂ) / 2) := by simpa using hf.hasDerivAt
  have hd := hf'.comp (0 : ℂ) hg
  change HasDerivAt (fun s : ℂ => f (s / 2)) _ 0 at hd
  rw [hd.deriv]
  simp [Complex.mul_re]
  <;> ring

theorem epstein_two_deriv_re :
    (deriv (epstein 2 (latticeTheta 2)) 0).re =
      (1 / 2 : ℝ) * (deriv SphericalRiesz.hexEpsteinZetaCont 0).re := by
  have he : epstein 2 (latticeTheta 2) = fun s : ℂ => SphericalRiesz.hexEpsteinZetaCont (s / 2) :=
    funext epstein_two_eq
  rw [he]
  exact deriv_comp_half_re (SphericalRiesz.hexEpsteinZetaCont_differentiableAt (by norm_num))

theorem epstein_twenty_four_deriv_re :
    (deriv (epstein 24 (latticeTheta 24)) 0).re =
      (1 / 2 : ℝ) * (deriv SphericalRiesz.leechEpsteinZetaCont 0).re := by
  have he : epstein 24 (latticeTheta 24) = fun s : ℂ => SphericalRiesz.leechEpsteinZetaCont (s / 2) :=
    funext epstein_twenty_four_eq
  rw [he]
  exact deriv_comp_half_re (SphericalRiesz.leechEpsteinZetaCont_differentiableAt (by norm_num))

end RieszSphereFC
