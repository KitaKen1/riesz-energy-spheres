import Riesz.SpherePoleAngle8

/-!
An actual two-dimensional change of variables for the one-pole integral.
The nonzero exact integral also establishes integrability, using the
total Bochner-integral API, before subsequent Fubini applications.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz

def poleRadialKernel4 (a r : ℝ) : ℝ :=
  if a ^ 2 + r ^ 2 < 1 then (2 - 2 * a / Real.sqrt (a ^ 2 + r ^ 2))⁻¹ ^ 2 else 0

def poleHalfPlane4 (p : ℝ × ℝ) : ℝ :=
  if 0 < p.2 then p.2 ^ 7 * poleRadialKernel4 p.1 p.2 else 0

def poleRectangle4 : ℝ × ℝ → ℝ :=
  (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) Real.pi).indicator
    (fun p => p.1 ^ 8 * poleAngular4 p.2)

theorem poleRadialKernel4_polar (r t : ℝ) (hr : 0 < r) :
    poleRadialKernel4 (r * Real.cos t) (r * Real.sin t) =
      if r < 1 then (2 - 2 * Real.cos t)⁻¹ ^ 2 else 0 := by
  have hs : (r * Real.cos t)^2 + (r * Real.sin t)^2 = r^2 := by
    calc
      _ = r^2 * (Real.cos t ^ 2 + Real.sin t ^ 2) := by ring
      _ = _ := by rw [Real.cos_sq_add_sin_sq]; ring
  have hi : r^2 < 1 ↔ r < 1 := by
    constructor <;> intro h <;> nlinarith
  unfold poleRadialKernel4
  simp only [hs, Real.sqrt_sq hr.le, hi, mul_div_assoc, mul_div_cancel_left₀ _ hr.ne']

theorem poleHalfPlane4_polar (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
    p.1 * poleHalfPlane4 (polarCoord.symm p) = poleRectangle4 p := by
  change p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi at hp
  have hr : 0 < p.1 := hp.1
  have htlo : -Real.pi < p.2 := hp.2.1
  have hthi : p.2 < Real.pi := hp.2.2
  change p.1 * (if 0 < p.1 * Real.sin p.2 then
      (p.1 * Real.sin p.2)^7 * poleRadialKernel4 (p.1 * Real.cos p.2) (p.1 * Real.sin p.2)
      else 0) = _
  rw [poleRadialKernel4_polar p.1 p.2 hr]
  by_cases ht : 0 < p.2
  · have hs := Real.sin_pos_of_pos_of_lt_pi ht hthi
    have hpos := mul_pos hr hs
    rw [ite_eq_left hpos]
    by_cases h1 : p.1 < 1
    · rw [ite_eq_left h1]
      have hm : p ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) Real.pi := ⟨⟨hr,h1⟩,⟨ht,hthi⟩⟩
      rw [poleRectangle4, indicator_of_mem hm]
      calc
        _ = p.1 ^ 8 * (Real.sin p.2 ^ 7 * (2 - 2 * Real.cos p.2)⁻¹ ^ 2) := by ring
        _ = _ := by rw [poleAngular4_kernel_cancel p.2 ⟨ht,hthi⟩]
    · have hm : p ∉ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) Real.pi := fun h => h1 h.1.2
      simp [h1, poleRectangle4, hm]
  · have hs : Real.sin p.2 ≤ 0 :=
      Real.sin_nonpos_of_nonpos_of_neg_pi_le (le_of_not_gt ht) htlo.le
    have hnon : ¬ 0 < p.1 * Real.sin p.2 :=
      not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hr.le hs)
    have hm : p ∉ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) Real.pi := fun h => ht h.2.1
    simp [hnon, poleRectangle4, hm]

theorem poleRectangle4_zero_off_target (p : ℝ × ℝ) (hp : p ∉ polarCoord.target) :
    poleRectangle4 p = 0 := by
  apply indicator_of_notMem
  intro hm
  apply hp
  change p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi
  exact ⟨hm.1.1, ⟨by linarith [hm.2.1, Real.pi_pos], hm.2.2⟩⟩

theorem poleHalfPlane4_integral : (∫ p, poleHalfPlane4 p) = 2 / 45 := by
  rw [← integral_comp_polarCoord_symm]
  have h : (∫ p in polarCoord.target, p.1 • poleHalfPlane4 (polarCoord.symm p)) =
      ∫ p in polarCoord.target, poleRectangle4 p := by
    apply setIntegral_congr_fun polarCoord.open_target.measurableSet
    intro p hp
    exact poleHalfPlane4_polar p hp
  rw [h, setIntegral_eq_integral_of_forall_compl_eq_zero poleRectangle4_zero_off_target,
    poleRectangle4, integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
  exact poleRectangle4_integral

theorem poleHalfPlane4_integrable : Integrable poleHalfPlane4 := by
  apply Integrable.of_integral_ne_zero
  rw [poleHalfPlane4_integral]
  norm_num

theorem poleHalfPlane4_iterated_integral :
    (∫ a : ℝ, ∫ r : ℝ, poleHalfPlane4 (a,r)) = 2 / 45 := by
  rw [← integral_prod poleHalfPlane4 poleHalfPlane4_integrable]
  exact poleHalfPlane4_integral

theorem poleHalfPlane4_radial_integral (a : ℝ) :
    (∫ r in Ioi (0 : ℝ), r^7 * poleRadialKernel4 a r) =
      ∫ r : ℝ, poleHalfPlane4 (a,r) := by
  rw [← integral_indicator measurableSet_Ioi]
  congr 1

#print axioms poleRadialKernel4_polar
#print axioms poleHalfPlane4_polar
#print axioms poleHalfPlane4_integral
#print axioms poleHalfPlane4_integrable
#print axioms poleHalfPlane4_iterated_integral
#print axioms poleHalfPlane4_radial_integral

end SphericalRiesz
