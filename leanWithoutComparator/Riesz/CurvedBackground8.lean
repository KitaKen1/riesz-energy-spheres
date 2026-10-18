import Riesz.CurvedFarPotential8

/-! Integrability and the exact near/far partition of the actual singular
background. Relative E8 distances provide domination; no integral is
treated as a genuine integral before its integrability is proved. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalRiesz
open Boundary

def CurvedRelativeE8Distance8 (F : (Fin 8 → ℝ) → Ambient9) : Prop :=
  ∀ x ∈ UnitCube 8, ∀ y ∈ UnitCube 8,
    |dist (F x) (F y)-
      dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y))| ≤
      (1/2:ℝ)*dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y))

theorem curvedNearRieszFour8_integrableOn (F : (Fin 8 → ℝ) → Ambient9)
    (hF : Continuous F) (hd : CurvedRelativeE8Distance8 F)
    (r : ℝ) (hr : 0 < r) (x : Fin 8 → ℝ) (hx : x ∈ UnitCube 8) :
    IntegrableOn (curvedNearRieszFour F r x) (UnitCube 8) := by
  have hi := (e8Near_integrable r hr x).integrableOn (s := UnitCube 8)
  have hG := hF.measurable
  have hm : Measurable (fun y => curvedNearRieszFour F r x y-nearObliqueRieszFour 8 e8Map r x y) := by
    have hb := (outerUnitBump 8).continuous.measurable
    have hA := e8Map.continuous.measurable
    unfold curvedNearRieszFour curvedRieszFour nearObliqueRieszFour
      obliqueRieszFour flatRieszFour squaredDistance
    fun_prop
  have he : ∀ᵐ y ∂volume.restrict (UnitCube 8),
      ‖curvedNearRieszFour F r x y-nearObliqueRieszFour 8 e8Map r x y‖ ≤
        (64*(1/2:ℝ))*nearObliqueRieszFour 8 e8Map r x y := by
    filter_upwards [ae_restrict_mem (unitCube_measurableSet 8)] with y hy
    simpa only [Real.norm_eq_abs] using curvedNearRieszFour_relative_error F r x y
      (1/2) (by norm_num) le_rfl (hd x hx y hy)
  have hid := (hi.const_mul (64*(1/2:ℝ))).mono' hm.aestronglyMeasurable.restrict he
  exact (hid.add hi).congr (Eventually.of_forall (fun y => sub_add_cancel _ _))

theorem curvedNearPotential8_integrableOn (F : (Fin 8 → ℝ) → Ambient9)
    (hF : Continuous F) (hd : CurvedRelativeE8Distance8 F) (r : ℝ) (hr : 0 < r) :
    IntegrableOn (curvedNearPotential F r) (UnitCube 8) := by
  let M : ℝ := 64*(1/2:ℝ)*e8NearIntegralConstant*r^4
  have he : ∀ᵐ x ∂volume.restrict (UnitCube 8),
      ‖curvedNearPotential F r x-e8NearPotential r x‖ ≤ M := by
    filter_upwards [ae_restrict_mem (unitCube_measurableSet 8)] with x hx
    simpa only [Real.norm_eq_abs] using curvedNearPotential_relative_error F hF.measurable r hr x
      (1/2) (by norm_num) le_rfl (hd x hx)
  have hconst : Integrable (fun _ : Fin 8 → ℝ => M) (volume.restrict (UnitCube 8)) :=
    continuousOn_const.integrableOn_compact (unitCube_isCompact 8)
  have hm := (curvedNearPotential_measurable F hF.measurable r).sub
    (e8NearPotential_continuous r hr).measurable
  have hid := hconst.mono' hm.aestronglyMeasurable.restrict he
  have hi : IntegrableOn (e8NearPotential r) (UnitCube 8) :=
    (e8NearPotential_continuous r hr).continuousOn.integrableOn_compact (unitCube_isCompact 8)
  exact (hid.add hi).congr (Eventually.of_forall (fun x => sub_add_cancel _ _))

def curvedPotential8 (F : (Fin 8 → ℝ) → Ambient9) (x : Fin 8 → ℝ) : ℝ :=
  ∫ y in UnitCube 8, curvedRieszFour F x y

def curvedBackground8 (F : (Fin 8 → ℝ) → Ambient9) (m : ℕ) : ℝ :=
  (m:ℝ)^4*(cubeQuadrature 8 m (curvedPotential8 F)-∫ x in UnitCube 8, curvedPotential8 F x)

theorem curvedRieszFour8_integrableOn (F : (Fin 8 → ℝ) → Ambient9)
    (hF : CurvedAnnularData8 F) (hd : CurvedRelativeE8Distance8 F)
    (x : Fin 8 → ℝ) (hx : x ∈ UnitCube 8) :
    IntegrableOn (curvedRieszFour F x) (UnitCube 8) := by
  have hf : IntegrableOn (curvedFarRieszFour8 F 2 x) (UnitCube 8) :=
    (curvedFarRieszFour8_continuousOn F hF 2 (by norm_num) x hx).integrableOn_compact (unitCube_isCompact 8)
  have hn := curvedNearRieszFour8_integrableOn F hF.continuous hd 1 (by norm_num) x hx
  apply (hf.add hn).congr
  exact Eventually.of_forall (fun y => by simp [curvedFarRieszFour8])

theorem curvedPotential8_partition (F : (Fin 8 → ℝ) → Ambient9)
    (hF : CurvedAnnularData8 F) (hd : CurvedRelativeE8Distance8 F)
    (r : ℝ) (hr : 0 < r) (x : Fin 8 → ℝ) (hx : x ∈ UnitCube 8) :
    curvedPotential8 F x = curvedFarPotential8 F r x+curvedNearPotential F (r/2) x := by
  have hf : IntegrableOn (curvedFarRieszFour8 F r x) (UnitCube 8) :=
    (curvedFarRieszFour8_continuousOn F hF r hr x hx).integrableOn_compact (unitCube_isCompact 8)
  have hn := curvedNearRieszFour8_integrableOn F hF.continuous hd (r/2) (by positivity) x hx
  unfold curvedPotential8 curvedFarPotential8 curvedNearPotential
  rw [← integral_add hf hn]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by simp [curvedFarRieszFour8])

theorem curvedPotential8_integrableOn (F : (Fin 8 → ℝ) → Ambient9)
    (hF : CurvedAnnularData8 F) (hd : CurvedRelativeE8Distance8 F) :
    IntegrableOn (curvedPotential8 F) (UnitCube 8) := by
  have hf : IntegrableOn (curvedFarPotential8 F 2) (UnitCube 8) :=
    (curvedFarPotential8_continuousOn F hF 2 (by norm_num)).integrableOn_compact (unitCube_isCompact 8)
  have hn := curvedNearPotential8_integrableOn F hF.continuous hd 1 (by norm_num)
  apply (hf.add hn).congr
  filter_upwards [ae_restrict_mem (unitCube_measurableSet 8)] with x hx
  simpa only [show (2:ℝ)/2 = 1 by norm_num,Pi.add_apply] using
    (curvedPotential8_partition F hF hd 2 (by norm_num) x hx).symm

theorem cubeQuadrature_add8 (m : ℕ) (f g : (Fin 8 → ℝ) → ℝ) :
    cubeQuadrature 8 m (fun x => f x+g x) = cubeQuadrature 8 m f+cubeQuadrature 8 m g := by
  simp_rw [cubeQuadrature_as_node_sum]
  rw [Finset.sum_add_distrib,add_div]

theorem curvedBackground8_partition (F : (Fin 8 → ℝ) → Ambient9)
    (hF : CurvedAnnularData8 F) (hd : CurvedRelativeE8Distance8 F)
    (R : ℝ) (hR : 0 < R) (m : ℕ) (hm : 8 ≤ m) :
    curvedBackground8 F m =
      (m:ℝ)^4*(cubeQuadrature 8 m (curvedFarPotential8 F (2*R/(m:ℝ)))-
        ∫ x in UnitCube 8, curvedFarPotential8 F (2*R/(m:ℝ)) x)+
      (m:ℝ)^4*(cubeQuadrature 8 m (curvedNearPotential F (R/(m:ℝ)))-
        ∫ x in UnitCube 8, curvedNearPotential F (R/(m:ℝ)) x) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hr : 0 < 2*R/(m:ℝ) := by positivity
  have heq : EqOn (curvedPotential8 F)
      (fun x => curvedFarPotential8 F (2*R/(m:ℝ)) x+curvedNearPotential F (R/(m:ℝ)) x) (UnitCube 8) := by
    intro x hx
    have hs : (2*R/(m:ℝ))/2 = R/(m:ℝ) := by ring
    simpa only [hs] using curvedPotential8_partition F hF hd _ hr x hx
  unfold curvedBackground8
  rw [cubeQuadrature_congr 8 m hm heq,setIntegral_congr_fun (unitCube_measurableSet 8) heq,
    cubeQuadrature_add8,integral_add
      ((curvedFarPotential8_continuousOn F hF _ hr).integrableOn_compact (unitCube_isCompact 8))
      (curvedNearPotential8_integrableOn F hF.continuous hd _ (div_pos hR hm0))]
  ring

theorem curvedBackground8_radius_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : (Fin 8 → ℝ) → Ambient9, CurvedAnnularData8 F →
      CurvedRelativeE8Distance8 F → ∀ R : ℝ, 1 ≤ R → ∀ m : ℕ, 8 ≤ m →
      |curvedBackground8 F m| ≤ C/R^2+
        |(m:ℝ)^4*(cubeQuadrature 8 m (curvedNearPotential F (R/(m:ℝ)))-
          ∫ x in UnitCube 8, curvedNearPotential F (R/(m:ℝ)) x)| := by
  obtain ⟨C,hC,hb⟩ := curvedFarPotential8_scaled_quadrature_bound
  refine ⟨C,hC,?_⟩
  intro F hF hd R hR m hm
  have h := hb F hF m hm (2*R) (by linarith)
  have hc : C/(2*R)^2 ≤ C/R^2 :=
    div_le_div_of_nonneg_left hC (by positivity) (by nlinarith [sq_nonneg R])
  rw [curvedBackground8_partition F hF hd R (by linarith) m hm]
  exact (abs_add_le _ _).trans (add_le_add (h.trans hc) le_rfl)

end SphericalRiesz
