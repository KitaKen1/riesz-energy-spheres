import Riesz.EqualAreaChart8
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The explicit inverse on the positive first-coordinate hemisphere.
Verifying this known formula avoids a general inverse-function theorem.
The inverse is continuous only where the first coordinate is nonzero. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Metric
open scoped Topology
namespace SphericalRiesz

def equalAreaInverse8 (q : Ambient9) : Fin 8 → ℝ :=
  Fin.cons (Real.arctan (q 1/q 0)) (fun j : Fin 7 => q j.succ.succ)

def equalAreaHemisphere8 : Set Sphere8 := {q | 0 < (q : Ambient9) 0}

theorem sphere8_coordinate_norm_identity (q : Sphere8) :
    (q : Ambient9) 0 ^ 2 + (q : Ambient9) 1 ^ 2 +
      equalAreaSquaredNorm (equalAreaInverse8 q) = 1 := by
  have hn : ‖(q : Ambient9)‖ = 1 := mem_sphere_zero_iff_norm.mp q.property
  have hs := EuclideanSpace.real_norm_sq_eq (q : Ambient9)
  rw [hn, Fin.sum_univ_succ, Fin.sum_univ_succ] at hs
  simpa only [one_pow, equalAreaSquaredNorm, equalAreaInverse8, Fin.cons_succ,
    show (0 : Fin 8).succ = (1 : Fin 9) from rfl, add_assoc] using hs.symm

theorem equalAreaInverse8_mem_domain (q : Sphere8) (hq : 0 < (q : Ambient9) 0) :
    equalAreaInverse8 q ∈ equalAreaChartDomain := by
  refine ⟨?_, Real.arctan_mem_Ioo _⟩
  have h := sphere8_coordinate_norm_identity q
  nlinarith [sq_nonneg ((q : Ambient9) 1), sq_pos_of_pos hq]

theorem equalAreaInverse8_height (q : Sphere8) (hq : 0 < (q : Ambient9) 0) :
    equalAreaHeight (equalAreaInverse8 q) =
      (q : Ambient9) 0 * Real.sqrt (1+((q : Ambient9) 1/(q : Ambient9) 0)^2) := by
  have hd := equalAreaInverse8_mem_domain q hq
  have hh := equalAreaHeight_sq (equalAreaInverse8 q) hd.1
  have hs := sphere8_coordinate_norm_identity q
  have hr : 0 < 1+((q : Ambient9) 1/(q : Ambient9) 0)^2 := by positivity
  have hroot := Real.sq_sqrt hr.le
  have hsq : ((q : Ambient9) 0 *
      Real.sqrt (1+((q : Ambient9) 1/(q : Ambient9) 0)^2))^2 =
      (q : Ambient9) 0 ^ 2+(q : Ambient9) 1 ^ 2 := by
    rw [mul_pow,hroot]
    field_simp
  nlinarith [equalAreaHeight_pos (equalAreaInverse8 q) hd.1,
    mul_pos hq (Real.sqrt_pos.mpr hr)]

theorem equalAreaPhi_inverse8 (q : Sphere8) (hq : 0 < (q : Ambient9) 0) :
    equalAreaPhi (equalAreaInverse8 q) = (q : Ambient9) := by
  have hr : 0 < Real.sqrt (1+((q : Ambient9) 1/(q : Ambient9) 0)^2) := by positivity
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change equalAreaHeight (equalAreaInverse8 q) *
      Real.cos (Real.arctan ((q : Ambient9) 1/(q : Ambient9) 0)) = (q : Ambient9) 0
    rw [equalAreaInverse8_height q hq, Real.cos_arctan]
    field_simp
  · refine Fin.cases ?_ (fun k => ?_) j
    · change equalAreaHeight (equalAreaInverse8 q) *
        Real.sin (Real.arctan ((q : Ambient9) 1/(q : Ambient9) 0)) = (q : Ambient9) 1
      rw [equalAreaInverse8_height q hq, Real.sin_arctan]
      field_simp
    · simp only [equalAreaPhi, PiLp.toLp_apply, Fin.cons_succ, equalAreaInverse8,
        Fin.tail]

theorem equalAreaPhi_first_pos (p : Fin 8 → ℝ) (hp : p ∈ equalAreaChartDomain) :
    0 < equalAreaPhi p 0 := by
  change 0 < equalAreaHeight p * Real.cos (p 0)
  exact mul_pos (equalAreaHeight_pos p hp.1) (Real.cos_pos_of_mem_Ioo hp.2)

theorem equalAreaInverse8_phi (p : Fin 8 → ℝ) (hp : p ∈ equalAreaChartDomain) :
    equalAreaInverse8 (equalAreaPhi p) = p := by
  let q : Sphere8 := ⟨equalAreaPhi p,equalAreaPhi_mem_sphere p hp.1⟩
  exact equalAreaPhi_injOn
    (equalAreaInverse8_mem_domain q (equalAreaPhi_first_pos p hp)) hp
    (equalAreaPhi_inverse8 q (equalAreaPhi_first_pos p hp))

theorem equalAreaPhi_image_domain :
    equalAreaPhi '' equalAreaChartDomain =
      {q : Ambient9 | q ∈ Sphere8 ∧ 0 < q 0} := by
  ext q
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact ⟨equalAreaPhi_mem_sphere p hp.1,equalAreaPhi_first_pos p hp⟩
  · rintro ⟨hs,hq⟩
    exact ⟨equalAreaInverse8 q,equalAreaInverse8_mem_domain ⟨q,hs⟩ hq,
      equalAreaPhi_inverse8 ⟨q,hs⟩ hq⟩

theorem equalAreaInverse8_continuousOn :
    ContinuousOn equalAreaInverse8 {q : Ambient9 | q 0 ≠ 0} := by
  unfold equalAreaInverse8
  apply continuousOn_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact Real.continuous_arctan.comp_continuousOn
      ((by fun_prop : Continuous (fun q : Ambient9 => q 1)).continuousOn.div
        (by fun_prop : Continuous (fun q : Ambient9 => q 0)).continuousOn
        (fun q hq => hq))
  · simp only [Fin.cons_succ]
    fun_prop

theorem equalAreaHemisphere8_isOpen : IsOpen equalAreaHemisphere8 := by
  exact isOpen_lt continuous_const (by fun_prop)

def equalAreaHemisphereHomeomorph8 : equalAreaChartDomain ≃ₜ equalAreaHemisphere8 where
  toFun p := ⟨equalAreaSphereChart p, equalAreaPhi_first_pos p p.property⟩
  invFun q := ⟨equalAreaInverse8 (q : Sphere8),
    equalAreaInverse8_mem_domain (q : Sphere8) q.property⟩
  left_inv p := Subtype.ext (equalAreaInverse8_phi p p.property)
  right_inv q := Subtype.ext (Subtype.ext (equalAreaPhi_inverse8 (q : Sphere8) q.property))
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact equalAreaPhi_continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply equalAreaInverse8_continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val)
    intro q
    exact q.property.ne'

end SphericalRiesz
