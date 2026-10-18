import Riesz.EqualAreaChartD
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

variable {n : ℕ}

def equalAreaInverseD (q : (AmbientD (n+1))) : Fin (n+1) → ℝ :=
  Fin.cons (Real.arctan (q (Fin.succ 0)/q 0)) (fun j : Fin n => q j.succ.succ)

def equalAreaHemisphereD : Set (SphereD (n+1)) := {q | 0 < (q : (AmbientD (n+1))) 0}

theorem sphereD_coordinate_norm_identity (q : (SphereD (n+1))) :
    (q : (AmbientD (n+1))) 0 ^ 2 + (q : (AmbientD (n+1))) (Fin.succ 0) ^ 2 +
      equalAreaSquaredNormD (equalAreaInverseD (q : (AmbientD (n+1)))) = 1 := by
  have hn : ‖(q : (AmbientD (n+1)))‖ = 1 := mem_sphere_zero_iff_norm.mp q.property
  have hs := EuclideanSpace.real_norm_sq_eq (q : (AmbientD (n+1)))
  rw [hn, Fin.sum_univ_succ, Fin.sum_univ_succ] at hs
  simpa only [one_pow, equalAreaSquaredNormD, equalAreaInverseD, Fin.cons_succ, add_assoc] using hs.symm

theorem equalAreaInverseD_mem_domain (q : (SphereD (n+1))) (hq : 0 < (q : (AmbientD (n+1))) 0) :
    equalAreaInverseD (q : (AmbientD (n+1))) ∈ equalAreaChartDomainD := by
  refine ⟨?_, Real.arctan_mem_Ioo _⟩
  have h := sphereD_coordinate_norm_identity q
  nlinarith [sq_nonneg ((q : (AmbientD (n+1))) (Fin.succ 0)), sq_pos_of_pos hq]

theorem equalAreaInverseD_height (q : (SphereD (n+1))) (hq : 0 < (q : (AmbientD (n+1))) 0) :
    equalAreaHeightD (equalAreaInverseD (q : (AmbientD (n+1)))) =
      (q : (AmbientD (n+1))) 0 * Real.sqrt (1+((q : (AmbientD (n+1))) (Fin.succ 0)/(q : (AmbientD (n+1))) 0)^2) := by
  have hd := equalAreaInverseD_mem_domain q hq
  have hh := equalAreaHeightD_sq (equalAreaInverseD (q : (AmbientD (n+1)))) hd.1
  have hs := sphereD_coordinate_norm_identity q
  have hr : 0 < 1+((q : (AmbientD (n+1))) (Fin.succ 0)/(q : (AmbientD (n+1))) 0)^2 := by positivity
  have hroot := Real.sq_sqrt hr.le
  have hsq : ((q : (AmbientD (n+1))) 0 *
      Real.sqrt (1+((q : (AmbientD (n+1))) (Fin.succ 0)/(q : (AmbientD (n+1))) 0)^2))^2 =
      (q : (AmbientD (n+1))) 0 ^ 2+(q : (AmbientD (n+1))) (Fin.succ 0) ^ 2 := by
    rw [mul_pow,hroot]
    field_simp
  nlinarith [equalAreaHeightD_pos (equalAreaInverseD (q : (AmbientD (n+1)))) hd.1,
    mul_pos hq (Real.sqrt_pos.mpr hr)]

theorem equalAreaPhiD_inverse8 (q : (SphereD (n+1))) (hq : 0 < (q : (AmbientD (n+1))) 0) :
    equalAreaPhiD (equalAreaInverseD (q : (AmbientD (n+1)))) = (q : (AmbientD (n+1))) := by
  have hr : 0 < Real.sqrt (1+((q : (AmbientD (n+1))) (Fin.succ 0)/(q : (AmbientD (n+1))) 0)^2) := by positivity
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change equalAreaHeightD (equalAreaInverseD (q : (AmbientD (n+1)))) *
      Real.cos (Real.arctan ((q : (AmbientD (n+1))) (Fin.succ 0)/(q : (AmbientD (n+1))) 0)) = (q : (AmbientD (n+1))) 0
    rw [equalAreaInverseD_height q hq, Real.cos_arctan]
    field_simp
  · refine Fin.cases ?_ (fun k => ?_) j
    · change equalAreaHeightD (equalAreaInverseD (q : (AmbientD (n+1)))) *
        Real.sin (Real.arctan ((q : (AmbientD (n+1))) (Fin.succ 0)/(q : (AmbientD (n+1))) 0)) = (q : (AmbientD (n+1))) (Fin.succ 0)
      rw [equalAreaInverseD_height q hq, Real.sin_arctan]
      field_simp
    · simp only [equalAreaPhiD, PiLp.toLp_apply, Fin.cons_succ, equalAreaInverseD,
        Fin.tail]

theorem equalAreaPhiD_first_pos (p : Fin (n+1) → ℝ) (hp : p ∈ equalAreaChartDomainD) :
    0 < equalAreaPhiD p 0 := by
  change 0 < equalAreaHeightD p * Real.cos (p 0)
  exact mul_pos (equalAreaHeightD_pos p hp.1) (Real.cos_pos_of_mem_Ioo hp.2)

theorem equalAreaInverseD_phi (p : Fin (n+1) → ℝ) (hp : p ∈ equalAreaChartDomainD) :
    equalAreaInverseD (equalAreaPhiD p) = p := by
  let q : (SphereD (n+1)) := ⟨equalAreaPhiD p,equalAreaPhiD_mem_sphere p hp.1⟩
  exact equalAreaPhiD_injOn
    (equalAreaInverseD_mem_domain q (equalAreaPhiD_first_pos p hp)) hp
    (equalAreaPhiD_inverse8 q (equalAreaPhiD_first_pos p hp))

theorem equalAreaPhiD_image_domain :
    equalAreaPhiD '' equalAreaChartDomainD =
      {q : (AmbientD (n+1)) | q ∈ (SphereD (n+1)) ∧ 0 < q 0} := by
  ext q
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact ⟨equalAreaPhiD_mem_sphere p hp.1,equalAreaPhiD_first_pos p hp⟩
  · rintro ⟨hs,hq⟩
    exact ⟨equalAreaInverseD (q : (AmbientD (n+1))),equalAreaInverseD_mem_domain ⟨q,hs⟩ hq,
      equalAreaPhiD_inverse8 ⟨q,hs⟩ hq⟩

theorem equalAreaInverseD_continuousOn :
    ContinuousOn equalAreaInverseD {q : (AmbientD (n+1)) | q 0 ≠ 0} := by
  unfold equalAreaInverseD
  apply continuousOn_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Fin.cons_zero]
    exact Real.continuous_arctan.comp_continuousOn
      ((by fun_prop : Continuous (fun q : (AmbientD (n+1)) => q (Fin.succ 0))).continuousOn.div
        (by fun_prop : Continuous (fun q : (AmbientD (n+1)) => q 0)).continuousOn
        (fun q hq => hq))
  · simp only [Fin.cons_succ]
    fun_prop

theorem equalAreaHemisphereD_isOpen : IsOpen (equalAreaHemisphereD (n := n)) := by
  exact isOpen_lt continuous_const (by fun_prop)

def equalAreaHemisphereHomeomorphD : (equalAreaChartDomainD (n := n)) ≃ₜ (equalAreaHemisphereD (n := n)) where
  toFun p := ⟨⟨equalAreaPhiD p.1, equalAreaPhiD_mem_sphere p.1 p.2.1⟩,
    equalAreaPhiD_first_pos p.1 p.2⟩
  invFun q := ⟨equalAreaInverseD (((q : (SphereD (n+1))) : (AmbientD (n+1)))),
    equalAreaInverseD_mem_domain (q : (SphereD (n+1))) q.property⟩
  left_inv p := Subtype.ext (equalAreaInverseD_phi p.1 p.2)
  right_inv q := Subtype.ext (Subtype.ext (equalAreaPhiD_inverse8 q.1 q.2))
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact equalAreaPhiD_continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply equalAreaInverseD_continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val)
    intro q
    exact q.property.ne'

end SphericalRiesz
