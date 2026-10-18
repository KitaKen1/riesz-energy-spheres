import Riesz.EqualAreaGram8

/-!
# The actual radial cone of the explicit spherical chart

This connects the explicit coordinates to the cone set appearing in the
existing definition of sphereArea8. It proves actual cone injectivity and
set identities, but does not yet prove a change-of-variables measure formula.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped Pointwise
namespace SphericalRiesz

def equalAreaCone (z : Fin 9 → ℝ) : Ambient9 :=
  z 0 • equalAreaPhi (Fin.tail z)

def equalAreaConeDomain : Set (Fin 9 → ℝ) :=
  {z | z 0 ∈ Ioo (0:ℝ) 1 ∧ Fin.tail z ∈ equalAreaChartDomain}

theorem equalAreaCone_continuous : Continuous equalAreaCone := by
  unfold equalAreaCone
  exact (continuous_apply 0).smul (equalAreaPhi_continuous.comp (by fun_prop))

theorem equalAreaCone_norm (z : Fin 9 → ℝ)
    (hz : equalAreaSquaredNorm (Fin.tail z) < 1) :
    ‖equalAreaCone z‖ = |z 0| := by
  have h : ‖equalAreaPhi (Fin.tail z)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp (equalAreaPhi_mem_sphere _ hz)
  simp only [equalAreaCone,norm_smul,Real.norm_eq_abs,h,mul_one]

theorem equalAreaCone_injOn : InjOn equalAreaCone equalAreaConeDomain := by
  intro z hz w hw h
  have hr : z 0 = w 0 := by
    have he := congrArg norm h
    rw [equalAreaCone_norm z hz.2.1,equalAreaCone_norm w hw.2.1,
      abs_of_pos hz.1.1,abs_of_pos hw.1.1] at he
    exact he
  have hp : equalAreaPhi (Fin.tail z) = equalAreaPhi (Fin.tail w) := by
    change z 0 • equalAreaPhi (Fin.tail z) = w 0 • equalAreaPhi (Fin.tail w) at h
    rw [←hr] at h
    exact (smul_right_injective Ambient9 (ne_of_gt hz.1.1)) h
  have ht : Fin.tail z = Fin.tail w := equalAreaPhi_injOn hz.2 hw.2 hp
  funext i
  exact Fin.cases hr (fun j => congrFun ht j) i

theorem equalAreaCone_image (s : Set (Fin 8 → ℝ)) :
    equalAreaCone '' {z | z 0 ∈ Ioo (0:ℝ) 1 ∧ Fin.tail z ∈ s} =
      Ioo (0:ℝ) 1 • (equalAreaPhi '' s) := by
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z 0,hz.1,equalAreaPhi (Fin.tail z),⟨Fin.tail z,hz.2,rfl⟩,rfl⟩
  · rintro ⟨t,ht,x,⟨p,hp,rfl⟩,rfl⟩
    refine ⟨Fin.cons t p,?_,?_⟩
    · simpa only [Set.mem_ofPred_eq,Fin.cons_zero,Fin.tail_cons] using And.intro ht hp
    · simp only [equalAreaCone,Fin.cons_zero,Fin.tail_cons]

theorem equalAreaCone_domain_image :
    equalAreaCone '' equalAreaConeDomain =
      Ioo (0:ℝ) 1 • (equalAreaPhi '' equalAreaChartDomain) :=
  equalAreaCone_image equalAreaChartDomain

/-- The existing actual sphere measure is tied to this very cone set.
Measurability is explicit; no equal-area measure equality is assumed. -/
theorem sphereArea8_equalAreaChart_cone (s : Set equalAreaChartDomain)
    (hs : MeasurableSet (equalAreaSphereChart '' s)) :
    sphereArea8 (equalAreaSphereChart '' s) =
      9 * (volume : Measure Ambient9)
        (equalAreaCone '' {z | z 0 ∈ Ioo (0:ℝ) 1 ∧ Fin.tail z ∈ Subtype.val '' s}) := by
  rw [sphereArea8,Measure.toSphere_apply' _ hs,equalAreaCone_image]
  have hi : Subtype.val '' (equalAreaSphereChart '' s) =
      equalAreaPhi '' (Subtype.val '' s) := by
    rw [image_image,image_image]
    rfl
  rw [hi]
  congr 1
  norm_num [Ambient9]

end SphericalRiesz
