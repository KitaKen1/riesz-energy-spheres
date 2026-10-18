import Riesz.EqualAreaGramD

/-!
# The actual radial cone of the explicit spherical chart

This connects the explicit coordinates to the cone set appearing in the
existing definition of sphereAreaD. It proves actual cone injectivity and
set identities, but does not yet prove a change-of-variables measure formula.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Pointwise
namespace SphericalRiesz

variable {n : ℕ}

def equalAreaConeD (z : Fin (n+1+1) → ℝ) : AmbientD (n+1) :=
  z 0 • equalAreaPhiD (Fin.tail z)

def equalAreaConeDomainD : Set (Fin (n+1+1) → ℝ) :=
  {z | z 0 ∈ Ioo (0:ℝ) 1 ∧ Fin.tail z ∈ equalAreaChartDomainD}

theorem equalAreaConeD_continuous : Continuous (equalAreaConeD (n := n)) := by
  unfold equalAreaConeD
  exact (continuous_apply 0).smul (equalAreaPhiD_continuous.comp (by fun_prop))

theorem equalAreaConeD_norm (z : Fin (n+1+1) → ℝ)
    (hz : equalAreaSquaredNormD (Fin.tail z) < 1) :
    ‖equalAreaConeD z‖ = |z 0| := by
  have h : ‖equalAreaPhiD (Fin.tail z)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp (equalAreaPhiD_mem_sphere _ hz)
  simp only [equalAreaConeD,norm_smul,Real.norm_eq_abs,h,mul_one]

theorem equalAreaConeD_injOn : InjOn (equalAreaConeD (n := n)) (equalAreaConeDomainD (n := n)) := by
  intro z hz w hw h
  have hr : z 0 = w 0 := by
    have he := congrArg norm h
    rw [equalAreaConeD_norm z hz.2.1,equalAreaConeD_norm w hw.2.1,
      abs_of_pos hz.1.1,abs_of_pos hw.1.1] at he
    exact he
  have hp : equalAreaPhiD (Fin.tail z) = equalAreaPhiD (Fin.tail w) := by
    change z 0 • equalAreaPhiD (Fin.tail z) = w 0 • equalAreaPhiD (Fin.tail w) at h
    rw [←hr] at h
    exact (smul_right_injective (AmbientD (n+1)) (ne_of_gt hz.1.1)) h
  have ht : Fin.tail z = Fin.tail w := equalAreaPhiD_injOn hz.2 hw.2 hp
  funext i
  exact Fin.cases hr (fun j => congrFun ht j) i

theorem equalAreaConeD_image (s : Set (Fin (n+1) → ℝ)) :
    equalAreaConeD '' {z | z 0 ∈ Ioo (0:ℝ) 1 ∧ Fin.tail z ∈ s} =
      Ioo (0:ℝ) 1 • (equalAreaPhiD '' s) := by
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z 0,hz.1,equalAreaPhiD (Fin.tail z),⟨Fin.tail z,hz.2,rfl⟩,rfl⟩
  · rintro ⟨t,ht,x,⟨p,hp,rfl⟩,rfl⟩
    refine ⟨Fin.cons t p,?_,?_⟩
    · simpa only [Set.mem_ofPred_eq,Fin.cons_zero,Fin.tail_cons] using And.intro ht hp
    · simp only [equalAreaConeD,Fin.cons_zero,Fin.tail_cons]

theorem equalAreaConeD_domain_image :
    (equalAreaConeD (n := n)) '' (equalAreaConeDomainD (n := n)) =
      Ioo (0:ℝ) 1 • ((equalAreaPhiD (n := n)) '' (equalAreaChartDomainD (n := n))) :=
  equalAreaConeD_image equalAreaChartDomainD

/-- The existing actual sphere measure is tied to this very cone set.
Measurability is explicit; no equal-area measure equality is assumed. -/
theorem sphereAreaD_equalAreaChart_cone (s : Set equalAreaChartDomainD)
    (hs : MeasurableSet (equalAreaSphereChartD '' s)) :
    sphereAreaD (n+1) (equalAreaSphereChartD '' s) =
      (n+1+1:ℕ) * (volume : Measure (AmbientD (n+1)))
        (equalAreaConeD '' {z | z 0 ∈ Ioo (0:ℝ) 1 ∧ Fin.tail z ∈ Subtype.val '' s}) := by
  rw [sphereAreaD,Measure.toSphere_apply' _ hs,equalAreaConeD_image]
  have hi : Subtype.val '' (equalAreaSphereChartD '' s) =
      equalAreaPhiD '' (Subtype.val '' s) := by
    rw [image_image,image_image]
    rfl
  rw [hi]
  congr 1
  simp [AmbientD]

end SphericalRiesz
