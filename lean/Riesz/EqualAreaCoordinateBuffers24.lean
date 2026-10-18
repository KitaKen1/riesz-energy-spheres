import Riesz.EqualAreaInverseD
import Riesz.PatchSupportD

/-! Pull actual physical open buffers and compact cores back to coordinates.
The determinant-one E8 coordinate change is an existing linear equivalence;
no new inverse matrix or general manifold atlas is needed. -/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Topology
namespace SphericalRiesz

def equalAreaRotatedSphereChart24 (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) :
    (equalAreaChartDomainD (n := 23)) → (SphereD 24) := fun p => sphereRotationD g (equalAreaSphereChartD p)

def equalAreaRotatedInverse24 (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (q : (SphereD 24)) : Fin 24 → ℝ :=
  equalAreaInverseD (g.symm q)

def equalAreaRotatedHemisphere24 (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) : Set (SphereD 24) :=
  {q | 0 < (g.symm (q : (AmbientD 24))) 0}

def equalAreaCoordinateBuffer24 (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (U : Set (SphereD 24)) :
    Set (Fin 24 → ℝ) :=
  (Subtype.val : equalAreaChartDomainD → Fin 24 → ℝ) ''
    (equalAreaRotatedSphereChart24 g ⁻¹' U)

def leechCoordinateInverse24 : (Fin 24 → ℝ) ≃L[ℝ] (Fin 24 → ℝ) :=
  leechBasis.equivFun.toContinuousLinearEquiv

theorem equalAreaRotatedSphereChart24_continuous (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) :
    Continuous (equalAreaRotatedSphereChart24 g) := by
  apply (sphereRotationD g).continuous.comp
  apply Continuous.subtype_mk
  exact equalAreaPhiD_continuous.comp continuous_subtype_val

theorem equalAreaRotatedInverse24_mem_domain (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (q : (SphereD 24)) (hq : q ∈ equalAreaRotatedHemisphere24 g) :
    equalAreaRotatedInverse24 g q ∈ equalAreaChartDomainD :=
  equalAreaInverseD_mem_domain (sphereRotationD g.symm q) hq

theorem equalAreaRotatedPhi24_inverse8 (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (q : (SphereD 24)) (hq : q ∈ equalAreaRotatedHemisphere24 g) :
    g (equalAreaPhiD (equalAreaRotatedInverse24 g q)) = (q : (AmbientD 24)) := by
  change g (equalAreaPhiD (equalAreaInverseD (sphereRotationD g.symm q))) = (q : (AmbientD 24))
  rw [equalAreaPhiD_inverse8 (sphereRotationD g.symm q) hq]
  exact g.apply_symm_apply q

theorem equalAreaRotatedInverse24_continuousOn (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) :
    ContinuousOn (equalAreaRotatedInverse24 g) (equalAreaRotatedHemisphere24 g) := by
  apply equalAreaInverseD_continuousOn.comp
    (g.symm.continuous.comp continuous_subtype_val).continuousOn
  intro q hq
  exact hq.ne'

theorem equalAreaCoordinateBuffer24_isOpen (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (U : Set (SphereD 24)) (hU : IsOpen U) : IsOpen (equalAreaCoordinateBuffer24 g U) :=
  equalAreaChartDomainD_isOpen.isOpenMap_subtype_val _
    (hU.preimage (equalAreaRotatedSphereChart24_continuous g))

theorem equalAreaCoordinateBuffer24_mem (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (U : Set (SphereD 24)) (u : Fin 24 → ℝ) (hu : u ∈ equalAreaCoordinateBuffer24 g U) :
    u ∈ equalAreaChartDomainD ∧ ∃ q ∈ U, g (equalAreaPhiD u) = (q : (AmbientD 24)) := by
  obtain ⟨p,hp,rfl⟩ := hu
  exact ⟨p.property,equalAreaRotatedSphereChart24 g p,hp,rfl⟩

theorem equalAreaCoordinateCore24_isCompact (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (k : Set (SphereD 24)) (hk : IsCompact k) (hkh : k ⊆ equalAreaRotatedHemisphere24 g) :
    IsCompact (equalAreaRotatedInverse24 g '' k) :=
  hk.image_of_continuousOn ((equalAreaRotatedInverse24_continuousOn g).mono hkh)

theorem equalAreaCoordinateCore24_subset_buffer (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (k U : Set (SphereD 24)) (hkh : k ⊆ equalAreaRotatedHemisphere24 g) (hkU : k ⊆ U) :
    equalAreaRotatedInverse24 g '' k ⊆ equalAreaCoordinateBuffer24 g U := by
  rintro _ ⟨q,hq,rfl⟩
  let p : equalAreaChartDomainD := ⟨equalAreaRotatedInverse24 g q,
    equalAreaRotatedInverse24_mem_domain g q (hkh hq)⟩
  refine ⟨p,?_,rfl⟩
  have he : equalAreaRotatedSphereChart24 g p = q :=
    Subtype.ext (equalAreaRotatedPhi24_inverse8 g q (hkh hq))
  simpa only [mem_preimage,he] using hkU hq

theorem leechMap_coordinateInverse8 (u : Fin 24 → ℝ) : leechMap (leechCoordinateInverse24 u) = u :=
  leechBasis.equivFun.symm_apply_apply u

theorem leechCoordinateInverse24_map (x : Fin 24 → ℝ) : leechCoordinateInverse24 (leechMap x) = x :=
  leechBasis.equivFun.apply_symm_apply x

theorem leechCoordinateCore24_isCompact (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (k : Set (SphereD 24)) (hk : IsCompact k) (hkh : k ⊆ equalAreaRotatedHemisphere24 g) :
    IsCompact (leechCoordinateInverse24 '' (equalAreaRotatedInverse24 g '' k)) :=
  (equalAreaCoordinateCore24_isCompact g k hk hkh).image leechCoordinateInverse24.continuous

theorem leechCoordinateBuffer24_isOpen (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (U : Set (SphereD 24)) (hU : IsOpen U) :
    IsOpen (leechCoordinateInverse24 '' equalAreaCoordinateBuffer24 g U) :=
  leechCoordinateInverse24.toHomeomorph.isOpenMap _ (equalAreaCoordinateBuffer24_isOpen g U hU)

end SphericalRiesz
