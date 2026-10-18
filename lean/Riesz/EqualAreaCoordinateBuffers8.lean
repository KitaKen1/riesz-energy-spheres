import Riesz.EqualAreaInverse8
import Riesz.E8Coordinates

/-! Pull actual physical open buffers and compact cores back to coordinates.
The determinant-one E8 coordinate change is an existing linear equivalence;
no new inverse matrix or general manifold atlas is needed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Metric
open scoped Topology
namespace SphericalRiesz

def equalAreaRotatedSphereChart8 (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) :
    equalAreaChartDomain → Sphere8 := fun p => sphereRotation8 g (equalAreaSphereChart p)

def equalAreaRotatedInverse8 (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) (q : Sphere8) : Fin 8 → ℝ :=
  equalAreaInverse8 (g.symm q)

def equalAreaRotatedHemisphere8 (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) : Set Sphere8 :=
  {q | 0 < (g.symm (q : Ambient9)) 0}

def equalAreaCoordinateBuffer8 (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) (U : Set Sphere8) :
    Set (Fin 8 → ℝ) :=
  (Subtype.val : equalAreaChartDomain → Fin 8 → ℝ) ''
    (equalAreaRotatedSphereChart8 g ⁻¹' U)

def e8CoordinateInverse8 : (Fin 8 → ℝ) ≃L[ℝ] (Fin 8 → ℝ) :=
  e8Basis.equivFun.toContinuousLinearEquiv

theorem equalAreaRotatedSphereChart8_continuous (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) :
    Continuous (equalAreaRotatedSphereChart8 g) := by
  apply (sphereRotation8 g).continuous.comp
  apply Continuous.subtype_mk
  exact equalAreaPhi_continuous.comp continuous_subtype_val

theorem equalAreaRotatedInverse8_mem_domain (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (q : Sphere8) (hq : q ∈ equalAreaRotatedHemisphere8 g) :
    equalAreaRotatedInverse8 g q ∈ equalAreaChartDomain :=
  equalAreaInverse8_mem_domain (sphereRotation8 g.symm q) hq

theorem equalAreaRotatedPhi_inverse8 (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (q : Sphere8) (hq : q ∈ equalAreaRotatedHemisphere8 g) :
    g (equalAreaPhi (equalAreaRotatedInverse8 g q)) = (q : Ambient9) := by
  change g (equalAreaPhi (equalAreaInverse8 (sphereRotation8 g.symm q))) = (q : Ambient9)
  rw [equalAreaPhi_inverse8 (sphereRotation8 g.symm q) hq]
  exact g.apply_symm_apply q

theorem equalAreaRotatedInverse8_continuousOn (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) :
    ContinuousOn (equalAreaRotatedInverse8 g) (equalAreaRotatedHemisphere8 g) := by
  apply equalAreaInverse8_continuousOn.comp
    (g.symm.continuous.comp continuous_subtype_val).continuousOn
  intro q hq
  exact hq.ne'

theorem equalAreaCoordinateBuffer8_isOpen (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (U : Set Sphere8) (hU : IsOpen U) : IsOpen (equalAreaCoordinateBuffer8 g U) :=
  equalAreaChartDomain_isOpen.isOpenMap_subtype_val _
    (hU.preimage (equalAreaRotatedSphereChart8_continuous g))

theorem equalAreaCoordinateBuffer8_mem (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (U : Set Sphere8) (u : Fin 8 → ℝ) (hu : u ∈ equalAreaCoordinateBuffer8 g U) :
    u ∈ equalAreaChartDomain ∧ ∃ q ∈ U, g (equalAreaPhi u) = (q : Ambient9) := by
  obtain ⟨p,hp,rfl⟩ := hu
  exact ⟨p.property,equalAreaRotatedSphereChart8 g p,hp,rfl⟩

theorem equalAreaCoordinateCore8_isCompact (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (k : Set Sphere8) (hk : IsCompact k) (hkh : k ⊆ equalAreaRotatedHemisphere8 g) :
    IsCompact (equalAreaRotatedInverse8 g '' k) :=
  hk.image_of_continuousOn ((equalAreaRotatedInverse8_continuousOn g).mono hkh)

theorem equalAreaCoordinateCore8_subset_buffer (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (k U : Set Sphere8) (hkh : k ⊆ equalAreaRotatedHemisphere8 g) (hkU : k ⊆ U) :
    equalAreaRotatedInverse8 g '' k ⊆ equalAreaCoordinateBuffer8 g U := by
  rintro _ ⟨q,hq,rfl⟩
  let p : equalAreaChartDomain := ⟨equalAreaRotatedInverse8 g q,
    equalAreaRotatedInverse8_mem_domain g q (hkh hq)⟩
  refine ⟨p,?_,rfl⟩
  have he : equalAreaRotatedSphereChart8 g p = q :=
    Subtype.ext (equalAreaRotatedPhi_inverse8 g q (hkh hq))
  simpa only [mem_preimage,he] using hkU hq

theorem e8Map_coordinateInverse8 (u : Fin 8 → ℝ) : e8Map (e8CoordinateInverse8 u) = u :=
  e8Basis.equivFun.symm_apply_apply u

theorem e8CoordinateInverse8_map (x : Fin 8 → ℝ) : e8CoordinateInverse8 (e8Map x) = x :=
  e8Basis.equivFun.apply_symm_apply x

theorem e8CoordinateCore8_isCompact (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (k : Set Sphere8) (hk : IsCompact k) (hkh : k ⊆ equalAreaRotatedHemisphere8 g) :
    IsCompact (e8CoordinateInverse8 '' (equalAreaRotatedInverse8 g '' k)) :=
  (equalAreaCoordinateCore8_isCompact g k hk hkh).image e8CoordinateInverse8.continuous

theorem e8CoordinateBuffer8_isOpen (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (U : Set Sphere8) (hU : IsOpen U) :
    IsOpen (e8CoordinateInverse8 '' equalAreaCoordinateBuffer8 g U) :=
  e8CoordinateInverse8.toHomeomorph.isOpenMap _ (equalAreaCoordinateBuffer8_isOpen g U hU)

end SphericalRiesz
