import Riesz.EqualAreaEuclideanGeometry8
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
Actual Euclidean-coordinate transport of the equal-area hemisphere chart.
The area identity is inherited from the checked cone Jacobian and the actual
Lebesgue-preserving ofLp equivalence. The final weighted integral identity
uses the actual supported cutoff and the actual sphere probability measure.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal SchwartzMap FourierTransform
namespace SphericalRiesz

def equalAreaEuclideanDomain8 : Set (EuclideanSpace ℝ (Fin 8)) :=
  WithLp.ofLp ⁻¹' equalAreaChartDomain

theorem equalAreaEuclideanDomain8_isOpen : IsOpen equalAreaEuclideanDomain8 :=
  equalAreaChartDomain_isOpen.preimage
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 8 => ℝ)).continuous

theorem equalAreaEuclideanDomain8_measurable : MeasurableSet equalAreaEuclideanDomain8 :=
  equalAreaEuclideanDomain8_isOpen.measurableSet

def equalAreaEuclideanSphereChart8 : equalAreaEuclideanDomain8 ↪ Sphere8 where
  toFun u := ⟨equalAreaPhiEuclidean8 u, equalAreaPhi_mem_sphere _ u.property.1⟩
  inj' := by
    intro u v h
    apply Subtype.ext
    apply WithLp.ofLp_injective
    exact equalAreaPhi_injOn u.property v.property (congrArg Subtype.val h)

theorem equalAreaEuclideanSphereChart8_continuous : Continuous equalAreaEuclideanSphereChart8 := by
  apply Continuous.subtype_mk
  exact equalAreaPhiEuclidean8_continuous.comp continuous_subtype_val

theorem equalAreaEuclideanSphereChart8_measurableEmbedding :
    MeasurableEmbedding equalAreaEuclideanSphereChart8 := by
  let : PolishSpace equalAreaEuclideanDomain8 := equalAreaEuclideanDomain8_isOpen.polishSpace
  exact equalAreaEuclideanSphereChart8_continuous.measurableEmbedding
    equalAreaEuclideanSphereChart8.injective

theorem equalAreaEuclideanSphereChart8_image (s : Set equalAreaEuclideanDomain8) :
    equalAreaEuclideanSphereChart8 '' s =
      equalAreaSpherePatch (WithLp.ofLp '' (Subtype.val '' s)) := by
  ext y
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨WithLp.ofLp (u : EuclideanSpace ℝ (Fin 8)),⟨u,⟨u,hu,rfl⟩,rfl⟩,rfl⟩
  · rintro ⟨p,⟨u,⟨z,hz,rfl⟩,rfl⟩,h⟩
    exact ⟨z,hz,Subtype.ext h⟩

theorem equalAreaEuclideanSphereChart8_range :
    range equalAreaEuclideanSphereChart8 = equalAreaHemisphere8 := by
  ext x
  constructor
  · rintro ⟨u,rfl⟩
    exact equalAreaPhi_first_pos _ u.property
  · intro hx
    refine ⟨⟨sphereEqualAreaCoordinates8 x,?_⟩,?_⟩
    · simpa only [equalAreaEuclideanDomain8, mem_preimage, sphereEqualAreaCoordinates8,
        WithLp.ofLp_toLp] using equalAreaInverse8_mem_domain x hx
    · apply Subtype.ext
      exact equalAreaPhiEuclidean8_inverse x hx

theorem equalAreaEuclideanSphereChart8_coordinates (u : equalAreaEuclideanDomain8) :
    sphereEqualAreaCoordinates8 (equalAreaEuclideanSphereChart8 u) = (u : EuclideanSpace ℝ (Fin 8)) := by
  change WithLp.toLp 2 (equalAreaInverse8 (equalAreaPhi (WithLp.ofLp (u : EuclideanSpace ℝ (Fin 8))))) = _
  rw [equalAreaInverse8_phi _ u.property, WithLp.toLp_ofLp]

theorem equalAreaEuclideanSphereChart8_comap_area :
    sphereArea8.comap equalAreaEuclideanSphereChart8 =
      volume.comap (Subtype.val : equalAreaEuclideanDomain8 → EuclideanSpace ℝ (Fin 8)) := by
  ext s hs
  have hS : MeasurableSet (Subtype.val '' s) :=
    (MeasurableEmbedding.subtype_coe equalAreaEuclideanDomain8_measurable).measurableSet_image.2 hs
  have hPi : MeasurableSet (WithLp.ofLp '' (Subtype.val '' s)) :=
    (MeasurableEquiv.toLp 2 (Fin 8 → ℝ)).symm.measurableEmbedding.measurableSet_image.2 hS
  have hdom : WithLp.ofLp '' (Subtype.val '' s) ⊆ equalAreaChartDomain := by
    rintro p ⟨u,⟨z,hz,rfl⟩,rfl⟩
    exact z.property
  rw [equalAreaEuclideanSphereChart8_measurableEmbedding.comap_apply,
    equalAreaEuclideanSphereChart8_image, sphereArea8_equalAreaSpherePatch _ hPi hdom,
    comap_subtype_coe_apply equalAreaEuclideanDomain8_measurable]
  have h := (PiLp.volume_preserving_ofLp (Fin 8)).measure_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 8 → ℝ)).symm.measurableEmbedding
    (WithLp.ofLp '' (Subtype.val '' s))
  rw [preimage_image_eq _ (WithLp.ofLp_injective 2)] at h
  exact h.symm

theorem equalAreaEuclideanSphereChart8_map_area :
    Measure.map equalAreaEuclideanSphereChart8
      (volume.comap (Subtype.val : equalAreaEuclideanDomain8 → EuclideanSpace ℝ (Fin 8))) =
      sphereArea8.restrict equalAreaHemisphere8 := by
  rw [← equalAreaEuclideanSphereChart8_comap_area,
    equalAreaEuclideanSphereChart8_measurableEmbedding.map_comap, equalAreaEuclideanSphereChart8_range]

theorem equalAreaEuclideanSphereChart8_area_integral (g : Sphere8 → ℝ) :
    (∫ x in equalAreaHemisphere8, g x ∂sphereArea8) =
      ∫ u : equalAreaEuclideanDomain8, g (equalAreaEuclideanSphereChart8 u)
        ∂(volume.comap (Subtype.val : equalAreaEuclideanDomain8 → EuclideanSpace ℝ (Fin 8))) := by
  rw [← equalAreaEuclideanSphereChart8_map_area,
    equalAreaEuclideanSphereChart8_measurableEmbedding.integral_map]

theorem equalAreaEuclideanSphereChart8_probability_integral (g : Sphere8 → ℝ) :
    (∫ x in equalAreaHemisphere8, g x ∂sphereProbability8) =
      (sphereArea8.real univ)⁻¹ *
        ∫ u : equalAreaEuclideanDomain8, g (equalAreaEuclideanSphereChart8 u)
          ∂(volume.comap (Subtype.val : equalAreaEuclideanDomain8 → EuclideanSpace ℝ (Fin 8))) := by
  rw [sphereProbability8, Measure.restrict_smul, integral_smul_measure,
    equalAreaEuclideanSphereChart8_area_integral, ENNReal.toReal_inv]
  rfl

theorem sphereChartCutoff8_chart (ρ : ℝ) (hρ : 0 < ρ) (u : equalAreaEuclideanDomain8) :
    sphereChartCutoff8 ρ hρ (equalAreaEuclideanSphereChart8 u) =
      coordinateCutoff ρ hρ (u : EuclideanSpace ℝ (Fin 8)) := by
  have hp : 0 < (equalAreaEuclideanSphereChart8 u : Ambient9) 0 :=
    equalAreaPhi_first_pos _ u.property
  rw [sphereChartCutoff8, ite_eq_left hp, equalAreaEuclideanSphereChart8_coordinates]

theorem coordinateCutoff8_zero_off_domain (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ 1/8)
    (u : EuclideanSpace ℝ (Fin 8)) (hu : u ∉ equalAreaEuclideanDomain8) :
    coordinateCutoff ρ hρ u = 0 := by
  apply coordinateCutoff_zero_of_norm
  by_contra hn
  exact hu (equalAreaEuclidean8_small_norm_domain u ((not_le.mp hn).le.trans hr))

theorem sphereChartCutoff8_probability_integral (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ 1/8)
    (g : EuclideanSpace ℝ (Fin 8) → ℝ) :
    (∫ x, sphereChartCutoff8 ρ hρ x*g (sphereEqualAreaCoordinates8 x) ∂sphereProbability8) =
      (sphereArea8.real univ)⁻¹ * ∫ u, coordinateCutoff ρ hρ u*g u := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := equalAreaHemisphere8) (fun x hx => by
      have hx' : ¬ 0 < (x : Ambient9) 0 := hx
      simp only [sphereChartCutoff8, hx', ite_false, zero_mul]),
    equalAreaEuclideanSphereChart8_probability_integral]
  simp_rw [sphereChartCutoff8_chart, equalAreaEuclideanSphereChart8_coordinates]
  congr 1
  calc
    _ = ∫ u in equalAreaEuclideanDomain8, coordinateCutoff ρ hρ u*g u :=
      integral_subtype_comap equalAreaEuclideanDomain8_measurable
        (fun u : EuclideanSpace ℝ (Fin 8) => coordinateCutoff ρ hρ u*g u)
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun u hu => by rw [coordinateCutoff8_zero_off_domain ρ hρ hr u hu, zero_mul])

end SphericalRiesz
