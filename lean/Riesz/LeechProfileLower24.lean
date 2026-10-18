import Riesz.CompactUniformApproximateIdentity
import Riesz.EqualAreaChartD
import Riesz.EqualAreaInverseD
import Riesz.EqualAreaMeasureD
import Riesz.EqualAreaRescaling24
import Riesz.EqualAreaRescalingLimit24
import Riesz.FiniteCutoffSquarePartition
import Riesz.LeechGaussianContact24
import Riesz.LocalizedSchwartzPSD
import Riesz.PoissonLattice
import Riesz.PoissonSchwartz
import Riesz.SpherePartitionUniformRows8
import Riesz.SupportedChartCutoff8
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! # The universal Gaussian profile lower bound on `S^24` (stage P24-3)

Declaration-level extraction port of the `S⁸` chain behind
`sphereGaussianSharpProfileLower8_of_schwartz_input`: rotated cutoff partitions of the sphere,
partition Schwartz rows and their uniform limits, localized Schwartz positive-definiteness and
the Gaussian comparison. The only lattice input is the Leech theta function (continuity on
`(0, ∞)`) and the Leech sharp Schwartz input, which follows from CKMRV-shaped Leech
certificates. Result: for every sequence of configurations on `S^24` and every scale `α`, the
normalized Gaussian energy is eventually at least `Θ_Λ(α) - ε`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Metric Topology
open scoped ENNReal NNReal Topology Pointwise ContDiff FourierTransform SchwartzMap RealInnerProductSpace
namespace SphericalRiesz
open Boundary

theorem sphereProbabilityD_integral_rotation {d : ℕ} (g : AmbientD d ≃ₗᵢ[ℝ] AmbientD d)
    (f : SphereD d → ℝ) :
    (∫ y, f (sphereRotationD g y) ∂(sphereProbabilityD d)) = ∫ y, f y ∂(sphereProbabilityD d) :=
  (sphereProbabilityD_rotation_preserving g).integral_comp (sphereRotationD g).measurableEmbedding f

def equalAreaPhiEuclidean24 (u : EuclideanSpace ℝ (Fin 24)) : (AmbientD 24) :=
  equalAreaPhiD (WithLp.ofLp u)

def equalAreaEuclideanDerivative24 : EuclideanSpace ℝ (Fin 24) →L[ℝ] (AmbientD 24) :=
  (equalAreaPhiDerivativeD 0).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 24 => ℝ)).toContinuousLinearMap

theorem equalAreaPhiEuclidean24_continuous : Continuous equalAreaPhiEuclidean24 :=
  equalAreaPhiD_continuous.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 24 => ℝ)).continuous

theorem equalAreaEuclideanDerivative24_apply (v : EuclideanSpace ℝ (Fin 24)) :
    equalAreaEuclideanDerivative24 v = (ambientConsD 23) (0,WithLp.ofLp v) :=
  equalAreaPhiDerivative24_zero_apply _

theorem equalAreaEuclideanDerivative24_norm (v : EuclideanSpace ℝ (Fin 24)) :
    ‖equalAreaEuclideanDerivative24 v‖ = ‖v‖ := by
  have h := ambientConsD_norm_sq (0,WithLp.ofLp v)
  rw [← equalAreaEuclideanDerivative24_apply] at h
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add, WithLp.toLp_ofLp] at h
  nlinarith [norm_nonneg (equalAreaEuclideanDerivative24 v), norm_nonneg v]

theorem equalAreaEuclideanDerivative24_opNorm_le : ‖equalAreaEuclideanDerivative24‖ ≤ 1 := by
  apply equalAreaEuclideanDerivative24.opNorm_le_bound zero_le_one
  intro v
  rw [equalAreaEuclideanDerivative24_norm, one_mul]

theorem equalAreaPhiEuclidean24_hasStrictFDerivAt_zero :
    HasStrictFDerivAt equalAreaPhiEuclidean24 equalAreaEuclideanDerivative24 0 := by
  have h0 : equalAreaSquaredNormD (0 : Fin 24 → ℝ) < 1 := by simp [equalAreaSquaredNormD]
  have hs := (equalAreaPhi24_contDiffAt 0 h0).hasStrictFDerivAt'
    (equalAreaPhiD_hasFDerivAt 0 h0) (by simp : (∞ : ℕ∞ω) ≠ 0)
  have he := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 24 => ℝ)).hasStrictFDerivAt
    (x := (0 : EuclideanSpace ℝ (Fin 24)))
  convert! hs.comp 0 he using 1

theorem equalAreaEuclidean24_small_norm_domain (u : EuclideanSpace ℝ (Fin 24))
    (hu : ‖u‖ ≤ 1/8) : WithLp.ofLp u ∈ equalAreaChartDomainD := by
  have hp : ‖WithLp.ofLp u‖ ≤ ‖u‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
    intro i
    exact PiLp.norm_apply_le u i
  refine ⟨equalArea24_small_norm_domain _ (hp.trans hu),?_⟩
  have hi : |(WithLp.ofLp u) 0| ≤ 1/8 := by
    exact (show |(WithLp.ofLp u) 0| ≤ ‖u‖ from PiLp.norm_apply_le u 0).trans hu
  have hpi := Real.pi_gt_three
  exact ⟨by linarith [(abs_le.mp hi).1],by linarith [(abs_le.mp hi).2]⟩

def sphereEqualAreaCoordinates24 (q : (SphereD 24)) : EuclideanSpace ℝ (Fin 24) :=
  WithLp.toLp 2 (equalAreaInverseD q)

theorem equalAreaPhiEuclidean24_inverse (x : (SphereD 24)) (hx : 0 < (x : (AmbientD 24)) 0) :
    equalAreaPhiEuclidean24 (sphereEqualAreaCoordinates24 x) = (x : (AmbientD 24)) := by
  simpa only [equalAreaPhiEuclidean24, sphereEqualAreaCoordinates24, WithLp.ofLp_toLp] using
    equalAreaPhiD_inverse8 x hx

theorem equalAreaPhiEuclidean24_near_isometry (L : ℝ) (hL : 1 < L) :
    ∃ ρ > 0, ρ ≤ 1/8 ∧
      ∀ u ∈ ball (0 : EuclideanSpace ℝ (Fin 24)) ρ,
        ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin 24)) ρ,
          dist (equalAreaPhiEuclidean24 u) (equalAreaPhiEuclidean24 v) ≤ L*dist u v := by
  have hL0 : 0 ≤ L := (by norm_num : (0 : ℝ) ≤ 1).trans hL.le
  have hk : ‖equalAreaEuclideanDerivative24‖₊ < Real.toNNReal L := by
    apply NNReal.coe_lt_coe.mp
    simpa only [coe_nnnorm, Real.coe_toNNReal _ hL0] using
      equalAreaEuclideanDerivative24_opNorm_le.trans_lt hL
  obtain ⟨s,hs,hLip⟩ := equalAreaPhiEuclidean24_hasStrictFDerivAt_zero.exists_lipschitzOnWith_of_nnnorm_lt
    (Real.toNNReal L) hk
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨min δ (1/8),lt_min hδ (by norm_num),min_le_right _ _,?_⟩
  intro u hu v hv
  have hu' := hsub (ball_subset_ball (min_le_left δ (1/8)) hu)
  have hv' := hsub (ball_subset_ball (min_le_left δ (1/8)) hv)
  simpa only [Real.coe_toNNReal _ hL0] using hLip.dist_le_mul u hu' v hv'

section
variable {d : ℕ}

def sphereChartCutoff24 (ρ : ℝ) (hρ : 0 < ρ) (x : (SphereD 24)) : ℝ :=
  if 0 < (x : (AmbientD 24)) 0 then coordinateCutoff ρ hρ (sphereEqualAreaCoordinates24 x) else 0

theorem sphereChartCutoff24_support (ρ : ℝ) (hρ : 0 < ρ) :
    Function.support (sphereChartCutoff24 ρ hρ) =
      {x : (SphereD 24) | 0 < (x : (AmbientD 24)) 0 ∧ ‖sphereEqualAreaCoordinates24 x‖ < ρ} := by
  ext x
  by_cases hx : 0 < (x : (AmbientD 24)) 0
  · simp only [Function.mem_support, sphereChartCutoff24, hx, ite_true,
      Set.mem_ofPred_eq, true_and]
    have h := Set.ext_iff.mp (coordinateCutoff_support (d := 24) ρ hρ)
      (sphereEqualAreaCoordinates24 x)
    simpa only [Function.mem_support, mem_ball, dist_zero_right] using h
  · simp only [Function.mem_support, sphereChartCutoff24, hx, ite_false,
      ne_eq, not_true_eq_false, Set.mem_ofPred_eq, false_and]

end

theorem sphereChartCutoff24_chord_bound (ρ : ℝ) (hρ : 0 < ρ) (L : ℝ)
    (hLip : ∀ u ∈ ball (0 : EuclideanSpace ℝ (Fin 24)) ρ,
      ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin 24)) ρ,
        dist (equalAreaPhiEuclidean24 u) (equalAreaPhiEuclidean24 v) ≤ L*dist u v)
    (x y : (SphereD 24)) (hx : sphereChartCutoff24 ρ hρ x ≠ 0)
    (hy : sphereChartCutoff24 ρ hρ y ≠ 0) :
    dist x y ≤ L*‖sphereEqualAreaCoordinates24 x-sphereEqualAreaCoordinates24 y‖ := by
  have hxs := hx
  change x ∈ Function.support (sphereChartCutoff24 ρ hρ) at hxs
  rw [sphereChartCutoff24_support] at hxs
  have hys := hy
  change y ∈ Function.support (sphereChartCutoff24 ρ hρ) at hys
  rw [sphereChartCutoff24_support] at hys
  have h := hLip _ (by simpa only [mem_ball,dist_zero_right] using hxs.2)
    _ (by simpa only [mem_ball,dist_zero_right] using hys.2)
  rw [equalAreaPhiEuclidean24_inverse x hxs.1, equalAreaPhiEuclidean24_inverse y hys.1] at h
  simpa only [Subtype.dist_eq, dist_eq_norm] using h

def equalAreaEuclideanDomain24 : Set (EuclideanSpace ℝ (Fin 24)) :=
  WithLp.ofLp ⁻¹' equalAreaChartDomainD

theorem equalAreaEuclideanDomain24_isOpen : IsOpen equalAreaEuclideanDomain24 :=
  equalAreaChartDomainD_isOpen.preimage
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 24 => ℝ)).continuous

theorem equalAreaEuclideanDomain24_measurable : MeasurableSet equalAreaEuclideanDomain24 :=
  equalAreaEuclideanDomain24_isOpen.measurableSet

def equalAreaEuclideanSphereChart24 : equalAreaEuclideanDomain24 ↪ (SphereD 24) where
  toFun u := ⟨equalAreaPhiEuclidean24 u, equalAreaPhiD_mem_sphere _ u.property.1⟩
  inj' := by
    intro u v h
    apply Subtype.ext
    apply WithLp.ofLp_injective
    exact equalAreaPhiD_injOn u.property v.property (congrArg Subtype.val h)

theorem equalAreaEuclideanSphereChart24_continuous : Continuous equalAreaEuclideanSphereChart24 := by
  apply Continuous.subtype_mk
  exact equalAreaPhiEuclidean24_continuous.comp continuous_subtype_val

theorem equalAreaEuclideanSphereChart24_measurableEmbedding :
    MeasurableEmbedding equalAreaEuclideanSphereChart24 := by
  let : PolishSpace equalAreaEuclideanDomain24 := equalAreaEuclideanDomain24_isOpen.polishSpace
  exact equalAreaEuclideanSphereChart24_continuous.measurableEmbedding
    equalAreaEuclideanSphereChart24.injective

theorem equalAreaEuclideanSphereChart24_image (s : Set equalAreaEuclideanDomain24) :
    equalAreaEuclideanSphereChart24 '' s =
      equalAreaSpherePatchD (WithLp.ofLp '' (Subtype.val '' s)) := by
  ext y
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨WithLp.ofLp (u : EuclideanSpace ℝ (Fin 24)),⟨u,⟨u,hu,rfl⟩,rfl⟩,rfl⟩
  · rintro ⟨p,⟨u,⟨z,hz,rfl⟩,rfl⟩,h⟩
    exact ⟨z,hz,Subtype.ext h⟩

theorem equalAreaEuclideanSphereChart24_range :
    range equalAreaEuclideanSphereChart24 = equalAreaHemisphereD := by
  ext x
  constructor
  · rintro ⟨u,rfl⟩
    exact equalAreaPhiD_first_pos _ u.property
  · intro hx
    refine ⟨⟨sphereEqualAreaCoordinates24 x,?_⟩,?_⟩
    · simpa only [equalAreaEuclideanDomain24, mem_preimage, sphereEqualAreaCoordinates24,
        WithLp.ofLp_toLp] using equalAreaInverseD_mem_domain x hx
    · apply Subtype.ext
      exact equalAreaPhiEuclidean24_inverse x hx

theorem equalAreaEuclideanSphereChart24_coordinates (u : equalAreaEuclideanDomain24) :
    sphereEqualAreaCoordinates24 (equalAreaEuclideanSphereChart24 u) = (u : EuclideanSpace ℝ (Fin 24)) := by
  change WithLp.toLp 2 (equalAreaInverseD (equalAreaPhiD (WithLp.ofLp (u : EuclideanSpace ℝ (Fin 24))))) = _
  rw [equalAreaInverseD_phi _ u.property, WithLp.toLp_ofLp]

theorem equalAreaEuclideanSphereChart24_comap_area :
    (sphereAreaD 24).comap equalAreaEuclideanSphereChart24 =
      volume.comap (Subtype.val : equalAreaEuclideanDomain24 → EuclideanSpace ℝ (Fin 24)) := by
  ext s hs
  have hS : MeasurableSet (Subtype.val '' s) :=
    (MeasurableEmbedding.subtype_coe equalAreaEuclideanDomain24_measurable).measurableSet_image.2 hs
  have hPi : MeasurableSet (WithLp.ofLp '' (Subtype.val '' s)) :=
    (MeasurableEquiv.toLp 2 (Fin 24 → ℝ)).symm.measurableEmbedding.measurableSet_image.2 hS
  have hdom : WithLp.ofLp '' (Subtype.val '' s) ⊆ equalAreaChartDomainD := by
    rintro p ⟨u,⟨z,hz,rfl⟩,rfl⟩
    exact z.property
  rw [equalAreaEuclideanSphereChart24_measurableEmbedding.comap_apply,
    equalAreaEuclideanSphereChart24_image, sphereAreaD_equalAreaSpherePatch _ hPi hdom,
    comap_subtype_coe_apply equalAreaEuclideanDomain24_measurable]
  have h := (PiLp.volume_preserving_ofLp (Fin 24)).measure_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 24 → ℝ)).symm.measurableEmbedding
    (WithLp.ofLp '' (Subtype.val '' s))
  rw [preimage_image_eq _ (WithLp.ofLp_injective 2)] at h
  exact h.symm

theorem equalAreaEuclideanSphereChart24_map_area :
    Measure.map equalAreaEuclideanSphereChart24
      (volume.comap (Subtype.val : equalAreaEuclideanDomain24 → EuclideanSpace ℝ (Fin 24))) =
      (sphereAreaD 24).restrict equalAreaHemisphereD := by
  rw [← equalAreaEuclideanSphereChart24_comap_area,
    equalAreaEuclideanSphereChart24_measurableEmbedding.map_comap, equalAreaEuclideanSphereChart24_range]

theorem equalAreaEuclideanSphereChart24_area_integral (g : (SphereD 24) → ℝ) :
    (∫ x in equalAreaHemisphereD, g x ∂(sphereAreaD 24)) =
      ∫ u : equalAreaEuclideanDomain24, g (equalAreaEuclideanSphereChart24 u)
        ∂(volume.comap (Subtype.val : equalAreaEuclideanDomain24 → EuclideanSpace ℝ (Fin 24))) := by
  rw [← equalAreaEuclideanSphereChart24_map_area,
    equalAreaEuclideanSphereChart24_measurableEmbedding.integral_map]

theorem equalAreaEuclideanSphereChart24_probability_integral (g : (SphereD 24) → ℝ) :
    (∫ x in equalAreaHemisphereD, g x ∂(sphereProbabilityD 24)) =
      ((sphereAreaD 24).real univ)⁻¹ *
        ∫ u : equalAreaEuclideanDomain24, g (equalAreaEuclideanSphereChart24 u)
          ∂(volume.comap (Subtype.val : equalAreaEuclideanDomain24 → EuclideanSpace ℝ (Fin 24))) := by
  rw [sphereProbabilityD, Measure.restrict_smul, integral_smul_measure,
    equalAreaEuclideanSphereChart24_area_integral, ENNReal.toReal_inv]
  rfl

theorem sphereChartCutoff24_chart (ρ : ℝ) (hρ : 0 < ρ) (u : equalAreaEuclideanDomain24) :
    sphereChartCutoff24 ρ hρ (equalAreaEuclideanSphereChart24 u) =
      coordinateCutoff ρ hρ (u : EuclideanSpace ℝ (Fin 24)) := by
  have hp : 0 < (equalAreaEuclideanSphereChart24 u : (AmbientD 24)) 0 :=
    equalAreaPhiD_first_pos _ u.property
  rw [sphereChartCutoff24, ite_eq_left hp, equalAreaEuclideanSphereChart24_coordinates]

theorem sphereEqualAreaCoordinates24_continuousAt (x : (SphereD 24))
    (hx : 0 < (x : (AmbientD 24)) 0) : ContinuousAt sphereEqualAreaCoordinates24 x := by
  have hs : IsOpen {q : (AmbientD 24) | q 0 ≠ 0} := isOpen_ne.preimage (by fun_prop)
  have hi := equalAreaInverseD_continuousOn.continuousAt (hs.mem_nhds hx.ne')
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 24 => ℝ)).symm.continuousAt.comp
    (hi.comp continuous_subtype_val.continuousAt)

theorem sphereChartCutoff24_continuousAt_positive (ρ : ℝ) (hρ : 0 < ρ)
    (x : (SphereD 24)) (hx : 0 < (x : (AmbientD 24)) 0) :
    ContinuousAt (sphereChartCutoff24 ρ hρ) x := by
  have he : ∀ᶠ y : (SphereD 24) in 𝓝 x, 0 < (y : (AmbientD 24)) 0 :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds hx
  apply ((coordinateCutoff_continuous ρ hρ).continuousAt.comp
    (sphereEqualAreaCoordinates24_continuousAt x hx)).congr_of_eventuallyEq
  filter_upwards [he] with y hy
  simp only [sphereChartCutoff24, ite_eq_left hy, Function.comp_apply]

def northPole24 : (SphereD 24) :=
  ⟨EuclideanSpace.single (0 : Fin 25) (1 : ℝ), by simp⟩

theorem sphere24_coordinate_difference_le_dist (q p : (SphereD 24)) (i : Fin 25) :
    |(q : (AmbientD 24)) i-(p : (AmbientD 24)) i| ≤ dist q p := by
  change |(q : (AmbientD 24)) i-(p : (AmbientD 24)) i| ≤ ‖(q : (AmbientD 24))-(p : (AmbientD 24))‖
  simpa only [PiLp.sub_apply, Real.norm_eq_abs] using
    (PiLp.norm_apply_le ((q : (AmbientD 24))-(p : (AmbientD 24))) i)

theorem northPole24_ball_first_pos (q : (SphereD 24)) (r : ℝ)
    (hr : r ≤ 1/2) (hq : q ∈ ball northPole24 r) :
    1/2 < (q : (AmbientD 24)) 0 := by
  have h := (sphere24_coordinate_difference_le_dist q northPole24 0).trans_lt hq
  have hcoord : |(q : (AmbientD 24)) 0-1| < r := by
    simpa [northPole24] using h
  linarith [(abs_lt.mp hcoord).1]

section
variable {d : ℕ}

theorem sphereEqualAreaCoordinates24_northPole : sphereEqualAreaCoordinates24 northPole24 = 0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [sphereEqualAreaCoordinates24, equalAreaInverseD, northPole24]
  · simp [sphereEqualAreaCoordinates24, equalAreaInverseD, northPole24]

theorem sphereChartCutoff24_northPole (ρ : ℝ) (hρ : 0 < ρ) :
    sphereChartCutoff24 ρ hρ northPole24 = 1 := by
  have hp : 0 < (northPole24 : (AmbientD 24)) 0 := by simp [northPole24]
  rw [sphereChartCutoff24, if_pos hp, sphereEqualAreaCoordinates24_northPole, coordinateCutoff_zero]

end

theorem sphereChartCutoff24_support_height_of_chord_bound (ρ : ℝ) (hρ : 0 < ρ)
    (hr : ρ ≤ 1/8)
    (hB : ∀ x y : (SphereD 24), sphereChartCutoff24 ρ hρ x ≠ 0 →
      sphereChartCutoff24 ρ hρ y ≠ 0 →
      dist x y ≤ 2*‖sphereEqualAreaCoordinates24 x-sphereEqualAreaCoordinates24 y‖)
    (x : (SphereD 24)) (hx : sphereChartCutoff24 ρ hρ x ≠ 0) :
    1/2 < (x : (AmbientD 24)) 0 := by
  have hxs : x ∈ Function.support (sphereChartCutoff24 ρ hρ) := hx
  rw [sphereChartCutoff24_support] at hxs
  have hp : sphereChartCutoff24 ρ hρ northPole24 ≠ 0 := by
    rw [sphereChartCutoff24_northPole]
    exact one_ne_zero
  have hd := hB x northPole24 hx hp
  rw [sphereEqualAreaCoordinates24_northPole, sub_zero] at hd
  apply northPole24_ball_first_pos x (1/2) le_rfl
  change dist x northPole24 < 1/2
  linarith [hxs.2]

theorem sphereChartCutoff24_continuous_of_chord_bound (ρ : ℝ) (hρ : 0 < ρ)
    (hr : ρ ≤ 1/8)
    (hB : ∀ x y : (SphereD 24), sphereChartCutoff24 ρ hρ x ≠ 0 →
      sphereChartCutoff24 ρ hρ y ≠ 0 →
      dist x y ≤ 2*‖sphereEqualAreaCoordinates24 x-sphereEqualAreaCoordinates24 y‖) :
    Continuous (sphereChartCutoff24 ρ hρ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : 0 < (x : (AmbientD 24)) 0
  · exact sphereChartCutoff24_continuousAt_positive ρ hρ x hx
  · have hx0 : (x : (AmbientD 24)) 0 < (1/2 : ℝ) :=
      lt_of_le_of_lt (not_lt.mp hx) (by norm_num)
    have ho : IsOpen {y : (SphereD 24) | (y : (AmbientD 24)) 0 < (1/2 : ℝ)} :=
      isOpen_lt (by fun_prop) continuous_const
    have he : ∀ᶠ y : (SphereD 24) in 𝓝 x, (y : (AmbientD 24)) 0 < 1/2 := ho.mem_nhds hx0
    apply (continuousAt_const : ContinuousAt (fun _ : (SphereD 24) => (0 : ℝ)) x).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    by_contra hn
    have hh := sphereChartCutoff24_support_height_of_chord_bound ρ hρ hr hB y hn
    linarith

def rotatedSphereChartCutoff24 (ρ : ℝ) (hρ : 0 < ρ)
    (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (x : (SphereD 24)) : ℝ :=
  sphereChartCutoff24 ρ hρ (sphereRotationD g.symm x)

def rotatedSphereEqualAreaCoordinates24 (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (x : (SphereD 24)) : EuclideanSpace ℝ (Fin 24) :=
  sphereEqualAreaCoordinates24 (sphereRotationD g.symm x)

section
variable {d : ℕ}

theorem sphereChartCutoff24_nonneg (ρ : ℝ) (hρ : 0 < ρ) (x : (SphereD 24)) :
    0 ≤ sphereChartCutoff24 ρ hρ x := by
  unfold sphereChartCutoff24
  split_ifs
  · exact coordinateCutoff_nonneg ρ hρ _
  · exact le_rfl

end

theorem rotatedSphereChartCutoff24_nonneg (ρ : ℝ) (hρ : 0 < ρ)
    (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (x : (SphereD 24)) :
    0 ≤ rotatedSphereChartCutoff24 ρ hρ g x := sphereChartCutoff24_nonneg ρ hρ _

theorem rotatedSphereChartCutoff24_center (ρ : ℝ) (hρ : 0 < ρ)
    (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) :
    rotatedSphereChartCutoff24 ρ hρ g (sphereRotationD g northPole24) = 1 := by
  unfold rotatedSphereChartCutoff24
  rw [show sphereRotationD g.symm (sphereRotationD g northPole24) = northPole24 from
    (sphereRotationD g).left_inv northPole24, sphereChartCutoff24_northPole]

theorem rotatedSphereChartCutoff24_continuous (ρ : ℝ) (hρ : 0 < ρ)
    (hc : Continuous (sphereChartCutoff24 ρ hρ)) (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) :
    Continuous (rotatedSphereChartCutoff24 ρ hρ g) :=
  hc.comp (sphereRotationD g.symm).continuous

theorem sphereRotation24_transitive (x y : (SphereD 24)) :
    ∃ g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24), sphereRotationD g x = y := by
  refine ⟨Submodule.reflection (ℝ ∙ ((x : (AmbientD 24)) - y))ᗮ, ?_⟩
  apply Subtype.ext
  apply Submodule.reflection_sub
  exact (mem_sphere_zero_iff_norm.1 x.property).trans
    (mem_sphere_zero_iff_norm.1 y.property).symm

theorem sphere24_finite_rotated_cutoff_cover (ρ : ℝ) (hρ : 0 < ρ)
    (hc : Continuous (sphereChartCutoff24 ρ hρ)) :
    ∃ K : ℕ, ∃ g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24),
      ∀ x : (SphereD 24), ∃ i, 0 < rotatedSphereChartCutoff24 ρ hρ (g i) x := by
  classical
  let : CompactSpace (SphereD 24) := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : (AmbientD 24)) 1)
  have ht : ∀ p : (SphereD 24), ∃ g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24),
      sphereRotationD g northPole24 = p := fun p => sphereRotation24_transitive northPole24 p
  choose g hg using ht
  let U : (SphereD 24) → Set (SphereD 24) := fun p => {x | 0 < rotatedSphereChartCutoff24 ρ hρ (g p) x}
  have hU : ∀ p, IsOpen (U p) := fun p =>
    isOpen_lt continuous_const (rotatedSphereChartCutoff24_continuous ρ hρ hc (g p))
  have hcenter (p : (SphereD 24)) : p ∈ U p := by
    change 0 < rotatedSphereChartCutoff24 ρ hρ (g p) p
    have he := rotatedSphereChartCutoff24_center ρ hρ (g p)
    rw [hg p] at he
    rw [he]
    exact zero_lt_one
  obtain ⟨t,ht⟩ := (isCompact_univ : IsCompact (univ : Set (SphereD 24))).elim_finite_subcover
    U hU (fun p _ => mem_iUnion.mpr ⟨p,hcenter p⟩)
  let gs : Fin t.card → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24) := fun i => g (t.equivFin.symm i).val
  refine ⟨t.card,gs,?_⟩
  intro x
  obtain ⟨p,hp⟩ := mem_iUnion.mp (ht (mem_univ x))
  obtain ⟨hpt,hxp⟩ := mem_iUnion.mp hp
  change 0 < rotatedSphereChartCutoff24 ρ hρ (g p) x at hxp
  refine ⟨t.equivFin ⟨p,hpt⟩,?_⟩
  simpa only [gs, Equiv.symm_apply_apply] using hxp

def sphereFiniteCutoffMass24 {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) : (SphereD 24) → ℝ :=
  finiteCutoffSquareMass (fun i => rotatedSphereChartCutoff24 ρ hρ (g i))

def sphereFiniteCutoffWeight24 {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) : Fin K → (SphereD 24) → ℝ :=
  finiteCutoffSquarePartition (fun i => rotatedSphereChartCutoff24 ρ hρ (g i))

theorem sphereFiniteCutoffMass24_pos {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (hcover : ∀ x : (SphereD 24), ∃ i, 0 < rotatedSphereChartCutoff24 ρ hρ (g i) x) (x : (SphereD 24)) :
    0 < sphereFiniteCutoffMass24 ρ hρ g x :=
  finiteCutoffSquareMass_pos_of_cover _ hcover x

theorem sphereFiniteCutoffWeight24_nonneg {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (i : Fin K) (x : (SphereD 24)) :
    0 ≤ sphereFiniteCutoffWeight24 ρ hρ g i x :=
  finiteCutoffSquarePartition_nonneg _ (fun j y => rotatedSphereChartCutoff24_nonneg ρ hρ (g j) y) i x

theorem sphereFiniteCutoffWeight24_le_one {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x) (i : Fin K) (x : (SphereD 24)) :
    sphereFiniteCutoffWeight24 ρ hρ g i x ≤ 1 :=
  finiteCutoffSquarePartition_le_one _ hpos i x

theorem sphereFiniteCutoffWeight24_continuous {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (hc : Continuous (sphereChartCutoff24 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x) (i : Fin K) :
    Continuous (sphereFiniteCutoffWeight24 ρ hρ g i) :=
  finiteCutoffSquarePartition_continuous _ (fun j => rotatedSphereChartCutoff24_continuous ρ hρ hc (g j))
    hpos i

theorem sphereFiniteCutoffWeight24_sum_square {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x) (x : (SphereD 24)) :
    (∑ i, (sphereFiniteCutoffWeight24 ρ hρ g i x)^2) = 1 :=
  finiteCutoffSquarePartition_sum_square _ hpos x

theorem sphereFiniteCutoffWeight24_ne_zero_iff {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x) (i : Fin K) (x : (SphereD 24)) :
    sphereFiniteCutoffWeight24 ρ hρ g i x ≠ 0 ↔ rotatedSphereChartCutoff24 ρ hρ (g i) x ≠ 0 :=
  finiteCutoffSquarePartition_ne_zero_iff _ hpos i x

theorem sphereFiniteCutoffWeight24_correlation_le_one {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x) (x y : (SphereD 24)) :
    (∑ i, sphereFiniteCutoffWeight24 ρ hρ g i x*sphereFiniteCutoffWeight24 ρ hρ g i y) ≤ 1 :=
  finiteCutoffSquarePartition_correlation_le_one _ hpos x y

theorem sphereFiniteCutoffWeight24_chord_bound {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x) (L : ℝ)
    (hB : ∀ x y : (SphereD 24), sphereChartCutoff24 ρ hρ x ≠ 0 →
      sphereChartCutoff24 ρ hρ y ≠ 0 →
      dist x y ≤ L*‖sphereEqualAreaCoordinates24 x-sphereEqualAreaCoordinates24 y‖)
    (i : Fin K) (x y : (SphereD 24))
    (hx : sphereFiniteCutoffWeight24 ρ hρ g i x ≠ 0)
    (hy : sphereFiniteCutoffWeight24 ρ hρ g i y ≠ 0) :
    dist x y ≤ L*‖rotatedSphereEqualAreaCoordinates24 (g i) x-
      rotatedSphereEqualAreaCoordinates24 (g i) y‖ := by
  have hx' := (sphereFiniteCutoffWeight24_ne_zero_iff ρ hρ g hpos i x).mp hx
  have hy' := (sphereFiniteCutoffWeight24_ne_zero_iff ρ hρ g hpos i y).mp hy
  have h := hB (sphereRotationD (g i).symm x) (sphereRotationD (g i).symm y) hx' hy'
  rw [sphereRotationD_dist] at h
  exact h

theorem sphere24_exists_finite_cutoff_square_partition (L : ℝ) (hL : 1 < L) :
    ∃ ρ > 0, ∃ hρ : 0 < ρ, ρ ≤ 1/8 ∧
      ∃ K : ℕ, ∃ g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24),
        Continuous (sphereChartCutoff24 ρ hρ) ∧
        (∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x) ∧
        (∀ i, Continuous (sphereFiniteCutoffWeight24 ρ hρ g i)) ∧
        (∀ i x, 0 ≤ sphereFiniteCutoffWeight24 ρ hρ g i x ∧ sphereFiniteCutoffWeight24 ρ hρ g i x ≤ 1) ∧
        (∀ x, (∑ i, (sphereFiniteCutoffWeight24 ρ hρ g i x)^2) = 1) ∧
        (∀ i x y, sphereFiniteCutoffWeight24 ρ hρ g i x ≠ 0 →
          sphereFiniteCutoffWeight24 ρ hρ g i y ≠ 0 →
          dist x y ≤ L*‖rotatedSphereEqualAreaCoordinates24 (g i) x-
            rotatedSphereEqualAreaCoordinates24 (g i) y‖) := by
  have hL0 : 1 < min L 2 := lt_min hL (by norm_num)
  obtain ⟨ρ,hρ,hr,hLip⟩ := equalAreaPhiEuclidean24_near_isometry (min L 2) hL0
  have hB : ∀ x y : (SphereD 24), sphereChartCutoff24 ρ hρ x ≠ 0 →
      sphereChartCutoff24 ρ hρ y ≠ 0 →
      dist x y ≤ min L 2*‖sphereEqualAreaCoordinates24 x-sphereEqualAreaCoordinates24 y‖ :=
    fun x y hx hy => sphereChartCutoff24_chord_bound ρ hρ (min L 2) hLip x y hx hy
  have hB2 : ∀ x y : (SphereD 24), sphereChartCutoff24 ρ hρ x ≠ 0 →
      sphereChartCutoff24 ρ hρ y ≠ 0 →
      dist x y ≤ 2*‖sphereEqualAreaCoordinates24 x-sphereEqualAreaCoordinates24 y‖ :=
    fun x y hx hy => (hB x y hx hy).trans
      (mul_le_mul_of_nonneg_right (min_le_right L 2) (norm_nonneg _))
  have hBL : ∀ x y : (SphereD 24), sphereChartCutoff24 ρ hρ x ≠ 0 →
      sphereChartCutoff24 ρ hρ y ≠ 0 →
      dist x y ≤ L*‖sphereEqualAreaCoordinates24 x-sphereEqualAreaCoordinates24 y‖ :=
    fun x y hx hy => (hB x y hx hy).trans
      (mul_le_mul_of_nonneg_right (min_le_left L 2) (norm_nonneg _))
  have hc := sphereChartCutoff24_continuous_of_chord_bound ρ hρ hr hB2
  obtain ⟨K,g,hcover⟩ := sphere24_finite_rotated_cutoff_cover ρ hρ hc
  have hpos := sphereFiniteCutoffMass24_pos ρ hρ g hcover
  refine ⟨ρ,hρ,hρ,hr,K,g,hc,hpos,?_,?_,?_,?_⟩
  · exact sphereFiniteCutoffWeight24_continuous ρ hρ g hc hpos
  · exact fun i x => ⟨sphereFiniteCutoffWeight24_nonneg ρ hρ g i x,
      sphereFiniteCutoffWeight24_le_one ρ hρ g hpos i x⟩
  · exact sphereFiniteCutoffWeight24_sum_square ρ hρ g hpos
  · exact sphereFiniteCutoffWeight24_chord_bound ρ hρ g hpos L hBL

def sphereGaussianKernel24 (t : ℝ) (x y : (SphereD 24)) : ℝ :=
  Real.exp (-(t*(dist x y)^2))

theorem sphereGaussianKernel24_nonneg (t : ℝ) (x y : (SphereD 24)) :
    0 ≤ sphereGaussianKernel24 t x y := (Real.exp_pos _).le

@[simp]
theorem sphereGaussianKernel24_self (t : ℝ) (x : (SphereD 24)) :
    sphereGaussianKernel24 t x x = 1 := by simp [sphereGaussianKernel24]

def sphereGaussianScale24 (N : ℕ) (α : ℝ) : ℝ :=
  Real.pi*α*((N:ℝ)/(sphereAreaD 24).real univ)^(1/12:ℝ)

def sphereGaussianFullScaled24 {N : ℕ} (α : ℝ) (X : (ConfigurationD 24) N) : ℝ :=
  (∑ i : Fin N, ∑ j : Fin N,
    sphereGaussianKernel24 (sphereGaussianScale24 N α) (X i) (X j))/(N:ℝ)

/-- This is the missing actual sphere localization output, not a supplied axiom. -/

def SphereGaussianSharpProfileLower24 : Prop :=
  ∀ (N : ℕ → ℕ), Tendsto N atTop atTop → (∀ k, 0 < N k) →
    ∀ (X : ∀ k, (ConfigurationD 24) (N k)) (α : ℝ), 0 < α →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
        leechGaussianThetaReal24 α-ε ≤ sphereGaussianFullScaled24 α (X k)

def spherePartitionSchwartzComponent24 {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) (a : ℝ) (i : Fin K)
    (x y : (SphereD 24)) : ℝ :=
  sphereFiniteCutoffWeight24 ρ hρ g i x*sphereFiniteCutoffWeight24 ρ hρ g i y*
    (f (a • (rotatedSphereEqualAreaCoordinates24 (g i) x-
      rotatedSphereEqualAreaCoordinates24 (g i) y))).re

def spherePartitionSchwartzKernel24 {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) (a : ℝ) (x y : (SphereD 24)) : ℝ :=
  ∑ i, spherePartitionSchwartzComponent24 ρ hρ g f a i x y

def spherePartitionSchwartzRow24 {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) (a : ℝ) (x : (SphereD 24)) : ℝ :=
  ∫ y, spherePartitionSchwartzKernel24 ρ hρ g f a x y ∂(sphereProbabilityD 24)

theorem spherePartitionSchwartzRow24_sum_lower {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (hN : 0 < N) (X : Fin N → (SphereD 24))
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) (a H δ : ℝ)
    (hrow : ∀ x, |(N : ℝ)*spherePartitionSchwartzRow24 ρ hρ g f a x-H| < δ) :
    H-δ ≤ ∑ p, spherePartitionSchwartzRow24 ρ hρ g f a (X p) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hp (p : Fin N) : H-δ ≤ (N : ℝ)*spherePartitionSchwartzRow24 ρ hρ g f a (X p) := by
    have h := (abs_lt.mp (hrow (X p))).1
    linarith
  have hs := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset (Fin N))) => hp p)
  have hs' : (N : ℝ)*(H-δ) ≤ (N : ℝ)*(∑ p, spherePartitionSchwartzRow24 ρ hρ g f a (X p)) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum] using hs
  nlinarith

def spherePartitionDensityScale24 (N : ℕ) : ℝ :=
  ((N : ℝ)/(sphereAreaD 24).real univ)^((24 : ℝ)⁻¹)

theorem spherePartitionDensityScale24_pos {N : ℕ} (hN : 0 < N) :
    0 < spherePartitionDensityScale24 N := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hA : 0 < (sphereAreaD 24).real univ := sphereAreaD_univ_pos 24
  exact Real.rpow_pos_of_pos (div_pos hNR hA) _

theorem spherePartitionDensityScale24_pow (N : ℕ) :
    (spherePartitionDensityScale24 N)^24 = (N : ℝ)/(sphereAreaD 24).real univ := by
  apply Real.rpow_inv_natCast_pow
  · have hA : 0 < (sphereAreaD 24).real univ := sphereAreaD_univ_pos 24
    exact div_nonneg (Nat.cast_nonneg _) hA.le
  · decide

theorem spherePartitionDensityScale24_mass (N : ℕ) :
    (spherePartitionDensityScale24 N)^24*(sphereAreaD 24).real univ = (N : ℝ) := by
  have hA : (sphereAreaD 24).real univ ≠ 0 := (sphereAreaD_univ_pos 24).ne'
  rw [spherePartitionDensityScale24_pow, div_mul_cancel₀ _ hA]

theorem spherePartitionDensityScale24_tendsto :
    Tendsto spherePartitionDensityScale24 atTop atTop := by
  have hA : 0 < (sphereAreaD 24).real univ := sphereAreaD_univ_pos 24
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hdiv : Tendsto (fun N : ℕ => (N : ℝ)/(sphereAreaD 24).real univ) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [hN.eventually (eventually_ge_atTop (b*(sphereAreaD 24).real univ))] with N hN
    exact (le_div_iff₀ hA).mpr hN
  exact (tendsto_rpow_atTop (by positivity : 0 < (24 : ℝ)⁻¹)).comp hdiv

def sphereFiniteCutoffProfile24 {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (i : Fin K)
    (u : EuclideanSpace ℝ (Fin 24)) : ℝ := by
  classical
  exact if hu : u ∈ equalAreaEuclideanDomain24 then
    sphereFiniteCutoffWeight24 ρ hρ g i
      (sphereRotationD (g i) (equalAreaEuclideanSphereChart24 ⟨u,hu⟩)) else 0

theorem rotatedSphereChartCutoff24_apply (ρ : ℝ) (hρ : 0 < ρ)
    (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (x : (SphereD 24)) :
    rotatedSphereChartCutoff24 ρ hρ g (sphereRotationD g x) = sphereChartCutoff24 ρ hρ x := by
  unfold rotatedSphereChartCutoff24
  rw [show sphereRotationD g.symm (sphereRotationD g x) = x from (sphereRotationD g).left_inv x]

theorem sphereFiniteCutoffProfile24_zero_off_domain {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (i : Fin K) (u : EuclideanSpace ℝ (Fin 24))
    (hu : u ∉ equalAreaEuclideanDomain24) : sphereFiniteCutoffProfile24 ρ hρ g i u = 0 := by
  rw [sphereFiniteCutoffProfile24, dite_eq_right hu]

theorem sphereFiniteCutoffProfile24_zero_of_norm {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (i : Fin K) (u : EuclideanSpace ℝ (Fin 24))
    (hu : ρ ≤ ‖u‖) : sphereFiniteCutoffProfile24 ρ hρ g i u = 0 := by
  by_cases hd : u ∈ equalAreaEuclideanDomain24
  · rw [sphereFiniteCutoffProfile24, dite_eq_left hd]
    simp only [sphereFiniteCutoffWeight24, finiteCutoffSquarePartition,
      rotatedSphereChartCutoff24_apply, sphereChartCutoff24_chart,
      coordinateCutoff_zero_of_norm ρ hρ u hu, zero_div]
  · exact sphereFiniteCutoffProfile24_zero_off_domain ρ hρ g i u hd

theorem sphereFiniteCutoffProfile24_compactSupport {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (i : Fin K) :
    HasCompactSupport (sphereFiniteCutoffProfile24 ρ hρ g i) := by
  apply (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 24)) ρ).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ isClosed_closedBall
  intro u hu
  have hn : ‖u‖ < ρ := by
    by_contra h
    exact hu (sphereFiniteCutoffProfile24_zero_of_norm ρ hρ g i u (not_lt.mp h))
  simpa only [mem_closedBall, dist_zero_right] using hn.le

theorem sphereFiniteCutoffProfile24_chart {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (i : Fin K) (u : equalAreaEuclideanDomain24) :
    sphereFiniteCutoffProfile24 ρ hρ g i (u : EuclideanSpace ℝ (Fin 24)) =
      sphereFiniteCutoffWeight24 ρ hρ g i (sphereRotationD (g i) (equalAreaEuclideanSphereChart24 u)) := by
  rw [sphereFiniteCutoffProfile24, dite_eq_left u.property]

theorem sphereFiniteCutoffProfile24_continuous {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ 1/8)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (hc : Continuous (sphereChartCutoff24 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x) (i : Fin K) :
    Continuous (sphereFiniteCutoffProfile24 ρ hρ g i) := by
  have hD : ContinuousOn (sphereFiniteCutoffProfile24 ρ hρ g i) equalAreaEuclideanDomain24 := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have he : equalAreaEuclideanDomain24.domRestrict (sphereFiniteCutoffProfile24 ρ hρ g i) =
        fun u => sphereFiniteCutoffWeight24 ρ hρ g i
          (sphereRotationD (g i) (equalAreaEuclideanSphereChart24 u)) := by
      funext u
      exact sphereFiniteCutoffProfile24_chart ρ hρ g i u
    rw [he]
    exact (sphereFiniteCutoffWeight24_continuous ρ hρ g hc hpos i).comp
      ((sphereRotationD (g i)).continuous.comp equalAreaEuclideanSphereChart24_continuous)
  apply continuous_iff_continuousAt.mpr
  intro u
  by_cases hu : u ∈ equalAreaEuclideanDomain24
  · exact hD.continuousAt (equalAreaEuclideanDomain24_isOpen.mem_nhds hu)
  · have hn : ρ < ‖u‖ := by
      by_contra h
      exact hu (equalAreaEuclidean24_small_norm_domain u ((not_lt.mp h).trans hr))
    have he : ∀ᶠ v : EuclideanSpace ℝ (Fin 24) in 𝓝 u, ρ < ‖v‖ :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds hn
    apply (continuousAt_const : ContinuousAt (fun _ : EuclideanSpace ℝ (Fin 24) => (0 : ℝ)) u).congr_of_eventuallyEq
    filter_upwards [he] with v hv
    exact sphereFiniteCutoffProfile24_zero_of_norm ρ hρ g i v hv.le

theorem sphereEqualAreaCoordinates24_measurable : Measurable sphereEqualAreaCoordinates24 := by
  unfold sphereEqualAreaCoordinates24 equalAreaInverseD
  fun_prop

theorem rotatedSphereEqualAreaCoordinates24_measurable (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) :
    Measurable (rotatedSphereEqualAreaCoordinates24 g) :=
  sphereEqualAreaCoordinates24_measurable.comp (sphereRotationD g.symm).measurable

theorem spherePartitionSchwartzComponent24_measurable {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (hc : Continuous (sphereChartCutoff24 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) (a : ℝ) (i : Fin K) :
    Measurable (fun p : (SphereD 24) × (SphereD 24) => spherePartitionSchwartzComponent24 ρ hρ g f a i p.1 p.2) := by
  have hw := (sphereFiniteCutoffWeight24_continuous ρ hρ g hc hpos i).measurable
  have hu := rotatedSphereEqualAreaCoordinates24_measurable (g i)
  have hfu : Continuous (fun z : EuclideanSpace ℝ (Fin 24) => (f (a • z)).re) := by fun_prop
  exact ((hw.comp measurable_fst).mul (hw.comp measurable_snd)).mul
    (hfu.measurable.comp ((hu.comp measurable_fst).sub (hu.comp measurable_snd)))

theorem spherePartitionSchwartzComponent24_norm_le {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) (a : ℝ) (i : Fin K) (x y : (SphereD 24)) :
    ‖spherePartitionSchwartzComponent24 ρ hρ g f a i x y‖ ≤ SchwartzMap.seminorm ℝ 0 0 f := by
  have hx0 := sphereFiniteCutoffWeight24_nonneg ρ hρ g i x
  have hy0 := sphereFiniteCutoffWeight24_nonneg ρ hρ g i y
  have hx1 := sphereFiniteCutoffWeight24_le_one ρ hρ g hpos i x
  have hy1 := sphereFiniteCutoffWeight24_le_one ρ hρ g hpos i y
  have hw : sphereFiniteCutoffWeight24 ρ hρ g i x*sphereFiniteCutoffWeight24 ρ hρ g i y ≤ 1 := by
    simpa using mul_le_mul hx1 hy1 hy0 zero_le_one
  have hf : |(f (a • (rotatedSphereEqualAreaCoordinates24 (g i) x-
      rotatedSphereEqualAreaCoordinates24 (g i) y))).re| ≤ SchwartzMap.seminorm ℝ 0 0 f :=
    (Complex.abs_re_le_norm _).trans (SchwartzMap.norm_le_seminorm ℝ f _)
  simp only [spherePartitionSchwartzComponent24, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg hx0, abs_of_nonneg hy0]
  simpa using mul_le_mul hw hf (abs_nonneg _) zero_le_one

theorem spherePartitionSchwartzComponent24_row_integrable {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (hc : Continuous (sphereChartCutoff24 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) (a : ℝ) (i : Fin K) (x : (SphereD 24)) :
    Integrable (spherePartitionSchwartzComponent24 ρ hρ g f a i x) (sphereProbabilityD 24) := by
  apply (integrable_const (SchwartzMap.seminorm ℝ 0 0 f)).mono'
    ((spherePartitionSchwartzComponent24_measurable ρ hρ g hc hpos f a i).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact Eventually.of_forall (spherePartitionSchwartzComponent24_norm_le ρ hρ g hpos f a i x)

theorem spherePartitionSchwartzRow24_eq_sum {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (hc : Continuous (sphereChartCutoff24 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) (a : ℝ) (x : (SphereD 24)) :
    spherePartitionSchwartzRow24 ρ hρ g f a x =
      ∑ i, ∫ y, spherePartitionSchwartzComponent24 ρ hρ g f a i x y ∂(sphereProbabilityD 24) := by
  classical
  exact integral_finsetSum _ fun i _ =>
    spherePartitionSchwartzComponent24_row_integrable ρ hρ g hc hpos f a i x

theorem sphereFiniteCutoffProfile24_coordinates_on_hemisphere {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (i : Fin K) (x : (SphereD 24))
    (hx : sphereRotationD (g i).symm x ∈ equalAreaHemisphereD) :
    sphereFiniteCutoffProfile24 ρ hρ g i (rotatedSphereEqualAreaCoordinates24 (g i) x) =
      sphereFiniteCutoffWeight24 ρ hρ g i x := by
  have hd : sphereEqualAreaCoordinates24 (sphereRotationD (g i).symm x) ∈ equalAreaEuclideanDomain24 := by
    simpa only [equalAreaEuclideanDomain24, mem_preimage, sphereEqualAreaCoordinates24,
      WithLp.ofLp_toLp] using equalAreaInverseD_mem_domain _ hx
  have hchart : equalAreaEuclideanSphereChart24
      ⟨sphereEqualAreaCoordinates24 (sphereRotationD (g i).symm x),hd⟩ =
      sphereRotationD (g i).symm x := by
    apply Subtype.ext
    exact equalAreaPhiEuclidean24_inverse _ hx
  rw [rotatedSphereEqualAreaCoordinates24, sphereFiniteCutoffProfile24, dite_eq_left hd, hchart]
  rw [show sphereRotationD (g i) (sphereRotationD (g i).symm x) = x from
    (sphereRotationD (g i)).right_inv x]

theorem sphereFiniteCutoffWeight24_times_profile_eq_square {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x) (i : Fin K) (x : (SphereD 24)) :
    sphereFiniteCutoffWeight24 ρ hρ g i x*
      sphereFiniteCutoffProfile24 ρ hρ g i (rotatedSphereEqualAreaCoordinates24 (g i) x) =
      (sphereFiniteCutoffWeight24 ρ hρ g i x)^2 := by
  by_cases hx : sphereFiniteCutoffWeight24 ρ hρ g i x = 0
  · rw [hx, zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  · have hr := (sphereFiniteCutoffWeight24_ne_zero_iff ρ hρ g hpos i x).mp hx
    change sphereRotationD (g i).symm x ∈ Function.support (sphereChartCutoff24 ρ hρ) at hr
    rw [sphereChartCutoff24_support] at hr
    rw [sphereFiniteCutoffProfile24_coordinates_on_hemisphere ρ hρ g i x hr.1, pow_two]

theorem sphereProbability24_integral_rotation (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (f : (SphereD 24) → ℝ) :
    (∫ y, f (sphereRotationD g y) ∂(sphereProbabilityD 24)) = ∫ y, f y ∂(sphereProbabilityD 24) :=
  (sphereProbabilityD_rotation_preserving g).integral_comp
    (sphereRotationD g).measurableEmbedding f

/-- A reflection in the orthogonal complement of24 x-y moves x to y. -/

theorem rotatedSphereEqualAreaCoordinates24_apply (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (x : (SphereD 24)) :
    rotatedSphereEqualAreaCoordinates24 g (sphereRotationD g x) = sphereEqualAreaCoordinates24 x := by
  unfold rotatedSphereEqualAreaCoordinates24
  rw [show sphereRotationD g.symm (sphereRotationD g x) = x from (sphereRotationD g).left_inv x]

theorem sphereFiniteCutoffWeight24_rotated_zero_off_hemisphere {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x) (i : Fin K) (x : (SphereD 24))
    (hx : x ∉ equalAreaHemisphereD) :
    sphereFiniteCutoffWeight24 ρ hρ g i (sphereRotationD (g i) x) = 0 := by
  by_contra hn
  have h := (sphereFiniteCutoffWeight24_ne_zero_iff ρ hρ g hpos i _).mp hn
  rw [rotatedSphereChartCutoff24_apply] at h
  have hx' : ¬ 0 < (x : (AmbientD 24)) 0 := hx
  exact h (by simp only [sphereChartCutoff24, hx', ite_false])

theorem sphereFiniteCutoffWeight24_probability_integral {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x) (i : Fin K)
    (F : EuclideanSpace ℝ (Fin 24) → ℝ) :
    (∫ x, sphereFiniteCutoffWeight24 ρ hρ g i x*F (rotatedSphereEqualAreaCoordinates24 (g i) x)
      ∂(sphereProbabilityD 24)) = ((sphereAreaD 24).real univ)⁻¹ *
      ∫ u, sphereFiniteCutoffProfile24 ρ hρ g i u*F u := by
  rw [← sphereProbabilityD_integral_rotation (g i)
    (fun x => sphereFiniteCutoffWeight24 ρ hρ g i x*F (rotatedSphereEqualAreaCoordinates24 (g i) x))]
  simp_rw [rotatedSphereEqualAreaCoordinates24_apply]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := equalAreaHemisphereD)
    (fun x hx => by rw [sphereFiniteCutoffWeight24_rotated_zero_off_hemisphere ρ hρ g hpos i x hx,
      zero_mul]), equalAreaEuclideanSphereChart24_probability_integral]
  simp_rw [equalAreaEuclideanSphereChart24_coordinates, ← sphereFiniteCutoffProfile24_chart]
  congr 1
  calc
    _ = ∫ u in equalAreaEuclideanDomain24, sphereFiniteCutoffProfile24 ρ hρ g i u*F u :=
      integral_subtype_comap equalAreaEuclideanDomain24_measurable
        (fun u => sphereFiniteCutoffProfile24 ρ hρ g i u*F u)
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun u hu => by rw [sphereFiniteCutoffProfile24_zero_off_domain ρ hρ g i u hu, zero_mul])

theorem spherePartitionSchwartzComponent24_row_transport {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) (a : ℝ) (i : Fin K) (x : (SphereD 24)) :
    (∫ y, spherePartitionSchwartzComponent24 ρ hρ g f a i x y ∂(sphereProbabilityD 24)) =
      sphereFiniteCutoffWeight24 ρ hρ g i x*((sphereAreaD 24).real univ)⁻¹*
        ∫ v, sphereFiniteCutoffProfile24 ρ hρ g i v*
          (f (a • (rotatedSphereEqualAreaCoordinates24 (g i) x-v))).re := by
  simp only [spherePartitionSchwartzComponent24, mul_assoc]
  rw [integral_const_mul, sphereFiniteCutoffWeight24_probability_integral ρ hρ g hpos i
    (fun v => (f (a • (rotatedSphereEqualAreaCoordinates24 (g i) x-v))).re)]

theorem spherePartitionSchwartzComponent24_scaled_row {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) {a : ℝ} (ha : 0 < a) (i : Fin K) (x : (SphereD 24)) :
    a^24*(sphereAreaD 24).real univ*
      (∫ y, spherePartitionSchwartzComponent24 ρ hρ g f a i x y ∂(sphereProbabilityD 24)) =
      sphereFiniteCutoffWeight24 ρ hρ g i x*
        compactApproximateRow (sphereFiniteCutoffProfile24 ρ hρ g i) (fun h => (f h).re) a
          (rotatedSphereEqualAreaCoordinates24 (g i) x) := by
  have hA : (sphereAreaD 24).real univ ≠ 0 := (sphereAreaD_univ_pos 24).ne'
  rw [spherePartitionSchwartzComponent24_row_transport ρ hρ g hpos,
    compactDilationRow_eq_approximateRow (sphereFiniteCutoffProfile24 ρ hρ g i)
      (fun h => (f h).re) ha (rotatedSphereEqualAreaCoordinates24 (g i) x)]
  have ha8 : a^24 ≠ 0 := pow_ne_zero _ ha.ne'
  field_simp

theorem spherePartitionSchwartzComponent24_scaled_row_error {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) {a : ℝ} (ha : 0 < a) (i : Fin K) (x : (SphereD 24)) :
    a^24*(sphereAreaD 24).real univ*
      (∫ y, spherePartitionSchwartzComponent24 ρ hρ g f a i x y ∂(sphereProbabilityD 24))-
      (sphereFiniteCutoffWeight24 ρ hρ g i x)^2*((𝓕 f) 0).re =
      sphereFiniteCutoffWeight24 ρ hρ g i x*
        (compactApproximateRow (sphereFiniteCutoffProfile24 ρ hρ g i) (fun h => (f h).re) a
          (rotatedSphereEqualAreaCoordinates24 (g i) x)-
          sphereFiniteCutoffProfile24 ρ hρ g i (rotatedSphereEqualAreaCoordinates24 (g i) x)*((𝓕 f) 0).re) := by
  rw [spherePartitionSchwartzComponent24_scaled_row ρ hρ g hpos f ha,
    mul_sub, ← mul_assoc, sphereFiniteCutoffWeight24_times_profile_eq_square ρ hρ g hpos]

theorem spherePartitionSchwartzRow24_uniform {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ 1/8)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (hc : Continuous (sphereChartCutoff24 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) {a : ℕ → ℝ}
    (ha : Tendsto a atTop atTop) (ha0 : ∀ n, 0 < a n) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x,
      |(a n)^24*(sphereAreaD 24).real univ*spherePartitionSchwartzRow24 ρ hρ g f (a n) x-((𝓕 f) 0).re| < ε := by
  classical
  intro ε hε
  let δ : ℝ := ε/((K : ℝ)+1)
  have hK : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hsmall : ∀ᶠ n in atTop, ∀ i : Fin K, ∀ u,
      |compactApproximateRow (sphereFiniteCutoffProfile24 ρ hρ g i) (fun h => (f h).re) (a n) u-
        sphereFiniteCutoffProfile24 ρ hρ g i u*((𝓕 f) 0).re| < δ := by
    apply eventually_all.mpr
    intro i
    exact compactSchwartzApproximateRow_uniform _
      (sphereFiniteCutoffProfile24_continuous ρ hρ hr g hc hpos i)
      (sphereFiniteCutoffProfile24_compactSupport ρ hρ g i) f ha δ hδ
  filter_upwards [hsmall] with n hn
  intro x
  have heq : (a n)^24*(sphereAreaD 24).real univ*spherePartitionSchwartzRow24 ρ hρ g f (a n) x-((𝓕 f) 0).re =
      ∑ i, ((a n)^24*(sphereAreaD 24).real univ*
        (∫ y, spherePartitionSchwartzComponent24 ρ hρ g f (a n) i x y ∂(sphereProbabilityD 24))-
        (sphereFiniteCutoffWeight24 ρ hρ g i x)^2*((𝓕 f) 0).re) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      sphereFiniteCutoffWeight24_sum_square ρ hρ g hpos, one_mul,
      spherePartitionSchwartzRow24_eq_sum ρ hρ g hc hpos]
  rw [heq]
  calc
    _ ≤ ∑ i, |(a n)^24*(sphereAreaD 24).real univ*
        (∫ y, spherePartitionSchwartzComponent24 ρ hρ g f (a n) i x y ∂(sphereProbabilityD 24))-
        (sphereFiniteCutoffWeight24 ρ hρ g i x)^2*((𝓕 f) 0).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin K, δ := by
      apply Finset.sum_le_sum
      intro i _
      rw [spherePartitionSchwartzComponent24_scaled_row_error ρ hρ g hpos f (ha0 n), abs_mul,
        abs_of_nonneg (sphereFiniteCutoffWeight24_nonneg ρ hρ g i x)]
      calc
        _ ≤ sphereFiniteCutoffWeight24 ρ hρ g i x*δ :=
          mul_le_mul_of_nonneg_left (hn i _).le (sphereFiniteCutoffWeight24_nonneg ρ hρ g i x)
        _ ≤ δ := by
          simpa using mul_le_mul_of_nonneg_right (sphereFiniteCutoffWeight24_le_one ρ hρ g hpos i x) hδ.le
    _ = (K : ℝ)*δ := by simp [Finset.sum_const, nsmul_eq_mul]
    _ < ε := by
      dsimp [δ]
      rw [← mul_div_assoc, div_lt_iff₀ (show 0 < (K : ℝ)+1 by positivity)]
      nlinarith

theorem spherePartitionSchwartzRow24_density_uniform {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (hr : ρ ≤ 1/8) (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (hc : Continuous (sphereChartCutoff24 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) {N : ℕ → ℕ}
    (hN : Tendsto N atTop atTop) (hN0 : ∀ n, 0 < N n) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x,
      |(N n : ℝ)*spherePartitionSchwartzRow24 ρ hρ g f (spherePartitionDensityScale24 (N n)) x-
        ((𝓕 f) 0).re| < ε := by
  have h := spherePartitionSchwartzRow24_uniform ρ hρ hr g hc hpos f
    (spherePartitionDensityScale24_tendsto.comp hN) (fun n => spherePartitionDensityScale24_pos (hN0 n))
  simpa only [Function.comp_apply, spherePartitionDensityScale24_mass] using h

def spherePartitionSchwartzBackground24 {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) (a : ℝ) : ℝ :=
  ∫ x, ∫ y, spherePartitionSchwartzKernel24 ρ hρ g f a x y
    ∂(sphereProbabilityD 24) ∂(sphereProbabilityD 24)

theorem sphereProbability24_mass : (sphereProbabilityD 24) univ = 1 := measure_univ

theorem spherePartitionSchwartzComponent24_product_integrable {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (hc : Continuous (sphereChartCutoff24 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) (a : ℝ) (i : Fin K) :
    Integrable (fun p : (SphereD 24) × (SphereD 24) => spherePartitionSchwartzComponent24 ρ hρ g f a i p.1 p.2)
      ((sphereProbabilityD 24).prod (sphereProbabilityD 24)) := by
  apply (integrable_const (SchwartzMap.seminorm ℝ 0 0 f)).mono'
    (spherePartitionSchwartzComponent24_measurable ρ hρ g hc hpos f a i).aestronglyMeasurable
  exact Eventually.of_forall fun p => spherePartitionSchwartzComponent24_norm_le ρ hρ g hpos f a i p.1 p.2

theorem spherePartitionSchwartzKernel24_product_integrable {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (hc : Continuous (sphereChartCutoff24 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) (a : ℝ) :
    Integrable (fun p : (SphereD 24) × (SphereD 24) => spherePartitionSchwartzKernel24 ρ hρ g f a p.1 p.2)
      ((sphereProbabilityD 24).prod (sphereProbabilityD 24)) := by
  classical
  exact integrable_finsetSum _ fun i _ =>
    spherePartitionSchwartzComponent24_product_integrable ρ hρ g hc hpos f a i

theorem spherePartitionSchwartzRow24_integrable {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (hc : Continuous (sphereChartCutoff24 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) (a : ℝ) :
    Integrable (spherePartitionSchwartzRow24 ρ hρ g f a) (sphereProbabilityD 24) :=
  (spherePartitionSchwartzKernel24_product_integrable ρ hρ g hc hpos f a).integral_prod_left

theorem spherePartitionSchwartzBackground24_scaled_tendsto {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (hr : ρ ≤ 1/8) (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (hc : Continuous (sphereChartCutoff24 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) {a : ℕ → ℝ}
    (ha : Tendsto a atTop atTop) (ha0 : ∀ n, 0 < a n) :
    Tendsto (fun n => (a n)^24*(sphereAreaD 24).real univ*spherePartitionSchwartzBackground24 ρ hρ g f (a n))
      atTop (𝓝 ((𝓕 f) 0).re) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he := spherePartitionSchwartzRow24_uniform ρ hρ hr g hc hpos f ha ha0 (ε/2) (by positivity)
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨N,fun n hn => ?_⟩
  have hi := spherePartitionSchwartzRow24_integrable ρ hρ g hc hpos f (a n)
  have hdiff : (a n)^24*(sphereAreaD 24).real univ*spherePartitionSchwartzBackground24 ρ hρ g f (a n)-((𝓕 f) 0).re =
      ∫ x, (a n)^24*(sphereAreaD 24).real univ*spherePartitionSchwartzRow24 ρ hρ g f (a n) x-((𝓕 f) 0).re ∂(sphereProbabilityD 24) := by
    rw [integral_sub (hi.const_mul _) (integrable_const _), integral_const_mul]
    simp [spherePartitionSchwartzBackground24, spherePartitionSchwartzRow24]
  rw [Real.dist_eq, hdiff]
  have hb := norm_integral_le_of_norm_le_const (μ := (sphereProbabilityD 24))
    (f := fun x => (a n)^24*(sphereAreaD 24).real univ*spherePartitionSchwartzRow24 ρ hρ g f (a n) x-((𝓕 f) 0).re)
    (C := ε/2)
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using (hN n hn x).le)
  have hb' : |∫ x, (a n)^24*(sphereAreaD 24).real univ*spherePartitionSchwartzRow24 ρ hρ g f (a n) x-((𝓕 f) 0).re ∂(sphereProbabilityD 24)| ≤ ε/2 := by
    simpa only [Real.norm_eq_abs, measureReal_def, sphereProbability24_mass, ENNReal.toReal_one, mul_one] using hb
  exact hb'.trans_lt (by linarith)

theorem spherePartitionSchwartzBackground24_density_tendsto {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (hr : ρ ≤ 1/8) (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (hc : Continuous (sphereChartCutoff24 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) {N : ℕ → ℕ}
    (hN : Tendsto N atTop atTop) (hN0 : ∀ n, 0 < N n) :
    Tendsto (fun n => (N n : ℝ)*
      spherePartitionSchwartzBackground24 ρ hρ g f (spherePartitionDensityScale24 (N n)))
      atTop (𝓝 ((𝓕 f) 0).re) := by
  have h := spherePartitionSchwartzBackground24_scaled_tendsto ρ hρ hr g hc hpos f
    (spherePartitionDensityScale24_tendsto.comp hN) (fun n => spherePartitionDensityScale24_pos (hN0 n))
  simpa only [Function.comp_apply, spherePartitionDensityScale24_mass] using h

theorem sphereChartGaussian24_comparison (L α a : ℝ) (hL : 0 ≤ L) (hα : 0 ≤ α)
    (x y : (SphereD 24)) (z : EuclideanSpace ℝ (Fin 24)) (hd : dist x y ≤ L*‖z‖) :
    Real.exp (-(Real.pi*(α*L^2)*‖a • z‖^2)) ≤
      sphereGaussianKernel24 (Real.pi*α*a^2) x y := by
  have hd2 : (dist x y)^2 ≤ (L*‖z‖)^2 := pow_le_pow_left₀ dist_nonneg hd 2
  have hm := mul_le_mul_of_nonneg_left hd2
    (mul_nonneg (mul_nonneg Real.pi_pos.le hα) (sq_nonneg a))
  apply Real.exp_le_exp.mpr
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, sphereGaussianKernel24] at *
  nlinarith

theorem spherePartitionSchwartzComponent24_gaussian_le {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (L α a : ℝ) (hL : 0 ≤ L) (hα : 0 ≤ α)
    (hLip : ∀ i x y, sphereFiniteCutoffWeight24 ρ hρ g i x ≠ 0 →
      sphereFiniteCutoffWeight24 ρ hρ g i y ≠ 0 →
      dist x y ≤ L*‖rotatedSphereEqualAreaCoordinates24 (g i) x-
        rotatedSphereEqualAreaCoordinates24 (g i) y‖)
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ))
    (hminor : ∀ z, (f z).re ≤ Real.exp (-(Real.pi*(α*L^2)*‖z‖^2)))
    (i : Fin K) (x y : (SphereD 24)) :
    spherePartitionSchwartzComponent24 ρ hρ g f a i x y ≤
      sphereFiniteCutoffWeight24 ρ hρ g i x*sphereFiniteCutoffWeight24 ρ hρ g i y*
        sphereGaussianKernel24 (Real.pi*α*a^2) x y := by
  by_cases hx : sphereFiniteCutoffWeight24 ρ hρ g i x = 0
  · simp [spherePartitionSchwartzComponent24, hx]
  by_cases hy : sphereFiniteCutoffWeight24 ρ hρ g i y = 0
  · simp [spherePartitionSchwartzComponent24, hy]
  have h := (hminor _).trans (sphereChartGaussian24_comparison L α a hL hα x y _ (hLip i x y hx hy))
  exact mul_le_mul_of_nonneg_left h
    (mul_nonneg (sphereFiniteCutoffWeight24_nonneg ρ hρ g i x)
      (sphereFiniteCutoffWeight24_nonneg ρ hρ g i y))

theorem spherePartitionSchwartzKernel24_gaussian_le {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x)
    (L α a : ℝ) (hL : 0 ≤ L) (hα : 0 ≤ α)
    (hLip : ∀ i x y, sphereFiniteCutoffWeight24 ρ hρ g i x ≠ 0 →
      sphereFiniteCutoffWeight24 ρ hρ g i y ≠ 0 →
      dist x y ≤ L*‖rotatedSphereEqualAreaCoordinates24 (g i) x-
        rotatedSphereEqualAreaCoordinates24 (g i) y‖)
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ))
    (hminor : ∀ z, (f z).re ≤ Real.exp (-(Real.pi*(α*L^2)*‖z‖^2))) (x y : (SphereD 24)) :
    spherePartitionSchwartzKernel24 ρ hρ g f a x y ≤ sphereGaussianKernel24 (Real.pi*α*a^2) x y := by
  classical
  calc
    _ ≤ ∑ i, sphereFiniteCutoffWeight24 ρ hρ g i x*sphereFiniteCutoffWeight24 ρ hρ g i y*
        sphereGaussianKernel24 (Real.pi*α*a^2) x y :=
      Finset.sum_le_sum fun i _ => spherePartitionSchwartzComponent24_gaussian_le ρ hρ g L α a hL hα hLip f hminor i x y
    _ = (∑ i, sphereFiniteCutoffWeight24 ρ hρ g i x*sphereFiniteCutoffWeight24 ρ hρ g i y)*
        sphereGaussianKernel24 (Real.pi*α*a^2) x y := (Finset.sum_mul _ _ _).symm
    _ ≤ 1*sphereGaussianKernel24 (Real.pi*α*a^2) x y :=
      mul_le_mul_of_nonneg_right (sphereFiniteCutoffWeight24_correlation_le_one ρ hρ g hpos x y)
        (sphereGaussianKernel24_nonneg _ _ _)
    _ = _ := one_mul _

theorem spherePartitionSchwartzKernel24_diagonal {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) (a : ℝ) (x : (SphereD 24)) :
    spherePartitionSchwartzKernel24 ρ hρ g f a x x = (f 0).re := by
  classical
  simp only [spherePartitionSchwartzKernel24, spherePartitionSchwartzComponent24,
    sub_self, smul_zero, ← pow_two]
  rw [← Finset.sum_mul, sphereFiniteCutoffWeight24_sum_square ρ hρ g hpos, one_mul]

theorem spherePartitionSchwartzKernel24_diagonal_corrected_sum_le {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x) (X : Fin N → (SphereD 24))
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) (a t : ℝ)
    (hminor : ∀ x y, spherePartitionSchwartzKernel24 ρ hρ g f a x y ≤ sphereGaussianKernel24 t x y) :
    (∑ p, ∑ q, spherePartitionSchwartzKernel24 ρ hρ g f a (X p) (X q))+
      (N : ℝ)*(1-(f 0).re) ≤ ∑ p, ∑ q, sphereGaussianKernel24 t (X p) (X q) := by
  classical
  have hpq (p q : Fin N) : spherePartitionSchwartzKernel24 ρ hρ g f a (X p) (X q)+
      (if p=q then 1-(f 0).re else 0) ≤ sphereGaussianKernel24 t (X p) (X q) := by
    by_cases h : p=q
    · subst q
      simp only [spherePartitionSchwartzKernel24_diagonal ρ hρ g hpos,
        sphereGaussianKernel24_self, ↓reduceIte]
      linarith
    · simpa only [ite_eq_right h, add_zero] using hminor (X p) (X q)
  have hs := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset (Fin N))) =>
    Finset.sum_le_sum (fun q (_ : q ∈ (Finset.univ : Finset (Fin N))) => hpq p q))
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hs

def spherePartitionSchwartzDefect24 {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (X : Fin N → (SphereD 24))
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) (a : ℝ) : ℝ :=
  (∑ p, ∑ q, spherePartitionSchwartzKernel24 ρ hρ g f a (X p) (X q))-
    2*(N : ℝ)*(∑ p, spherePartitionSchwartzRow24 ρ hρ g f a (X p))+
    (N : ℝ)^2*spherePartitionSchwartzBackground24 ρ hρ g f a

theorem sphereCutoff24_integrable (χ : (SphereD 24) → ℝ) (hχmeas : Measurable χ)
    (hχnonneg : ∀ x, 0 ≤ χ x) (hχle : ∀ x, χ x ≤ 1)
    (μ : Measure (SphereD 24)) [IsFiniteMeasure μ] : Integrable χ μ := by
  apply (integrable_const (1 : ℝ)).mono' hχmeas.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (hχnonneg x)]
  exact hχle x

def spherePartitionSchwartzComponentDefect24 {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (X : Fin N → (SphereD 24))
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) (a : ℝ) (i : Fin K) : ℝ :=
  (∑ p, ∑ q, spherePartitionSchwartzComponent24 ρ hρ g f a i (X p) (X q))-
    2*(N : ℝ)*(∑ p, ∫ y, spherePartitionSchwartzComponent24 ρ hρ g f a i (X p) y ∂(sphereProbabilityD 24))+
    (N : ℝ)^2*(∫ x, ∫ y, spherePartitionSchwartzComponent24 ρ hρ g f a i x y
      ∂(sphereProbabilityD 24) ∂(sphereProbabilityD 24))

def spherePointMeasure24 {N : ℕ} (X : Fin N → (SphereD 24)) : Measure (SphereD 24) :=
  ∑ i, Measure.dirac (X i)

instance spherePointMeasure24_finite {N : ℕ} (X : Fin N → (SphereD 24)) :
    IsFiniteMeasure (spherePointMeasure24 X) := by
  unfold spherePointMeasure24
  infer_instance

theorem spherePointMeasure24_integral {N : ℕ} (X : Fin N → (SphereD 24))
    (g : (SphereD 24) → ℝ) : (∫ x, g x ∂spherePointMeasure24 X) = ∑ i, g (X i) := by
  unfold spherePointMeasure24
  rw [integral_finsetSum_measure (fun i _ => integrable_dirac (by simp))]
  simp only [integral_dirac]

theorem spherePartitionSchwartzComponentDefect24_eq_localized {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (X : Fin N → (SphereD 24))
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) (a : ℝ) (i : Fin K) :
    spherePartitionSchwartzComponentDefect24 ρ hρ g X f a i =
      localizedSchwartzDefect f a N (sphereFiniteCutoffWeight24 ρ hρ g i)
        (rotatedSphereEqualAreaCoordinates24 (g i)) (spherePointMeasure24 X) (sphereProbabilityD 24) := by
  unfold spherePartitionSchwartzComponentDefect24 localizedSchwartzDefect localizedSchwartzPair
    spherePartitionSchwartzComponent24
  simp only [spherePointMeasure24_integral]

theorem spherePartitionSchwartzComponentDefect24_nonneg {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (hc : Continuous (sphereChartCutoff24 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x) (X : Fin N → (SphereD 24))
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ))
    (hFnonneg : ∀ z, 0 ≤ ((𝓕 f) z).re) (hFreal : ∀ z, ((𝓕 f) z).im = 0)
    (a : ℝ) (i : Fin K) :
    0 ≤ spherePartitionSchwartzComponentDefect24 ρ hρ g X f a i := by
  have hmeas := (sphereFiniteCutoffWeight24_continuous ρ hρ g hc hpos i).measurable
  have hn := sphereFiniteCutoffWeight24_nonneg ρ hρ g i
  have hle := sphereFiniteCutoffWeight24_le_one ρ hρ g hpos i
  rw [spherePartitionSchwartzComponentDefect24_eq_localized]
  exact localizedSchwartzDefect_nonneg f hFnonneg hFreal a N _ _ _ _ hmeas hn
    (rotatedSphereEqualAreaCoordinates24_measurable (g i))
    (sphereCutoff24_integrable _ hmeas hn hle _)
    (sphereCutoff24_integrable _ hmeas hn hle _)

theorem spherePartitionSchwartzKernel24_point_sum {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (X : Fin N → (SphereD 24))
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) (a : ℝ) :
    (∑ p, ∑ q, spherePartitionSchwartzKernel24 ρ hρ g f a (X p) (X q)) =
      ∑ i, ∑ p, ∑ q, spherePartitionSchwartzComponent24 ρ hρ g f a i (X p) (X q) := by
  classical
  unfold spherePartitionSchwartzKernel24
  calc
    _ = ∑ p, ∑ i, ∑ q, spherePartitionSchwartzComponent24 ρ hρ g f a i (X p) (X q) := by
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem spherePartitionSchwartzRow24_point_sum {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (hc : Continuous (sphereChartCutoff24 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x) (X : Fin N → (SphereD 24))
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) (a : ℝ) :
    (∑ p, spherePartitionSchwartzRow24 ρ hρ g f a (X p)) =
      ∑ i, ∑ p, ∫ y, spherePartitionSchwartzComponent24 ρ hρ g f a i (X p) y ∂(sphereProbabilityD 24) := by
  classical
  simp_rw [spherePartitionSchwartzRow24_eq_sum ρ hρ g hc hpos]
  exact Finset.sum_comm

theorem spherePartitionSchwartzBackground24_eq_sum {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (hc : Continuous (sphereChartCutoff24 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) (a : ℝ) :
    spherePartitionSchwartzBackground24 ρ hρ g f a =
      ∑ i, ∫ x, ∫ y, spherePartitionSchwartzComponent24 ρ hρ g f a i x y ∂(sphereProbabilityD 24) ∂(sphereProbabilityD 24) := by
  classical
  change (∫ x, spherePartitionSchwartzRow24 ρ hρ g f a x ∂(sphereProbabilityD 24)) = _
  simp_rw [spherePartitionSchwartzRow24_eq_sum ρ hρ g hc hpos]
  exact integral_finsetSum _ fun i _ =>
    (spherePartitionSchwartzComponent24_product_integrable ρ hρ g hc hpos f a i).integral_prod_left

theorem spherePartitionSchwartzDefect24_eq_sum {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (hc : Continuous (sphereChartCutoff24 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x) (X : Fin N → (SphereD 24))
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ)) (a : ℝ) :
    spherePartitionSchwartzDefect24 ρ hρ g X f a =
      ∑ i, spherePartitionSchwartzComponentDefect24 ρ hρ g X f a i := by
  classical
  rw [spherePartitionSchwartzDefect24, spherePartitionSchwartzKernel24_point_sum,
    spherePartitionSchwartzRow24_point_sum ρ hρ g hc hpos,
    spherePartitionSchwartzBackground24_eq_sum ρ hρ g hc hpos]
  simp only [spherePartitionSchwartzComponentDefect24, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum]

theorem spherePartitionSchwartzDefect24_nonneg {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (hc : Continuous (sphereChartCutoff24 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x) (X : Fin N → (SphereD 24))
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ))
    (hFnonneg : ∀ z, 0 ≤ ((𝓕 f) z).re) (hFreal : ∀ z, ((𝓕 f) z).im = 0) (a : ℝ) :
    0 ≤ spherePartitionSchwartzDefect24 ρ hρ g X f a := by
  rw [spherePartitionSchwartzDefect24_eq_sum ρ hρ g hc hpos]
  exact Finset.sum_nonneg fun i _ =>
    spherePartitionSchwartzComponentDefect24_nonneg ρ hρ g hc hpos X f hFnonneg hFreal a i

theorem spherePartitionSchwartzKernel24_normalized_lower {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (hc : Continuous (sphereChartCutoff24 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x) (hN : 0 < N) (X : Fin N → (SphereD 24))
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ))
    (hFnonneg : ∀ z, 0 ≤ ((𝓕 f) z).re) (hFreal : ∀ z, ((𝓕 f) z).im = 0) (a : ℝ) :
    2*(∑ p, spherePartitionSchwartzRow24 ρ hρ g f a (X p))-
      (N : ℝ)*spherePartitionSchwartzBackground24 ρ hρ g f a ≤
      (∑ p, ∑ q, spherePartitionSchwartzKernel24 ρ hρ g f a (X p) (X q))/(N : ℝ) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hd := spherePartitionSchwartzDefect24_nonneg ρ hρ g hc hpos X f hFnonneg hFreal a
  unfold spherePartitionSchwartzDefect24 at hd
  apply (le_div_iff₀ hNR).mpr
  nlinarith

theorem spherePartitionGaussian24_normalized_lower {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (hc : Continuous (sphereChartCutoff24 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x) (hN : 0 < N) (X : Fin N → (SphereD 24))
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ))
    (hFnonneg : ∀ z, 0 ≤ ((𝓕 f) z).re) (hFreal : ∀ z, ((𝓕 f) z).im = 0) (a t : ℝ)
    (hminor : ∀ x y, spherePartitionSchwartzKernel24 ρ hρ g f a x y ≤ sphereGaussianKernel24 t x y) :
    2*(∑ p, spherePartitionSchwartzRow24 ρ hρ g f a (X p))-
      (N : ℝ)*spherePartitionSchwartzBackground24 ρ hρ g f a+1-(f 0).re ≤
      (∑ p, ∑ q, sphereGaussianKernel24 t (X p) (X q))/(N : ℝ) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hs := spherePartitionSchwartzKernel24_diagonal_corrected_sum_le ρ hρ g hpos X f a t hminor
  have hd := spherePartitionSchwartzKernel24_normalized_lower ρ hρ g hc hpos hN X f hFnonneg hFreal a
  have hs' := div_le_div_of_nonneg_right hs hNR.le
  have he : ((∑ p, ∑ q, spherePartitionSchwartzKernel24 ρ hρ g f a (X p) (X q))+
      (N : ℝ)*(1-(f 0).re))/(N : ℝ) =
      (∑ p, ∑ q, spherePartitionSchwartzKernel24 ρ hρ g f a (X p) (X q))/(N : ℝ)+1-(f 0).re := by
    field_simp [hNR.ne']
    <;> ring
  rw [he] at hs'
  linarith

theorem sphereGaussianScale24_eq_partition_density (N : ℕ) (α : ℝ) :
    sphereGaussianScale24 N α = Real.pi*α*(spherePartitionDensityScale24 N)^2 := by
  have hA : 0 < (sphereAreaD 24).real univ := sphereAreaD_univ_pos 24
  have hρ : 0 ≤ (N : ℝ)/(sphereAreaD 24).real univ := div_nonneg (Nat.cast_nonneg _) hA.le
  have hp : (spherePartitionDensityScale24 N)^2 = ((N : ℝ)/(sphereAreaD 24).real univ)^(1/12:ℝ) := by
    unfold spherePartitionDensityScale24
    rw [← Real.rpow_mul_natCast hρ]
    norm_num
  rw [hp]
  rfl

theorem sphereGaussian24_uniform_lower_of_schwartz {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (hr : ρ ≤ 1/8) (g : Fin K → (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24))
    (hc : Continuous (sphereChartCutoff24 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass24 ρ hρ g x)
    (L α : ℝ) (hL : 0 ≤ L) (hα : 0 ≤ α)
    (hLip : ∀ i x y, sphereFiniteCutoffWeight24 ρ hρ g i x ≠ 0 →
      sphereFiniteCutoffWeight24 ρ hρ g i y ≠ 0 →
      dist x y ≤ L*‖rotatedSphereEqualAreaCoordinates24 (g i) x-
        rotatedSphereEqualAreaCoordinates24 (g i) y‖)
    (f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ))
    (hFnonneg : ∀ z, 0 ≤ ((𝓕 f) z).re) (hFreal : ∀ z, ((𝓕 f) z).im = 0)
    (hminor : ∀ z, (f z).re ≤ Real.exp (-(Real.pi*(α*L^2)*‖z‖^2)))
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) (hN0 : ∀ k, 0 < N k) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ X : Fin (N k) → (SphereD 24),
      ((𝓕 f) 0).re+1-(f 0).re-ε ≤
        (∑ p, ∑ q, sphereGaussianKernel24 (sphereGaussianScale24 (N k) α) (X p) (X q))/(N k : ℝ) := by
  intro ε hε
  let δ : ℝ := ε/4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hrow := spherePartitionSchwartzRow24_density_uniform ρ hρ hr g hc hpos f hN hN0 δ hδ
  have hbg : ∀ᶠ k in atTop, (N k : ℝ)*
      spherePartitionSchwartzBackground24 ρ hρ g f (spherePartitionDensityScale24 (N k)) < ((𝓕 f) 0).re+δ :=
    (tendsto_order.mp (spherePartitionSchwartzBackground24_density_tendsto ρ hρ hr g hc hpos f hN hN0)).2
      _ (by linarith)
  filter_upwards [hrow,hbg] with k hk hb
  intro X
  have hmin : ∀ x y, spherePartitionSchwartzKernel24 ρ hρ g f (spherePartitionDensityScale24 (N k)) x y ≤
      sphereGaussianKernel24 (sphereGaussianScale24 (N k) α) x y := by
    intro x y
    rw [sphereGaussianScale24_eq_partition_density]
    exact spherePartitionSchwartzKernel24_gaussian_le ρ hρ g hpos L α _ hL hα hLip f hminor x y
  have hsum := spherePartitionSchwartzRow24_sum_lower ρ hρ g (hN0 k) X f _ _ _ hk
  have hd := spherePartitionGaussian24_normalized_lower ρ hρ g hc hpos (hN0 k) X f
    hFnonneg hFreal (spherePartitionDensityScale24 (N k)) (sphereGaussianScale24 (N k) α) hmin
  dsimp [δ] at *
  linarith

theorem leechGaussianThetaReal24_exists_near_one_dilation {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) :
    ∃ L : ℝ, 1 < L ∧ leechGaussianThetaReal24 α-ε < leechGaussianThetaReal24 (α*L^2) := by
  have hc : ContinuousAt leechGaussianThetaReal24 α :=
    leechGaussianThetaReal24_continuousOn.continuousAt (isOpen_Ioi.mem_nhds hα)
  have hL : Tendsto (fun L : ℝ => α*L^2) (𝓝[>] (1 : ℝ)) (𝓝 α) := by
    have h : ContinuousAt (fun L : ℝ => α*L^2) 1 := by fun_prop
    simpa only [one_pow, mul_one] using h.tendsto.mono_left nhdsWithin_le_nhds
  have ht := hc.tendsto.comp hL
  have he : ∀ᶠ L in 𝓝[>] (1 : ℝ), leechGaussianThetaReal24 α-ε < leechGaussianThetaReal24 (α*L^2) :=
    (tendsto_order.mp ht).1 _ (by linarith)
  have hlo : ∀ᶠ L in 𝓝[>] (1 : ℝ), 1 < L := self_mem_nhdsWithin
  exact (hlo.and he).exists

/-- The missing all-scale Gaussian input, stated using actual Schwartz maps,
actual Mathlib Fourier transform, actual Gaussian and actual E8 theta.
No proof of24 this existence statement is supplied by defining it. -/

def LeechSharpGaussianSchwartzInput24 : Prop :=
  ∀ β : ℝ, 0 < β → ∃ f : 𝓢(EuclideanSpace ℝ (Fin 24), ℂ),
    (∀ z, 0 ≤ ((𝓕 f) z).re) ∧
    (∀ z, ((𝓕 f) z).im = 0) ∧
    (∀ z, (f z).re ≤ Real.exp (-(Real.pi*β*‖z‖^2))) ∧
    ((𝓕 f) 0).re-(f 0).re = leechGaussianThetaReal24 β-1

theorem sphereGaussianSharpProfileLower24_of_schwartz_input (hG8 : LeechSharpGaussianSchwartzInput24) :
    SphereGaussianSharpProfileLower24 := by
  intro N hN hN0 X α hα ε hε
  obtain ⟨L,hL,hθ⟩ := leechGaussianThetaReal24_exists_near_one_dilation hα (by positivity : 0 < ε/2)
  obtain ⟨ρ,hρ,hρ',hr,K,g,hc,hpos,_hwc,_hw,_hpart,hLip⟩ :=
    sphere24_exists_finite_cutoff_square_partition L hL
  have hL0 : 0 < L := zero_lt_one.trans hL
  obtain ⟨f,hFnonneg,hFreal,hminor,hvalue⟩ := hG8 (α*L^2) (by positivity)
  have he := sphereGaussian24_uniform_lower_of_schwartz ρ hρ' hr g hc hpos L α hL0.le hα.le
    hLip f hFnonneg hFreal hminor hN hN0 (ε/2) (by positivity)
  filter_upwards [he] with k hk
  have hx := hk (fun i => X k i)
  change leechGaussianThetaReal24 α-ε ≤
    (∑ p, ∑ q, sphereGaussianKernel24 (sphereGaussianScale24 (N k) α) (X k p) (X k q))/(N k : ℝ)
  linarith

/-- Leech certificates (CKMRV Lemma 6.2 form) give the sharp Schwartz input. -/
theorem leechSharpGaussianSchwartzInput24_of_contact
    (h : ∀ β : ℝ, 0 < β → ∃ f, LeechGaussianContactCertificate24 β f) :
    LeechSharpGaussianSchwartzInput24 := by
  intro β hβ
  obtain ⟨f, hf⟩ := h β hβ
  exact ⟨f, hf.fourier_nonneg, hf.fourier_real, fun z => hf.minorant z, hf.value hβ⟩

/-- The universal Gaussian profile lower bound on `S^24` from Leech certificates. -/
theorem sphereGaussianSharpProfileLower24_of_contact
    (h : ∀ β : ℝ, 0 < β → ∃ f, LeechGaussianContactCertificate24 β f) :
    SphereGaussianSharpProfileLower24 :=
  sphereGaussianSharpProfileLower24_of_schwartz_input (leechSharpGaussianSchwartzInput24_of_contact h)

#print axioms sphereGaussianSharpProfileLower24_of_schwartz_input
#print axioms leechSharpGaussianSchwartzInput24_of_contact
#print axioms sphereGaussianSharpProfileLower24_of_contact

end SphericalRiesz
