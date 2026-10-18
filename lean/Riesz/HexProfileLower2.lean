import Riesz.CompactUniformApproximateIdentity
import Riesz.EqualAreaChartD
import Riesz.EqualAreaInverseD
import Riesz.EqualAreaMeasureD
import Riesz.EqualAreaHex2
import Riesz.FiniteCutoffSquarePartition
import Riesz.HexLattice2
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
import Riesz.DiffuseGaussianBackground

/-! The sharp lower Gaussian profile of the sphere S² and its Gaussian background (stage S2-2 of the
S² chain; dimension-2 counterparts of `LeechProfileLower24` and `SphereGaussianBackground24`).

* `HexProfileLower2`: charts, a square-summable partition of unity, localized Schwartz kernels
  and positive definiteness turn a flat Gaussian certificate of the triangular lattice into the
  sharp lower bound of the Gaussian sums of point configurations on S²:
  `Σ_Λ exp(-π α |v|²) - ε ≤ N⁻¹ Σ_{i,j} exp(-π α (N/A₂) |x_i - x_j|²)` eventually, for every
  `α > 0`, under `∀ β > 0, ∃ f, HexGaussianContactCertificate2 β f`.  Also the area `A₂ = 4π`
  and the density scale `sphereGaussianScale2 N α = π α (N/A₂)`.
* `SphereGaussianBackground2`: the Gaussian potential and background of the uniform measure of
  S² and the nonnegative Gaussian defect of a configuration.

The certificates are a hypothesis here; they are not constructed in this module. -/

section

/-! # The universal Gaussian profile lower bound on `S²` (stage S2-2)

Dimension-2 port of `LeechProfileLower24`: the unit sphere `S² ⊂ ℝ³`, the equal-area chart
`ℝ² → S²` (Archimedes' hat-box map), and the triangular lattice of covolume one in place of the
Leech lattice.

* Charts: the chart in Euclidean coordinates, its derivative at the origin (an isometry), the
  inverse on the hemisphere, the north pole, rotated chart cutoffs and a finite partition of unity
  of squares of continuous cutoffs with chordal distances at most `L` times coordinate distances.
* Scales: the density scale `a = (N/A)^(1/2)`, `A` the area of `S²` (so `a² A = N`), and the
  Gaussian scale `sphereGaussianScale2 N α = π α (N/A)^1 = π α a²` (the exponent `2/d` is `1`).
* Rows: partition Schwartz kernels, their rows and backgrounds; uniform limits of the rows at
  the density scale (approximate identities in the chart).
* Positive definiteness: the localized Schwartz defect of a function with nonnegative Fourier
  transform is nonnegative; with a minorant of the Gaussian this bounds the Gaussian energy of
  every configuration from below.
* Lattice input: continuity of the theta function `Θ` of the triangular lattice on `(0, ∞)` and,
  for every `β > 0`, a Schwartz minorant `f` of `exp(-π β |x|²)` with `𝓕 f ≥ 0` and
  `𝓕 f(0) - f(0) = Θ(β) - 1` (`HexSharpGaussianSchwartzInput2`).  A sharp Gaussian certificate
  `HexGaussianContactCertificate2 β f` (contact on the lattice, Fourier zeros on the dual lattice)
  gives such an `f` by Poisson summation.

Result (`sphereGaussianSharpProfileLower2_of_contact`): for every sequence of configurations on
`S²` with `N → ∞` and every `α > 0`, the normalized Gaussian energy
`N⁻¹ Σ_{i,j} exp(-π α (N/A) |x_i - x_j|²)` is eventually at least `Θ(α) - ε`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Metric Topology
open scoped ENNReal NNReal Topology Pointwise ContDiff FourierTransform SchwartzMap RealInnerProductSpace
namespace SphericalRiesz
open Boundary

/-- The area of `S²` is `4π`: the dimension-2 counterpart of `sphereArea24_univ_real` (it belongs
next to it in `SphereMeasureD`).  From the general formula `(d+1) √π^(d+1)/Γ((d+1)/2+1)` and
`Γ(5/2) = (3/4) √π`. -/
theorem sphereArea2_univ_real : (sphereAreaD 2).real univ = 4*Real.pi := by
  have hs : Real.sqrt Real.pi*Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
  have hG : Real.Gamma (((2+1:ℕ):ℝ)/2+1) = 3/4*Real.sqrt Real.pi := by
    rw [show ((2+1:ℕ):ℝ)/2+1 = (1/2+1)+1 by norm_num,
      Real.Gamma_add_one (by norm_num), Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  rw [sphereAreaD_univ_real, hG, ← mul_div_assoc, div_eq_iff (by positivity)]
  linear_combination (3*Real.sqrt Real.pi)*hs

/-- Rotations preserve integrals against the uniform probability measure of `S²`. -/
theorem sphereProbability2_integral_rotation (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (f : (SphereD 2) → ℝ) :
    (∫ y, f (sphereRotationD g y) ∂(sphereProbabilityD 2)) = ∫ y, f y ∂(sphereProbabilityD 2) :=
  (sphereProbabilityD_rotation_preserving g).integral_comp
    (sphereRotationD g).measurableEmbedding f

def equalAreaPhiEuclidean2 (u : EuclideanSpace ℝ (Fin 2)) : (AmbientD 2) :=
  equalAreaPhiD (WithLp.ofLp u)

def equalAreaEuclideanDerivative2 : EuclideanSpace ℝ (Fin 2) →L[ℝ] (AmbientD 2) :=
  (equalAreaPhiDerivativeD 0).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).toContinuousLinearMap

theorem equalAreaPhiEuclidean2_continuous : Continuous equalAreaPhiEuclidean2 :=
  equalAreaPhiD_continuous.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).continuous

theorem equalAreaEuclideanDerivative2_apply (v : EuclideanSpace ℝ (Fin 2)) :
    equalAreaEuclideanDerivative2 v = (ambientConsD 1) (0,WithLp.ofLp v) :=
  equalAreaPhiDerivative2_zero_apply _

theorem equalAreaEuclideanDerivative2_norm (v : EuclideanSpace ℝ (Fin 2)) :
    ‖equalAreaEuclideanDerivative2 v‖ = ‖v‖ := by
  have h := ambientConsD_norm_sq (0,WithLp.ofLp v)
  rw [← equalAreaEuclideanDerivative2_apply] at h
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add, WithLp.toLp_ofLp] at h
  nlinarith [norm_nonneg (equalAreaEuclideanDerivative2 v), norm_nonneg v]

theorem equalAreaEuclideanDerivative2_opNorm_le : ‖equalAreaEuclideanDerivative2‖ ≤ 1 := by
  apply equalAreaEuclideanDerivative2.opNorm_le_bound zero_le_one
  intro v
  rw [equalAreaEuclideanDerivative2_norm, one_mul]

theorem equalAreaPhiEuclidean2_hasStrictFDerivAt_zero :
    HasStrictFDerivAt equalAreaPhiEuclidean2 equalAreaEuclideanDerivative2 0 := by
  have h0 : equalAreaSquaredNormD (0 : Fin 2 → ℝ) < 1 := by simp [equalAreaSquaredNormD]
  have hs := (equalAreaPhi2_contDiffAt 0 h0).hasStrictFDerivAt'
    (equalAreaPhiD_hasFDerivAt 0 h0) (by simp : (∞ : ℕ∞ω) ≠ 0)
  have he := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).hasStrictFDerivAt
    (x := (0 : EuclideanSpace ℝ (Fin 2)))
  convert! hs.comp 0 he using 1

theorem equalAreaEuclidean2_small_norm_domain (u : EuclideanSpace ℝ (Fin 2))
    (hu : ‖u‖ ≤ 1/8) : WithLp.ofLp u ∈ equalAreaChartDomainD := by
  have hp : ‖WithLp.ofLp u‖ ≤ ‖u‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
    intro i
    exact PiLp.norm_apply_le u i
  refine ⟨equalArea2_small_norm_domain _ (hp.trans hu),?_⟩
  have hi : |(WithLp.ofLp u) 0| ≤ 1/8 := by
    exact (show |(WithLp.ofLp u) 0| ≤ ‖u‖ from PiLp.norm_apply_le u 0).trans hu
  have hpi := Real.pi_gt_three
  exact ⟨by linarith [(abs_le.mp hi).1],by linarith [(abs_le.mp hi).2]⟩

def sphereEqualAreaCoordinates2 (q : (SphereD 2)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (equalAreaInverseD q)

theorem equalAreaPhiEuclidean2_inverse (x : (SphereD 2)) (hx : 0 < (x : (AmbientD 2)) 0) :
    equalAreaPhiEuclidean2 (sphereEqualAreaCoordinates2 x) = (x : (AmbientD 2)) := by
  simpa only [equalAreaPhiEuclidean2, sphereEqualAreaCoordinates2, WithLp.ofLp_toLp] using
    equalAreaPhiD_inverse8 x hx

theorem equalAreaPhiEuclidean2_near_isometry (L : ℝ) (hL : 1 < L) :
    ∃ ρ > 0, ρ ≤ 1/8 ∧
      ∀ u ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ,
        ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ,
          dist (equalAreaPhiEuclidean2 u) (equalAreaPhiEuclidean2 v) ≤ L*dist u v := by
  have hL0 : 0 ≤ L := (by norm_num : (0 : ℝ) ≤ 1).trans hL.le
  have hk : ‖equalAreaEuclideanDerivative2‖₊ < Real.toNNReal L := by
    apply NNReal.coe_lt_coe.mp
    simpa only [coe_nnnorm, Real.coe_toNNReal _ hL0] using
      equalAreaEuclideanDerivative2_opNorm_le.trans_lt hL
  obtain ⟨s,hs,hLip⟩ := equalAreaPhiEuclidean2_hasStrictFDerivAt_zero.exists_lipschitzOnWith_of_nnnorm_lt
    (Real.toNNReal L) hk
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨min δ (1/8),lt_min hδ (by norm_num),min_le_right _ _,?_⟩
  intro u hu v hv
  have hu' := hsub (ball_subset_ball (min_le_left δ (1/8)) hu)
  have hv' := hsub (ball_subset_ball (min_le_left δ (1/8)) hv)
  simpa only [Real.coe_toNNReal _ hL0] using hLip.dist_le_mul u hu' v hv'

def sphereChartCutoff2 (ρ : ℝ) (hρ : 0 < ρ) (x : (SphereD 2)) : ℝ :=
  if 0 < (x : (AmbientD 2)) 0 then coordinateCutoff ρ hρ (sphereEqualAreaCoordinates2 x) else 0

theorem sphereChartCutoff2_support (ρ : ℝ) (hρ : 0 < ρ) :
    Function.support (sphereChartCutoff2 ρ hρ) =
      {x : (SphereD 2) | 0 < (x : (AmbientD 2)) 0 ∧ ‖sphereEqualAreaCoordinates2 x‖ < ρ} := by
  ext x
  by_cases hx : 0 < (x : (AmbientD 2)) 0
  · simp only [Function.mem_support, sphereChartCutoff2, hx, ite_true,
      Set.mem_ofPred_eq, true_and]
    have h := Set.ext_iff.mp (coordinateCutoff_support (d := 2) ρ hρ)
      (sphereEqualAreaCoordinates2 x)
    simpa only [Function.mem_support, mem_ball, dist_zero_right] using h
  · simp only [Function.mem_support, sphereChartCutoff2, hx, ite_false,
      ne_eq, not_true_eq_false, Set.mem_ofPred_eq, false_and]

theorem sphereChartCutoff2_chord_bound (ρ : ℝ) (hρ : 0 < ρ) (L : ℝ)
    (hLip : ∀ u ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ,
      ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) ρ,
        dist (equalAreaPhiEuclidean2 u) (equalAreaPhiEuclidean2 v) ≤ L*dist u v)
    (x y : (SphereD 2)) (hx : sphereChartCutoff2 ρ hρ x ≠ 0)
    (hy : sphereChartCutoff2 ρ hρ y ≠ 0) :
    dist x y ≤ L*‖sphereEqualAreaCoordinates2 x-sphereEqualAreaCoordinates2 y‖ := by
  have hxs := hx
  change x ∈ Function.support (sphereChartCutoff2 ρ hρ) at hxs
  rw [sphereChartCutoff2_support] at hxs
  have hys := hy
  change y ∈ Function.support (sphereChartCutoff2 ρ hρ) at hys
  rw [sphereChartCutoff2_support] at hys
  have h := hLip _ (by simpa only [mem_ball,dist_zero_right] using hxs.2)
    _ (by simpa only [mem_ball,dist_zero_right] using hys.2)
  rw [equalAreaPhiEuclidean2_inverse x hxs.1, equalAreaPhiEuclidean2_inverse y hys.1] at h
  simpa only [Subtype.dist_eq, dist_eq_norm] using h

def equalAreaEuclideanDomain2 : Set (EuclideanSpace ℝ (Fin 2)) :=
  WithLp.ofLp ⁻¹' equalAreaChartDomainD

theorem equalAreaEuclideanDomain2_isOpen : IsOpen equalAreaEuclideanDomain2 :=
  equalAreaChartDomainD_isOpen.preimage
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).continuous

theorem equalAreaEuclideanDomain2_measurable : MeasurableSet equalAreaEuclideanDomain2 :=
  equalAreaEuclideanDomain2_isOpen.measurableSet

def equalAreaEuclideanSphereChart2 : equalAreaEuclideanDomain2 ↪ (SphereD 2) where
  toFun u := ⟨equalAreaPhiEuclidean2 u, equalAreaPhiD_mem_sphere _ u.property.1⟩
  inj' := by
    intro u v h
    apply Subtype.ext
    apply WithLp.ofLp_injective
    exact equalAreaPhiD_injOn u.property v.property (congrArg Subtype.val h)

theorem equalAreaEuclideanSphereChart2_continuous : Continuous equalAreaEuclideanSphereChart2 := by
  apply Continuous.subtype_mk
  exact equalAreaPhiEuclidean2_continuous.comp continuous_subtype_val

theorem equalAreaEuclideanSphereChart2_measurableEmbedding :
    MeasurableEmbedding equalAreaEuclideanSphereChart2 := by
  let : PolishSpace equalAreaEuclideanDomain2 := equalAreaEuclideanDomain2_isOpen.polishSpace
  exact equalAreaEuclideanSphereChart2_continuous.measurableEmbedding
    equalAreaEuclideanSphereChart2.injective

theorem equalAreaEuclideanSphereChart2_image (s : Set equalAreaEuclideanDomain2) :
    equalAreaEuclideanSphereChart2 '' s =
      equalAreaSpherePatchD (WithLp.ofLp '' (Subtype.val '' s)) := by
  ext y
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨WithLp.ofLp (u : EuclideanSpace ℝ (Fin 2)),⟨u,⟨u,hu,rfl⟩,rfl⟩,rfl⟩
  · rintro ⟨p,⟨u,⟨z,hz,rfl⟩,rfl⟩,h⟩
    exact ⟨z,hz,Subtype.ext h⟩

theorem equalAreaEuclideanSphereChart2_range :
    range equalAreaEuclideanSphereChart2 = equalAreaHemisphereD := by
  ext x
  constructor
  · rintro ⟨u,rfl⟩
    exact equalAreaPhiD_first_pos _ u.property
  · intro hx
    refine ⟨⟨sphereEqualAreaCoordinates2 x,?_⟩,?_⟩
    · simpa only [equalAreaEuclideanDomain2, mem_preimage, sphereEqualAreaCoordinates2,
        WithLp.ofLp_toLp] using equalAreaInverseD_mem_domain x hx
    · apply Subtype.ext
      exact equalAreaPhiEuclidean2_inverse x hx

theorem equalAreaEuclideanSphereChart2_coordinates (u : equalAreaEuclideanDomain2) :
    sphereEqualAreaCoordinates2 (equalAreaEuclideanSphereChart2 u) = (u : EuclideanSpace ℝ (Fin 2)) := by
  change WithLp.toLp 2 (equalAreaInverseD (equalAreaPhiD (WithLp.ofLp (u : EuclideanSpace ℝ (Fin 2))))) = _
  rw [equalAreaInverseD_phi _ u.property, WithLp.toLp_ofLp]

theorem equalAreaEuclideanSphereChart2_comap_area :
    (sphereAreaD 2).comap equalAreaEuclideanSphereChart2 =
      volume.comap (Subtype.val : equalAreaEuclideanDomain2 → EuclideanSpace ℝ (Fin 2)) := by
  ext s hs
  have hS : MeasurableSet (Subtype.val '' s) :=
    (MeasurableEmbedding.subtype_coe equalAreaEuclideanDomain2_measurable).measurableSet_image.2 hs
  have hPi : MeasurableSet (WithLp.ofLp '' (Subtype.val '' s)) :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.measurableEmbedding.measurableSet_image.2 hS
  have hdom : WithLp.ofLp '' (Subtype.val '' s) ⊆ equalAreaChartDomainD := by
    rintro p ⟨u,⟨z,hz,rfl⟩,rfl⟩
    exact z.property
  rw [equalAreaEuclideanSphereChart2_measurableEmbedding.comap_apply,
    equalAreaEuclideanSphereChart2_image, sphereAreaD_equalAreaSpherePatch _ hPi hdom,
    comap_subtype_coe_apply equalAreaEuclideanDomain2_measurable]
  have h := (PiLp.volume_preserving_ofLp (Fin 2)).measure_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.measurableEmbedding
    (WithLp.ofLp '' (Subtype.val '' s))
  rw [preimage_image_eq _ (WithLp.ofLp_injective 2)] at h
  exact h.symm

theorem equalAreaEuclideanSphereChart2_map_area :
    Measure.map equalAreaEuclideanSphereChart2
      (volume.comap (Subtype.val : equalAreaEuclideanDomain2 → EuclideanSpace ℝ (Fin 2))) =
      (sphereAreaD 2).restrict equalAreaHemisphereD := by
  rw [← equalAreaEuclideanSphereChart2_comap_area,
    equalAreaEuclideanSphereChart2_measurableEmbedding.map_comap, equalAreaEuclideanSphereChart2_range]

theorem equalAreaEuclideanSphereChart2_area_integral (g : (SphereD 2) → ℝ) :
    (∫ x in equalAreaHemisphereD, g x ∂(sphereAreaD 2)) =
      ∫ u : equalAreaEuclideanDomain2, g (equalAreaEuclideanSphereChart2 u)
        ∂(volume.comap (Subtype.val : equalAreaEuclideanDomain2 → EuclideanSpace ℝ (Fin 2))) := by
  rw [← equalAreaEuclideanSphereChart2_map_area,
    equalAreaEuclideanSphereChart2_measurableEmbedding.integral_map]

theorem equalAreaEuclideanSphereChart2_probability_integral (g : (SphereD 2) → ℝ) :
    (∫ x in equalAreaHemisphereD, g x ∂(sphereProbabilityD 2)) =
      ((sphereAreaD 2).real univ)⁻¹ *
        ∫ u : equalAreaEuclideanDomain2, g (equalAreaEuclideanSphereChart2 u)
          ∂(volume.comap (Subtype.val : equalAreaEuclideanDomain2 → EuclideanSpace ℝ (Fin 2))) := by
  rw [sphereProbabilityD, Measure.restrict_smul, integral_smul_measure,
    equalAreaEuclideanSphereChart2_area_integral, ENNReal.toReal_inv]
  rfl

theorem sphereChartCutoff2_chart (ρ : ℝ) (hρ : 0 < ρ) (u : equalAreaEuclideanDomain2) :
    sphereChartCutoff2 ρ hρ (equalAreaEuclideanSphereChart2 u) =
      coordinateCutoff ρ hρ (u : EuclideanSpace ℝ (Fin 2)) := by
  have hp : 0 < (equalAreaEuclideanSphereChart2 u : (AmbientD 2)) 0 :=
    equalAreaPhiD_first_pos _ u.property
  rw [sphereChartCutoff2, ite_eq_left hp, equalAreaEuclideanSphereChart2_coordinates]

theorem sphereEqualAreaCoordinates2_continuousAt (x : (SphereD 2))
    (hx : 0 < (x : (AmbientD 2)) 0) : ContinuousAt sphereEqualAreaCoordinates2 x := by
  have hs : IsOpen {q : (AmbientD 2) | q 0 ≠ 0} := isOpen_ne.preimage (by fun_prop)
  have hi := equalAreaInverseD_continuousOn.continuousAt (hs.mem_nhds hx.ne')
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.continuousAt.comp
    (hi.comp continuous_subtype_val.continuousAt)

theorem sphereChartCutoff2_continuousAt_positive (ρ : ℝ) (hρ : 0 < ρ)
    (x : (SphereD 2)) (hx : 0 < (x : (AmbientD 2)) 0) :
    ContinuousAt (sphereChartCutoff2 ρ hρ) x := by
  have he : ∀ᶠ y : (SphereD 2) in 𝓝 x, 0 < (y : (AmbientD 2)) 0 :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds hx
  apply ((coordinateCutoff_continuous ρ hρ).continuousAt.comp
    (sphereEqualAreaCoordinates2_continuousAt x hx)).congr_of_eventuallyEq
  filter_upwards [he] with y hy
  simp only [sphereChartCutoff2, ite_eq_left hy, Function.comp_apply]

def northPole2 : (SphereD 2) :=
  ⟨EuclideanSpace.single (0 : Fin 3) (1 : ℝ), by simp⟩

theorem sphere2_coordinate_difference_le_dist (q p : (SphereD 2)) (i : Fin 3) :
    |(q : (AmbientD 2)) i-(p : (AmbientD 2)) i| ≤ dist q p := by
  change |(q : (AmbientD 2)) i-(p : (AmbientD 2)) i| ≤ ‖(q : (AmbientD 2))-(p : (AmbientD 2))‖
  simpa only [PiLp.sub_apply, Real.norm_eq_abs] using
    (PiLp.norm_apply_le ((q : (AmbientD 2))-(p : (AmbientD 2))) i)

theorem northPole2_ball_first_pos (q : (SphereD 2)) (r : ℝ)
    (hr : r ≤ 1/2) (hq : q ∈ ball northPole2 r) :
    1/2 < (q : (AmbientD 2)) 0 := by
  have h := (sphere2_coordinate_difference_le_dist q northPole2 0).trans_lt hq
  have hcoord : |(q : (AmbientD 2)) 0-1| < r := by
    simpa [northPole2] using h
  linarith [(abs_lt.mp hcoord).1]

theorem sphereEqualAreaCoordinates2_northPole : sphereEqualAreaCoordinates2 northPole2 = 0 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [sphereEqualAreaCoordinates2, equalAreaInverseD, northPole2]
  · simp [sphereEqualAreaCoordinates2, equalAreaInverseD, northPole2]

theorem sphereChartCutoff2_northPole (ρ : ℝ) (hρ : 0 < ρ) :
    sphereChartCutoff2 ρ hρ northPole2 = 1 := by
  have hp : 0 < (northPole2 : (AmbientD 2)) 0 := by simp [northPole2]
  rw [sphereChartCutoff2, ite_eq_left hp, sphereEqualAreaCoordinates2_northPole,
    coordinateCutoff_zero]

theorem sphereChartCutoff2_support_height_of_chord_bound (ρ : ℝ) (hρ : 0 < ρ)
    (hr : ρ ≤ 1/8)
    (hB : ∀ x y : (SphereD 2), sphereChartCutoff2 ρ hρ x ≠ 0 →
      sphereChartCutoff2 ρ hρ y ≠ 0 →
      dist x y ≤ 2*‖sphereEqualAreaCoordinates2 x-sphereEqualAreaCoordinates2 y‖)
    (x : (SphereD 2)) (hx : sphereChartCutoff2 ρ hρ x ≠ 0) :
    1/2 < (x : (AmbientD 2)) 0 := by
  have hxs : x ∈ Function.support (sphereChartCutoff2 ρ hρ) := hx
  rw [sphereChartCutoff2_support] at hxs
  have hp : sphereChartCutoff2 ρ hρ northPole2 ≠ 0 := by
    rw [sphereChartCutoff2_northPole]
    exact one_ne_zero
  have hd := hB x northPole2 hx hp
  rw [sphereEqualAreaCoordinates2_northPole, sub_zero] at hd
  apply northPole2_ball_first_pos x (1/2) le_rfl
  change dist x northPole2 < 1/2
  linarith [hxs.2]

theorem sphereChartCutoff2_continuous_of_chord_bound (ρ : ℝ) (hρ : 0 < ρ)
    (hr : ρ ≤ 1/8)
    (hB : ∀ x y : (SphereD 2), sphereChartCutoff2 ρ hρ x ≠ 0 →
      sphereChartCutoff2 ρ hρ y ≠ 0 →
      dist x y ≤ 2*‖sphereEqualAreaCoordinates2 x-sphereEqualAreaCoordinates2 y‖) :
    Continuous (sphereChartCutoff2 ρ hρ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : 0 < (x : (AmbientD 2)) 0
  · exact sphereChartCutoff2_continuousAt_positive ρ hρ x hx
  · have hx0 : (x : (AmbientD 2)) 0 < (1/2 : ℝ) :=
      lt_of_le_of_lt (not_lt.mp hx) (by norm_num)
    have ho : IsOpen {y : (SphereD 2) | (y : (AmbientD 2)) 0 < (1/2 : ℝ)} :=
      isOpen_lt (by fun_prop) continuous_const
    have he : ∀ᶠ y : (SphereD 2) in 𝓝 x, (y : (AmbientD 2)) 0 < 1/2 := ho.mem_nhds hx0
    apply (continuousAt_const : ContinuousAt (fun _ : (SphereD 2) => (0 : ℝ)) x).congr_of_eventuallyEq
    filter_upwards [he] with y hy
    by_contra hn
    have hh := sphereChartCutoff2_support_height_of_chord_bound ρ hρ hr hB y hn
    linarith

def rotatedSphereChartCutoff2 (ρ : ℝ) (hρ : 0 < ρ)
    (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (x : (SphereD 2)) : ℝ :=
  sphereChartCutoff2 ρ hρ (sphereRotationD g.symm x)

def rotatedSphereEqualAreaCoordinates2 (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (x : (SphereD 2)) : EuclideanSpace ℝ (Fin 2) :=
  sphereEqualAreaCoordinates2 (sphereRotationD g.symm x)

theorem sphereChartCutoff2_nonneg (ρ : ℝ) (hρ : 0 < ρ) (x : (SphereD 2)) :
    0 ≤ sphereChartCutoff2 ρ hρ x := by
  unfold sphereChartCutoff2
  split_ifs
  · exact coordinateCutoff_nonneg ρ hρ _
  · exact le_rfl

theorem rotatedSphereChartCutoff2_nonneg (ρ : ℝ) (hρ : 0 < ρ)
    (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (x : (SphereD 2)) :
    0 ≤ rotatedSphereChartCutoff2 ρ hρ g x := sphereChartCutoff2_nonneg ρ hρ _

theorem rotatedSphereChartCutoff2_center (ρ : ℝ) (hρ : 0 < ρ)
    (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) :
    rotatedSphereChartCutoff2 ρ hρ g (sphereRotationD g northPole2) = 1 := by
  unfold rotatedSphereChartCutoff2
  rw [show sphereRotationD g.symm (sphereRotationD g northPole2) = northPole2 from
    (sphereRotationD g).left_inv northPole2, sphereChartCutoff2_northPole]

theorem rotatedSphereChartCutoff2_continuous (ρ : ℝ) (hρ : 0 < ρ)
    (hc : Continuous (sphereChartCutoff2 ρ hρ)) (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) :
    Continuous (rotatedSphereChartCutoff2 ρ hρ g) :=
  hc.comp (sphereRotationD g.symm).continuous

/-- The reflection in the orthogonal complement of `x - y` moves `x` to `y`. -/
theorem sphereRotation2_transitive (x y : (SphereD 2)) :
    ∃ g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2), sphereRotationD g x = y := by
  refine ⟨Submodule.reflection (ℝ ∙ ((x : (AmbientD 2)) - y))ᗮ, ?_⟩
  apply Subtype.ext
  apply Submodule.reflection_sub
  exact (mem_sphere_zero_iff_norm.1 x.property).trans
    (mem_sphere_zero_iff_norm.1 y.property).symm

theorem sphere2_finite_rotated_cutoff_cover (ρ : ℝ) (hρ : 0 < ρ)
    (hc : Continuous (sphereChartCutoff2 ρ hρ)) :
    ∃ K : ℕ, ∃ g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2),
      ∀ x : (SphereD 2), ∃ i, 0 < rotatedSphereChartCutoff2 ρ hρ (g i) x := by
  classical
  let : CompactSpace (SphereD 2) := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : (AmbientD 2)) 1)
  have ht : ∀ p : (SphereD 2), ∃ g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2),
      sphereRotationD g northPole2 = p := fun p => sphereRotation2_transitive northPole2 p
  choose g hg using ht
  let U : (SphereD 2) → Set (SphereD 2) := fun p => {x | 0 < rotatedSphereChartCutoff2 ρ hρ (g p) x}
  have hU : ∀ p, IsOpen (U p) := fun p =>
    isOpen_lt continuous_const (rotatedSphereChartCutoff2_continuous ρ hρ hc (g p))
  have hcenter (p : (SphereD 2)) : p ∈ U p := by
    change 0 < rotatedSphereChartCutoff2 ρ hρ (g p) p
    have he := rotatedSphereChartCutoff2_center ρ hρ (g p)
    rw [hg p] at he
    rw [he]
    exact zero_lt_one
  obtain ⟨t,ht⟩ := (isCompact_univ : IsCompact (univ : Set (SphereD 2))).elim_finite_subcover
    U hU (fun p _ => mem_iUnion.mpr ⟨p,hcenter p⟩)
  let gs : Fin t.card → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2) := fun i => g (t.equivFin.symm i).val
  refine ⟨t.card,gs,?_⟩
  intro x
  obtain ⟨p,hp⟩ := mem_iUnion.mp (ht (mem_univ x))
  obtain ⟨hpt,hxp⟩ := mem_iUnion.mp hp
  change 0 < rotatedSphereChartCutoff2 ρ hρ (g p) x at hxp
  refine ⟨t.equivFin ⟨p,hpt⟩,?_⟩
  simpa only [gs, Equiv.symm_apply_apply] using hxp

def sphereFiniteCutoffMass2 {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) : (SphereD 2) → ℝ :=
  finiteCutoffSquareMass (fun i => rotatedSphereChartCutoff2 ρ hρ (g i))

def sphereFiniteCutoffWeight2 {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) : Fin K → (SphereD 2) → ℝ :=
  finiteCutoffSquarePartition (fun i => rotatedSphereChartCutoff2 ρ hρ (g i))

theorem sphereFiniteCutoffMass2_pos {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (hcover : ∀ x : (SphereD 2), ∃ i, 0 < rotatedSphereChartCutoff2 ρ hρ (g i) x) (x : (SphereD 2)) :
    0 < sphereFiniteCutoffMass2 ρ hρ g x :=
  finiteCutoffSquareMass_pos_of_cover _ hcover x

theorem sphereFiniteCutoffWeight2_nonneg {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (i : Fin K) (x : (SphereD 2)) :
    0 ≤ sphereFiniteCutoffWeight2 ρ hρ g i x :=
  finiteCutoffSquarePartition_nonneg _ (fun j y => rotatedSphereChartCutoff2_nonneg ρ hρ (g j) y) i x

theorem sphereFiniteCutoffWeight2_le_one {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x) (i : Fin K) (x : (SphereD 2)) :
    sphereFiniteCutoffWeight2 ρ hρ g i x ≤ 1 :=
  finiteCutoffSquarePartition_le_one _ hpos i x

theorem sphereFiniteCutoffWeight2_continuous {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (hc : Continuous (sphereChartCutoff2 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x) (i : Fin K) :
    Continuous (sphereFiniteCutoffWeight2 ρ hρ g i) :=
  finiteCutoffSquarePartition_continuous _ (fun j => rotatedSphereChartCutoff2_continuous ρ hρ hc (g j))
    hpos i

theorem sphereFiniteCutoffWeight2_sum_square {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x) (x : (SphereD 2)) :
    (∑ i, (sphereFiniteCutoffWeight2 ρ hρ g i x)^2) = 1 :=
  finiteCutoffSquarePartition_sum_square _ hpos x

theorem sphereFiniteCutoffWeight2_ne_zero_iff {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x) (i : Fin K) (x : (SphereD 2)) :
    sphereFiniteCutoffWeight2 ρ hρ g i x ≠ 0 ↔ rotatedSphereChartCutoff2 ρ hρ (g i) x ≠ 0 :=
  finiteCutoffSquarePartition_ne_zero_iff _ hpos i x

theorem sphereFiniteCutoffWeight2_correlation_le_one {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x) (x y : (SphereD 2)) :
    (∑ i, sphereFiniteCutoffWeight2 ρ hρ g i x*sphereFiniteCutoffWeight2 ρ hρ g i y) ≤ 1 :=
  finiteCutoffSquarePartition_correlation_le_one _ hpos x y

theorem sphereFiniteCutoffWeight2_chord_bound {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x) (L : ℝ)
    (hB : ∀ x y : (SphereD 2), sphereChartCutoff2 ρ hρ x ≠ 0 →
      sphereChartCutoff2 ρ hρ y ≠ 0 →
      dist x y ≤ L*‖sphereEqualAreaCoordinates2 x-sphereEqualAreaCoordinates2 y‖)
    (i : Fin K) (x y : (SphereD 2))
    (hx : sphereFiniteCutoffWeight2 ρ hρ g i x ≠ 0)
    (hy : sphereFiniteCutoffWeight2 ρ hρ g i y ≠ 0) :
    dist x y ≤ L*‖rotatedSphereEqualAreaCoordinates2 (g i) x-
      rotatedSphereEqualAreaCoordinates2 (g i) y‖ := by
  have hx' := (sphereFiniteCutoffWeight2_ne_zero_iff ρ hρ g hpos i x).mp hx
  have hy' := (sphereFiniteCutoffWeight2_ne_zero_iff ρ hρ g hpos i y).mp hy
  have h := hB (sphereRotationD (g i).symm x) (sphereRotationD (g i).symm y) hx' hy'
  rw [sphereRotationD_dist] at h
  exact h

theorem sphere2_exists_finite_cutoff_square_partition (L : ℝ) (hL : 1 < L) :
    ∃ ρ > 0, ∃ hρ : 0 < ρ, ρ ≤ 1/8 ∧
      ∃ K : ℕ, ∃ g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2),
        Continuous (sphereChartCutoff2 ρ hρ) ∧
        (∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x) ∧
        (∀ i, Continuous (sphereFiniteCutoffWeight2 ρ hρ g i)) ∧
        (∀ i x, 0 ≤ sphereFiniteCutoffWeight2 ρ hρ g i x ∧ sphereFiniteCutoffWeight2 ρ hρ g i x ≤ 1) ∧
        (∀ x, (∑ i, (sphereFiniteCutoffWeight2 ρ hρ g i x)^2) = 1) ∧
        (∀ i x y, sphereFiniteCutoffWeight2 ρ hρ g i x ≠ 0 →
          sphereFiniteCutoffWeight2 ρ hρ g i y ≠ 0 →
          dist x y ≤ L*‖rotatedSphereEqualAreaCoordinates2 (g i) x-
            rotatedSphereEqualAreaCoordinates2 (g i) y‖) := by
  have hL0 : 1 < min L 2 := lt_min hL (by norm_num)
  obtain ⟨ρ,hρ,hr,hLip⟩ := equalAreaPhiEuclidean2_near_isometry (min L 2) hL0
  have hB : ∀ x y : (SphereD 2), sphereChartCutoff2 ρ hρ x ≠ 0 →
      sphereChartCutoff2 ρ hρ y ≠ 0 →
      dist x y ≤ min L 2*‖sphereEqualAreaCoordinates2 x-sphereEqualAreaCoordinates2 y‖ :=
    fun x y hx hy => sphereChartCutoff2_chord_bound ρ hρ (min L 2) hLip x y hx hy
  have hB2 : ∀ x y : (SphereD 2), sphereChartCutoff2 ρ hρ x ≠ 0 →
      sphereChartCutoff2 ρ hρ y ≠ 0 →
      dist x y ≤ 2*‖sphereEqualAreaCoordinates2 x-sphereEqualAreaCoordinates2 y‖ :=
    fun x y hx hy => (hB x y hx hy).trans
      (mul_le_mul_of_nonneg_right (min_le_right L 2) (norm_nonneg _))
  have hBL : ∀ x y : (SphereD 2), sphereChartCutoff2 ρ hρ x ≠ 0 →
      sphereChartCutoff2 ρ hρ y ≠ 0 →
      dist x y ≤ L*‖sphereEqualAreaCoordinates2 x-sphereEqualAreaCoordinates2 y‖ :=
    fun x y hx hy => (hB x y hx hy).trans
      (mul_le_mul_of_nonneg_right (min_le_left L 2) (norm_nonneg _))
  have hc := sphereChartCutoff2_continuous_of_chord_bound ρ hρ hr hB2
  obtain ⟨K,g,hcover⟩ := sphere2_finite_rotated_cutoff_cover ρ hρ hc
  have hpos := sphereFiniteCutoffMass2_pos ρ hρ g hcover
  refine ⟨ρ,hρ,hρ,hr,K,g,hc,hpos,?_,?_,?_,?_⟩
  · exact sphereFiniteCutoffWeight2_continuous ρ hρ g hc hpos
  · exact fun i x => ⟨sphereFiniteCutoffWeight2_nonneg ρ hρ g i x,
      sphereFiniteCutoffWeight2_le_one ρ hρ g hpos i x⟩
  · exact sphereFiniteCutoffWeight2_sum_square ρ hρ g hpos
  · exact sphereFiniteCutoffWeight2_chord_bound ρ hρ g hpos L hBL

/-- The Gaussian kernel `exp(-t |x - y|²)` of the chordal distance on `S²`. -/
def sphereGaussianKernel2 (t : ℝ) (x y : (SphereD 2)) : ℝ :=
  Real.exp (-(t*(dist x y)^2))

theorem sphereGaussianKernel2_nonneg (t : ℝ) (x y : (SphereD 2)) :
    0 ≤ sphereGaussianKernel2 t x y := (Real.exp_pos _).le

@[simp]
theorem sphereGaussianKernel2_self (t : ℝ) (x : (SphereD 2)) :
    sphereGaussianKernel2 t x x = 1 := by simp [sphereGaussianKernel2]

/-- The Gaussian parameter at density scale: `π α (N/A)^(2/d)` with `d = 2`, `A` the area of
`S²`.  The exponent `2/d = 1` is kept as a real exponent, as in the higher-dimensional chains;
`sphereGaussianScale2_eq` removes it. -/
def sphereGaussianScale2 (N : ℕ) (α : ℝ) : ℝ :=
  Real.pi*α*((N:ℝ)/(sphereAreaD 2).real univ)^(1:ℝ)

/-- In dimension two the Gaussian scale is linear in the number of points. -/
theorem sphereGaussianScale2_eq (N : ℕ) (α : ℝ) :
    sphereGaussianScale2 N α = Real.pi*α*((N:ℝ)/(sphereAreaD 2).real univ) := by
  rw [sphereGaussianScale2, Real.rpow_one]

/-- The normalized Gaussian energy (diagonal included) of a configuration at scale `α`. -/
def sphereGaussianFullScaled2 {N : ℕ} (α : ℝ) (X : (ConfigurationD 2) N) : ℝ :=
  (∑ i : Fin N, ∑ j : Fin N,
    sphereGaussianKernel2 (sphereGaussianScale2 N α) (X i) (X j))/(N:ℝ)

/-- The sharp lower Gaussian profile of `S²`: along every sequence of configurations with
`N → ∞` the normalized Gaussian energy at scale `α` is eventually at least `Θ(α) - ε`, `Θ` the
theta function of the triangular lattice of covolume one.  A statement, proved below from
Gaussian certificates of the lattice. -/
def SphereGaussianSharpProfileLower2 : Prop :=
  ∀ (N : ℕ → ℕ), Tendsto N atTop atTop → (∀ k, 0 < N k) →
    ∀ (X : ∀ k, (ConfigurationD 2) (N k)) (α : ℝ), 0 < α →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
        hexGaussianThetaReal2 α-ε ≤ sphereGaussianFullScaled2 α (X k)

def spherePartitionSchwartzComponent2 {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) (a : ℝ) (i : Fin K)
    (x y : (SphereD 2)) : ℝ :=
  sphereFiniteCutoffWeight2 ρ hρ g i x*sphereFiniteCutoffWeight2 ρ hρ g i y*
    (f (a • (rotatedSphereEqualAreaCoordinates2 (g i) x-
      rotatedSphereEqualAreaCoordinates2 (g i) y))).re

def spherePartitionSchwartzKernel2 {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) (a : ℝ) (x y : (SphereD 2)) : ℝ :=
  ∑ i, spherePartitionSchwartzComponent2 ρ hρ g f a i x y

def spherePartitionSchwartzRow2 {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) (a : ℝ) (x : (SphereD 2)) : ℝ :=
  ∫ y, spherePartitionSchwartzKernel2 ρ hρ g f a x y ∂(sphereProbabilityD 2)

theorem spherePartitionSchwartzRow2_sum_lower {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (hN : 0 < N) (X : Fin N → (SphereD 2))
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) (a H δ : ℝ)
    (hrow : ∀ x, |(N : ℝ)*spherePartitionSchwartzRow2 ρ hρ g f a x-H| < δ) :
    H-δ ≤ ∑ p, spherePartitionSchwartzRow2 ρ hρ g f a (X p) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hp (p : Fin N) : H-δ ≤ (N : ℝ)*spherePartitionSchwartzRow2 ρ hρ g f a (X p) := by
    have h := (abs_lt.mp (hrow (X p))).1
    linarith
  have hs := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset (Fin N))) => hp p)
  have hs' : (N : ℝ)*(H-δ) ≤ (N : ℝ)*(∑ p, spherePartitionSchwartzRow2 ρ hρ g f a (X p)) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum] using hs
  nlinarith

def spherePartitionDensityScale2 (N : ℕ) : ℝ :=
  ((N : ℝ)/(sphereAreaD 2).real univ)^((2 : ℝ)⁻¹)

theorem spherePartitionDensityScale2_pos {N : ℕ} (hN : 0 < N) :
    0 < spherePartitionDensityScale2 N := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hA : 0 < (sphereAreaD 2).real univ := sphereAreaD_univ_pos 2
  exact Real.rpow_pos_of_pos (div_pos hNR hA) _

theorem spherePartitionDensityScale2_pow (N : ℕ) :
    (spherePartitionDensityScale2 N)^2 = (N : ℝ)/(sphereAreaD 2).real univ := by
  apply Real.rpow_inv_natCast_pow
  · have hA : 0 < (sphereAreaD 2).real univ := sphereAreaD_univ_pos 2
    exact div_nonneg (Nat.cast_nonneg _) hA.le
  · decide

theorem spherePartitionDensityScale2_mass (N : ℕ) :
    (spherePartitionDensityScale2 N)^2*(sphereAreaD 2).real univ = (N : ℝ) := by
  have hA : (sphereAreaD 2).real univ ≠ 0 := (sphereAreaD_univ_pos 2).ne'
  rw [spherePartitionDensityScale2_pow, div_mul_cancel₀ _ hA]

theorem spherePartitionDensityScale2_tendsto :
    Tendsto spherePartitionDensityScale2 atTop atTop := by
  have hA : 0 < (sphereAreaD 2).real univ := sphereAreaD_univ_pos 2
  have hN : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hdiv : Tendsto (fun N : ℕ => (N : ℝ)/(sphereAreaD 2).real univ) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [hN.eventually (eventually_ge_atTop (b*(sphereAreaD 2).real univ))] with N hN
    exact (le_div_iff₀ hA).mpr hN
  exact (tendsto_rpow_atTop (by positivity : 0 < (2 : ℝ)⁻¹)).comp hdiv

def sphereFiniteCutoffProfile2 {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (i : Fin K)
    (u : EuclideanSpace ℝ (Fin 2)) : ℝ := by
  classical
  exact if hu : u ∈ equalAreaEuclideanDomain2 then
    sphereFiniteCutoffWeight2 ρ hρ g i
      (sphereRotationD (g i) (equalAreaEuclideanSphereChart2 ⟨u,hu⟩)) else 0

theorem rotatedSphereChartCutoff2_apply (ρ : ℝ) (hρ : 0 < ρ)
    (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (x : (SphereD 2)) :
    rotatedSphereChartCutoff2 ρ hρ g (sphereRotationD g x) = sphereChartCutoff2 ρ hρ x := by
  unfold rotatedSphereChartCutoff2
  rw [show sphereRotationD g.symm (sphereRotationD g x) = x from (sphereRotationD g).left_inv x]

theorem sphereFiniteCutoffProfile2_zero_off_domain {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (i : Fin K) (u : EuclideanSpace ℝ (Fin 2))
    (hu : u ∉ equalAreaEuclideanDomain2) : sphereFiniteCutoffProfile2 ρ hρ g i u = 0 := by
  rw [sphereFiniteCutoffProfile2, dite_eq_right hu]

theorem sphereFiniteCutoffProfile2_zero_of_norm {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (i : Fin K) (u : EuclideanSpace ℝ (Fin 2))
    (hu : ρ ≤ ‖u‖) : sphereFiniteCutoffProfile2 ρ hρ g i u = 0 := by
  by_cases hd : u ∈ equalAreaEuclideanDomain2
  · rw [sphereFiniteCutoffProfile2, dite_eq_left hd]
    simp only [sphereFiniteCutoffWeight2, finiteCutoffSquarePartition,
      rotatedSphereChartCutoff2_apply, sphereChartCutoff2_chart,
      coordinateCutoff_zero_of_norm ρ hρ u hu, zero_div]
  · exact sphereFiniteCutoffProfile2_zero_off_domain ρ hρ g i u hd

theorem sphereFiniteCutoffProfile2_compactSupport {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (i : Fin K) :
    HasCompactSupport (sphereFiniteCutoffProfile2 ρ hρ g i) := by
  apply (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) ρ).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ isClosed_closedBall
  intro u hu
  have hn : ‖u‖ < ρ := by
    by_contra h
    exact hu (sphereFiniteCutoffProfile2_zero_of_norm ρ hρ g i u (not_lt.mp h))
  simpa only [mem_closedBall, dist_zero_right] using hn.le

theorem sphereFiniteCutoffProfile2_chart {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (i : Fin K) (u : equalAreaEuclideanDomain2) :
    sphereFiniteCutoffProfile2 ρ hρ g i (u : EuclideanSpace ℝ (Fin 2)) =
      sphereFiniteCutoffWeight2 ρ hρ g i (sphereRotationD (g i) (equalAreaEuclideanSphereChart2 u)) := by
  rw [sphereFiniteCutoffProfile2, dite_eq_left u.property]

theorem sphereFiniteCutoffProfile2_continuous {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ 1/8)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (hc : Continuous (sphereChartCutoff2 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x) (i : Fin K) :
    Continuous (sphereFiniteCutoffProfile2 ρ hρ g i) := by
  have hD : ContinuousOn (sphereFiniteCutoffProfile2 ρ hρ g i) equalAreaEuclideanDomain2 := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have he : equalAreaEuclideanDomain2.domRestrict (sphereFiniteCutoffProfile2 ρ hρ g i) =
        fun u => sphereFiniteCutoffWeight2 ρ hρ g i
          (sphereRotationD (g i) (equalAreaEuclideanSphereChart2 u)) := by
      funext u
      exact sphereFiniteCutoffProfile2_chart ρ hρ g i u
    rw [he]
    exact (sphereFiniteCutoffWeight2_continuous ρ hρ g hc hpos i).comp
      ((sphereRotationD (g i)).continuous.comp equalAreaEuclideanSphereChart2_continuous)
  apply continuous_iff_continuousAt.mpr
  intro u
  by_cases hu : u ∈ equalAreaEuclideanDomain2
  · exact hD.continuousAt (equalAreaEuclideanDomain2_isOpen.mem_nhds hu)
  · have hn : ρ < ‖u‖ := by
      by_contra h
      exact hu (equalAreaEuclidean2_small_norm_domain u ((not_lt.mp h).trans hr))
    have he : ∀ᶠ v : EuclideanSpace ℝ (Fin 2) in 𝓝 u, ρ < ‖v‖ :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds hn
    apply (continuousAt_const : ContinuousAt (fun _ : EuclideanSpace ℝ (Fin 2) => (0 : ℝ)) u).congr_of_eventuallyEq
    filter_upwards [he] with v hv
    exact sphereFiniteCutoffProfile2_zero_of_norm ρ hρ g i v hv.le

theorem sphereEqualAreaCoordinates2_measurable : Measurable sphereEqualAreaCoordinates2 := by
  unfold sphereEqualAreaCoordinates2 equalAreaInverseD
  fun_prop

theorem rotatedSphereEqualAreaCoordinates2_measurable (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) :
    Measurable (rotatedSphereEqualAreaCoordinates2 g) :=
  sphereEqualAreaCoordinates2_measurable.comp (sphereRotationD g.symm).measurable

theorem spherePartitionSchwartzComponent2_measurable {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (hc : Continuous (sphereChartCutoff2 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) (a : ℝ) (i : Fin K) :
    Measurable (fun p : (SphereD 2) × (SphereD 2) => spherePartitionSchwartzComponent2 ρ hρ g f a i p.1 p.2) := by
  have hw := (sphereFiniteCutoffWeight2_continuous ρ hρ g hc hpos i).measurable
  have hu := rotatedSphereEqualAreaCoordinates2_measurable (g i)
  have hfu : Continuous (fun z : EuclideanSpace ℝ (Fin 2) => (f (a • z)).re) := by fun_prop
  exact ((hw.comp measurable_fst).mul (hw.comp measurable_snd)).mul
    (hfu.measurable.comp ((hu.comp measurable_fst).sub (hu.comp measurable_snd)))

theorem spherePartitionSchwartzComponent2_norm_le {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) (a : ℝ) (i : Fin K) (x y : (SphereD 2)) :
    ‖spherePartitionSchwartzComponent2 ρ hρ g f a i x y‖ ≤ SchwartzMap.seminorm ℝ 0 0 f := by
  have hx0 := sphereFiniteCutoffWeight2_nonneg ρ hρ g i x
  have hy0 := sphereFiniteCutoffWeight2_nonneg ρ hρ g i y
  have hx1 := sphereFiniteCutoffWeight2_le_one ρ hρ g hpos i x
  have hy1 := sphereFiniteCutoffWeight2_le_one ρ hρ g hpos i y
  have hw : sphereFiniteCutoffWeight2 ρ hρ g i x*sphereFiniteCutoffWeight2 ρ hρ g i y ≤ 1 := by
    simpa using mul_le_mul hx1 hy1 hy0 zero_le_one
  have hf : |(f (a • (rotatedSphereEqualAreaCoordinates2 (g i) x-
      rotatedSphereEqualAreaCoordinates2 (g i) y))).re| ≤ SchwartzMap.seminorm ℝ 0 0 f :=
    (Complex.abs_re_le_norm _).trans (SchwartzMap.norm_le_seminorm ℝ f _)
  simp only [spherePartitionSchwartzComponent2, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg hx0, abs_of_nonneg hy0]
  simpa using mul_le_mul hw hf (abs_nonneg _) zero_le_one

theorem spherePartitionSchwartzComponent2_row_integrable {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (hc : Continuous (sphereChartCutoff2 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) (a : ℝ) (i : Fin K) (x : (SphereD 2)) :
    Integrable (spherePartitionSchwartzComponent2 ρ hρ g f a i x) (sphereProbabilityD 2) := by
  apply (integrable_const (SchwartzMap.seminorm ℝ 0 0 f)).mono'
    ((spherePartitionSchwartzComponent2_measurable ρ hρ g hc hpos f a i).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact Eventually.of_forall (spherePartitionSchwartzComponent2_norm_le ρ hρ g hpos f a i x)

theorem spherePartitionSchwartzRow2_eq_sum {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (hc : Continuous (sphereChartCutoff2 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) (a : ℝ) (x : (SphereD 2)) :
    spherePartitionSchwartzRow2 ρ hρ g f a x =
      ∑ i, ∫ y, spherePartitionSchwartzComponent2 ρ hρ g f a i x y ∂(sphereProbabilityD 2) := by
  classical
  exact integral_finsetSum _ fun i _ =>
    spherePartitionSchwartzComponent2_row_integrable ρ hρ g hc hpos f a i x

theorem sphereFiniteCutoffProfile2_coordinates_on_hemisphere {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (i : Fin K) (x : (SphereD 2))
    (hx : sphereRotationD (g i).symm x ∈ equalAreaHemisphereD) :
    sphereFiniteCutoffProfile2 ρ hρ g i (rotatedSphereEqualAreaCoordinates2 (g i) x) =
      sphereFiniteCutoffWeight2 ρ hρ g i x := by
  have hd : sphereEqualAreaCoordinates2 (sphereRotationD (g i).symm x) ∈ equalAreaEuclideanDomain2 := by
    simpa only [equalAreaEuclideanDomain2, mem_preimage, sphereEqualAreaCoordinates2,
      WithLp.ofLp_toLp] using equalAreaInverseD_mem_domain _ hx
  have hchart : equalAreaEuclideanSphereChart2
      ⟨sphereEqualAreaCoordinates2 (sphereRotationD (g i).symm x),hd⟩ =
      sphereRotationD (g i).symm x := by
    apply Subtype.ext
    exact equalAreaPhiEuclidean2_inverse _ hx
  rw [rotatedSphereEqualAreaCoordinates2, sphereFiniteCutoffProfile2, dite_eq_left hd, hchart]
  rw [show sphereRotationD (g i) (sphereRotationD (g i).symm x) = x from
    (sphereRotationD (g i)).right_inv x]

theorem sphereFiniteCutoffWeight2_times_profile_eq_square {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x) (i : Fin K) (x : (SphereD 2)) :
    sphereFiniteCutoffWeight2 ρ hρ g i x*
      sphereFiniteCutoffProfile2 ρ hρ g i (rotatedSphereEqualAreaCoordinates2 (g i) x) =
      (sphereFiniteCutoffWeight2 ρ hρ g i x)^2 := by
  by_cases hx : sphereFiniteCutoffWeight2 ρ hρ g i x = 0
  · rw [hx, zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0)]
  · have hr := (sphereFiniteCutoffWeight2_ne_zero_iff ρ hρ g hpos i x).mp hx
    change sphereRotationD (g i).symm x ∈ Function.support (sphereChartCutoff2 ρ hρ) at hr
    rw [sphereChartCutoff2_support] at hr
    rw [sphereFiniteCutoffProfile2_coordinates_on_hemisphere ρ hρ g i x hr.1, pow_two]

theorem rotatedSphereEqualAreaCoordinates2_apply (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (x : (SphereD 2)) :
    rotatedSphereEqualAreaCoordinates2 g (sphereRotationD g x) = sphereEqualAreaCoordinates2 x := by
  unfold rotatedSphereEqualAreaCoordinates2
  rw [show sphereRotationD g.symm (sphereRotationD g x) = x from (sphereRotationD g).left_inv x]

theorem sphereFiniteCutoffWeight2_rotated_zero_off_hemisphere {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x) (i : Fin K) (x : (SphereD 2))
    (hx : x ∉ equalAreaHemisphereD) :
    sphereFiniteCutoffWeight2 ρ hρ g i (sphereRotationD (g i) x) = 0 := by
  by_contra hn
  have h := (sphereFiniteCutoffWeight2_ne_zero_iff ρ hρ g hpos i _).mp hn
  rw [rotatedSphereChartCutoff2_apply] at h
  have hx' : ¬ 0 < (x : (AmbientD 2)) 0 := hx
  exact h (by simp only [sphereChartCutoff2, hx', ite_false])

theorem sphereFiniteCutoffWeight2_probability_integral {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x) (i : Fin K)
    (F : EuclideanSpace ℝ (Fin 2) → ℝ) :
    (∫ x, sphereFiniteCutoffWeight2 ρ hρ g i x*F (rotatedSphereEqualAreaCoordinates2 (g i) x)
      ∂(sphereProbabilityD 2)) = ((sphereAreaD 2).real univ)⁻¹ *
      ∫ u, sphereFiniteCutoffProfile2 ρ hρ g i u*F u := by
  rw [← sphereProbability2_integral_rotation (g i)
    (fun x => sphereFiniteCutoffWeight2 ρ hρ g i x*F (rotatedSphereEqualAreaCoordinates2 (g i) x))]
  simp_rw [rotatedSphereEqualAreaCoordinates2_apply]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := equalAreaHemisphereD)
    (fun x hx => by rw [sphereFiniteCutoffWeight2_rotated_zero_off_hemisphere ρ hρ g hpos i x hx,
      zero_mul]), equalAreaEuclideanSphereChart2_probability_integral]
  simp_rw [equalAreaEuclideanSphereChart2_coordinates, ← sphereFiniteCutoffProfile2_chart]
  congr 1
  calc
    _ = ∫ u in equalAreaEuclideanDomain2, sphereFiniteCutoffProfile2 ρ hρ g i u*F u :=
      integral_subtype_comap equalAreaEuclideanDomain2_measurable
        (fun u => sphereFiniteCutoffProfile2 ρ hρ g i u*F u)
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun u hu => by rw [sphereFiniteCutoffProfile2_zero_off_domain ρ hρ g i u hu, zero_mul])

theorem spherePartitionSchwartzComponent2_row_transport {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) (a : ℝ) (i : Fin K) (x : (SphereD 2)) :
    (∫ y, spherePartitionSchwartzComponent2 ρ hρ g f a i x y ∂(sphereProbabilityD 2)) =
      sphereFiniteCutoffWeight2 ρ hρ g i x*((sphereAreaD 2).real univ)⁻¹*
        ∫ v, sphereFiniteCutoffProfile2 ρ hρ g i v*
          (f (a • (rotatedSphereEqualAreaCoordinates2 (g i) x-v))).re := by
  simp only [spherePartitionSchwartzComponent2, mul_assoc]
  rw [integral_const_mul, sphereFiniteCutoffWeight2_probability_integral ρ hρ g hpos i
    (fun v => (f (a • (rotatedSphereEqualAreaCoordinates2 (g i) x-v))).re)]

theorem spherePartitionSchwartzComponent2_scaled_row {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) {a : ℝ} (ha : 0 < a) (i : Fin K) (x : (SphereD 2)) :
    a^2*(sphereAreaD 2).real univ*
      (∫ y, spherePartitionSchwartzComponent2 ρ hρ g f a i x y ∂(sphereProbabilityD 2)) =
      sphereFiniteCutoffWeight2 ρ hρ g i x*
        compactApproximateRow (sphereFiniteCutoffProfile2 ρ hρ g i) (fun h => (f h).re) a
          (rotatedSphereEqualAreaCoordinates2 (g i) x) := by
  have hA : (sphereAreaD 2).real univ ≠ 0 := (sphereAreaD_univ_pos 2).ne'
  rw [spherePartitionSchwartzComponent2_row_transport ρ hρ g hpos,
    compactDilationRow_eq_approximateRow (sphereFiniteCutoffProfile2 ρ hρ g i)
      (fun h => (f h).re) ha (rotatedSphereEqualAreaCoordinates2 (g i) x)]
  have hap : a^2 ≠ 0 := pow_ne_zero _ ha.ne'
  field_simp

theorem spherePartitionSchwartzComponent2_scaled_row_error {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) {a : ℝ} (ha : 0 < a) (i : Fin K) (x : (SphereD 2)) :
    a^2*(sphereAreaD 2).real univ*
      (∫ y, spherePartitionSchwartzComponent2 ρ hρ g f a i x y ∂(sphereProbabilityD 2))-
      (sphereFiniteCutoffWeight2 ρ hρ g i x)^2*((𝓕 f) 0).re =
      sphereFiniteCutoffWeight2 ρ hρ g i x*
        (compactApproximateRow (sphereFiniteCutoffProfile2 ρ hρ g i) (fun h => (f h).re) a
          (rotatedSphereEqualAreaCoordinates2 (g i) x)-
          sphereFiniteCutoffProfile2 ρ hρ g i (rotatedSphereEqualAreaCoordinates2 (g i) x)*((𝓕 f) 0).re) := by
  rw [spherePartitionSchwartzComponent2_scaled_row ρ hρ g hpos f ha,
    mul_sub, ← mul_assoc, sphereFiniteCutoffWeight2_times_profile_eq_square ρ hρ g hpos]

theorem spherePartitionSchwartzRow2_uniform {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ 1/8)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (hc : Continuous (sphereChartCutoff2 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) {a : ℕ → ℝ}
    (ha : Tendsto a atTop atTop) (ha0 : ∀ n, 0 < a n) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x,
      |(a n)^2*(sphereAreaD 2).real univ*spherePartitionSchwartzRow2 ρ hρ g f (a n) x-((𝓕 f) 0).re| < ε := by
  classical
  intro ε hε
  let δ : ℝ := ε/((K : ℝ)+1)
  have hK : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hsmall : ∀ᶠ n in atTop, ∀ i : Fin K, ∀ u,
      |compactApproximateRow (sphereFiniteCutoffProfile2 ρ hρ g i) (fun h => (f h).re) (a n) u-
        sphereFiniteCutoffProfile2 ρ hρ g i u*((𝓕 f) 0).re| < δ := by
    apply eventually_all.mpr
    intro i
    exact compactSchwartzApproximateRow_uniform _
      (sphereFiniteCutoffProfile2_continuous ρ hρ hr g hc hpos i)
      (sphereFiniteCutoffProfile2_compactSupport ρ hρ g i) f ha δ hδ
  filter_upwards [hsmall] with n hn
  intro x
  have heq : (a n)^2*(sphereAreaD 2).real univ*spherePartitionSchwartzRow2 ρ hρ g f (a n) x-((𝓕 f) 0).re =
      ∑ i, ((a n)^2*(sphereAreaD 2).real univ*
        (∫ y, spherePartitionSchwartzComponent2 ρ hρ g f (a n) i x y ∂(sphereProbabilityD 2))-
        (sphereFiniteCutoffWeight2 ρ hρ g i x)^2*((𝓕 f) 0).re) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
      sphereFiniteCutoffWeight2_sum_square ρ hρ g hpos, one_mul,
      spherePartitionSchwartzRow2_eq_sum ρ hρ g hc hpos]
  rw [heq]
  calc
    _ ≤ ∑ i, |(a n)^2*(sphereAreaD 2).real univ*
        (∫ y, spherePartitionSchwartzComponent2 ρ hρ g f (a n) i x y ∂(sphereProbabilityD 2))-
        (sphereFiniteCutoffWeight2 ρ hρ g i x)^2*((𝓕 f) 0).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin K, δ := by
      apply Finset.sum_le_sum
      intro i _
      rw [spherePartitionSchwartzComponent2_scaled_row_error ρ hρ g hpos f (ha0 n), abs_mul,
        abs_of_nonneg (sphereFiniteCutoffWeight2_nonneg ρ hρ g i x)]
      calc
        _ ≤ sphereFiniteCutoffWeight2 ρ hρ g i x*δ :=
          mul_le_mul_of_nonneg_left (hn i _).le (sphereFiniteCutoffWeight2_nonneg ρ hρ g i x)
        _ ≤ δ := by
          simpa using mul_le_mul_of_nonneg_right (sphereFiniteCutoffWeight2_le_one ρ hρ g hpos i x) hδ.le
    _ = (K : ℝ)*δ := by simp [Finset.sum_const, nsmul_eq_mul]
    _ < ε := by
      dsimp [δ]
      rw [← mul_div_assoc, div_lt_iff₀ (show 0 < (K : ℝ)+1 by positivity)]
      nlinarith

theorem spherePartitionSchwartzRow2_density_uniform {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (hr : ρ ≤ 1/8) (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (hc : Continuous (sphereChartCutoff2 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) {N : ℕ → ℕ}
    (hN : Tendsto N atTop atTop) (hN0 : ∀ n, 0 < N n) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x,
      |(N n : ℝ)*spherePartitionSchwartzRow2 ρ hρ g f (spherePartitionDensityScale2 (N n)) x-
        ((𝓕 f) 0).re| < ε := by
  have h := spherePartitionSchwartzRow2_uniform ρ hρ hr g hc hpos f
    (spherePartitionDensityScale2_tendsto.comp hN) (fun n => spherePartitionDensityScale2_pos (hN0 n))
  simpa only [Function.comp_apply, spherePartitionDensityScale2_mass] using h

def spherePartitionSchwartzBackground2 {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) (a : ℝ) : ℝ :=
  ∫ x, ∫ y, spherePartitionSchwartzKernel2 ρ hρ g f a x y
    ∂(sphereProbabilityD 2) ∂(sphereProbabilityD 2)

theorem sphereProbability2_mass : (sphereProbabilityD 2) univ = 1 := measure_univ

theorem spherePartitionSchwartzComponent2_product_integrable {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (hc : Continuous (sphereChartCutoff2 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) (a : ℝ) (i : Fin K) :
    Integrable (fun p : (SphereD 2) × (SphereD 2) => spherePartitionSchwartzComponent2 ρ hρ g f a i p.1 p.2)
      ((sphereProbabilityD 2).prod (sphereProbabilityD 2)) := by
  apply (integrable_const (SchwartzMap.seminorm ℝ 0 0 f)).mono'
    (spherePartitionSchwartzComponent2_measurable ρ hρ g hc hpos f a i).aestronglyMeasurable
  exact Eventually.of_forall fun p => spherePartitionSchwartzComponent2_norm_le ρ hρ g hpos f a i p.1 p.2

theorem spherePartitionSchwartzKernel2_product_integrable {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (hc : Continuous (sphereChartCutoff2 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) (a : ℝ) :
    Integrable (fun p : (SphereD 2) × (SphereD 2) => spherePartitionSchwartzKernel2 ρ hρ g f a p.1 p.2)
      ((sphereProbabilityD 2).prod (sphereProbabilityD 2)) := by
  classical
  exact integrable_finsetSum _ fun i _ =>
    spherePartitionSchwartzComponent2_product_integrable ρ hρ g hc hpos f a i

theorem spherePartitionSchwartzRow2_integrable {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (hc : Continuous (sphereChartCutoff2 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) (a : ℝ) :
    Integrable (spherePartitionSchwartzRow2 ρ hρ g f a) (sphereProbabilityD 2) :=
  (spherePartitionSchwartzKernel2_product_integrable ρ hρ g hc hpos f a).integral_prod_left

theorem spherePartitionSchwartzBackground2_scaled_tendsto {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (hr : ρ ≤ 1/8) (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (hc : Continuous (sphereChartCutoff2 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) {a : ℕ → ℝ}
    (ha : Tendsto a atTop atTop) (ha0 : ∀ n, 0 < a n) :
    Tendsto (fun n => (a n)^2*(sphereAreaD 2).real univ*spherePartitionSchwartzBackground2 ρ hρ g f (a n))
      atTop (𝓝 ((𝓕 f) 0).re) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he := spherePartitionSchwartzRow2_uniform ρ hρ hr g hc hpos f ha ha0 (ε/2) (by positivity)
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨N,fun n hn => ?_⟩
  have hi := spherePartitionSchwartzRow2_integrable ρ hρ g hc hpos f (a n)
  have hdiff : (a n)^2*(sphereAreaD 2).real univ*spherePartitionSchwartzBackground2 ρ hρ g f (a n)-((𝓕 f) 0).re =
      ∫ x, (a n)^2*(sphereAreaD 2).real univ*spherePartitionSchwartzRow2 ρ hρ g f (a n) x-((𝓕 f) 0).re ∂(sphereProbabilityD 2) := by
    rw [integral_sub (hi.const_mul _) (integrable_const _), integral_const_mul]
    simp [spherePartitionSchwartzBackground2, spherePartitionSchwartzRow2]
  rw [Real.dist_eq, hdiff]
  have hb := norm_integral_le_of_norm_le_const (μ := (sphereProbabilityD 2))
    (f := fun x => (a n)^2*(sphereAreaD 2).real univ*spherePartitionSchwartzRow2 ρ hρ g f (a n) x-((𝓕 f) 0).re)
    (C := ε/2)
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using (hN n hn x).le)
  have hb' : |∫ x, (a n)^2*(sphereAreaD 2).real univ*spherePartitionSchwartzRow2 ρ hρ g f (a n) x-((𝓕 f) 0).re ∂(sphereProbabilityD 2)| ≤ ε/2 := by
    simpa only [Real.norm_eq_abs, measureReal_def, sphereProbability2_mass, ENNReal.toReal_one, mul_one] using hb
  exact hb'.trans_lt (by linarith)

theorem spherePartitionSchwartzBackground2_density_tendsto {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (hr : ρ ≤ 1/8) (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (hc : Continuous (sphereChartCutoff2 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) {N : ℕ → ℕ}
    (hN : Tendsto N atTop atTop) (hN0 : ∀ n, 0 < N n) :
    Tendsto (fun n => (N n : ℝ)*
      spherePartitionSchwartzBackground2 ρ hρ g f (spherePartitionDensityScale2 (N n)))
      atTop (𝓝 ((𝓕 f) 0).re) := by
  have h := spherePartitionSchwartzBackground2_scaled_tendsto ρ hρ hr g hc hpos f
    (spherePartitionDensityScale2_tendsto.comp hN) (fun n => spherePartitionDensityScale2_pos (hN0 n))
  simpa only [Function.comp_apply, spherePartitionDensityScale2_mass] using h

theorem sphereChartGaussian2_comparison (L α a : ℝ) (_hL : 0 ≤ L) (hα : 0 ≤ α)
    (x y : (SphereD 2)) (z : EuclideanSpace ℝ (Fin 2)) (hd : dist x y ≤ L*‖z‖) :
    Real.exp (-(Real.pi*(α*L^2)*‖a • z‖^2)) ≤
      sphereGaussianKernel2 (Real.pi*α*a^2) x y := by
  have hd2 : (dist x y)^2 ≤ (L*‖z‖)^2 := pow_le_pow_left₀ dist_nonneg hd 2
  have hm := mul_le_mul_of_nonneg_left hd2
    (mul_nonneg (mul_nonneg Real.pi_pos.le hα) (sq_nonneg a))
  apply Real.exp_le_exp.mpr
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at *
  nlinarith

theorem spherePartitionSchwartzComponent2_gaussian_le {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (L α a : ℝ) (hL : 0 ≤ L) (hα : 0 ≤ α)
    (hLip : ∀ i x y, sphereFiniteCutoffWeight2 ρ hρ g i x ≠ 0 →
      sphereFiniteCutoffWeight2 ρ hρ g i y ≠ 0 →
      dist x y ≤ L*‖rotatedSphereEqualAreaCoordinates2 (g i) x-
        rotatedSphereEqualAreaCoordinates2 (g i) y‖)
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ))
    (hminor : ∀ z, (f z).re ≤ Real.exp (-(Real.pi*(α*L^2)*‖z‖^2)))
    (i : Fin K) (x y : (SphereD 2)) :
    spherePartitionSchwartzComponent2 ρ hρ g f a i x y ≤
      sphereFiniteCutoffWeight2 ρ hρ g i x*sphereFiniteCutoffWeight2 ρ hρ g i y*
        sphereGaussianKernel2 (Real.pi*α*a^2) x y := by
  by_cases hx : sphereFiniteCutoffWeight2 ρ hρ g i x = 0
  · simp [spherePartitionSchwartzComponent2, hx]
  by_cases hy : sphereFiniteCutoffWeight2 ρ hρ g i y = 0
  · simp [spherePartitionSchwartzComponent2, hy]
  have h := (hminor _).trans (sphereChartGaussian2_comparison L α a hL hα x y _ (hLip i x y hx hy))
  exact mul_le_mul_of_nonneg_left h
    (mul_nonneg (sphereFiniteCutoffWeight2_nonneg ρ hρ g i x)
      (sphereFiniteCutoffWeight2_nonneg ρ hρ g i y))

theorem spherePartitionSchwartzKernel2_gaussian_le {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x)
    (L α a : ℝ) (hL : 0 ≤ L) (hα : 0 ≤ α)
    (hLip : ∀ i x y, sphereFiniteCutoffWeight2 ρ hρ g i x ≠ 0 →
      sphereFiniteCutoffWeight2 ρ hρ g i y ≠ 0 →
      dist x y ≤ L*‖rotatedSphereEqualAreaCoordinates2 (g i) x-
        rotatedSphereEqualAreaCoordinates2 (g i) y‖)
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ))
    (hminor : ∀ z, (f z).re ≤ Real.exp (-(Real.pi*(α*L^2)*‖z‖^2))) (x y : (SphereD 2)) :
    spherePartitionSchwartzKernel2 ρ hρ g f a x y ≤ sphereGaussianKernel2 (Real.pi*α*a^2) x y := by
  classical
  calc
    _ ≤ ∑ i, sphereFiniteCutoffWeight2 ρ hρ g i x*sphereFiniteCutoffWeight2 ρ hρ g i y*
        sphereGaussianKernel2 (Real.pi*α*a^2) x y :=
      Finset.sum_le_sum fun i _ => spherePartitionSchwartzComponent2_gaussian_le ρ hρ g L α a hL hα hLip f hminor i x y
    _ = (∑ i, sphereFiniteCutoffWeight2 ρ hρ g i x*sphereFiniteCutoffWeight2 ρ hρ g i y)*
        sphereGaussianKernel2 (Real.pi*α*a^2) x y := (Finset.sum_mul _ _ _).symm
    _ ≤ 1*sphereGaussianKernel2 (Real.pi*α*a^2) x y :=
      mul_le_mul_of_nonneg_right (sphereFiniteCutoffWeight2_correlation_le_one ρ hρ g hpos x y)
        (sphereGaussianKernel2_nonneg _ _ _)
    _ = _ := one_mul _

theorem spherePartitionSchwartzKernel2_diagonal {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) (a : ℝ) (x : (SphereD 2)) :
    spherePartitionSchwartzKernel2 ρ hρ g f a x x = (f 0).re := by
  classical
  simp only [spherePartitionSchwartzKernel2, spherePartitionSchwartzComponent2,
    sub_self, smul_zero, ← pow_two]
  rw [← Finset.sum_mul, sphereFiniteCutoffWeight2_sum_square ρ hρ g hpos, one_mul]

theorem spherePartitionSchwartzKernel2_diagonal_corrected_sum_le {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x) (X : Fin N → (SphereD 2))
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) (a t : ℝ)
    (hminor : ∀ x y, spherePartitionSchwartzKernel2 ρ hρ g f a x y ≤ sphereGaussianKernel2 t x y) :
    (∑ p, ∑ q, spherePartitionSchwartzKernel2 ρ hρ g f a (X p) (X q))+
      (N : ℝ)*(1-(f 0).re) ≤ ∑ p, ∑ q, sphereGaussianKernel2 t (X p) (X q) := by
  classical
  have hpq (p q : Fin N) : spherePartitionSchwartzKernel2 ρ hρ g f a (X p) (X q)+
      (if p=q then 1-(f 0).re else 0) ≤ sphereGaussianKernel2 t (X p) (X q) := by
    by_cases h : p=q
    · subst q
      simp only [spherePartitionSchwartzKernel2_diagonal ρ hρ g hpos,
        sphereGaussianKernel2_self, ↓reduceIte]
      linarith
    · simpa only [ite_eq_right h, add_zero] using hminor (X p) (X q)
  have hs := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset (Fin N))) =>
    Finset.sum_le_sum (fun q (_ : q ∈ (Finset.univ : Finset (Fin N))) => hpq p q))
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hs

def spherePartitionSchwartzDefect2 {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (X : Fin N → (SphereD 2))
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) (a : ℝ) : ℝ :=
  (∑ p, ∑ q, spherePartitionSchwartzKernel2 ρ hρ g f a (X p) (X q))-
    2*(N : ℝ)*(∑ p, spherePartitionSchwartzRow2 ρ hρ g f a (X p))+
    (N : ℝ)^2*spherePartitionSchwartzBackground2 ρ hρ g f a

theorem sphereCutoff2_integrable (χ : (SphereD 2) → ℝ) (hχmeas : Measurable χ)
    (hχnonneg : ∀ x, 0 ≤ χ x) (hχle : ∀ x, χ x ≤ 1)
    (μ : Measure (SphereD 2)) [IsFiniteMeasure μ] : Integrable χ μ := by
  apply (integrable_const (1 : ℝ)).mono' hχmeas.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (hχnonneg x)]
  exact hχle x

def spherePartitionSchwartzComponentDefect2 {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (X : Fin N → (SphereD 2))
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) (a : ℝ) (i : Fin K) : ℝ :=
  (∑ p, ∑ q, spherePartitionSchwartzComponent2 ρ hρ g f a i (X p) (X q))-
    2*(N : ℝ)*(∑ p, ∫ y, spherePartitionSchwartzComponent2 ρ hρ g f a i (X p) y ∂(sphereProbabilityD 2))+
    (N : ℝ)^2*(∫ x, ∫ y, spherePartitionSchwartzComponent2 ρ hρ g f a i x y
      ∂(sphereProbabilityD 2) ∂(sphereProbabilityD 2))

def spherePointMeasure2 {N : ℕ} (X : Fin N → (SphereD 2)) : Measure (SphereD 2) :=
  ∑ i, Measure.dirac (X i)

instance spherePointMeasure2_finite {N : ℕ} (X : Fin N → (SphereD 2)) :
    IsFiniteMeasure (spherePointMeasure2 X) := by
  unfold spherePointMeasure2
  infer_instance

theorem spherePointMeasure2_integral {N : ℕ} (X : Fin N → (SphereD 2))
    (g : (SphereD 2) → ℝ) : (∫ x, g x ∂spherePointMeasure2 X) = ∑ i, g (X i) := by
  unfold spherePointMeasure2
  rw [integral_finsetSum_measure (fun i _ => integrable_dirac (by simp))]
  simp only [integral_dirac]

theorem spherePartitionSchwartzComponentDefect2_eq_localized {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (X : Fin N → (SphereD 2))
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) (a : ℝ) (i : Fin K) :
    spherePartitionSchwartzComponentDefect2 ρ hρ g X f a i =
      localizedSchwartzDefect f a N (sphereFiniteCutoffWeight2 ρ hρ g i)
        (rotatedSphereEqualAreaCoordinates2 (g i)) (spherePointMeasure2 X) (sphereProbabilityD 2) := by
  unfold spherePartitionSchwartzComponentDefect2 localizedSchwartzDefect localizedSchwartzPair
    spherePartitionSchwartzComponent2
  simp only [spherePointMeasure2_integral]

theorem spherePartitionSchwartzComponentDefect2_nonneg {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (hc : Continuous (sphereChartCutoff2 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x) (X : Fin N → (SphereD 2))
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ))
    (hFnonneg : ∀ z, 0 ≤ ((𝓕 f) z).re) (hFreal : ∀ z, ((𝓕 f) z).im = 0)
    (a : ℝ) (i : Fin K) :
    0 ≤ spherePartitionSchwartzComponentDefect2 ρ hρ g X f a i := by
  have hmeas := (sphereFiniteCutoffWeight2_continuous ρ hρ g hc hpos i).measurable
  have hn := sphereFiniteCutoffWeight2_nonneg ρ hρ g i
  have hle := sphereFiniteCutoffWeight2_le_one ρ hρ g hpos i
  rw [spherePartitionSchwartzComponentDefect2_eq_localized]
  exact localizedSchwartzDefect_nonneg f hFnonneg hFreal a N _ _ _ _ hmeas hn
    (rotatedSphereEqualAreaCoordinates2_measurable (g i))
    (sphereCutoff2_integrable _ hmeas hn hle _)
    (sphereCutoff2_integrable _ hmeas hn hle _)

theorem spherePartitionSchwartzKernel2_point_sum {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (X : Fin N → (SphereD 2))
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) (a : ℝ) :
    (∑ p, ∑ q, spherePartitionSchwartzKernel2 ρ hρ g f a (X p) (X q)) =
      ∑ i, ∑ p, ∑ q, spherePartitionSchwartzComponent2 ρ hρ g f a i (X p) (X q) := by
  classical
  unfold spherePartitionSchwartzKernel2
  calc
    _ = ∑ p, ∑ i, ∑ q, spherePartitionSchwartzComponent2 ρ hρ g f a i (X p) (X q) := by
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem spherePartitionSchwartzRow2_point_sum {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (hc : Continuous (sphereChartCutoff2 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x) (X : Fin N → (SphereD 2))
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) (a : ℝ) :
    (∑ p, spherePartitionSchwartzRow2 ρ hρ g f a (X p)) =
      ∑ i, ∑ p, ∫ y, spherePartitionSchwartzComponent2 ρ hρ g f a i (X p) y ∂(sphereProbabilityD 2) := by
  classical
  simp_rw [spherePartitionSchwartzRow2_eq_sum ρ hρ g hc hpos]
  exact Finset.sum_comm

theorem spherePartitionSchwartzBackground2_eq_sum {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (hc : Continuous (sphereChartCutoff2 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x)
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) (a : ℝ) :
    spherePartitionSchwartzBackground2 ρ hρ g f a =
      ∑ i, ∫ x, ∫ y, spherePartitionSchwartzComponent2 ρ hρ g f a i x y ∂(sphereProbabilityD 2) ∂(sphereProbabilityD 2) := by
  classical
  change (∫ x, spherePartitionSchwartzRow2 ρ hρ g f a x ∂(sphereProbabilityD 2)) = _
  simp_rw [spherePartitionSchwartzRow2_eq_sum ρ hρ g hc hpos]
  exact integral_finsetSum _ fun i _ =>
    (spherePartitionSchwartzComponent2_product_integrable ρ hρ g hc hpos f a i).integral_prod_left

theorem spherePartitionSchwartzDefect2_eq_sum {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (hc : Continuous (sphereChartCutoff2 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x) (X : Fin N → (SphereD 2))
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ)) (a : ℝ) :
    spherePartitionSchwartzDefect2 ρ hρ g X f a =
      ∑ i, spherePartitionSchwartzComponentDefect2 ρ hρ g X f a i := by
  classical
  rw [spherePartitionSchwartzDefect2, spherePartitionSchwartzKernel2_point_sum,
    spherePartitionSchwartzRow2_point_sum ρ hρ g hc hpos,
    spherePartitionSchwartzBackground2_eq_sum ρ hρ g hc hpos]
  simp only [spherePartitionSchwartzComponentDefect2, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum]

theorem spherePartitionSchwartzDefect2_nonneg {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (hc : Continuous (sphereChartCutoff2 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x) (X : Fin N → (SphereD 2))
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ))
    (hFnonneg : ∀ z, 0 ≤ ((𝓕 f) z).re) (hFreal : ∀ z, ((𝓕 f) z).im = 0) (a : ℝ) :
    0 ≤ spherePartitionSchwartzDefect2 ρ hρ g X f a := by
  rw [spherePartitionSchwartzDefect2_eq_sum ρ hρ g hc hpos]
  exact Finset.sum_nonneg fun i _ =>
    spherePartitionSchwartzComponentDefect2_nonneg ρ hρ g hc hpos X f hFnonneg hFreal a i

theorem spherePartitionSchwartzKernel2_normalized_lower {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (hc : Continuous (sphereChartCutoff2 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x) (hN : 0 < N) (X : Fin N → (SphereD 2))
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ))
    (hFnonneg : ∀ z, 0 ≤ ((𝓕 f) z).re) (hFreal : ∀ z, ((𝓕 f) z).im = 0) (a : ℝ) :
    2*(∑ p, spherePartitionSchwartzRow2 ρ hρ g f a (X p))-
      (N : ℝ)*spherePartitionSchwartzBackground2 ρ hρ g f a ≤
      (∑ p, ∑ q, spherePartitionSchwartzKernel2 ρ hρ g f a (X p) (X q))/(N : ℝ) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hd := spherePartitionSchwartzDefect2_nonneg ρ hρ g hc hpos X f hFnonneg hFreal a
  unfold spherePartitionSchwartzDefect2 at hd
  apply (le_div_iff₀ hNR).mpr
  nlinarith

theorem spherePartitionGaussian2_normalized_lower {K N : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (hc : Continuous (sphereChartCutoff2 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x) (hN : 0 < N) (X : Fin N → (SphereD 2))
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ))
    (hFnonneg : ∀ z, 0 ≤ ((𝓕 f) z).re) (hFreal : ∀ z, ((𝓕 f) z).im = 0) (a t : ℝ)
    (hminor : ∀ x y, spherePartitionSchwartzKernel2 ρ hρ g f a x y ≤ sphereGaussianKernel2 t x y) :
    2*(∑ p, spherePartitionSchwartzRow2 ρ hρ g f a (X p))-
      (N : ℝ)*spherePartitionSchwartzBackground2 ρ hρ g f a+1-(f 0).re ≤
      (∑ p, ∑ q, sphereGaussianKernel2 t (X p) (X q))/(N : ℝ) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hs := spherePartitionSchwartzKernel2_diagonal_corrected_sum_le ρ hρ g hpos X f a t hminor
  have hd := spherePartitionSchwartzKernel2_normalized_lower ρ hρ g hc hpos hN X f hFnonneg hFreal a
  have hs' := div_le_div_of_nonneg_right hs hNR.le
  have he : ((∑ p, ∑ q, spherePartitionSchwartzKernel2 ρ hρ g f a (X p) (X q))+
      (N : ℝ)*(1-(f 0).re))/(N : ℝ) =
      (∑ p, ∑ q, spherePartitionSchwartzKernel2 ρ hρ g f a (X p) (X q))/(N : ℝ)+1-(f 0).re := by
    field_simp [hNR.ne']
    ring
  rw [he] at hs'
  linarith

theorem sphereGaussianScale2_eq_partition_density (N : ℕ) (α : ℝ) :
    sphereGaussianScale2 N α = Real.pi*α*(spherePartitionDensityScale2 N)^2 := by
  rw [spherePartitionDensityScale2_pow, sphereGaussianScale2, Real.rpow_one]

theorem sphereGaussian2_uniform_lower_of_schwartz {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (hr : ρ ≤ 1/8) (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (hc : Continuous (sphereChartCutoff2 ρ hρ))
    (hpos : ∀ x, 0 < sphereFiniteCutoffMass2 ρ hρ g x)
    (L α : ℝ) (hL : 0 ≤ L) (hα : 0 ≤ α)
    (hLip : ∀ i x y, sphereFiniteCutoffWeight2 ρ hρ g i x ≠ 0 →
      sphereFiniteCutoffWeight2 ρ hρ g i y ≠ 0 →
      dist x y ≤ L*‖rotatedSphereEqualAreaCoordinates2 (g i) x-
        rotatedSphereEqualAreaCoordinates2 (g i) y‖)
    (f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ))
    (hFnonneg : ∀ z, 0 ≤ ((𝓕 f) z).re) (hFreal : ∀ z, ((𝓕 f) z).im = 0)
    (hminor : ∀ z, (f z).re ≤ Real.exp (-(Real.pi*(α*L^2)*‖z‖^2)))
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) (hN0 : ∀ k, 0 < N k) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ X : Fin (N k) → (SphereD 2),
      ((𝓕 f) 0).re+1-(f 0).re-ε ≤
        (∑ p, ∑ q, sphereGaussianKernel2 (sphereGaussianScale2 (N k) α) (X p) (X q))/(N k : ℝ) := by
  intro ε hε
  let δ : ℝ := ε/4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hrow := spherePartitionSchwartzRow2_density_uniform ρ hρ hr g hc hpos f hN hN0 δ hδ
  have hbg : ∀ᶠ k in atTop, (N k : ℝ)*
      spherePartitionSchwartzBackground2 ρ hρ g f (spherePartitionDensityScale2 (N k)) < ((𝓕 f) 0).re+δ :=
    (tendsto_order.mp (spherePartitionSchwartzBackground2_density_tendsto ρ hρ hr g hc hpos f hN hN0)).2
      _ (by linarith)
  filter_upwards [hrow,hbg] with k hk hb
  intro X
  have hmin : ∀ x y, spherePartitionSchwartzKernel2 ρ hρ g f (spherePartitionDensityScale2 (N k)) x y ≤
      sphereGaussianKernel2 (sphereGaussianScale2 (N k) α) x y := by
    intro x y
    rw [sphereGaussianScale2_eq_partition_density]
    exact spherePartitionSchwartzKernel2_gaussian_le ρ hρ g hpos L α _ hL hα hLip f hminor x y
  have hsum := spherePartitionSchwartzRow2_sum_lower ρ hρ g (hN0 k) X f _ _ _ hk
  have hd := spherePartitionGaussian2_normalized_lower ρ hρ g hc hpos (hN0 k) X f
    hFnonneg hFreal (spherePartitionDensityScale2 (N k)) (sphereGaussianScale2 (N k) α) hmin
  dsimp [δ] at *
  linarith

theorem hexGaussianThetaReal2_exists_near_one_dilation {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) :
    ∃ L : ℝ, 1 < L ∧ hexGaussianThetaReal2 α-ε < hexGaussianThetaReal2 (α*L^2) := by
  have hc : ContinuousAt hexGaussianThetaReal2 α :=
    hexGaussianThetaReal2_continuousOn.continuousAt (isOpen_Ioi.mem_nhds hα)
  have hL : Tendsto (fun L : ℝ => α*L^2) (𝓝[>] (1 : ℝ)) (𝓝 α) := by
    have h : ContinuousAt (fun L : ℝ => α*L^2) 1 := by fun_prop
    simpa only [one_pow, mul_one] using h.tendsto.mono_left nhdsWithin_le_nhds
  have ht := hc.tendsto.comp hL
  have he : ∀ᶠ L in 𝓝[>] (1 : ℝ), hexGaussianThetaReal2 α-ε < hexGaussianThetaReal2 (α*L^2) :=
    (tendsto_order.mp ht).1 _ (by linarith)
  have hlo : ∀ᶠ L in 𝓝[>] (1 : ℝ), 1 < L := self_mem_nhdsWithin
  exact (hlo.and he).exists

/-- The all-scale Gaussian input of the triangular lattice: for every `β > 0` a Schwartz minorant
of `exp(-π β |x|²)` with real nonnegative Fourier transform and the sharp value
`𝓕 f(0) - f(0) = Θ(β) - 1`.  A statement; it follows from Gaussian certificates below. -/
def HexSharpGaussianSchwartzInput2 : Prop :=
  ∀ β : ℝ, 0 < β → ∃ f : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ),
    (∀ z, 0 ≤ ((𝓕 f) z).re) ∧
    (∀ z, ((𝓕 f) z).im = 0) ∧
    (∀ z, (f z).re ≤ Real.exp (-(Real.pi*β*‖z‖^2))) ∧
    ((𝓕 f) 0).re-(f 0).re = hexGaussianThetaReal2 β-1

/-- The sharp lower Gaussian profile of `S²` from the all-scale Schwartz input. -/
theorem sphereGaussianSharpProfileLower2_of_schwartz_input (hG : HexSharpGaussianSchwartzInput2) :
    SphereGaussianSharpProfileLower2 := by
  intro N hN hN0 X α hα ε hε
  obtain ⟨L,hL,hθ⟩ := hexGaussianThetaReal2_exists_near_one_dilation hα (by positivity : 0 < ε/2)
  obtain ⟨ρ,hρ,hρ',hr,K,g,hc,hpos,_hwc,_hw,_hpart,hLip⟩ :=
    sphere2_exists_finite_cutoff_square_partition L hL
  have hL0 : 0 < L := zero_lt_one.trans hL
  obtain ⟨f,hFnonneg,hFreal,hminor,hvalue⟩ := hG (α*L^2) (by positivity)
  have he := sphereGaussian2_uniform_lower_of_schwartz ρ hρ' hr g hc hpos L α hL0.le hα.le
    hLip f hFnonneg hFreal hminor hN hN0 (ε/2) (by positivity)
  filter_upwards [he] with k hk
  have hx := hk (fun i => X k i)
  change hexGaussianThetaReal2 α-ε ≤
    (∑ p, ∑ q, sphereGaussianKernel2 (sphereGaussianScale2 (N k) α) (X k p) (X k q))/(N k : ℝ)
  linarith

/-- Gaussian certificates of the triangular lattice (contact on the lattice, Fourier zeros on
the dual lattice) give the sharp Schwartz input: the value is Poisson summation. -/
theorem hexSharpGaussianSchwartzInput2_of_contact
    (h : ∀ β : ℝ, 0 < β → ∃ f, HexGaussianContactCertificate2 β f) :
    HexSharpGaussianSchwartzInput2 := by
  intro β hβ
  obtain ⟨f, hf⟩ := h β hβ
  exact ⟨f, hf.fourier_nonneg, hf.fourier_real, fun z => hf.minorant z, hf.value hβ⟩

/-- The universal Gaussian profile lower bound on `S²` from Gaussian certificates of the
triangular lattice at all scales. -/
theorem sphereGaussianSharpProfileLower2_of_contact
    (h : ∀ β : ℝ, 0 < β → ∃ f, HexGaussianContactCertificate2 β f) :
    SphereGaussianSharpProfileLower2 :=
  sphereGaussianSharpProfileLower2_of_schwartz_input (hexSharpGaussianSchwartzInput2_of_contact h)

end SphericalRiesz
end
end

section

/-! # The Gaussian background of `S²` and the Gaussian defect (stage S2-2)

Dimension-2 port of `SphereGaussianBackground24`, on the unit sphere `S² ⊂ ℝ³` with its uniform
probability measure `σ`.

* `sphereGaussianPotential2 t x = ∫ exp(-t |x - y|²) dσ(y)` does not depend on `x` (rotations),
  and equals the background `sphereGaussianBackground2 t = ∫∫ exp(-t |x - y|²) dσ dσ ∈ [0, 1]`.
* `sphereGaussianDefect2 t M X = Σ_{i,j} K(x_i, x_j) - 2 M Σ_i U(x_i) + M² B` is the Gaussian
  energy of the signed measure `Σ δ_{x_i} - M σ`; it is an integral of a squared modulus against
  the standard Gaussian measure of `ℝ³`, hence nonnegative, and for `M = N` it is
  `Σ_{i,j} K(x_i, x_j) - N² B`.

No positive-definiteness hypothesis is assumed: it is proved through the characteristic function
of the image of `σ` in `ℝ³`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ComplexConjugate
namespace SphericalRiesz

theorem sphereGaussianKernel2_eq_ambient (t : ℝ) (x y : (SphereD 2)) :
    sphereGaussianKernel2 t x y = gaussianKernel t (x:(AmbientD 2)) (y:(AmbientD 2)) := by
  change Real.exp (-(t*(dist (x:(AmbientD 2)) (y:(AmbientD 2)))^2)) = _
  rw [dist_eq_norm]
  rfl

theorem sphereGaussianKernel2_le_one {t : ℝ} (ht : 0 ≤ t) (x y : (SphereD 2)) :
    sphereGaussianKernel2 t x y ≤ 1 := by
  rw [sphereGaussianKernel2_eq_ambient]
  exact gaussianKernel_le_one ht _ _

theorem sphereGaussianKernel2_rotation (t : ℝ) (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (x y : (SphereD 2)) :
    sphereGaussianKernel2 t (sphereRotationD g x) (sphereRotationD g y) =
      sphereGaussianKernel2 t x y := by
  unfold sphereGaussianKernel2
  rw [sphereRotationD_dist]

theorem sphereGaussianKernel2_integrable {t : ℝ} (ht : 0 ≤ t) (x : (SphereD 2)) :
    Integrable (sphereGaussianKernel2 t x) (sphereProbabilityD 2) := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold sphereGaussianKernel2; fun_prop)
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (sphereGaussianKernel2_nonneg _ _ _)]
  exact sphereGaussianKernel2_le_one ht x y

theorem sphereGaussianKernel2_pair_integrable {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun p : (SphereD 2) × (SphereD 2) => sphereGaussianKernel2 t p.1 p.2)
      ((sphereProbabilityD 2).prod (sphereProbabilityD 2)) := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold sphereGaussianKernel2; fun_prop)
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (sphereGaussianKernel2_nonneg _ _ _)]
  exact sphereGaussianKernel2_le_one ht p.1 p.2

/-- The Gaussian potential of the uniform measure of `S²` at the point `x`. -/
def sphereGaussianPotential2 (t : ℝ) (x : (SphereD 2)) : ℝ :=
  ∫ y, sphereGaussianKernel2 t x y ∂(sphereProbabilityD 2)

/-- The Gaussian background (self-energy of the uniform measure) of `S²`. -/
def sphereGaussianBackground2 (t : ℝ) : ℝ :=
  ∫ p : (SphereD 2) × (SphereD 2), sphereGaussianKernel2 t p.1 p.2
    ∂(sphereProbabilityD 2).prod (sphereProbabilityD 2)

theorem sphereGaussianPotential2_rotation (t : ℝ) (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (x : (SphereD 2)) :
    sphereGaussianPotential2 t (sphereRotationD g x) = sphereGaussianPotential2 t x := by
  unfold sphereGaussianPotential2
  rw [← sphereProbability2_integral_rotation g (sphereGaussianKernel2 t (sphereRotationD g x))]
  simp_rw [sphereGaussianKernel2_rotation]

theorem sphereGaussianPotential2_constant (t : ℝ) (x y : (SphereD 2)) :
    sphereGaussianPotential2 t x = sphereGaussianPotential2 t y := by
  obtain ⟨g, hg⟩ := sphereRotation2_transitive x y
  calc
    _ = sphereGaussianPotential2 t (sphereRotationD g x) :=
      (sphereGaussianPotential2_rotation t g x).symm
    _ = _ := by rw [hg]

theorem sphereGaussianBackground2_iterated {t : ℝ} (ht : 0 ≤ t) :
    sphereGaussianBackground2 t = ∫ x, sphereGaussianPotential2 t x ∂(sphereProbabilityD 2) := by
  exact integral_prod _ (sphereGaussianKernel2_pair_integrable ht)

theorem sphereGaussianBackground2_eq_potential {t : ℝ} (ht : 0 ≤ t) (p : (SphereD 2)) :
    sphereGaussianBackground2 t = sphereGaussianPotential2 t p := by
  rw [sphereGaussianBackground2_iterated ht]
  calc
    _ = ∫ x : (SphereD 2), sphereGaussianPotential2 t p ∂(sphereProbabilityD 2) :=
      integral_congr_ae (.of_forall fun x => sphereGaussianPotential2_constant t x p)
    _ = _ := by simp

theorem sphereGaussianBackground2_nonneg (t : ℝ) : 0 ≤ sphereGaussianBackground2 t :=
  integral_nonneg fun p => sphereGaussianKernel2_nonneg t p.1 p.2

theorem sphereGaussianBackground2_le_one {t : ℝ} (ht : 0 ≤ t) :
    sphereGaussianBackground2 t ≤ 1 := by
  calc
    sphereGaussianBackground2 t ≤
        ∫ _ : (SphereD 2) × (SphereD 2), (1:ℝ) ∂(sphereProbabilityD 2).prod (sphereProbabilityD 2) :=
      integral_mono (sphereGaussianKernel2_pair_integrable ht) (integrable_const (1:ℝ))
        (fun p => sphereGaussianKernel2_le_one ht p.1 p.2)
    _ = 1 := by simp

/-- The uniform probability measure of `S²` as a measure on `ℝ³`. -/
def ambientSphereProbability2 : Measure (AmbientD 2) :=
  (sphereProbabilityD 2).map (fun x : (SphereD 2) => (x:(AmbientD 2)))

instance ambientSphereProbability2_probability : IsProbabilityMeasure ambientSphereProbability2 := by
  unfold ambientSphereProbability2
  infer_instance

theorem ambientSphereProbability2_charFun (z : (AmbientD 2)) :
    charFun ambientSphereProbability2 z =
      ∫ y : (SphereD 2), Complex.exp (⟪(y:(AmbientD 2)), z⟫ * Complex.I) ∂(sphereProbabilityD 2) := by
  rw [charFun_apply, ambientSphereProbability2, integral_map (by fun_prop) (by fun_prop)]

theorem ambientSphereProbability2_kernel_integral (t : ℝ) (x : (SphereD 2)) :
    (∫ y : (AmbientD 2), gaussianKernel t (x:(AmbientD 2)) y ∂ambientSphereProbability2) =
      sphereGaussianPotential2 t x := by
  rw [ambientSphereProbability2, integral_map (by fun_prop) (by unfold gaussianKernel; fun_prop)]
  simp only [sphereGaussianPotential2, sphereGaussianKernel2_eq_ambient]

theorem ambientSphereProbability2_kernel_pair (t : ℝ) :
    gaussianMeasurePair t ambientSphereProbability2 ambientSphereProbability2 =
      sphereGaussianBackground2 t := by
  unfold gaussianMeasurePair ambientSphereProbability2
  rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    integral_map (by fun_prop) (by unfold gaussianKernel; fun_prop)]
  simp only [sphereGaussianBackground2, sphereGaussianKernel2_eq_ambient,
    Prod.map_fst, Prod.map_snd]

/-- The Gaussian energy of the signed measure `Σ δ_{X i} - M σ` on `S²`. -/
def sphereGaussianDefect2 {N : ℕ} (t M : ℝ) (X : (ConfigurationD 2) N) : ℝ :=
  (∑ i, ∑ j, sphereGaussianKernel2 t (X i) (X j)) -
    2*M*(∑ i, sphereGaussianPotential2 t (X i)) + M^2*sphereGaussianBackground2 t

theorem sphereGaussianDefect2_eq_diffuse {N : ℕ} {t : ℝ} (_ht : 0 ≤ t)
    (M : ℝ) (X : (ConfigurationD 2) N) :
    sphereGaussianDefect2 t M X = diffuseGaussianDefect t M
      (fun i : Fin N => (X i:(AmbientD 2))) ambientSphereProbability2 := by
  unfold sphereGaussianDefect2 diffuseGaussianDefect
  simp only [sphereGaussianKernel2_eq_ambient, ambientSphereProbability2_kernel_integral,
    ambientSphereProbability2_kernel_pair]

theorem sphereGaussianDefect2_eq_normSq {N : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (M : ℝ) (X : (ConfigurationD 2) N) :
    sphereGaussianDefect2 t M X = ∫ z : (AmbientD 2),
      Complex.normSq ((∑ i : Fin N,
        Complex.exp (⟪(X i:(AmbientD 2)), Real.sqrt (2*t) • z⟫ * Complex.I)) -
        (M:ℂ)*(∫ y : (SphereD 2),
          Complex.exp (⟪(y:(AmbientD 2)), Real.sqrt (2*t) • z⟫ * Complex.I) ∂(sphereProbabilityD 2)))
      ∂stdGaussian (AmbientD 2) := by
  rw [sphereGaussianDefect2_eq_diffuse ht, diffuseGaussianDefect_eq_normSq ht]
  simp only [ambientSphereProbability2_charFun]

theorem sphereGaussianDefect2_nonneg {N : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (M : ℝ) (X : (ConfigurationD 2) N) : 0 ≤ sphereGaussianDefect2 t M X := by
  rw [sphereGaussianDefect2_eq_diffuse ht]
  exact diffuseGaussianDefect_nonneg ht M _ _

theorem sphereGaussianDefect2_charge_N {N : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (X : (ConfigurationD 2) N) :
    sphereGaussianDefect2 t (N:ℝ) X =
      (∑ i, ∑ j, sphereGaussianKernel2 t (X i) (X j)) - (N:ℝ)^2*sphereGaussianBackground2 t := by
  unfold sphereGaussianDefect2
  simp_rw [← sphereGaussianBackground2_eq_potential ht]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end SphericalRiesz
end
end
