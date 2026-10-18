import Riesz.EqualAreaMeasureD
import Riesz.PatchSupportD
import Riesz.HexLattice2
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Data.Finset.Lattice.Fold
import Riesz.EqualAreaInverseD
import Riesz.ExactMassSlices
import Riesz.SphereMeasureD
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Equal-area geometry on S² for the triangular lattice (stage S2-2 of the S² chain; dimension-2
counterparts of the fifteen geometry modules of the S²⁴ chain).

The parts, in dependency order: the rescaled equal-area chart and its flat limit
(`EqualAreaRescaling2`, `EqualAreaRescalingLimit2`, `EqualAreaRescalingGeometry2`), moving
charts with uniform derivative bounds (`EqualAreaMovingRescaling2`, `EqualAreaMovingBounds2`,
`EqualAreaMovingHigherBounds2`), the class of small patches and affine cubes
(`EqualAreaPatchClass2`, `EqualAreaAffine2`), exact patch measure and transport
(`EqualAreaPatchMeasure2`, `EqualAreaPatchTransport2`), finite patch families
(`EqualAreaFinitePatchGeometry2`, `EqualAreaFinitePatchMass2`), coordinate buffers
(`EqualAreaCoordinateBuffers2`), equal-mass residual cells (`SphereResidualCells2`) and the
rational size ceiling `(d m)²` (`RationalSizeCeiling2`).

The statements are those of dimension 24 with `d = 2` (`d - 1 = 1`, ambient space `ℝ³`) and the
coordinate map `hexMap` of the triangular lattice in place of the Leech map.  No certificate and
no energy statement appears here. -/

section

/-! Rescaling of the exact-area chart of S² along the triangular lattice (stage S2-2).

The chart `equalAreaPhiD` of `S²` is composed with `ε • hexMap`, the coordinate map of the
triangular lattice of covolume one scaled by `ε`.  Local linear composition and compact bounds
keep the high-order derivative expressions intact; no coordinate expansion of the derivatives is
required.  Dimension-2 counterpart of `EqualAreaRescaling24`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace SphericalRiesz
open Boundary

def equalAreaHexChart (ε : ℝ) (x : Fin 2 → ℝ) : (AmbientD 2) :=
  equalAreaPhiD (ε • hexMap x)

def equalAreaNormalizedHexChart (ε : ℝ) (x : Fin 2 → ℝ) : (AmbientD 2) :=
  ε⁻¹ • (equalAreaHexChart ε x-equalAreaPhiD 0)

def equalAreaScaleRadius2 : ℝ := 1+‖hexMap‖

theorem equalAreaScaleRadius2_pos : 0 < equalAreaScaleRadius2 := by
  unfold equalAreaScaleRadius2
  positivity

theorem equalAreaSquaredNorm2_le_pi_norm (p : Fin 2 → ℝ) :
    equalAreaSquaredNormD p ≤ 1*‖p‖^2 := by
  calc
    _ ≤ ∑ _j : Fin 1, ‖p‖^2 := by
      apply Finset.sum_le_sum
      intro j _
      have h := norm_le_pi_norm p j.succ
      simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = _ := by simp

theorem equalArea2_small_norm_domain (p : Fin 2 → ℝ) (hp : ‖p‖ ≤ 1/8) :
    equalAreaSquaredNormD p < 1 := by
  have h := equalAreaSquaredNorm2_le_pi_norm p
  have hn := norm_nonneg p
  nlinarith

theorem equalAreaPhi2_contDiffAt (p : Fin 2 → ℝ) (hp : equalAreaSquaredNormD p < 1) :
    ContDiffAt ℝ ∞ equalAreaPhiD p := by
  have hq : Continuous (equalAreaSquaredNormD (n := 1)) := by unfold equalAreaSquaredNormD; fun_prop
  exact (equalAreaPhiD_contDiffOn p hp).contDiffAt ((isOpen_lt hq continuous_const).mem_nhds hp)

theorem equalAreaPhi2_iterated_derivatives_bounded (k : ℕ) :
    ∃ C ≥ 0, ∀ p : Fin 2 → ℝ, ‖p‖ ≤ 1/8 → ‖iteratedFDeriv ℝ k equalAreaPhiD p‖ ≤ C := by
  have hc : ContinuousOn (iteratedFDeriv ℝ k equalAreaPhiD)
      (Metric.closedBall (0 : Fin 2 → ℝ) (1/8)) := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    apply (equalAreaPhi2_contDiffAt p (equalArea2_small_norm_domain p
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hp))).continuousAt_iteratedFDeriv
    simp
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Fin 2 → ℝ) (1/8)).exists_bound_of_continuousOn hc
  exact ⟨max C 0,le_max_right _ _,fun p hp => (hC p
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hp)).trans (le_max_left _ _)⟩

/-- Local form of the linear-composition chain rule, for the actual
iterated derivative rather than a derivative supplied as an input. -/
theorem equalAreaPhi2_iterated_comp_linear (L : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ))
    (x : Fin 2 → ℝ) (hx : equalAreaSquaredNormD (L x) < 1) (k : ℕ) :
    iteratedFDeriv ℝ k (equalAreaPhiD ∘ L) x =
      (iteratedFDeriv ℝ k equalAreaPhiD (L x)).compContinuousLinearMap (fun _ => L) := by
  have hq : Continuous (equalAreaSquaredNormD (n := 1)) := by unfold equalAreaSquaredNormD; fun_prop
  have hu : IsOpen {p | equalAreaSquaredNormD p < 1} := isOpen_lt hq continuous_const
  have hp := hu.preimage L.continuous
  have h := L.iteratedFDerivWithin_comp_right equalAreaPhiD_contDiffOn
    hu.uniqueDiffOn hp.uniqueDiffOn hx (i := k) (by simp)
  rw [iteratedFDerivWithin_of_isOpen k hp hx,
    iteratedFDerivWithin_of_isOpen k hu hx] at h
  exact h

theorem equalAreaHexChart_contDiffAt (ε : ℝ) (x : Fin 2 → ℝ)
    (hx : equalAreaSquaredNormD (ε • hexMap x) < 1) :
    ContDiffAt ℝ ∞ (equalAreaHexChart ε) x :=
  (equalAreaPhi2_contDiffAt _ hx).comp x (by fun_prop)

theorem equalAreaNormalizedHexChart_contDiffAt (ε : ℝ) (x : Fin 2 → ℝ)
    (hx : equalAreaSquaredNormD (ε • hexMap x) < 1) :
    ContDiffAt ℝ ∞ (equalAreaNormalizedHexChart ε) x :=
  ((equalAreaHexChart_contDiffAt ε x hx).sub contDiffAt_const).const_smul ε⁻¹

theorem equalAreaNormalizedHexChart_iteratedFDeriv (ε : ℝ) (x : Fin 2 → ℝ)
    (hx : equalAreaSquaredNormD (ε • hexMap x) < 1) (k : ℕ) (hk : k ≠ 0) :
    iteratedFDeriv ℝ k (equalAreaNormalizedHexChart ε) x =
      ε⁻¹ • (iteratedFDeriv ℝ k equalAreaPhiD (ε • hexMap x)).compContinuousLinearMap
        (fun _ => ε • hexMap) := by
  have hf := (equalAreaHexChart_contDiffAt ε x hx).of_le (by simp : (k:ℕ∞ω) ≤ ∞)
  have hsub := hf.sub (contDiffAt_const (c := equalAreaPhiD 0))
  change iteratedFDeriv ℝ k (fun y => ε⁻¹ • (equalAreaHexChart ε y-equalAreaPhiD 0)) x = _
  rw [iteratedFDeriv_const_smul_apply' hsub]
  change ε⁻¹ • iteratedFDeriv ℝ k (equalAreaHexChart ε-(fun _ => equalAreaPhiD 0)) x = _
  rw [iteratedFDeriv_sub_apply hf contDiffAt_const,iteratedFDeriv_const_of_ne hk,Pi.zero_apply,sub_zero]
  exact congrArg (fun D => ε⁻¹ • D) (equalAreaPhi2_iterated_comp_linear (ε • hexMap) x hx k)

theorem equalAreaNormalizedHexChart_derivative_bound (ε : ℝ) (hε : 0 < ε)
    (x : Fin 2 → ℝ) (hx : equalAreaSquaredNormD (ε • hexMap x) < 1)
    (k : ℕ) (hk : 1 ≤ k) :
    ‖iteratedFDeriv ℝ k (equalAreaNormalizedHexChart ε) x‖ ≤
      ε^(k-1)*‖iteratedFDeriv ℝ k equalAreaPhiD (ε • hexMap x)‖*‖hexMap‖^k := by
  rw [equalAreaNormalizedHexChart_iteratedFDeriv ε x hx k (by omega),norm_smul]
  calc
    _ ≤ ‖ε⁻¹‖*(‖iteratedFDeriv ℝ k equalAreaPhiD (ε • hexMap x)‖*
        ∏ _i : Fin k, ‖ε • hexMap‖) := by
      apply mul_le_mul_of_nonneg_left
        (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) (norm_nonneg _)
    _ = _ := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,norm_smul,Real.norm_eq_abs,
        abs_inv,abs_of_pos hε,mul_pow]
      have he : ε⁻¹*ε^k = ε^(k-1) := by
        have heq : ε^k = ε^(k-1)*ε := by
          conv_lhs => rw [show k = (k-1)+1 by omega,pow_succ]
        rw [heq]
        field_simp
      calc
        _ = (ε⁻¹*ε^k)*‖iteratedFDeriv ℝ k equalAreaPhiD (ε • hexMap x)‖*‖hexMap‖^k := by ring
        _ = _ := by rw [he]

theorem equalAreaScaledHex_cube_norm (ε : ℝ) (x : Fin 2 → ℝ) (hx : x ∈ UnitCube 2) :
    ‖ε • hexMap x‖ ≤ |ε| * equalAreaScaleRadius2 := by
  rw [norm_smul,Real.norm_eq_abs]
  have hn : ‖x‖ ≤ (1:ℝ) := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    rw [Real.norm_eq_abs,abs_of_nonneg (hx i).1]
    exact (hx i).2
  calc
    _ ≤ |ε| * (‖hexMap‖*‖x‖) := mul_le_mul_of_nonneg_left (hexMap.le_opNorm x) (abs_nonneg ε)
    _ ≤ |ε| * (‖hexMap‖*1) := by gcongr
    _ ≤ _ := by unfold equalAreaScaleRadius2; nlinarith [norm_nonneg hexMap,abs_nonneg ε]

theorem equalAreaNormalizedHexChart_high_derivatives (k : ℕ) (hk : 2 ≤ k) :
    ∃ C ≥ 0, ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius2 ≤ 1/8 →
      ∀ x ∈ UnitCube 2, ‖iteratedFDeriv ℝ k (equalAreaNormalizedHexChart ε) x‖ ≤ C*ε^(k-1) := by
  obtain ⟨C,hC,hb⟩ := equalAreaPhi2_iterated_derivatives_bounded k
  refine ⟨C*‖hexMap‖^k,by positivity,?_⟩
  intro ε hε hs x hx
  have hn : ‖ε • hexMap x‖ ≤ 1/8 := (equalAreaScaledHex_cube_norm ε x hx).trans
    (by simpa only [abs_of_pos hε] using hs)
  calc
    _ ≤ ε^(k-1)*‖iteratedFDeriv ℝ k equalAreaPhiD (ε • hexMap x)‖*‖hexMap‖^k :=
      equalAreaNormalizedHexChart_derivative_bound ε hε x (equalArea2_small_norm_domain _ hn) k (by omega)
    _ ≤ ε^(k-1)*C*‖hexMap‖^k := by gcongr; exact hb _ hn
    _ = _ := by ring

end SphericalRiesz
end
end

section

/-! First and higher derivative limits of the rescaled exact-area chart of S² (stage S2-2).

Higher derivatives vanish by the exact scaling coefficient; the first derivative converges, by
continuity of the actual `fderiv` at the origin, to the flat map `x ↦ (0, hexMap x)` of the
triangular lattice.  Dimension-2 counterpart of `EqualAreaRescalingLimit24`. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace SphericalRiesz
open Boundary

def equalAreaFlatDerivative2 : (Fin 2 → ℝ) →L[ℝ] (AmbientD 2) :=
  (equalAreaPhiDerivativeD 0).comp hexMap

theorem equalAreaPhiDerivative2_zero_apply (v : Fin 2 → ℝ) :
    equalAreaPhiDerivativeD 0 v = (ambientConsD 1) (0,v) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [equalAreaPhiDerivativeD,equalAreaHeightGradientD,equalAreaNormGradientD,
      equalAreaHeightD,equalAreaSquaredNormD,ambientConsD_apply]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [equalAreaPhiDerivativeD,equalAreaHeightGradientD,equalAreaNormGradientD,
        equalAreaHeightD,equalAreaSquaredNormD,ambientConsD_apply]
    · simp [equalAreaPhiDerivativeD,ambientConsD_apply]

theorem equalAreaFlatDerivative2_apply (x : Fin 2 → ℝ) :
    equalAreaFlatDerivative2 x = (ambientConsD 1) (0,hexMap x) :=
  equalAreaPhiDerivative2_zero_apply _

theorem equalAreaNormalizedHexChart_hasFDerivAt (ε : ℝ) (hε : ε ≠ 0)
    (x : Fin 2 → ℝ) (hx : equalAreaSquaredNormD (ε • hexMap x) < 1) :
    HasFDerivAt (equalAreaNormalizedHexChart ε)
      ((equalAreaPhiDerivativeD (ε • hexMap x)).comp hexMap) x := by
  have hf := (equalAreaPhiD_hasFDerivAt _ hx).comp x
    (ε • hexMap).hasFDerivAt
  have hg := (hf.sub_const (equalAreaPhiD 0)).const_smul ε⁻¹
  apply hg.congr_fderiv
  ext v
  simp [ContinuousLinearMap.comp_apply,smul_smul,hε]

theorem equalAreaNormalizedHexChart_fderiv (ε : ℝ) (hε : ε ≠ 0)
    (x : Fin 2 → ℝ) (hx : equalAreaSquaredNormD (ε • hexMap x) < 1) :
    fderiv ℝ (equalAreaNormalizedHexChart ε) x =
      (fderiv ℝ equalAreaPhiD (ε • hexMap x)).comp hexMap := by
  rw [equalAreaPhiD_fderiv _ hx]
  exact (equalAreaNormalizedHexChart_hasFDerivAt ε hε x hx).fderiv

theorem equalAreaPhi2_fderiv_comp_continuousAt_zero :
    ContinuousAt (fun p : Fin 2 → ℝ => (fderiv ℝ equalAreaPhiD p).comp hexMap) 0 := by
  have hf := (equalAreaPhi2_contDiffAt 0 (by simp [equalAreaSquaredNormD])).continuousAt_fderiv
    (by simp : (∞:ℕ∞ω) ≠ 0)
  fun_prop

theorem equalAreaNormalizedHexChart_first_uniform_limit :
    TendstoUniformlyOn (fun ε x => fderiv ℝ (equalAreaNormalizedHexChart ε) x)
      (fun _ => equalAreaFlatDerivative2) (𝓝[>] (0:ℝ)) (UnitCube 2) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  obtain ⟨δ,hδ,hb⟩ := Metric.continuousAt_iff.mp
    equalAreaPhi2_fderiv_comp_continuousAt_zero η hη
  have ht : Tendsto (fun ε : ℝ => |ε| * equalAreaScaleRadius2) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => |ε| * equalAreaScaleRadius2) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0:ℝ)).mul_const equalAreaScaleRadius2
    exact h.mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,
    ht.eventually (gt_mem_nhds (show (0:ℝ) < min δ (1/8) by positivity))] with ε hε hs x hx
  have hn := (equalAreaScaledHex_cube_norm ε x hx).trans_lt hs
  have hdom := equalArea2_small_norm_domain (ε • hexMap x) (le_of_lt (hn.trans_le (min_le_right _ _)))
  rw [equalAreaNormalizedHexChart_fderiv ε (ne_of_gt hε) x hdom]
  have he : (fderiv ℝ equalAreaPhiD (0 : Fin 2 → ℝ)).comp hexMap = equalAreaFlatDerivative2 := by
    rw [equalAreaPhiD_fderiv _ (by simp [equalAreaSquaredNormD])]
    rfl
  rw [←he,dist_comm]
  exact hb (by simpa only [dist_zero_right] using hn.trans_le (min_le_left _ _))

theorem equalAreaNormalizedHexChart_high_uniform_limit (k : ℕ) (hk : 2 ≤ k) :
    TendstoUniformlyOn (fun ε x => iteratedFDeriv ℝ k (equalAreaNormalizedHexChart ε) x)
      (fun _ => 0) (𝓝[>] (0:ℝ)) (UnitCube 2) := by
  obtain ⟨C,hC,hb⟩ := equalAreaNormalizedHexChart_high_derivatives k hk
  have ht : Tendsto (fun ε : ℝ => C*ε^(k-1)) (𝓝[>] 0) (𝓝 0) := by
    have h0 : k-1 ≠ 0 := by omega
    have hc : Continuous (fun ε : ℝ => C*ε^(k-1)) := by fun_prop
    simpa [h0] using (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun ε : ℝ => ε*equalAreaScaleRadius2) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => ε*equalAreaScaleRadius2) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_id.tendsto (0:ℝ)).mul_const equalAreaScaleRadius2
    exact h.mono_left nhdsWithin_le_nhds
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  filter_upwards [self_mem_nhdsWithin,hs.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/8)),
    ht.eventually (gt_mem_nhds hη)] with ε hε hsmall hbound x hx
  rw [dist_zero_left]
  exact (hb ε hε hsmall.le x hx).trans_lt hbound

end SphericalRiesz
end
end

section

/-! The rescaled exact-area chart of S² approaches the flat map of the triangular lattice also in
order zero (stage S2-2).

The mean value theorem transfers first derivative control to two-point increments, including the
boundary of the unit square.  Dimension-2 counterpart of `EqualAreaRescalingGeometry24`. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace SphericalRiesz
open Boundary

theorem unitCube2_convex : Convex ℝ (UnitCube 2) := by
  rw [unitCube_eq_pi]
  exact convex_pi (fun _ _ => convex_Icc (0:ℝ) 1)

theorem equalAreaNormalizedHexChart_zero (ε : ℝ) :
    equalAreaNormalizedHexChart ε 0 = 0 := by
  simp [equalAreaNormalizedHexChart,equalAreaHexChart]

theorem equalAreaNormalizedHexChart_increment_error (ε : ℝ) (hε : 0 < ε)
    (hs : ε*equalAreaScaleRadius2 ≤ 1/8) (C : ℝ)
    (hb : ∀ x ∈ UnitCube 2,
      ‖fderiv ℝ (equalAreaNormalizedHexChart ε) x-equalAreaFlatDerivative2‖ ≤ C)
    (x y : Fin 2 → ℝ) (hx : x ∈ UnitCube 2) (hy : y ∈ UnitCube 2) :
    ‖(equalAreaNormalizedHexChart ε y-equalAreaFlatDerivative2 y)-
      (equalAreaNormalizedHexChart ε x-equalAreaFlatDerivative2 x)‖ ≤ C*‖y-x‖ := by
  apply unitCube2_convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f' := fun z => fderiv ℝ (equalAreaNormalizedHexChart ε) z-equalAreaFlatDerivative2) _ hb hx hy
  intro z hz
  have hn : ‖ε • hexMap z‖ ≤ 1/8 := (equalAreaScaledHex_cube_norm ε z hz).trans
    (by simpa only [abs_of_pos hε] using hs)
  have hg := equalAreaNormalizedHexChart_hasFDerivAt ε hε.ne' z (equalArea2_small_norm_domain _ hn)
  rw [hg.fderiv]
  exact (hg.sub equalAreaFlatDerivative2.hasFDerivAt).hasFDerivWithinAt

theorem equalAreaNormalizedHexChart_uniform_limit :
    TendstoUniformlyOn equalAreaNormalizedHexChart (fun x => (ambientConsD 1) (0,hexMap x))
      (𝓝[>] (0:ℝ)) (UnitCube 2) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  have hfirst := (Metric.tendstoUniformlyOn_iff.mp equalAreaNormalizedHexChart_first_uniform_limit)
    (η/2) (by positivity)
  have ht : Tendsto (fun ε : ℝ => ε*equalAreaScaleRadius2) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => ε*equalAreaScaleRadius2) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_id.tendsto (0:ℝ)).mul_const equalAreaScaleRadius2
    exact h.mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/8)),
    hfirst] with ε hε hs hb x hx
  have hC : ∀ z ∈ UnitCube 2,
      ‖fderiv ℝ (equalAreaNormalizedHexChart ε) z-equalAreaFlatDerivative2‖ ≤ η/2 := by
    intro z hz
    simpa only [dist_eq_norm, norm_sub_rev] using (hb z hz).le
  have h := equalAreaNormalizedHexChart_increment_error ε hε hs.le (η/2) hC 0 x
    (fun _ => by constructor <;> norm_num) hx
  simp only [equalAreaNormalizedHexChart_zero,map_zero,sub_zero] at h
  have hn := unitCube_norm_le_one 2 x hx
  rw [←equalAreaFlatDerivative2_apply,dist_eq_norm,norm_sub_rev]
  -- Use a smaller derivative tolerance to retain a strict final bound.
  exact (h.trans (mul_le_of_le_one_right (by positivity) hn)).trans_lt (by linarith)

theorem equalAreaFlatDerivative2_dist (x y : Fin 2 → ℝ) :
    dist (equalAreaFlatDerivative2 x) (equalAreaFlatDerivative2 y) =
      dist (WithLp.toLp 2 (hexMap x) : EuclideanSpace ℝ (Fin 2)) (WithLp.toLp 2 (hexMap y)) := by
  rw [equalAreaFlatDerivative2_apply,equalAreaFlatDerivative2_apply]
  have h := ambientConsD_dist_sq (0,hexMap x) (0,hexMap y)
  simp only [sub_self,zero_pow (by decide : (2:ℕ) ≠ 0),zero_add] at h
  exact (sq_eq_sq₀ dist_nonneg dist_nonneg).mp h

theorem equalAreaHex_distance_controls_coordinates (x y : Fin 2 → ℝ) :
    ‖x-y‖ ≤ (1+‖hexInverseMap‖)*
      dist (WithLp.toLp 2 (hexMap x) : EuclideanSpace ℝ (Fin 2)) (WithLp.toLp 2 (hexMap y)) := by
  have h : ‖x-y‖ ≤ ‖hexInverseMap‖*‖hexMap (x-y)‖ := by
    conv_lhs => rw [←hexInverseMap_hexMap (x-y)]
    exact hexInverseMap.le_opNorm _
  calc
    _ ≤ (1+‖hexInverseMap‖)*‖hexMap (x-y)‖ := h.trans (by gcongr; linarith)
    _ ≤ (1+‖hexInverseMap‖)*‖(WithLp.toLp 2 (hexMap (x-y)) : EuclideanSpace ℝ (Fin 2))‖ := by
      gcongr
      exact pi_norm_le_euclideanD _
    _ = _ := by rw [map_sub,WithLp.toLp_sub,dist_eq_norm]

theorem equalAreaNormalizedHexChart_relative_distance_of_derivative (ε : ℝ) (hε : 0 < ε)
    (hs : ε*equalAreaScaleRadius2 ≤ 1/8) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ z ∈ UnitCube 2,
      ‖fderiv ℝ (equalAreaNormalizedHexChart ε) z-equalAreaFlatDerivative2‖ ≤ C)
    (x y : Fin 2 → ℝ) (hx : x ∈ UnitCube 2) (hy : y ∈ UnitCube 2) :
    |dist (equalAreaNormalizedHexChart ε x) (equalAreaNormalizedHexChart ε y)-
      dist (WithLp.toLp 2 (hexMap x) : EuclideanSpace ℝ (Fin 2)) (WithLp.toLp 2 (hexMap y))| ≤
      (C*(1+‖hexInverseMap‖))*
        dist (WithLp.toLp 2 (hexMap x) : EuclideanSpace ℝ (Fin 2)) (WithLp.toLp 2 (hexMap y)) := by
  rw [←equalAreaFlatDerivative2_dist,dist_eq_norm,dist_eq_norm]
  have he : (equalAreaNormalizedHexChart ε x-equalAreaNormalizedHexChart ε y)-
      (equalAreaFlatDerivative2 x-equalAreaFlatDerivative2 y) =
      (equalAreaNormalizedHexChart ε x-equalAreaFlatDerivative2 x)-
        (equalAreaNormalizedHexChart ε y-equalAreaFlatDerivative2 y) := by abel
  calc
    _ ≤ ‖(equalAreaNormalizedHexChart ε x-equalAreaNormalizedHexChart ε y)-
        (equalAreaFlatDerivative2 x-equalAreaFlatDerivative2 y)‖ := abs_norm_sub_norm_le _ _
    _ ≤ C*‖x-y‖ := by
      rw [he]
      exact equalAreaNormalizedHexChart_increment_error ε hε hs C hb y x hy hx
    _ ≤ C*((1+‖hexInverseMap‖)*
        dist (WithLp.toLp 2 (hexMap x) : EuclideanSpace ℝ (Fin 2)) (WithLp.toLp 2 (hexMap y))) :=
      mul_le_mul_of_nonneg_left (equalAreaHex_distance_controls_coordinates x y) hC
    _ = _ := by rw [←equalAreaFlatDerivative2_dist,dist_eq_norm]; ring

theorem equalAreaNormalizedHexChart_relative_distance_eventually (η : ℝ) (hη : 0 < η) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ x ∈ UnitCube 2, ∀ y ∈ UnitCube 2,
      |dist (equalAreaNormalizedHexChart ε x) (equalAreaNormalizedHexChart ε y)-
        dist (WithLp.toLp 2 (hexMap x) : EuclideanSpace ℝ (Fin 2)) (WithLp.toLp 2 (hexMap y))| ≤
      η*dist (WithLp.toLp 2 (hexMap x) : EuclideanSpace ℝ (Fin 2)) (WithLp.toLp 2 (hexMap y)) := by
  have hd : 0 < 1+‖hexInverseMap‖ := by positivity
  let C : ℝ := η/(1+‖hexInverseMap‖)
  have hfirst := (Metric.tendstoUniformlyOn_iff.mp equalAreaNormalizedHexChart_first_uniform_limit)
    C (by dsimp [C]; positivity)
  have ht : Tendsto (fun ε : ℝ => ε*equalAreaScaleRadius2) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => ε*equalAreaScaleRadius2) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_id.tendsto (0:ℝ)).mul_const equalAreaScaleRadius2
    exact h.mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/8)),
    hfirst] with ε hε hs hb x hx y hy
  have h := equalAreaNormalizedHexChart_relative_distance_of_derivative ε hε hs.le C
    (by dsimp [C]; positivity) (fun z hz => by
      simpa only [dist_eq_norm,norm_sub_rev] using (hb z hz).le) x y hx hy
  simpa only [C,div_mul_cancel₀ _ hd.ne'] using h

end SphericalRiesz
end
end

section

/-! Moving coordinate centers in the exact-area chart of S² (stage S2-2).

All bounds use one fixed compact smooth domain, independently of the center; the linear part is
the coordinate map of the triangular lattice.  Dimension-2 counterpart of
`EqualAreaMovingRescaling24`. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace SphericalRiesz
open Boundary

def equalAreaMovingHexChart (v : Fin 2 → ℝ) (ε : ℝ) (x : Fin 2 → ℝ) : (AmbientD 2) :=
  equalAreaPhiD (v+ε • hexMap x)

def equalAreaMovingNormalizedHexChart (v : Fin 2 → ℝ) (ε : ℝ)
    (x : Fin 2 → ℝ) : (AmbientD 2) :=
  ε⁻¹ • (equalAreaMovingHexChart v ε x-equalAreaPhiD v)

theorem equalAreaPhi2_iterated_comp_affine (v : Fin 2 → ℝ)
    (L : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)) (x : Fin 2 → ℝ)
    (hx : equalAreaSquaredNormD (v+L x) < 1) (k : ℕ) :
    iteratedFDeriv ℝ k (fun y => equalAreaPhiD (v+L y)) x =
      (iteratedFDeriv ℝ k equalAreaPhiD (v+L x)).compContinuousLinearMap (fun _ => L) := by
  have hq : Continuous (fun p => equalAreaSquaredNormD (v+p)) := by
    unfold equalAreaSquaredNormD; fun_prop
  have hu : IsOpen {p | equalAreaSquaredNormD (v+p) < 1} := isOpen_lt hq continuous_const
  have hf : ContDiffOn ℝ ∞ (fun p => equalAreaPhiD (v+p))
      {p | equalAreaSquaredNormD (v+p) < 1} := by
    intro p hp
    exact ((equalAreaPhi2_contDiffAt _ hp).comp p (by fun_prop)).contDiffWithinAt
  have hp := hu.preimage L.continuous
  have h := L.iteratedFDerivWithin_comp_right hf hu.uniqueDiffOn hp.uniqueDiffOn hx
    (i := k) (by simp)
  rw [iteratedFDerivWithin_of_isOpen k hp hx,
    iteratedFDerivWithin_of_isOpen k hu hx,iteratedFDeriv_comp_add_left] at h
  exact h

theorem equalAreaMovingHexChart_contDiffAt (v : Fin 2 → ℝ) (ε : ℝ) (x : Fin 2 → ℝ)
    (hx : equalAreaSquaredNormD (v+ε • hexMap x) < 1) :
    ContDiffAt ℝ ∞ (equalAreaMovingHexChart v ε) x :=
  (equalAreaPhi2_contDiffAt _ hx).comp x (by fun_prop)

theorem equalAreaMovingNormalizedHexChart_contDiffAt (v : Fin 2 → ℝ) (ε : ℝ)
    (x : Fin 2 → ℝ) (hx : equalAreaSquaredNormD (v+ε • hexMap x) < 1) :
    ContDiffAt ℝ ∞ (equalAreaMovingNormalizedHexChart v ε) x :=
  ((equalAreaMovingHexChart_contDiffAt v ε x hx).sub contDiffAt_const).const_smul ε⁻¹

theorem equalAreaMovingNormalizedHexChart_iteratedFDeriv (v : Fin 2 → ℝ) (ε : ℝ)
    (x : Fin 2 → ℝ) (hx : equalAreaSquaredNormD (v+ε • hexMap x) < 1)
    (k : ℕ) (hk : k ≠ 0) :
    iteratedFDeriv ℝ k (equalAreaMovingNormalizedHexChart v ε) x =
      ε⁻¹ • (iteratedFDeriv ℝ k equalAreaPhiD (v+ε • hexMap x)).compContinuousLinearMap
        (fun _ => ε • hexMap) := by
  have hf := (equalAreaMovingHexChart_contDiffAt v ε x hx).of_le (by simp : (k:ℕ∞ω) ≤ ∞)
  have hsub := hf.sub (contDiffAt_const (c := equalAreaPhiD v))
  change iteratedFDeriv ℝ k (fun y => ε⁻¹ • (equalAreaMovingHexChart v ε y-equalAreaPhiD v)) x = _
  rw [iteratedFDeriv_const_smul_apply' hsub]
  change ε⁻¹ • iteratedFDeriv ℝ k (equalAreaMovingHexChart v ε-(fun _ => equalAreaPhiD v)) x = _
  rw [iteratedFDeriv_sub_apply hf contDiffAt_const,iteratedFDeriv_const_of_ne hk,Pi.zero_apply,sub_zero]
  exact congrArg (fun D => ε⁻¹ • D) (equalAreaPhi2_iterated_comp_affine v (ε • hexMap) x hx k)

theorem equalAreaMovingNormalizedHexChart_derivative_bound (v : Fin 2 → ℝ)
    (ε : ℝ) (hε : 0 < ε) (x : Fin 2 → ℝ)
    (hx : equalAreaSquaredNormD (v+ε • hexMap x) < 1) (k : ℕ) (hk : 1 ≤ k) :
    ‖iteratedFDeriv ℝ k (equalAreaMovingNormalizedHexChart v ε) x‖ ≤
      ε^(k-1)*‖iteratedFDeriv ℝ k equalAreaPhiD (v+ε • hexMap x)‖*‖hexMap‖^k := by
  rw [equalAreaMovingNormalizedHexChart_iteratedFDeriv v ε x hx k (by omega),norm_smul]
  calc
    _ ≤ ‖ε⁻¹‖*(‖iteratedFDeriv ℝ k equalAreaPhiD (v+ε • hexMap x)‖*
        ∏ _i : Fin k, ‖ε • hexMap‖) := by
      apply mul_le_mul_of_nonneg_left
        (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) (norm_nonneg _)
    _ = _ := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,norm_smul,Real.norm_eq_abs,
        abs_inv,abs_of_pos hε,mul_pow]
      have he : ε⁻¹*ε^k = ε^(k-1) := by
        have heq : ε^k = ε^(k-1)*ε := by
          conv_lhs => rw [show k = (k-1)+1 by omega,pow_succ]
        rw [heq]
        field_simp
      calc
        _ = (ε⁻¹*ε^k)*‖iteratedFDeriv ℝ k equalAreaPhiD (v+ε • hexMap x)‖*‖hexMap‖^k := by ring
        _ = _ := by rw [he]

theorem equalAreaMovingScaledHex_norm (v : Fin 2 → ℝ) (ε : ℝ)
    (x : Fin 2 → ℝ) (hx : ‖x‖ ≤ 1) :
    ‖v+ε • hexMap x‖ ≤ ‖v‖+|ε| * equalAreaScaleRadius2 := by
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  rw [norm_smul,Real.norm_eq_abs]
  calc
    _ ≤ |ε| * (‖hexMap‖*‖x‖) := mul_le_mul_of_nonneg_left (hexMap.le_opNorm x) (abs_nonneg ε)
    _ ≤ |ε| * (‖hexMap‖*1) := by gcongr
    _ ≤ _ := by unfold equalAreaScaleRadius2; nlinarith [norm_nonneg hexMap,abs_nonneg ε]

theorem equalAreaMovingNormalizedHexChart_high_derivatives (k : ℕ) (hk : 2 ≤ k) :
    ∃ C ≥ 0, ∀ v : Fin 2 → ℝ, ∀ ε : ℝ, 0 < ε →
      ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8 → ∀ x : Fin 2 → ℝ, ‖x‖ ≤ 1 →
      ‖iteratedFDeriv ℝ k (equalAreaMovingNormalizedHexChart v ε) x‖ ≤ C*ε^(k-1) := by
  obtain ⟨C,hC,hb⟩ := equalAreaPhi2_iterated_derivatives_bounded k
  refine ⟨C*‖hexMap‖^k,by positivity,?_⟩
  intro v ε hε hs x hx
  have hn : ‖v+ε • hexMap x‖ ≤ 1/8 := (equalAreaMovingScaledHex_norm v ε x hx).trans
    (by simpa only [abs_of_pos hε] using hs)
  calc
    _ ≤ ε^(k-1)*‖iteratedFDeriv ℝ k equalAreaPhiD (v+ε • hexMap x)‖*‖hexMap‖^k :=
      equalAreaMovingNormalizedHexChart_derivative_bound v ε hε x
        (equalArea2_small_norm_domain _ hn) k (by omega)
    _ ≤ ε^(k-1)*C*‖hexMap‖^k := by gcongr; exact hb _ hn
    _ = _ := by ring

theorem equalAreaMovingNormalizedHexChart_hasFDerivAt (v : Fin 2 → ℝ)
    (ε : ℝ) (hε : ε ≠ 0) (x : Fin 2 → ℝ)
    (hx : equalAreaSquaredNormD (v+ε • hexMap x) < 1) :
    HasFDerivAt (equalAreaMovingNormalizedHexChart v ε)
      ((equalAreaPhiDerivativeD (v+ε • hexMap x)).comp hexMap) x := by
  have hf := (equalAreaPhiD_hasFDerivAt _ hx).comp x
    ((ε • hexMap).hasFDerivAt.const_add v)
  have hg := (hf.sub_const (equalAreaPhiD v)).const_smul ε⁻¹
  apply hg.congr_fderiv
  ext w
  simp [ContinuousLinearMap.comp_apply,smul_smul,hε]

theorem equalAreaMovingNormalizedHexChart_fderiv (v : Fin 2 → ℝ)
    (ε : ℝ) (hε : ε ≠ 0) (x : Fin 2 → ℝ)
    (hx : equalAreaSquaredNormD (v+ε • hexMap x) < 1) :
    fderiv ℝ (equalAreaMovingNormalizedHexChart v ε) x =
      (fderiv ℝ equalAreaPhiD (v+ε • hexMap x)).comp hexMap := by
  rw [equalAreaPhiD_fderiv _ hx]
  exact (equalAreaMovingNormalizedHexChart_hasFDerivAt v ε hε x hx).fderiv

/-- One radius controls every moving center and scale, uniformly on the
unit coordinate ball. No rate or first derivative bound is supplied. -/
theorem equalAreaMovingNormalizedHexChart_first_uniform (η : ℝ) (hη : 0 < η) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ v : Fin 2 → ℝ, ‖v‖ ≤ ρ →
      ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ x : Fin 2 → ℝ, ‖x‖ ≤ 1 →
      ‖fderiv ℝ (equalAreaMovingNormalizedHexChart v ε) x-equalAreaFlatDerivative2‖ ≤ η := by
  obtain ⟨δ,hδ,hb⟩ := Metric.continuousAt_iff.mp
    equalAreaPhi2_fderiv_comp_continuousAt_zero η hη
  let ρ : ℝ := min (δ/4) (1/16)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  refine ⟨ρ,hρ,min_le_right _ _,?_⟩
  intro v hv ε hε hs x hx
  have hn : ‖v+ε • hexMap x‖ ≤ 2*ρ := (equalAreaMovingScaledHex_norm v ε x hx).trans
    (by rw [abs_of_pos hε]; linarith)
  have hsmall : ‖v+ε • hexMap x‖ ≤ 1/8 := hn.trans (by have := min_le_right (δ/4) (1/16); change ρ ≤ _ at this; linarith)
  have hclose : dist (v+ε • hexMap x) 0 < δ := by
    rw [dist_zero_right]
    have := min_le_left (δ/4) (1/16)
    change ρ ≤ _ at this
    linarith
  rw [equalAreaMovingNormalizedHexChart_fderiv v ε hε.ne' x (equalArea2_small_norm_domain _ hsmall)]
  have he : (fderiv ℝ equalAreaPhiD (0 : Fin 2 → ℝ)).comp hexMap = equalAreaFlatDerivative2 := by
    rw [equalAreaPhiD_fderiv _ (by simp [equalAreaSquaredNormD])]
    rfl
  simpa only [he,dist_eq_norm] using (hb hclose).le

end SphericalRiesz
end
end

section

/-! One C7 constant for the moving rescaled charts of S² over the triangular lattice
(stage S2-2).

A finite maximum of the actual derivative bounds supplies a single C7 constant.  This needs no
explicit expansion of seventh derivatives.  Dimension-2 counterpart of `EqualAreaMovingBounds24`. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace SphericalRiesz
open Boundary

theorem equalAreaMovingNormalizedHexChart_high_derivatives_through (n : ℕ) :
    ∃ C ≥ 0, ∀ k : ℕ, 2 ≤ k → k ≤ n → ∀ v : Fin 2 → ℝ,
      ∀ ε : ℝ, 0 < ε → ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8 →
      ∀ x : Fin 2 → ℝ, ‖x‖ ≤ 1 →
      ‖iteratedFDeriv ℝ k (equalAreaMovingNormalizedHexChart v ε) x‖ ≤ C*ε^(k-1) := by
  induction n with
  | zero => exact ⟨0,le_rfl,by intro k hk hkn; omega⟩
  | succ n ih =>
    obtain ⟨C,hC,hb⟩ := ih
    by_cases hn : 2 ≤ n+1
    · obtain ⟨D,hD,hd⟩ := equalAreaMovingNormalizedHexChart_high_derivatives (n+1) hn
      refine ⟨max C D,hC.trans (le_max_left _ _),?_⟩
      intro k hk hkn v ε hε hs x hx
      by_cases h : k ≤ n
      · exact (hb k hk h v ε hε hs x hx).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      · have he : k = n+1 := by omega
        subst k
        exact (hd v ε hε hs x hx).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    · exact ⟨0,le_rfl,by intro k hk hkn; omega⟩

theorem equalAreaMovingNormalizedHexChart_C7_uniform (η : ℝ) (hη : 0 < η) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ v : Fin 2 → ℝ, ‖v‖ ≤ ρ →
      ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ x : Fin 2 → ℝ, ‖x‖ ≤ 1 →
      ‖fderiv ℝ (equalAreaMovingNormalizedHexChart v ε) x-equalAreaFlatDerivative2‖ ≤ η ∧
      ∀ k : ℕ, 2 ≤ k → k ≤ 7 →
        ‖iteratedFDeriv ℝ k (equalAreaMovingNormalizedHexChart v ε) x‖ ≤ η := by
  obtain ⟨C,hC,hb⟩ := equalAreaMovingNormalizedHexChart_high_derivatives_through 7
  obtain ⟨r,hr,hr1,hfirst⟩ := equalAreaMovingNormalizedHexChart_first_uniform η hη
  let ρ : ℝ := min r (η/(C+1))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρr : ρ ≤ r := min_le_left _ _
  refine ⟨ρ,hρ,hρr.trans hr1,?_⟩
  intro v hv ε hε hs x hx
  refine ⟨hfirst v (hv.trans hρr) ε hε (hs.trans hρr) x hx,?_⟩
  intro k hk hk7
  have hs1 : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8 := by linarith
  have heρ : ε ≤ ρ := by
    have hrad : 1 ≤ equalAreaScaleRadius2 := by unfold equalAreaScaleRadius2; linarith [norm_nonneg hexMap]
    nlinarith
  have he1 : ε ≤ 1 := by linarith
  have hpow : ε^(k-1) ≤ ε := by
    simpa only [pow_one] using pow_le_pow_of_le_one hε.le he1 (show 1 ≤ k-1 by omega)
  calc
    _ ≤ C*ε^(k-1) := hb k hk hk7 v ε hε hs1 x hx
    _ ≤ C*ε := mul_le_mul_of_nonneg_left hpow hC
    _ ≤ C*ρ := mul_le_mul_of_nonneg_left heρ hC
    _ ≤ C*(η/(C+1)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hC
    _ ≤ η := by
      rw [←mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < C+1)).mpr
      nlinarith

end SphericalRiesz
end
end

section

/-! The arbitrary-order derivative bounds of the moving rescaled charts of S² over the triangular
lattice, at a chosen finite order (stage S2-2).  Dimension-2 counterpart of
`EqualAreaMovingHigherBounds24`. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace SphericalRiesz
open Boundary

/-- One common constant for any chosen finite derivative order. -/
theorem equalAreaMovingNormalizedHexChart_Cn_uniform (n : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ v : Fin 2 → ℝ, ‖v‖ ≤ ρ →
      ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ x : Fin 2 → ℝ, ‖x‖ ≤ 1 →
      ‖fderiv ℝ (equalAreaMovingNormalizedHexChart v ε) x-equalAreaFlatDerivative2‖ ≤ η ∧
      ∀ k : ℕ, 2 ≤ k → k ≤ n →
        ‖iteratedFDeriv ℝ k (equalAreaMovingNormalizedHexChart v ε) x‖ ≤ η := by
  obtain ⟨C,hC,hb⟩ := equalAreaMovingNormalizedHexChart_high_derivatives_through n
  obtain ⟨r,hr,hr1,hfirst⟩ := equalAreaMovingNormalizedHexChart_first_uniform η hη
  let ρ : ℝ := min r (η/(C+1))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρr : ρ ≤ r := min_le_left _ _
  refine ⟨ρ,hρ,hρr.trans hr1,?_⟩
  intro v hv ε hε hs x hx
  refine ⟨hfirst v (hv.trans hρr) ε hε (hs.trans hρr) x hx,?_⟩
  intro k hk hkn
  have hs1 : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8 := by linarith
  have heρ : ε ≤ ρ := by
    have hrad : 1 ≤ equalAreaScaleRadius2 := by unfold equalAreaScaleRadius2; linarith [norm_nonneg hexMap]
    nlinarith
  have he1 : ε ≤ 1 := by linarith
  have hpow : ε^(k-1) ≤ ε := by
    simpa only [pow_one] using pow_le_pow_of_le_one hε.le he1 (show 1 ≤ k-1 by omega)
  calc
    _ ≤ C*ε^(k-1) := hb k hk hkn v ε hε hs1 x hx
    _ ≤ C*ε := mul_le_mul_of_nonneg_left hpow hC
    _ ≤ C*ρ := mul_le_mul_of_nonneg_left heρ hC
    _ ≤ C*(η/(C+1)) := mul_le_mul_of_nonneg_left (min_le_right _ _) hC
    _ ≤ η := by
      rw [←mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < C+1)).mpr
      nlinarith

end SphericalRiesz
end
end

section

/-! Rotated and centered patches of S² over the triangular lattice (stage S2-2).

The radius in the C7 result is independent of the rotation, of the coordinate center and of the
center in the unit square.  This is a local chart class; finite global patch coverage is separate.
Dimension-2 counterpart of `EqualAreaPatchClass24`. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace SphericalRiesz
open Boundary

def equalAreaHexPatch (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (v c : Fin 2 → ℝ)
    (ε : ℝ) (x : Fin 2 → ℝ) : (AmbientD 2) :=
  g (equalAreaMovingHexChart v ε (x-c))

def equalAreaNormalizedHexPatch (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (x : Fin 2 → ℝ) : (AmbientD 2) :=
  g (equalAreaMovingNormalizedHexChart v ε (x-c))

def equalAreaRotatedFlatDerivative2 (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) :
    (Fin 2 → ℝ) →L[ℝ] (AmbientD 2) :=
  (g : (AmbientD 2) →L[ℝ] (AmbientD 2)).comp equalAreaFlatDerivative2

theorem unitCube2_sub_norm (x c : Fin 2 → ℝ) (hx : x ∈ UnitCube 2)
    (hc : c ∈ UnitCube 2) : ‖x-c‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  rw [Pi.sub_apply,Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [(hx i).1,(hc i).2],by linarith [(hx i).2,(hc i).1]⟩

theorem equalAreaNormalizedHexPatch_eq (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (x : Fin 2 → ℝ) :
    equalAreaNormalizedHexPatch g v c ε x =
      ε⁻¹ • (equalAreaHexPatch g v c ε x-equalAreaHexPatch g v c ε c) := by
  simp [equalAreaNormalizedHexPatch,equalAreaHexPatch,equalAreaMovingNormalizedHexChart,
    equalAreaMovingHexChart]

theorem equalAreaNormalizedHexPatch_center (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) : equalAreaNormalizedHexPatch g v c ε c = 0 := by
  rw [equalAreaNormalizedHexPatch_eq]
  simp

theorem equalAreaHexPatch_norm (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (v c : Fin 2 → ℝ)
    (ε : ℝ) (x : Fin 2 → ℝ) (hx : equalAreaSquaredNormD (v+ε • hexMap (x-c)) < 1) :
    ‖equalAreaHexPatch g v c ε x‖ = 1 := by
  rw [equalAreaHexPatch,g.norm_map]
  exact mem_sphere_zero_iff_norm.mp (equalAreaPhiD_mem_sphere _ hx)

theorem equalAreaNormalizedHexPatch_contDiffAt (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (x : Fin 2 → ℝ)
    (hx : equalAreaSquaredNormD (v+ε • hexMap (x-c)) < 1) :
    ContDiffAt ℝ ∞ (equalAreaNormalizedHexPatch g v c ε) x := by
  have hshift : ContDiffAt ℝ ∞ (fun z : Fin 2 → ℝ => z-c) x :=
    contDiffAt_id.sub contDiffAt_const
  have hf : ContDiffAt ℝ ∞ (fun z => equalAreaMovingNormalizedHexChart v ε (z-c)) x :=
    ContDiffAt.comp (g := equalAreaMovingNormalizedHexChart v ε) (f := fun z => z-c) x
      (equalAreaMovingNormalizedHexChart_contDiffAt v ε (x-c) hx) hshift
  exact ContDiffAt.comp (g := g.toContinuousLinearMap)
    (f := fun z => equalAreaMovingNormalizedHexChart v ε (z-c)) x
    g.toContinuousLinearMap.contDiff.contDiffAt hf

theorem equalAreaNormalizedHexPatch_hasFDerivAt (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (hε : ε ≠ 0) (x : Fin 2 → ℝ)
    (hx : equalAreaSquaredNormD (v+ε • hexMap (x-c)) < 1) :
    HasFDerivAt (equalAreaNormalizedHexPatch g v c ε)
      ((g : (AmbientD 2) →L[ℝ] (AmbientD 2)).comp
        ((equalAreaPhiDerivativeD (v+ε • hexMap (x-c))).comp hexMap)) x := by
  have hf : HasFDerivAt (fun z => equalAreaMovingNormalizedHexChart v ε (z-c))
      ((equalAreaPhiDerivativeD (v+ε • hexMap (x-c))).comp hexMap) x :=
    (hasFDerivAt_comp_sub c).mpr (equalAreaMovingNormalizedHexChart_hasFDerivAt v ε hε (x-c) hx)
  exact g.toContinuousLinearMap.hasFDerivAt.comp x hf

theorem equalAreaNormalizedHexPatch_fderiv (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (x : Fin 2 → ℝ) :
    fderiv ℝ (equalAreaNormalizedHexPatch g v c ε) x =
      (g : (AmbientD 2) →L[ℝ] (AmbientD 2)).comp
        (fderiv ℝ (equalAreaMovingNormalizedHexChart v ε) (x-c)) := by
  change fderiv ℝ (g ∘ (fun z => equalAreaMovingNormalizedHexChart v ε (z-c))) x = _
  rw [g.comp_fderiv,fderiv_comp_sub]

theorem equalAreaNormalizedHexPatch_iterated_norm (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (x : Fin 2 → ℝ) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (equalAreaNormalizedHexPatch g v c ε) x‖ =
      ‖iteratedFDeriv ℝ k (equalAreaMovingNormalizedHexChart v ε) (x-c)‖ := by
  change ‖iteratedFDeriv ℝ k (g ∘ (fun z => equalAreaMovingNormalizedHexChart v ε (z-c))) x‖ = _
  rw [g.norm_iteratedFDeriv_comp_left,iteratedFDeriv_comp_sub]

theorem equalAreaRotation2_comp_norm_le (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (L : (Fin 2 → ℝ) →L[ℝ] (AmbientD 2)) :
    ‖(g : (AmbientD 2) →L[ℝ] (AmbientD 2)).comp L‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
  intro x
  change ‖g (L x)‖ ≤ ‖L‖*‖x‖
  rw [g.norm_map]
  exact L.le_opNorm x

theorem equalAreaNormalizedHexPatch_first_error (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (x : Fin 2 → ℝ) :
    ‖fderiv ℝ (equalAreaNormalizedHexPatch g v c ε) x-equalAreaRotatedFlatDerivative2 g‖ ≤
      ‖fderiv ℝ (equalAreaMovingNormalizedHexChart v ε) (x-c)-equalAreaFlatDerivative2‖ := by
  rw [equalAreaNormalizedHexPatch_fderiv]
  change ‖(g : (AmbientD 2) →L[ℝ] (AmbientD 2)).comp _-(g : (AmbientD 2) →L[ℝ] (AmbientD 2)).comp _‖ ≤ _
  rw [←ContinuousLinearMap.comp_sub]
  exact equalAreaRotation2_comp_norm_le g _

theorem equalAreaNormalizedHexPatch_increment_error (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (hc : c ∈ UnitCube 2) (ε : ℝ) (hε : 0 < ε)
    (hs : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) (C : ℝ)
    (hb : ∀ z ∈ UnitCube 2,
      ‖fderiv ℝ (equalAreaNormalizedHexPatch g v c ε) z-equalAreaRotatedFlatDerivative2 g‖ ≤ C)
    (x y : Fin 2 → ℝ) (hx : x ∈ UnitCube 2) (hy : y ∈ UnitCube 2) :
    ‖(equalAreaNormalizedHexPatch g v c ε y-equalAreaRotatedFlatDerivative2 g (y-c))-
      (equalAreaNormalizedHexPatch g v c ε x-equalAreaRotatedFlatDerivative2 g (x-c))‖ ≤ C*‖y-x‖ := by
  apply unitCube2_convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f' := fun z => fderiv ℝ (equalAreaNormalizedHexPatch g v c ε) z-equalAreaRotatedFlatDerivative2 g)
    _ hb hx hy
  intro z hz
  have hn : ‖v+ε • hexMap (z-c)‖ ≤ 1/8 :=
    (equalAreaMovingScaledHex_norm v ε (z-c) (unitCube2_sub_norm z c hz hc)).trans
      (by simpa only [abs_of_pos hε] using hs)
  have hf := equalAreaNormalizedHexPatch_hasFDerivAt g v c ε hε.ne' z
    (equalArea2_small_norm_domain _ hn)
  have hl : HasFDerivAt (fun w => equalAreaRotatedFlatDerivative2 g (w-c))
      (equalAreaRotatedFlatDerivative2 g) z :=
    (hasFDerivAt_comp_sub c).mpr (equalAreaRotatedFlatDerivative2 g).hasFDerivAt
  rw [hf.fderiv]
  exact (hf.sub hl).hasFDerivWithinAt

theorem equalAreaRotatedFlatDerivative2_dist (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (c x y : Fin 2 → ℝ) :
    dist (equalAreaRotatedFlatDerivative2 g (x-c)) (equalAreaRotatedFlatDerivative2 g (y-c)) =
      dist (WithLp.toLp 2 (hexMap x) : EuclideanSpace ℝ (Fin 2)) (WithLp.toLp 2 (hexMap y)) := by
  change dist (g (equalAreaFlatDerivative2 (x-c))) (g (equalAreaFlatDerivative2 (y-c))) = _
  rw [g.dist_map,dist_eq_norm,←map_sub]
  have h : (x-c)-(y-c) = x-y := by abel
  rw [h,map_sub,←dist_eq_norm,equalAreaFlatDerivative2_dist]

theorem equalAreaNormalizedHexPatch_relative_distance_of_derivative
    (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (v c : Fin 2 → ℝ) (hc : c ∈ UnitCube 2)
    (ε : ℝ) (hε : 0 < ε) (hs : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ z ∈ UnitCube 2,
      ‖fderiv ℝ (equalAreaNormalizedHexPatch g v c ε) z-equalAreaRotatedFlatDerivative2 g‖ ≤ C)
    (x y : Fin 2 → ℝ) (hx : x ∈ UnitCube 2) (hy : y ∈ UnitCube 2) :
    |dist (equalAreaNormalizedHexPatch g v c ε x) (equalAreaNormalizedHexPatch g v c ε y)-
      dist (WithLp.toLp 2 (hexMap x) : EuclideanSpace ℝ (Fin 2)) (WithLp.toLp 2 (hexMap y))| ≤
      (C*(1+‖hexInverseMap‖))*
        dist (WithLp.toLp 2 (hexMap x) : EuclideanSpace ℝ (Fin 2)) (WithLp.toLp 2 (hexMap y)) := by
  rw [←equalAreaRotatedFlatDerivative2_dist g c,dist_eq_norm,dist_eq_norm]
  have he : (equalAreaNormalizedHexPatch g v c ε x-equalAreaNormalizedHexPatch g v c ε y)-
      (equalAreaRotatedFlatDerivative2 g (x-c)-equalAreaRotatedFlatDerivative2 g (y-c)) =
      (equalAreaNormalizedHexPatch g v c ε x-equalAreaRotatedFlatDerivative2 g (x-c))-
        (equalAreaNormalizedHexPatch g v c ε y-equalAreaRotatedFlatDerivative2 g (y-c)) := by abel
  calc
    _ ≤ ‖(equalAreaNormalizedHexPatch g v c ε x-equalAreaNormalizedHexPatch g v c ε y)-
        (equalAreaRotatedFlatDerivative2 g (x-c)-equalAreaRotatedFlatDerivative2 g (y-c))‖ :=
      abs_norm_sub_norm_le _ _
    _ ≤ C*‖x-y‖ := by
      rw [he]
      exact equalAreaNormalizedHexPatch_increment_error g v c hc ε hε hs C hb y x hy hx
    _ ≤ C*((1+‖hexInverseMap‖)*
        dist (WithLp.toLp 2 (hexMap x) : EuclideanSpace ℝ (Fin 2)) (WithLp.toLp 2 (hexMap y))) :=
      mul_le_mul_of_nonneg_left (equalAreaHex_distance_controls_coordinates x y) hC
    _ = _ := by rw [←equalAreaRotatedFlatDerivative2_dist g c,dist_eq_norm]; ring

/-- Uniform C7 closeness of actual normalized sphere patches to the
rotated flat embedding of the triangular lattice. The derivatives are actual fderiv/iteratedFDeriv. -/
theorem equalAreaNormalizedHexPatch_C7_uniform (η : ℝ) (hη : 0 < η) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ v : Fin 2 → ℝ, ‖v‖ ≤ ρ →
      ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2), ∀ c ∈ UnitCube 2, ∀ x ∈ UnitCube 2,
      ContDiffAt ℝ ∞ (equalAreaNormalizedHexPatch g v c ε) x ∧
      ‖equalAreaNormalizedHexPatch g v c ε x-equalAreaRotatedFlatDerivative2 g (x-c)‖ ≤ η ∧
      ‖fderiv ℝ (equalAreaNormalizedHexPatch g v c ε) x-equalAreaRotatedFlatDerivative2 g‖ ≤ η ∧
      ∀ k : ℕ, 2 ≤ k → k ≤ 7 →
        ‖iteratedFDeriv ℝ k (equalAreaNormalizedHexPatch g v c ε) x‖ ≤ η := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := equalAreaMovingNormalizedHexChart_C7_uniform η hη
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro v hv ε hε hs g c hc x hx
  have hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8 := by linarith
  have hnorm : ‖v+ε • hexMap (x-c)‖ ≤ 1/8 :=
    (equalAreaMovingScaledHex_norm v ε (x-c) (unitCube2_sub_norm x c hx hc)).trans
      (by simpa only [abs_of_pos hε] using hsmall)
  have hfirst : ∀ z ∈ UnitCube 2,
      ‖fderiv ℝ (equalAreaNormalizedHexPatch g v c ε) z-equalAreaRotatedFlatDerivative2 g‖ ≤ η := by
    intro z hz
    exact (equalAreaNormalizedHexPatch_first_error g v c ε z).trans
      (hb v hv ε hε hs (z-c) (unitCube2_sub_norm z c hz hc)).1
  refine ⟨equalAreaNormalizedHexPatch_contDiffAt g v c ε x (equalArea2_small_norm_domain _ hnorm),
    ?_,hfirst x hx,?_⟩
  · have h := equalAreaNormalizedHexPatch_increment_error g v c hc ε hε hsmall η hfirst c x hc hx
    simp only [equalAreaNormalizedHexPatch_center,sub_self,map_zero,sub_zero] at h
    exact h.trans (mul_le_of_le_one_right hη.le (unitCube2_sub_norm x c hx hc))
  · intro k hk hk7
    rw [equalAreaNormalizedHexPatch_iterated_norm]
    exact (hb v hv ε hε hs (x-c) (unitCube2_sub_norm x c hx hc)).2 k hk hk7

theorem equalAreaNormalizedHexPatch_relative_distance_uniform (η : ℝ) (hη : 0 < η) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ v : Fin 2 → ℝ, ‖v‖ ≤ ρ →
      ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2), ∀ c ∈ UnitCube 2,
      ∀ x ∈ UnitCube 2, ∀ y ∈ UnitCube 2,
      |dist (equalAreaNormalizedHexPatch g v c ε x) (equalAreaNormalizedHexPatch g v c ε y)-
        dist (WithLp.toLp 2 (hexMap x) : EuclideanSpace ℝ (Fin 2)) (WithLp.toLp 2 (hexMap y))| ≤
        η*dist (WithLp.toLp 2 (hexMap x) : EuclideanSpace ℝ (Fin 2)) (WithLp.toLp 2 (hexMap y)) := by
  have hd : 0 < 1+‖hexInverseMap‖ := by positivity
  let C : ℝ := η/(1+‖hexInverseMap‖)
  obtain ⟨ρ,hρ,hρ1,hb⟩ := equalAreaNormalizedHexPatch_C7_uniform C (by dsimp [C]; positivity)
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro v hv ε hε hs g c hc x hx y hy
  have h := equalAreaNormalizedHexPatch_relative_distance_of_derivative g v c hc ε hε
    (by linarith) C (by dsimp [C]; positivity)
    (fun z hz => (hb v hv ε hε hs g c hc z hz).2.2.1) x y hx hy
  simpa only [C,div_mul_cancel₀ _ hd.ne'] using h

/-- A single positive lower Lipschitz constant for the actual patch class,
needed by the singular far-kernel estimates. -/
theorem equalAreaNormalizedHexPatch_lower_distance_uniform :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ v : Fin 2 → ℝ, ‖v‖ ≤ ρ →
      ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius2 ≤ ρ →
      ∀ g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2), ∀ c ∈ UnitCube 2,
      ∀ x ∈ UnitCube 2, ∀ y ∈ UnitCube 2,
      (1/(2*(1+‖hexInverseMap‖)))*‖x-y‖ ≤
        dist (equalAreaNormalizedHexPatch g v c ε x) (equalAreaNormalizedHexPatch g v c ε y) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := equalAreaNormalizedHexPatch_relative_distance_uniform
    (1/2) (by norm_num)
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro v hv ε hε hs g c hc x hx y hy
  have hd := (abs_le.mp (hb v hv ε hε hs g c hc x hx y hy)).1
  have hflat : dist (WithLp.toLp 2 (hexMap x) : EuclideanSpace ℝ (Fin 2)) (WithLp.toLp 2 (hexMap y)) ≤
      2*dist (equalAreaNormalizedHexPatch g v c ε x) (equalAreaNormalizedHexPatch g v c ε y) := by
    linarith
  rw [div_mul_eq_mul_div,one_mul]
  apply (div_le_iff₀ (by positivity : 0 < 2*(1+‖hexInverseMap‖))).mpr
  have h := mul_le_mul_of_nonneg_left hflat (by positivity : 0 ≤ 1+‖hexInverseMap‖)
  have hcxy := equalAreaHex_distance_controls_coordinates x y
  nlinarith

end SphericalRiesz
end
end

section

/-! The affine coordinate change of a triangular-lattice patch of S² (stage S2-2).

Compose translation, the determinant-one coordinate map `hexMap` of the triangular lattice and
scalar dilation.  This gives the coordinate-volume factor `ε²` without recomputing the spherical
cone Jacobian.  Dimension-2 counterpart of `EqualAreaAffine24`. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Topology Pointwise
namespace SphericalRiesz
open Boundary

def equalAreaHexAffine2 (v c : Fin 2 → ℝ) (ε : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  v+ε • hexMap (x-c)

theorem equalAreaHexAffine2_continuous (v c : Fin 2 → ℝ) (ε : ℝ) :
    Continuous (equalAreaHexAffine2 v c ε) := by
  unfold equalAreaHexAffine2
  fun_prop

theorem equalAreaHexAffine2_injective (v c : Fin 2 → ℝ) (ε : ℝ) (hε : ε ≠ 0) :
    Function.Injective (equalAreaHexAffine2 v c ε) := by
  intro x y hxy
  have he : ε • hexMap (x-c) = ε • hexMap (y-c) := add_left_cancel hxy
  have h := congrArg (fun z : Fin 2 → ℝ => ε⁻¹ • z) he
  simp only [smul_smul,inv_mul_cancel₀ hε,one_smul] at h
  simpa using hexMap_injective h

theorem equalAreaHexAffine2_image_measurable (v c : Fin 2 → ℝ) (ε : ℝ) (hε : ε ≠ 0)
    (s : Set (Fin 2 → ℝ)) (hs : MeasurableSet s) :
    MeasurableSet (equalAreaHexAffine2 v c ε '' s) :=
  hs.image_of_continuousOn_injOn (equalAreaHexAffine2_continuous v c ε).continuousOn
    (equalAreaHexAffine2_injective v c ε hε).injOn

theorem volume2_image_preserving8 (f : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (hf : MeasurePreserving f volume volume) (he : MeasurableEmbedding f)
    (s : Set (Fin 2 → ℝ)) : volume (f '' s) = volume s := by
  rw [← hf.measure_preimage_emb he,he.injective.preimage_image]

theorem equalAreaHexAffine2_image_volume (v c : Fin 2 → ℝ) (ε : ℝ) (hε : 0 < ε)
    (s : Set (Fin 2 → ℝ)) :
    volume (equalAreaHexAffine2 v c ε '' s) = ENNReal.ofReal (ε^2)*volume s := by
  have himage : equalAreaHexAffine2 v c ε '' s =
      (fun z : Fin 2 → ℝ => v+z) ''
        ((fun z : Fin 2 → ℝ => ε • z) '' (hexMap '' ((fun x : Fin 2 → ℝ => x-c) '' s))) := by
    simp only [image_image]
    rfl
  rw [himage,volume2_image_preserving8 _ (measurePreserving_add_left volume v)
    (Homeomorph.addLeft v).measurableEmbedding]
  change volume (ε • (hexMap '' ((fun x : Fin 2 → ℝ => x-c) '' s))) = _
  rw [Measure.addHaar_smul_of_nonneg volume hε.le,
    volume2_image_preserving8 hexMap hexMap_measurePreserving hexMap_measurableEmbedding,
    volume2_image_preserving8 _ (measurePreserving_sub_right volume c)
      (Homeomorph.subRight c).measurableEmbedding]
  simp

theorem equalArea2_small_norm_chart_domain (p : Fin 2 → ℝ) (hp : ‖p‖ ≤ 1/8) :
    p ∈ equalAreaChartDomainD := by
  refine ⟨equalArea2_small_norm_domain p hp,?_⟩
  have hcoord : |p 0| ≤ 1/8 := (norm_le_pi_norm p 0).trans hp
  have hpi := Real.two_le_pi
  exact ⟨by linarith [(abs_le.mp hcoord).1],by linarith [(abs_le.mp hcoord).2]⟩

theorem equalAreaHexAffine2_cube_domain (v c : Fin 2 → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hc : c ∈ UnitCube 2) (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) :
    equalAreaHexAffine2 v c ε '' UnitCube 2 ⊆ equalAreaChartDomainD := by
  rintro _ ⟨x,hx,rfl⟩
  apply equalArea2_small_norm_chart_domain
  exact (equalAreaMovingScaledHex_norm v ε (x-c) (unitCube2_sub_norm x c hx hc)).trans
    (by simpa only [abs_of_pos hε] using hsmall)

end SphericalRiesz
end
end

section

/-! Area and probability of every measurable subset of a scaled, translated and rotated
triangular-lattice patch of S² (stage S2-2).

This composes the local area formula of the equal-area chart with exact affine volume and rotation
invariance: the image of a measurable subset `s` of the unit square has probability
`ε² |s| / |S²|`.  Dimension-2 counterpart of `EqualAreaPatchMeasure24`. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace SphericalRiesz
open Boundary

def equalAreaHexSpherePatch2 (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (s : Set (Fin 2 → ℝ)) : Set (SphereD 2) :=
  Subtype.val ⁻¹' (equalAreaHexPatch g v c ε '' s)

theorem equalAreaHexSpherePatch2_rotation_preimage (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (s : Set (Fin 2 → ℝ)) :
    equalAreaHexSpherePatch2 g v c ε s = (sphereRotationD g.symm) ⁻¹'
      equalAreaSpherePatchD (equalAreaHexAffine2 v c ε '' s) := by
  ext x
  change (∃ y ∈ s, equalAreaHexPatch g v c ε y = (x : (AmbientD 2))) ↔
    (∃ p ∈ equalAreaHexAffine2 v c ε '' s, equalAreaPhiD p = g.symm (x : (AmbientD 2)))
  constructor
  · rintro ⟨y,hy,h⟩
    refine ⟨equalAreaHexAffine2 v c ε y,⟨y,hy,rfl⟩,?_⟩
    simpa only [equalAreaHexPatch,equalAreaMovingHexChart,equalAreaHexAffine2,
      g.symm_apply_apply] using congrArg g.symm h
  · rintro ⟨p,⟨y,hy,rfl⟩,h⟩
    refine ⟨y,hy,?_⟩
    simpa only [equalAreaHexPatch,equalAreaMovingHexChart,equalAreaHexAffine2,
      g.apply_symm_apply] using congrArg g h

theorem equalAreaHexSpherePatch2_measurable (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (hε : 0 < ε) (s : Set (Fin 2 → ℝ))
    (hs : MeasurableSet s) (hsub : equalAreaHexAffine2 v c ε '' s ⊆ equalAreaChartDomainD) :
    MeasurableSet (equalAreaHexSpherePatch2 g v c ε s) := by
  rw [equalAreaHexSpherePatch2_rotation_preimage]
  exact (equalAreaSpherePatchD_measurable _
    (equalAreaHexAffine2_image_measurable v c ε hε.ne' s hs) hsub).preimage
      (sphereRotationD g.symm).measurable

theorem equalAreaHexSpherePatch2_area (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (hε : 0 < ε) (s : Set (Fin 2 → ℝ))
    (hs : MeasurableSet s) (hsub : equalAreaHexAffine2 v c ε '' s ⊆ equalAreaChartDomainD) :
    (sphereAreaD 2) (equalAreaHexSpherePatch2 g v c ε s) = ENNReal.ofReal (ε^2)*volume s := by
  rw [equalAreaHexSpherePatch2_rotation_preimage,
    (sphereAreaD_rotation_preserving g.symm).measure_preimage_emb
      (sphereRotationD g.symm).measurableEmbedding,
    sphereAreaD_equalAreaSpherePatch _
      (equalAreaHexAffine2_image_measurable v c ε hε.ne' s hs) hsub,
    equalAreaHexAffine2_image_volume v c ε hε]

def equalAreaHexPatchProbabilityDensity2 (ε : ℝ) : ℝ :=
  ε^2/((sphereAreaD 2).real univ)

theorem equalAreaHexPatchProbabilityDensity2_pos (ε : ℝ) (hε : 0 < ε) :
    0 < equalAreaHexPatchProbabilityDensity2 ε := by
  unfold equalAreaHexPatchProbabilityDensity2
  exact div_pos (pow_pos hε 2) (sphereAreaD_univ_pos 2)

theorem equalAreaHexPatchProbabilityDensity2_ofReal (ε : ℝ) :
    ENNReal.ofReal (equalAreaHexPatchProbabilityDensity2 ε) =
      ((sphereAreaD 2) univ)⁻¹*ENNReal.ofReal (ε^2) := by
  unfold equalAreaHexPatchProbabilityDensity2
  rw [ENNReal.ofReal_div_of_pos (sphereAreaD_univ_pos 2), ofReal_measureReal (measure_ne_top _ _)]
  rw [div_eq_mul_inv,mul_comm]

theorem equalAreaHexSpherePatch2_probability (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (hε : 0 < ε) (s : Set (Fin 2 → ℝ))
    (hs : MeasurableSet s) (hsub : equalAreaHexAffine2 v c ε '' s ⊆ equalAreaChartDomainD) :
    (sphereProbabilityD 2) (equalAreaHexSpherePatch2 g v c ε s) =
      ENNReal.ofReal (equalAreaHexPatchProbabilityDensity2 ε)*volume s := by
  rw [sphereProbabilityD,Measure.smul_apply,equalAreaHexSpherePatch2_area g v c ε hε s hs hsub,
    smul_eq_mul,← mul_assoc,← equalAreaHexPatchProbabilityDensity2_ofReal]

theorem equalAreaHexSpherePatch2_probability_real (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (hε : 0 < ε) (s : Set (Fin 2 → ℝ))
    (hs : MeasurableSet s) (hsub : equalAreaHexAffine2 v c ε '' s ⊆ equalAreaChartDomainD) :
    (sphereProbabilityD 2).real (equalAreaHexSpherePatch2 g v c ε s) =
      equalAreaHexPatchProbabilityDensity2 ε*(volume : Measure (Fin 2 → ℝ)).real s := by
  rw [Measure.real,equalAreaHexSpherePatch2_probability g v c ε hε s hs hsub,
    ENNReal.toReal_mul,ENNReal.toReal_ofReal (equalAreaHexPatchProbabilityDensity2_pos ε hε).le]
  rfl

theorem equalAreaHexSpherePatch2_subset_cube_probability (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 2)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8)
    (s : Set (Fin 2 → ℝ)) (hs : MeasurableSet s) (hsc : s ⊆ UnitCube 2) :
    (sphereProbabilityD 2) (equalAreaHexSpherePatch2 g v c ε s) =
      ENNReal.ofReal (ε^2/((sphereAreaD 2).real univ))*volume s :=
  equalAreaHexSpherePatch2_probability g v c ε hε s hs
    ((image_mono hsc).trans (equalAreaHexAffine2_cube_domain v c ε hε hc hsmall))

theorem equalAreaHexSpherePatch2_cube_probability (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 2)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) :
    (sphereProbabilityD 2) (equalAreaHexSpherePatch2 g v c ε (UnitCube 2)) =
      ENNReal.ofReal (ε^2/((sphereAreaD 2).real univ)) := by
  rw [equalAreaHexSpherePatch2_subset_cube_probability g v c ε hε hc hsmall _
    (unitCube_measurableSet 2) Subset.rfl,unitCube_volume,mul_one]

end SphericalRiesz
end
end

section

/-! Transport of measure and integrals to a triangular-lattice patch of S² (stage S2-2).

The sphere-valued embedding of the unit square transports the scaled coordinate measure to the
spherical probability restricted to the physical patch.  The Bochner formula is valid for
arbitrary test functions; integrability is transported separately, so singular kernels do not
silently become integrable.  Dimension-2 counterpart of `EqualAreaPatchTransport24`. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Topology ENNReal
namespace SphericalRiesz
open Boundary

def equalAreaHexCubeEmbedding2 (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 2)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) : UnitCube 2 ↪ (SphereD 2) where
  toFun x := ⟨equalAreaHexPatch g v c ε x, mem_sphere_zero_iff_norm.mpr
    (equalAreaHexPatch_norm g v c ε x
      ((equalAreaHexAffine2_cube_domain v c ε hε hc hsmall) ⟨x,x.property,rfl⟩).1)⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    apply equalAreaHexAffine2_injective v c ε hε.ne'
    apply equalAreaPhiD_injOn
      ((equalAreaHexAffine2_cube_domain v c ε hε hc hsmall) ⟨x,x.property,rfl⟩)
      ((equalAreaHexAffine2_cube_domain v c ε hε hc hsmall) ⟨y,y.property,rfl⟩)
    exact g.injective (congrArg Subtype.val h)

theorem equalAreaHexCubeEmbedding2_continuous (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 2)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) :
    Continuous (equalAreaHexCubeEmbedding2 g v c ε hε hc hsmall) := by
  apply Continuous.subtype_mk
  exact g.continuous.comp (equalAreaPhiD_continuous.comp
    ((equalAreaHexAffine2_continuous v c ε).comp continuous_subtype_val))

theorem equalAreaHexCubeEmbedding2_measurableEmbedding (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 2)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) :
    MeasurableEmbedding (equalAreaHexCubeEmbedding2 g v c ε hε hc hsmall) := by
  let : PolishSpace (UnitCube 2) := (unitCube_isCompact 2).isClosed.polishSpace
  exact (equalAreaHexCubeEmbedding2_continuous g v c ε hε hc hsmall).measurableEmbedding
    (equalAreaHexCubeEmbedding2 g v c ε hε hc hsmall).injective

theorem equalAreaHexCubeEmbedding2_image (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 2)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) (s : Set (UnitCube 2)) :
    equalAreaHexCubeEmbedding2 g v c ε hε hc hsmall '' s =
      equalAreaHexSpherePatch2 g v c ε (Subtype.val '' s) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x,⟨x,hx,rfl⟩,rfl⟩
  · rintro ⟨x,⟨z,hz,rfl⟩,h⟩
    exact ⟨z,hz,Subtype.ext h⟩

theorem equalAreaHexCubeEmbedding2_range (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 2)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) :
    range (equalAreaHexCubeEmbedding2 g v c ε hε hc hsmall) =
      equalAreaHexSpherePatch2 g v c ε (UnitCube 2) := by
  rw [← image_univ, equalAreaHexCubeEmbedding2_image, image_univ, Subtype.range_coe]

theorem equalAreaHexCubeEmbedding2_comap_probability (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 2)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) :
    (sphereProbabilityD 2).comap (equalAreaHexCubeEmbedding2 g v c ε hε hc hsmall) =
      ENNReal.ofReal (equalAreaHexPatchProbabilityDensity2 ε) •
        (volume.comap (Subtype.val : UnitCube 2 → (Fin 2 → ℝ))) := by
  ext s hs
  rw [(equalAreaHexCubeEmbedding2_measurableEmbedding g v c ε hε hc hsmall).comap_apply,
    equalAreaHexCubeEmbedding2_image,
    equalAreaHexSpherePatch2_subset_cube_probability g v c ε hε hc hsmall _
      ((MeasurableEmbedding.subtype_coe (unitCube_measurableSet 2)).measurableSet_image.2 hs)
      (Subtype.coe_image_subset _ _),
    Measure.smul_apply, comap_subtype_coe_apply (unitCube_measurableSet 2),smul_eq_mul]
  rfl

theorem equalAreaHexCubeEmbedding2_map_probability (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 2)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) :
    Measure.map (equalAreaHexCubeEmbedding2 g v c ε hε hc hsmall)
      (ENNReal.ofReal (equalAreaHexPatchProbabilityDensity2 ε) •
        (volume.comap (Subtype.val : UnitCube 2 → (Fin 2 → ℝ)))) =
      (sphereProbabilityD 2).restrict (equalAreaHexSpherePatch2 g v c ε (UnitCube 2)) := by
  rw [← equalAreaHexCubeEmbedding2_comap_probability g v c ε hε hc hsmall,
    (equalAreaHexCubeEmbedding2_measurableEmbedding g v c ε hε hc hsmall).map_comap,
    equalAreaHexCubeEmbedding2_range]

theorem equalAreaHexCubeEmbedding2_integral (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 2)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) (f : (SphereD 2) → ℝ) :
    (∫ y in equalAreaHexSpherePatch2 g v c ε (UnitCube 2), f y ∂(sphereProbabilityD 2)) =
      equalAreaHexPatchProbabilityDensity2 ε *
        ∫ x : UnitCube 2, f (equalAreaHexCubeEmbedding2 g v c ε hε hc hsmall x)
          ∂(volume.comap (Subtype.val : UnitCube 2 → (Fin 2 → ℝ))) := by
  rw [← equalAreaHexCubeEmbedding2_map_probability g v c ε hε hc hsmall,
    (equalAreaHexCubeEmbedding2_measurableEmbedding g v c ε hε hc hsmall).integral_map,
    integral_smul_measure,
    ENNReal.toReal_ofReal (equalAreaHexPatchProbabilityDensity2_pos ε hε).le,smul_eq_mul]

theorem equalAreaHexSpherePatch2_integral (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 2)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) (f : (AmbientD 2) → ℝ) :
    (∫ y in equalAreaHexSpherePatch2 g v c ε (UnitCube 2), f y ∂(sphereProbabilityD 2)) =
      equalAreaHexPatchProbabilityDensity2 ε *
        ∫ x in UnitCube 2, f (equalAreaHexPatch g v c ε x) := by
  rw [equalAreaHexCubeEmbedding2_integral g v c ε hε hc hsmall]
  congr 1
  exact integral_subtype_comap (unitCube_measurableSet 2)
    (fun x => f (equalAreaHexPatch g v c ε x))

theorem equalAreaHexCubeEmbedding2_integrable_iff (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 2)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) (f : (SphereD 2) → ℝ) :
    IntegrableOn f (equalAreaHexSpherePatch2 g v c ε (UnitCube 2)) (sphereProbabilityD 2) ↔
      Integrable (fun x : UnitCube 2 => f (equalAreaHexCubeEmbedding2 g v c ε hε hc hsmall x))
        (volume.comap (Subtype.val : UnitCube 2 → (Fin 2 → ℝ))) := by
  rw [← equalAreaHexCubeEmbedding2_range g v c ε hε hc hsmall,
    (equalAreaHexCubeEmbedding2_measurableEmbedding g v c ε hε hc hsmall).integrableOn_range_iff_comap,
    equalAreaHexCubeEmbedding2_comap_probability,
    integrable_smul_measure (ENNReal.ofReal_pos.mpr
      (equalAreaHexPatchProbabilityDensity2_pos ε hε)).ne' ENNReal.ofReal_ne_top]
  rfl

theorem equalAreaHexSpherePatch2_integrable_iff (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 2)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) (f : (AmbientD 2) → ℝ) :
    IntegrableOn (fun y : (SphereD 2) => f y)
      (equalAreaHexSpherePatch2 g v c ε (UnitCube 2)) (sphereProbabilityD 2) ↔
      IntegrableOn (fun x => f (equalAreaHexPatch g v c ε x)) (UnitCube 2) := by
  rw [equalAreaHexCubeEmbedding2_integrable_iff g v c ε hε hc hsmall]
  exact (integrableOn_iff_comap_subtypeVal (μ := volume)
    (f := fun x => f (equalAreaHexPatch g v c ε x)) (unitCube_measurableSet 2)).symm

end SphericalRiesz
end
end

section

/-! Compactness of the physical triangular-lattice patches of S² and common positive separation
of a finite disjoint compact family (stage S2-2).

The open buffers need not lie inside the compact cores: cores can have empty interior.
Dimension-2 counterpart of `EqualAreaFinitePatchGeometry24`. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped Topology
namespace SphericalRiesz
open Boundary

theorem equalAreaHexSpherePatch2_cube_isCompact (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 2)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8) :
    IsCompact (equalAreaHexSpherePatch2 g v c ε (UnitCube 2)) := by
  let : CompactSpace (UnitCube 2) := isCompact_iff_compactSpace.mp (unitCube_isCompact 2)
  rw [← equalAreaHexCubeEmbedding2_range g v c ε hε hc hsmall]
  exact isCompact_range (equalAreaHexCubeEmbedding2_continuous g v c ε hε hc hsmall)

theorem equalAreaHexSpherePatch2_isCompact (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : c ∈ UnitCube 2)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius2 ≤ 1/8)
    (s : Set (Fin 2 → ℝ)) (hs : IsCompact s) (hsc : s ⊆ UnitCube 2) :
    IsCompact (equalAreaHexSpherePatch2 g v c ε s) := by
  let : CompactSpace (UnitCube 2) := isCompact_iff_compactSpace.mp (unitCube_isCompact 2)
  have himage : Subtype.val '' (Subtype.val ⁻¹' s : Set (UnitCube 2)) = s := by
    rw [image_preimage_eq_inter_range,Subtype.range_coe,inter_eq_left.mpr hsc]
  rw [← himage,← equalAreaHexCubeEmbedding2_image g v c ε hε hc hsmall]
  exact (hs.isClosed.preimage continuous_subtype_val).isCompact.image
    (equalAreaHexCubeEmbedding2_continuous g v c ε hε hc hsmall)

theorem finite2_positive_lower_bound8 {ι : Type*} [Fintype ι]
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) : ∃ δ > 0, ∀ i, δ ≤ r i := by
  classical
  let f : Option ι → ℝ := fun i => i.elim 1 r
  have hne : (Finset.univ : Finset (Option ι)).Nonempty := ⟨none,Finset.mem_univ _⟩
  refine ⟨Finset.univ.inf' hne f,?_,?_⟩
  · change (0 : ℝ) < Finset.univ.inf' hne f
    apply (Finset.lt_inf'_iff hne).mpr
    intro i _
    cases i with
    | none => exact zero_lt_one
    | some i => exact hr i
  · intro i
    exact Finset.inf'_le f (Finset.mem_univ (some i))

theorem compact2_disjoint_distance8 (s t : Set (SphereD 2))
    (hs : IsCompact s) (ht : IsCompact t) (hd : Disjoint s t) :
    ∃ δ > 0, ∀ x ∈ s, ∀ y ∈ t, δ < dist x y := by
  obtain ⟨r,hr,h⟩ := exists_pos_forall_lt_edist hs ht.isClosed hd
  refine ⟨r,NNReal.coe_pos.mpr hr,?_⟩
  intro x hx y hy
  have hn : r < nndist x y := by
    simpa only [edist_nndist,ENNReal.coe_lt_coe] using h x hx y hy
  exact hn

theorem finite2_compact_disjoint_distance8 {K : ℕ} (s : Fin K → Set (SphereD 2))
    (hs : ∀ i, IsCompact (s i)) (hd : Pairwise (fun i j => Disjoint (s i) (s j))) :
    ∃ δ > 0, ∀ i j, i ≠ j → ∀ x ∈ s i, ∀ y ∈ s j, δ < dist x y := by
  classical
  have h : ∀ p : Fin K × Fin K, ∃ r > 0,
      p.1 ≠ p.2 → ∀ x ∈ s p.1, ∀ y ∈ s p.2, r < dist x y := by
    intro p
    by_cases hp : p.1 = p.2
    · exact ⟨1,zero_lt_one,fun hne => (hne hp).elim⟩
    · obtain ⟨r,hr,hb⟩ := compact2_disjoint_distance8 _ _ (hs p.1) (hs p.2) (hd hp)
      exact ⟨r,hr,fun _ => hb⟩
  choose r hr hb using h
  obtain ⟨δ,hδ,hle⟩ := finite2_positive_lower_bound8 r hr
  exact ⟨δ,hδ,fun i j hij x hx y hy => (hle (i,j)).trans_lt (hb (i,j) hij x hx y hy)⟩

theorem finite2_compact_disjoint_thickenings8 {K : ℕ} (s : Fin K → Set (SphereD 2))
    (hs : ∀ i, IsCompact (s i)) (hd : Pairwise (fun i j => Disjoint (s i) (s j))) :
    ∃ ρ > 0, Pairwise (fun i j => Disjoint (thickening ρ (s i)) (thickening ρ (s j))) := by
  obtain ⟨δ,hδ,hsep⟩ := finite2_compact_disjoint_distance8 s hs hd
  refine ⟨δ/3,by positivity,?_⟩
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hz hzj
  obtain ⟨x,hx,hzx⟩ := mem_thickening_iff.mp hz
  obtain ⟨y,hy,hzy⟩ := mem_thickening_iff.mp hzj
  have hl := hsep i j hij x hx y hy
  have ht := dist_triangle_left x y z
  linarith

theorem finite2_compact_chart_buffers8 {K : ℕ} (s U : Fin K → Set (SphereD 2))
    (hs : ∀ i, IsCompact (s i)) (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (hU : ∀ i, IsOpen (U i)) (hsub : ∀ i, s i ⊆ U i) :
    ∃ ρ > 0, (∀ i, IsOpen (thickening ρ (s i)) ∧ s i ⊆ thickening ρ (s i) ∧
      thickening ρ (s i) ⊆ U i) ∧
      Pairwise (fun i j => Disjoint (thickening ρ (s i)) (thickening ρ (s j))) := by
  classical
  obtain ⟨δ,hδ,hdis⟩ := finite2_compact_disjoint_thickenings8 s hs hd
  have h : ∀ i, ∃ r > 0, thickening r (s i) ⊆ U i := fun i =>
    (hs i).exists_thickening_subset_open (hU i) (hsub i)
  choose r hr hb using h
  obtain ⟨η,hη,hle⟩ := finite2_positive_lower_bound8 r hr
  refine ⟨min δ η,lt_min hδ hη,?_,?_⟩
  · intro i
    exact ⟨isOpen_thickening,self_subset_thickening (lt_min hδ hη) _,
      (thickening_mono ((min_le_right δ η).trans (hle i)) _).trans (hb i)⟩
  · intro i j hij
    exact (hdis hij).mono (thickening_mono (min_le_left δ η) _)
      (thickening_mono (min_le_left δ η) _)

theorem equalAreaHexCubeFamily2_separated {K : ℕ}
    (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (v c : Fin K → Fin 2 → ℝ)
    (e : Fin K → ℝ) (he : ∀ i, 0 < e i) (hc : ∀ i, c i ∈ UnitCube 2)
    (hsmall : ∀ i, ‖v i‖+e i*equalAreaScaleRadius2 ≤ 1/8)
    (hd : Pairwise (fun i j => Disjoint
      (equalAreaHexSpherePatch2 (g i) (v i) (c i) (e i) (UnitCube 2))
      (equalAreaHexSpherePatch2 (g j) (v j) (c j) (e j) (UnitCube 2)))) :
    ∃ δ > 0, ∀ i j, i ≠ j →
      ∀ x ∈ equalAreaHexSpherePatch2 (g i) (v i) (c i) (e i) (UnitCube 2),
      ∀ y ∈ equalAreaHexSpherePatch2 (g j) (v j) (c j) (e j) (UnitCube 2), δ < dist x y :=
  finite2_compact_disjoint_distance8 _ (fun i =>
    equalAreaHexSpherePatch2_cube_isCompact (g i) (v i) (c i) (e i) (he i) (hc i) (hsmall i)) hd

end SphericalRiesz
end
end

section

/-! Exact mass accounting for a finite, physically disjoint family of triangular-lattice patches
of S² (stage S2-2).

This does not assume that a covering theorem has been proved: the existence of near-full separated
families remains a separate obligation.  Dimension-2 counterpart of `EqualAreaFinitePatchMass24`. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Topology ENNReal
namespace SphericalRiesz
open Boundary

theorem equalAreaHexSpherePatch2_disjoint (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin 2 → ℝ) (ε : ℝ) (hε : 0 < ε) (s t : Set (Fin 2 → ℝ))
    (hs : equalAreaHexAffine2 v c ε '' s ⊆ equalAreaChartDomainD)
    (ht : equalAreaHexAffine2 v c ε '' t ⊆ equalAreaChartDomainD) (hd : Disjoint s t) :
    Disjoint (equalAreaHexSpherePatch2 g v c ε s) (equalAreaHexSpherePatch2 g v c ε t) := by
  apply Set.disjoint_left.mpr
  intro x hx hxt
  obtain ⟨y,hy,hxy⟩ := hx
  obtain ⟨z,hz,hxz⟩ := hxt
  have h : equalAreaPhiD (equalAreaHexAffine2 v c ε y) =
      equalAreaPhiD (equalAreaHexAffine2 v c ε z) := g.injective (hxy.trans hxz.symm)
  have he := equalAreaHexAffine2_injective v c ε hε.ne'
    (equalAreaPhiD_injOn (hs ⟨y,hy,rfl⟩) (ht ⟨z,hz,rfl⟩) h)
  exact Set.disjoint_left.mp hd hy (he.symm ▸ hz)

def equalAreaHexPatchUnion2 {K : ℕ} (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin K → Fin 2 → ℝ) (e : Fin K → ℝ) (s : Fin K → Set (Fin 2 → ℝ)) : Set (SphereD 2) :=
  ⋃ i : Fin K, equalAreaHexSpherePatch2 (g i) (v i) (c i) (e i) (s i)

theorem equalAreaHexPatchUnion2_probability {K : ℕ} (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin K → Fin 2 → ℝ) (e : Fin K → ℝ) (s : Fin K → Set (Fin 2 → ℝ))
    (he : ∀ i, 0 < e i) (hs : ∀ i, MeasurableSet (s i))
    (hdom : ∀ i, equalAreaHexAffine2 (v i) (c i) (e i) '' s i ⊆ equalAreaChartDomainD)
    (hd : Pairwise (fun i j => Disjoint
      (equalAreaHexSpherePatch2 (g i) (v i) (c i) (e i) (s i))
      (equalAreaHexSpherePatch2 (g j) (v j) (c j) (e j) (s j)))) :
    (sphereProbabilityD 2) (equalAreaHexPatchUnion2 g v c e s) =
      ∑ i : Fin K, ENNReal.ofReal (equalAreaHexPatchProbabilityDensity2 (e i))*volume (s i) := by
  rw [equalAreaHexPatchUnion2,measure_iUnion hd (fun i =>
    equalAreaHexSpherePatch2_measurable (g i) (v i) (c i) (e i) (he i) (s i) (hs i) (hdom i)),
    tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  exact equalAreaHexSpherePatch2_probability (g i) (v i) (c i) (e i) (he i) (s i) (hs i) (hdom i)

theorem equalAreaHexPatchUnion2_residual {K : ℕ} (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin K → Fin 2 → ℝ) (e : Fin K → ℝ) (s : Fin K → Set (Fin 2 → ℝ))
    (he : ∀ i, 0 < e i) (hs : ∀ i, MeasurableSet (s i))
    (hdom : ∀ i, equalAreaHexAffine2 (v i) (c i) (e i) '' s i ⊆ equalAreaChartDomainD)
    (hd : Pairwise (fun i j => Disjoint
      (equalAreaHexSpherePatch2 (g i) (v i) (c i) (e i) (s i))
      (equalAreaHexSpherePatch2 (g j) (v j) (c j) (e j) (s j)))) :
    (sphereProbabilityD 2) (equalAreaHexPatchUnion2 g v c e s)ᶜ =
      1-∑ i : Fin K, ENNReal.ofReal (equalAreaHexPatchProbabilityDensity2 (e i))*volume (s i) := by
  have hm : MeasurableSet (equalAreaHexPatchUnion2 g v c e s) :=
    MeasurableSet.iUnion (fun i => equalAreaHexSpherePatch2_measurable
      (g i) (v i) (c i) (e i) (he i) (s i) (hs i) (hdom i))
  rw [measure_compl hm (measure_ne_top _ _),measure_univ,
    equalAreaHexPatchUnion2_probability g v c e s he hs hdom hd]

theorem equalAreaHexCubeUnion2_probability {K : ℕ} (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin K → Fin 2 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : ∀ i, c i ∈ UnitCube 2)
    (hsmall : ∀ i, ‖v i‖+ε*equalAreaScaleRadius2 ≤ 1/8)
    (hd : Pairwise (fun i j => Disjoint
      (equalAreaHexSpherePatch2 (g i) (v i) (c i) ε (UnitCube 2))
      (equalAreaHexSpherePatch2 (g j) (v j) (c j) ε (UnitCube 2)))) :
    (sphereProbabilityD 2) (equalAreaHexPatchUnion2 g v c (fun _ => ε) (fun _ => UnitCube 2)) =
      (K : ℝ≥0∞)*ENNReal.ofReal (ε^2/((sphereAreaD 2).real univ)) := by
  simpa only [unitCube_volume,mul_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,equalAreaHexPatchProbabilityDensity2] using
    equalAreaHexPatchUnion2_probability g v c (fun _ => ε) (fun _ => UnitCube 2)
      (fun _ => hε) (fun _ => unitCube_measurableSet 2)
      (fun i => equalAreaHexAffine2_cube_domain (v i) (c i) ε hε (hc i) (hsmall i)) hd

theorem equalAreaHexCubeUnion2_residual {K : ℕ} (g : Fin K → (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (v c : Fin K → Fin 2 → ℝ) (ε : ℝ) (hε : 0 < ε) (hc : ∀ i, c i ∈ UnitCube 2)
    (hsmall : ∀ i, ‖v i‖+ε*equalAreaScaleRadius2 ≤ 1/8)
    (hd : Pairwise (fun i j => Disjoint
      (equalAreaHexSpherePatch2 (g i) (v i) (c i) ε (UnitCube 2))
      (equalAreaHexSpherePatch2 (g j) (v j) (c j) ε (UnitCube 2)))) :
    (sphereProbabilityD 2) (equalAreaHexPatchUnion2 g v c (fun _ => ε) (fun _ => UnitCube 2))ᶜ =
      1-(K : ℝ≥0∞)*ENNReal.ofReal (ε^2/((sphereAreaD 2).real univ)) := by
  simpa only [unitCube_volume,mul_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,equalAreaHexPatchProbabilityDensity2] using
    equalAreaHexPatchUnion2_residual g v c (fun _ => ε) (fun _ => UnitCube 2)
      (fun _ => hε) (fun _ => unitCube_measurableSet 2)
      (fun i => equalAreaHexAffine2_cube_domain (v i) (c i) ε hε (hc i) (hsmall i)) hd

end SphericalRiesz
end
end

section

/-! Pull physical open buffers and compact cores of S² back to coordinates (stage S2-2).

The determinant-one coordinate change of the triangular lattice is an existing linear
equivalence; no new inverse matrix or general manifold atlas is needed.  Dimension-2 counterpart
of `EqualAreaCoordinateBuffers24`. -/

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Topology
namespace SphericalRiesz

def equalAreaRotatedSphereChart2 (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) :
    (equalAreaChartDomainD (n := 1)) → (SphereD 2) := fun p => sphereRotationD g (equalAreaSphereChartD p)

def equalAreaRotatedInverse2 (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (q : (SphereD 2)) : Fin 2 → ℝ :=
  equalAreaInverseD (g.symm q)

def equalAreaRotatedHemisphere2 (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) : Set (SphereD 2) :=
  {q | 0 < (g.symm (q : (AmbientD 2))) 0}

def equalAreaCoordinateBuffer2 (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) (U : Set (SphereD 2)) :
    Set (Fin 2 → ℝ) :=
  (Subtype.val : equalAreaChartDomainD → Fin 2 → ℝ) ''
    (equalAreaRotatedSphereChart2 g ⁻¹' U)

def hexCoordinateInverse2 : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ) :=
  hexBasis.equivFun.toContinuousLinearEquiv

theorem equalAreaRotatedSphereChart2_continuous (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) :
    Continuous (equalAreaRotatedSphereChart2 g) := by
  apply (sphereRotationD g).continuous.comp
  apply Continuous.subtype_mk
  exact equalAreaPhiD_continuous.comp continuous_subtype_val

theorem equalAreaRotatedInverse2_mem_domain (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (q : (SphereD 2)) (hq : q ∈ equalAreaRotatedHemisphere2 g) :
    equalAreaRotatedInverse2 g q ∈ equalAreaChartDomainD :=
  equalAreaInverseD_mem_domain (sphereRotationD g.symm q) hq

theorem equalAreaRotatedPhi2_inverse8 (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (q : (SphereD 2)) (hq : q ∈ equalAreaRotatedHemisphere2 g) :
    g (equalAreaPhiD (equalAreaRotatedInverse2 g q)) = (q : (AmbientD 2)) := by
  change g (equalAreaPhiD (equalAreaInverseD (sphereRotationD g.symm q))) = (q : (AmbientD 2))
  rw [equalAreaPhiD_inverse8 (sphereRotationD g.symm q) hq]
  exact g.apply_symm_apply q

theorem equalAreaRotatedInverse2_continuousOn (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2)) :
    ContinuousOn (equalAreaRotatedInverse2 g) (equalAreaRotatedHemisphere2 g) := by
  apply equalAreaInverseD_continuousOn.comp
    (g.symm.continuous.comp continuous_subtype_val).continuousOn
  intro q hq
  exact hq.ne'

theorem equalAreaCoordinateBuffer2_isOpen (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (U : Set (SphereD 2)) (hU : IsOpen U) : IsOpen (equalAreaCoordinateBuffer2 g U) :=
  equalAreaChartDomainD_isOpen.isOpenMap_subtype_val _
    (hU.preimage (equalAreaRotatedSphereChart2_continuous g))

theorem equalAreaCoordinateBuffer2_mem (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (U : Set (SphereD 2)) (u : Fin 2 → ℝ) (hu : u ∈ equalAreaCoordinateBuffer2 g U) :
    u ∈ equalAreaChartDomainD ∧ ∃ q ∈ U, g (equalAreaPhiD u) = (q : (AmbientD 2)) := by
  obtain ⟨p,hp,rfl⟩ := hu
  exact ⟨p.property,equalAreaRotatedSphereChart2 g p,hp,rfl⟩

theorem equalAreaCoordinateCore2_isCompact (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (k : Set (SphereD 2)) (hk : IsCompact k) (hkh : k ⊆ equalAreaRotatedHemisphere2 g) :
    IsCompact (equalAreaRotatedInverse2 g '' k) :=
  hk.image_of_continuousOn ((equalAreaRotatedInverse2_continuousOn g).mono hkh)

theorem equalAreaCoordinateCore2_subset_buffer (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (k U : Set (SphereD 2)) (hkh : k ⊆ equalAreaRotatedHemisphere2 g) (hkU : k ⊆ U) :
    equalAreaRotatedInverse2 g '' k ⊆ equalAreaCoordinateBuffer2 g U := by
  rintro _ ⟨q,hq,rfl⟩
  let p : equalAreaChartDomainD := ⟨equalAreaRotatedInverse2 g q,
    equalAreaRotatedInverse2_mem_domain g q (hkh hq)⟩
  refine ⟨p,?_,rfl⟩
  have he : equalAreaRotatedSphereChart2 g p = q :=
    Subtype.ext (equalAreaRotatedPhi2_inverse8 g q (hkh hq))
  simpa only [mem_preimage,he] using hkU hq

theorem hexMap_coordinateInverse8 (u : Fin 2 → ℝ) : hexMap (hexCoordinateInverse2 u) = u :=
  hexBasis.equivFun.symm_apply_apply u

theorem hexCoordinateInverse2_map (x : Fin 2 → ℝ) : hexCoordinateInverse2 (hexMap x) = x :=
  hexBasis.equivFun.apply_symm_apply x

theorem hexCoordinateCore2_isCompact (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (k : Set (SphereD 2)) (hk : IsCompact k) (hkh : k ⊆ equalAreaRotatedHemisphere2 g) :
    IsCompact (hexCoordinateInverse2 '' (equalAreaRotatedInverse2 g '' k)) :=
  (equalAreaCoordinateCore2_isCompact g k hk hkh).image hexCoordinateInverse2.continuous

theorem hexCoordinateBuffer2_isOpen (g : (AmbientD 2) ≃ₗᵢ[ℝ] (AmbientD 2))
    (U : Set (SphereD 2)) (hU : IsOpen U) :
    IsOpen (hexCoordinateInverse2 '' equalAreaCoordinateBuffer2 g U) :=
  hexCoordinateInverse2.toHomeomorph.isOpenMap _ (equalAreaCoordinateBuffer2_isOpen g U hU)

end SphericalRiesz
end
end

section

/-! Equal-mass residual cells on S² (stage S2-2).

The level sets of the first coordinate are null for the sphere probability: the cone over
`{x₀ = c}` lies in `{v₀ = c ‖v‖}`, whose sections over a nonzero transverse vector have at most
one point.  Slicing a measurable region of probability `n/N` by the first coordinate therefore
gives `n` measurable pairwise disjoint cells of probability exactly `1/N` whose union is the
region.  No diameter bound is asserted; the Gaussian budgets of the residual points do not need
one.  Dimension-2 counterpart of `SphereResidualCells24`; the triangular lattice is not used
here. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped Pointwise ENNReal
namespace SphericalRiesz

theorem ambientD2_cone_level_null (c : ℝ) :
    (volume : Measure (AmbientD 2)) {v | v 0 = c*‖v‖} = 0 := by
  have hmeas : MeasurableSet {v : AmbientD 2 | v 0 = c*‖v‖} :=
    measurableSet_eq_fun (by fun_prop) (by fun_prop)
  have hcons : ∀ p : ℝ × (Fin 2 → ℝ), ‖ambientConsD 1 p‖ =
      Real.sqrt (p.1^2+‖(WithLp.toLp 2 p.2 : EuclideanSpace ℝ (Fin 2))‖^2) := by
    intro p
    rw [← ambientConsD_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have hmp : MeasurePreserving (ambientConsD 1) (volume : Measure (ℝ × (Fin 2 → ℝ)))
      (volume : Measure (AmbientD 2)) := ambientConsD_measurePreserving
  rw [← hmp.map_eq, Measure.map_apply (ambientConsD 1).measurable hmeas]
  have hE : MeasurableSet ((ambientConsD 1) ⁻¹' {v : AmbientD 2 | v 0 = c*‖v‖}) :=
    (ambientConsD 1).measurable hmeas
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hE]
  have ht : ∀ᵐ w ∂(volume : Measure (Fin 2 → ℝ)), w ≠ 0 := by simp [ae_iff]
  have hzero : (fun w : Fin 2 → ℝ => (volume : Measure ℝ)
      ((fun a => (a, w)) ⁻¹' ((ambientConsD 1) ⁻¹' {v : AmbientD 2 | v 0 = c*‖v‖}))) =ᵐ[volume]
      0 := by
    filter_upwards [ht] with w hw
    simp only [Pi.zero_apply]
    apply Set.Subsingleton.measure_zero
    set s := ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin 2))‖^2 with hsdef
    have hs : 0 < s := by
      rw [hsdef]
      have : (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
        intro h
        apply hw
        have := congrArg WithLp.ofLp h
        simpa using this
      positivity
    have hsec : ∀ a, a ∈ (fun a => (a, w)) ⁻¹'
        ((ambientConsD 1) ⁻¹' {v : AmbientD 2 | v 0 = c*‖v‖}) ↔
        a = c*Real.sqrt (a^2+s) := by
      intro a
      simp only [mem_preimage, mem_ofPred_eq]
      rw [hcons (a, w)]
      have h0 : (ambientConsD 1 (a, w)) 0 = a := by simp [ambientConsD_apply]
      rw [h0]
    intro a ha b hb
    rw [hsec] at ha hb
    have hA := Real.sqrt_pos.mpr (show 0 < a^2+s by positivity)
    have hB := Real.sqrt_pos.mpr (show 0 < b^2+s by positivity)
    have hA2 := Real.sq_sqrt (show 0 ≤ a^2+s by positivity)
    have hB2 := Real.sq_sqrt (show 0 ≤ b^2+s by positivity)
    by_cases hc : c = 0
    · rw [hc, zero_mul] at ha hb
      rw [ha, hb]
    have ha2 : a^2 = c^2*(a^2+s) := by
      rw [← hA2]
      nth_rewrite 1 [ha]
      ring
    have hb2 : b^2 = c^2*(b^2+s) := by
      rw [← hB2]
      nth_rewrite 1 [hb]
      ring
    have hc2 : c^2 ≠ 1 := by
      intro h1
      rw [h1] at ha2
      linarith
    have hsq : a^2 = b^2 := by
      have h1 : (a^2-b^2)*(1-c^2) = 0 := by linear_combination ha2-hb2
      rcases mul_eq_zero.mp h1 with h | h
      · linarith
      · exact absurd (by linarith : c^2 = 1) hc2
    have hab : 0 < a*b := by
      rw [ha, hb]
      have : 0 < c^2 := by positivity
      nlinarith [mul_pos hA hB]
    have hfac : (a-b)*(a+b) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · have : b = -a := by linarith
      rw [this] at hab
      nlinarith [sq_nonneg a]
  rw [lintegral_congr_ae hzero]
  simp

/-- The level sets of the first coordinate are null for the sphere probability on S². -/
theorem sphereProbability2_coord_level_null (c : ℝ) :
    (sphereProbabilityD 2) {x : SphereD 2 | (x : AmbientD 2) 0 = c} = 0 := by
  have hmeas : MeasurableSet {x : SphereD 2 | (x : AmbientD 2) 0 = c} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have hcone : Ioo (0:ℝ) 1 • (Subtype.val '' {x : SphereD 2 | (x : AmbientD 2) 0 = c}) ⊆
      {v : AmbientD 2 | v 0 = c*‖v‖} := by
    rintro z ⟨r, hr, w, ⟨y, hy, rfl⟩, rfl⟩
    simp only [mem_ofPred_eq] at hy ⊢
    have hy1 : ‖(y : AmbientD 2)‖ = 1 := by simp
    have hsm : (r • (y : AmbientD 2)) 0 = r*(y : AmbientD 2) 0 := by simp
    rw [hsm, norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hy1, hy]
    ring
  simp only [sphereProbabilityD, Measure.smul_apply, smul_eq_mul]
  unfold sphereAreaD
  rw [Measure.toSphere_apply' _ hmeas, measure_mono_null hcone (ambientD2_cone_level_null c),
    mul_zero, mul_zero]

theorem sphere2_abs_first_coord_le_one (x : SphereD 2) : |(x : AmbientD 2) 0| ≤ 1 := by
  have hx : ‖(x : AmbientD 2)‖ = 1 := by simp
  calc |(x : AmbientD 2) 0| = ‖(x : AmbientD 2) 0‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖(x : AmbientD 2)‖ := PiLp.norm_apply_le _ 0
    _ = 1 := hx

/-- A measurable region of probability `n/N` splits into `n` measurable pairwise disjoint cells
of probability exactly `1/N`. -/
theorem exists_sphere2_equal_mass_cells {N n : ℕ} (hN : 0 < N) (hn : 0 < n)
    {S : Set (SphereD 2)} (hS : MeasurableSet S)
    (hmass : (sphereProbabilityD 2).real S = (n:ℝ)/(N:ℝ)) :
    ∃ C : Fin n → Set (SphereD 2), (∀ j, MeasurableSet (C j)) ∧
      Pairwise (fun i j => Disjoint (C i) (C j)) ∧ (⋃ j, C j) = S ∧
      ∀ j, (sphereProbabilityD 2) (C j) = (N:ℝ≥0∞)⁻¹ := by
  have hf : Measurable (fun x : SphereD 2 => (x : AmbientD 2) 0) := by fun_prop
  have hnull : ∀ c, (sphereProbabilityD 2)
      ((fun x : SphereD 2 => (x : AmbientD 2) 0) ⁻¹' {c} ∩ S) = 0 := fun c =>
    measure_mono_null inter_subset_left (sphereProbability2_coord_level_null c)
  obtain ⟨C, hCm, hCd, hCu, hCmass⟩ := exists_exact_mass_slices (sphereProbabilityD 2) hS hf
    sphere2_abs_first_coord_le_one hnull hn
  refine ⟨C, hCm, hCd, hCu, fun j => ?_⟩
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hreal : (sphereProbabilityD 2).real (C j) = (N:ℝ)⁻¹ := by
    rw [hCmass j, hmass]
    field_simp
  have hof : (sphereProbabilityD 2) (C j) =
      ENNReal.ofReal ((sphereProbabilityD 2).real (C j)) :=
    (ENNReal.ofReal_toReal (measure_ne_top (sphereProbabilityD 2) (C j))).symm
  rw [hof, hreal, ENNReal.ofReal_inv_of_pos hNR, ENNReal.ofReal_natCast]

end SphericalRiesz
end
end

section

/-! A rational-size competitor immediately above every integer point count on S² (stage S2-2).

Dimension 2: the competitor sizes are the squares `(d m)²` (the point counts of the
triangular-lattice patch families), and the ceil/x limit avoids a separate discrete square-root
algorithm.  Dimension-2 counterpart of `RationalSizeCeiling24`. -/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace SphericalRiesz

def rationalSizeIndex2 (d N : ℕ) : ℕ :=
  ⌈((N:ℝ) ^ (1/2:ℝ))/(d:ℝ)⌉₊

def rationalSizeCeiling2 (d N : ℕ) : ℕ := (d*rationalSizeIndex2 d N)^2

theorem real_second_root_pow (N : ℕ) : ((N:ℝ) ^ (1/2:ℝ))^2 = (N:ℝ) := by
  have h : (1/2:ℝ) = ((2:ℕ):ℝ)⁻¹ := by norm_num
  rw [h]
  exact Real.rpow_inv_natCast_pow (Nat.cast_nonneg N) (by decide : (2:ℕ) ≠ 0)

theorem rationalSizeIndex2_argument_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => ((N:ℝ) ^ (1/2:ℝ))/(d:ℝ)) atTop atTop := by
  exact Tendsto.atTop_div_const (by exact_mod_cast hd)
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).comp
      tendsto_natCast_atTop_atTop)

theorem rationalSizeIndex2_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (rationalSizeIndex2 d) atTop atTop :=
  tendsto_nat_ceil_atTop.comp (rationalSizeIndex2_argument_tendsto d hd)

theorem rationalSizeCeiling2_ge (d N : ℕ) (hd : 0 < d) : N ≤ rationalSizeCeiling2 d N := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hr : (N:ℝ) ^ (1/2:ℝ) ≤ (d*rationalSizeIndex2 d N:ℕ) := by
    have h := Nat.le_ceil (((N:ℝ) ^ (1/2:ℝ))/(d:ℝ))
    change _ ≤ (rationalSizeIndex2 d N:ℝ) at h
    have hh := (div_le_iff₀ hdR).mp h
    simpa only [Nat.cast_mul, mul_comm] using hh
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg N) _) hr 2
  rw [real_second_root_pow] at hpow
  exact_mod_cast hpow

theorem rationalSizeCeiling2_ratio_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => (rationalSizeCeiling2 d N:ℝ)/(N:ℝ)) atTop (𝓝 1) := by
  have h := ((tendsto_nat_ceil_div_atTop (R := ℝ)).comp
    (rationalSizeIndex2_argument_tendsto d hd)).pow 2
  simp only [one_pow] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  have hnz : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hdz : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  change (((rationalSizeIndex2 d N:ℕ):ℝ)/((N:ℝ)^(1/2:ℝ)/(d:ℝ)))^2 = _
  rw [div_pow, div_pow, real_second_root_pow]
  unfold rationalSizeCeiling2
  push_cast
  field_simp [hnz, hdz]

theorem rationalSizeCeiling2_inverse_ratio_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (fun N : ℕ => (N:ℝ)/(rationalSizeCeiling2 d N:ℝ)) atTop (𝓝 1) := by
  simpa only [inv_div, inv_one] using (rationalSizeCeiling2_ratio_tendsto d hd).inv₀ one_ne_zero

end SphericalRiesz
end
end
