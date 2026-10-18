import Riesz.E8Coordinates
import Riesz.AnnularPartition

/-!
# Actual inverse-fourth annuli in a nonorthogonal basis

An injective linear map is placed inside one fixed cutoff kernel before
taking the compact derivative bound. The scalar r^-10 scaling is then
unchanged. Constants may depend on that map, but not on radius, center,
or mesh. Integration here is in the coordinate cube; its conversion to
physical volume and the full spherical recovery remain separate.
-/

set_option autoImplicit false
noncomputable section
open scoped ContDiff

namespace SphericalRiesz
open Boundary

def obliqueRieszFour (d : ℕ) (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (x v : Fin d → ℝ) : ℝ := flatRieszFour d 0 (A (v-x))

theorem obliqueRieszFour_eq_flat (d : ℕ) (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (x v : Fin d → ℝ) : obliqueRieszFour d A x v = flatRieszFour d (A x) (A v) := by
  unfold obliqueRieszFour flatRieszFour
  congr 2
  unfold squaredDistance
  simp only [map_sub, Pi.zero_apply, sub_zero, Pi.sub_apply]

theorem obliqueRieszFour_eq_dist (d : ℕ) (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (x v : Fin d → ℝ) : obliqueRieszFour d A x v =
      (dist (WithLp.toLp 2 (A x) : EuclideanSpace ℝ (Fin d))
        (WithLp.toLp 2 (A v)))⁻¹^4 := by
  rw [obliqueRieszFour_eq_flat]
  simpa only [PiLp.toLp_apply] using
    flatRieszFour_eq_dist d (WithLp.toLp 2 (A x)) (WithLp.toLp 2 (A v))

def unitObliqueAnnularRieszFour (d : ℕ) (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (v : Fin d → ℝ) : ℝ := obliqueRieszFour d A 0 v*unitAnnularCutoff d v

theorem unitObliqueAnnularRieszFour_contDiff (d : ℕ)
    (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Function.Injective A) :
    ContDiff ℝ ∞ (unitObliqueAnnularRieszFour d A) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : v = 0
  · subst v
    apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [unitAnnularCutoff_eventually_zero d] with v hv
    simp only [unitObliqueAnnularRieszFour, hv, Pi.zero_apply, mul_zero]
  · have hAv : A v ≠ 0 := fun h => hv (hA (by simpa only [map_zero] using h))
    have hq : squaredDistance d 0 (A v) ≠ 0 :=
      fun h => hAv ((squaredDistance_zero_iff d (A v)).mp h)
    unfold unitObliqueAnnularRieszFour obliqueRieszFour flatRieszFour
    simp only [sub_zero]
    apply ContDiffAt.mul
    · apply ContDiffAt.div contDiffAt_const
      · unfold squaredDistance
        fun_prop
      · exact pow_ne_zero 2 hq
    · exact (outerUnitBump d).contDiffAt.sub (innerUnitBump d).contDiffAt

theorem unitObliqueAnnularRieszFour_hasCompactSupport (d : ℕ)
    (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) :
    HasCompactSupport (unitObliqueAnnularRieszFour d A) := by
  have h : HasCompactSupport (unitAnnularCutoff d) :=
    (outerUnitBump d).hasCompactSupport.sub (innerUnitBump d).hasCompactSupport
  exact h.mul_left

theorem unitAnnularCutoff_zero_outside (d : ℕ) (v : Fin d → ℝ) (hv : 2 ≤ ‖v‖) :
    unitAnnularCutoff d v = 0 := by
  have ho : outerUnitBump d v = 0 := (outerUnitBump d).zero_of_le_dist (by
    simpa only [outerUnitBump, dist_zero_right] using hv)
  have hi : innerUnitBump d v = 0 := (innerUnitBump d).zero_of_le_dist (by
    simp only [innerUnitBump, dist_zero_right]
    linarith)
  rw [unitAnnularCutoff, ho, hi, sub_self]

theorem unitObliqueAnnularRieszFour_tsupport_subset (d : ℕ)
    (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) :
    tsupport (unitObliqueAnnularRieszFour d A) ⊆ Metric.closedBall 0 2 := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro v hv
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hn
  apply (Function.mem_support.mp hv)
  rw [unitObliqueAnnularRieszFour, unitAnnularCutoff_zero_outside d v (not_le.mp hn).le, mul_zero]

def scaledObliqueAnnularRieszFour (d : ℕ) (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (r : ℝ) (x v : Fin d → ℝ) : ℝ :=
  (r⁻¹)^4*unitObliqueAnnularRieszFour d A (r⁻¹ • (v-x))

theorem scaledObliqueAnnularRieszFour_eq_kernel (d : ℕ)
    (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (r : ℝ) (hr : 0 < r) (x v : Fin d → ℝ) :
    scaledObliqueAnnularRieszFour d A r x v =
      obliqueRieszFour d A x v*unitAnnularCutoff d (r⁻¹ • (v-x)) := by
  unfold scaledObliqueAnnularRieszFour unitObliqueAnnularRieszFour obliqueRieszFour flatRieszFour
  simp only [sub_zero, map_smul]
  have hq := squaredDistance_scaled d r 0 (A (v-x))
  simp only [sub_zero] at hq
  rw [hq, mul_pow, ← pow_mul]
  simp only [one_div, mul_inv, inv_pow, inv_inv]
  have hc : (r⁻¹)^4*r^4 = 1 := by rw [← mul_pow, inv_mul_cancel₀ hr.ne', one_pow]
  calc
    _ = ((r⁻¹)^4*r^4)*((squaredDistance d 0 (A (v-x)))^2)⁻¹*
        unitAnnularCutoff d (r⁻¹ • (v-x)) := by ring
    _ = _ := by rw [hc, one_mul]

theorem scaledObliqueAnnularRieszFour_contDiff (d : ℕ)
    (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Function.Injective A)
    (r : ℝ) (x : Fin d → ℝ) : ContDiff ℝ ∞ (scaledObliqueAnnularRieszFour d A r x) := by
  unfold scaledObliqueAnnularRieszFour
  apply ContDiff.mul contDiff_const
  exact (unitObliqueAnnularRieszFour_contDiff d A hA).comp (by fun_prop)

theorem scaledObliqueAnnularRieszFour_sixth_identity (d : ℕ)
    (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Function.Injective A)
    (r : ℝ) (x v : Fin d → ℝ) :
    iteratedFDeriv ℝ 6 (scaledObliqueAnnularRieszFour d A r x) v =
      (r⁻¹)^10 • iteratedFDeriv ℝ 6 (unitObliqueAnnularRieszFour d A) (r⁻¹ • (v-x)) := by
  have hf : ContDiff ℝ 6 (unitObliqueAnnularRieszFour d A) :=
    (unitObliqueAnnularRieszFour_contDiff d A hA).of_le (by simp)
  have hg : ContDiff ℝ 6 (fun z : Fin d → ℝ => unitObliqueAnnularRieszFour d A (r⁻¹ • z)) :=
    hf.comp (by fun_prop)
  have hh : ContDiff ℝ 6 (fun z : Fin d → ℝ => unitObliqueAnnularRieszFour d A (r⁻¹ • (z-x))) :=
    hg.comp (contDiff_id.sub contDiff_const)
  change iteratedFDeriv ℝ 6 (fun z => (r⁻¹)^4 • unitObliqueAnnularRieszFour d A (r⁻¹ • (z-x))) v = _
  rw [iteratedFDeriv_const_smul_apply' hh.contDiffAt,
    iteratedFDeriv_comp_sub (f := fun z : Fin d → ℝ => unitObliqueAnnularRieszFour d A (r⁻¹ • z)) 6 x v,
    iteratedFDeriv_comp_const_smul r⁻¹ hf, smul_smul, ← pow_add]

theorem scaledObliqueAnnularRieszFour_sixth_bounded (d : ℕ)
    (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Function.Injective A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ x v : Fin d → ℝ,
      ‖iteratedFDeriv ℝ 6 (scaledObliqueAnnularRieszFour d A r x) v‖ ≤ C/r^10 := by
  obtain ⟨C, hC, hb⟩ := (unitObliqueAnnularRieszFour_hasCompactSupport d A).exists_bound_iteratedFDeriv
    (unitObliqueAnnularRieszFour_contDiff d A hA) 6
  refine ⟨C, hC, ?_⟩
  intro r hr x v
  rw [scaledObliqueAnnularRieszFour_sixth_identity d A hA, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (r⁻¹)^10)]
  calc
    _ ≤ (r⁻¹)^10*C := mul_le_mul_of_nonneg_left (hb 6 (by rfl) _) (by positivity)
    _ = C/r^10 := by rw [inv_pow, div_eq_mul_inv]; ring

theorem scaledObliqueAnnularRieszFour_zero_outside (d : ℕ)
    (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (r : ℝ) (hr : 0 < r)
    (x v : Fin d → ℝ) (hn : ¬ ∀ i, |v i-x i| ≤ 2*r) :
    scaledObliqueAnnularRieszFour d A r x v = 0 := by
  rw [scaledObliqueAnnularRieszFour, unitObliqueAnnularRieszFour,
    unitAnnularCutoff_zero_outside d _ (scaled_annular_argument_norm d r hr x v hn).le,
    mul_zero, mul_zero]

theorem scaledObliqueAnnularRieszFour_sixth_zero_outside (d : ℕ)
    (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Function.Injective A)
    (r : ℝ) (hr : 0 < r) (x v : Fin d → ℝ) (hn : ¬ ∀ i, |v i-x i| ≤ 2*r) :
    iteratedFDeriv ℝ 6 (scaledObliqueAnnularRieszFour d A r x) v = 0 := by
  have hv : r⁻¹ • (v-x) ∉ tsupport (unitObliqueAnnularRieszFour d A) := by
    intro h
    have hh := unitObliqueAnnularRieszFour_tsupport_subset d A h
    rw [Metric.mem_closedBall, dist_zero_right] at hh
    exact (scaled_annular_argument_norm d r hr x v hn).not_ge hh
  have hz : iteratedFDeriv ℝ 6 (unitObliqueAnnularRieszFour d A) (r⁻¹ • (v-x)) = 0 := by
    apply Function.notMem_support.mp
    intro h
    exact hv (support_iteratedFDeriv_subset 6 h)
  rw [scaledObliqueAnnularRieszFour_sixth_identity d A hA, hz, smul_zero]

theorem scaledObliqueAnnularRieszFour_quadrature_bound (d : ℕ)
    (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Function.Injective A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 8 ≤ m → ∀ r : ℝ, 0 < r → ∀ x : Fin d → ℝ,
      |cubeQuadrature d m (scaledObliqueAnnularRieszFour d A r x)-
        cubeIntegral d (scaledObliqueAnnularRieszFour d A r x)| ≤
        (64/(m:ℝ)^6)*(d:ℝ)*(4*r+2/(m:ℝ))^d*(C/r^10) := by
  obtain ⟨C, hC, hb⟩ := scaledObliqueAnnularRieszFour_sixth_bounded d A hA
  refine ⟨C, hC, ?_⟩
  intro m hm r hr x
  have hf : ContDiff ℝ 6 (scaledObliqueAnnularRieszFour d A r x) :=
    (scaledObliqueAnnularRieszFour_contDiff d A hA r x).of_le (by simp)
  have hs : ∀ i v, v ∈ UnitCube d → ContDiffOn ℝ 6
      (fun t => scaledObliqueAnnularRieszFour d A r x (Function.update v i t)) (Set.Icc (0:ℝ) 1) := by
    intro i v _
    have hu : ContDiff ℝ 6 (fun t : ℝ => Function.update v i t) := by
      rw [show (fun t : ℝ => Function.update v i t) =
        (fun t => ContinuousLinearMap.single ℝ (fun _ : Fin d => ℝ) i t+Function.update v i 0)
        from funext (coordinate_update_as_line d i v)]
      fun_prop
    exact (hf.comp hu).contDiffOn
  have hbound : ∀ i v, v ∈ UnitCube d → ∀ t ∈ Set.Icc (0:ℝ) 1,
      |iteratedDerivWithin 6 (fun u => scaledObliqueAnnularRieszFour d A r x (Function.update v i u))
        (Set.Icc (0:ℝ) 1) t| ≤ C/r^10 :=
    fun i v _ t ht => (sixth_coordinate_within_abs_le d hf i v t ht).trans (hb r hr x _)
  have hsupport : ∀ v ∈ UnitCube d, (¬ ∀ i, |v i-x i| ≤ 2*r) →
      scaledObliqueAnnularRieszFour d A r x v = 0 :=
    fun v _ hn => scaledObliqueAnnularRieszFour_zero_outside d A r hr x v hn
  have hDsupport : ∀ i v, v ∈ UnitCube d → ∀ t ∈ Set.Icc (0:ℝ) 1,
      (¬ ∀ j, |Function.update v i t j-x j| ≤ 2*r) →
      iteratedDerivWithin 6 (fun u => scaledObliqueAnnularRieszFour d A r x (Function.update v i u))
        (Set.Icc (0:ℝ) 1) t = 0 := by
    intro i v _ t ht hn
    apply abs_nonpos_iff.mp
    have h := sixth_coordinate_within_abs_le d hf i v t ht
    rw [scaledObliqueAnnularRieszFour_sixth_zero_outside d A hA r hr x _ hn, norm_zero] at h
    exact h
  have h := cubeQuadrature_local_sixth_order_bound d hm x (2*r) (C/r^10)
    (by positivity) (by positivity) hf.continuous hs hbound hsupport hDsupport
  simpa only [show 2*(2*r) = 4*r by ring] using h

theorem scaledObliqueAnnularRieszFour_eight_bound
    (A : (Fin 8 → ℝ) →L[ℝ] (Fin 8 → ℝ)) (hA : Function.Injective A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 8 ≤ m → ∀ r : ℝ, 0 < r → 1/(m:ℝ) ≤ r →
      ∀ x : Fin 8 → ℝ,
      |cubeQuadrature 8 m (scaledObliqueAnnularRieszFour 8 A r x)-
        cubeIntegral 8 (scaledObliqueAnnularRieszFour 8 A r x)| ≤ C/((m:ℝ)^6*r^2) := by
  obtain ⟨C, hC, hb⟩ := scaledObliqueAnnularRieszFour_quadrature_bound 8 A hA
  refine ⟨859963392*C, by positivity, ?_⟩
  intro m hm r hr hmesh x
  have hmesh' : 2/(m:ℝ) ≤ 2*r := by
    convert mul_le_mul_of_nonneg_left hmesh (by norm_num : (0:ℝ) ≤ 2) using 1
    ring
  have hrad : 4*r+2/(m:ℝ) ≤ 6*r := by linarith
  calc
    _ ≤ (64/(m:ℝ)^6)*(8:ℝ)*(4*r+2/(m:ℝ))^8*(C/r^10) := hb m hm r hr x
    _ ≤ (64/(m:ℝ)^6)*(8:ℝ)*(6*r)^8*(C/r^10) := by gcongr
    _ = (859963392*C)/((m:ℝ)^6*r^2) := by
      have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
      field_simp [hr.ne', hm0]
      ring

theorem e8AnnularRieszFour_quadrature_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 8 ≤ m → ∀ r : ℝ, 0 < r → 1/(m:ℝ) ≤ r →
      ∀ x : Fin 8 → ℝ,
      |cubeQuadrature 8 m (scaledObliqueAnnularRieszFour 8 e8Map r x)-
        cubeIntegral 8 (scaledObliqueAnnularRieszFour 8 e8Map r x)| ≤ C/((m:ℝ)^6*r^2) :=
  scaledObliqueAnnularRieszFour_eight_bound e8Map e8Map_injective

def e8TensorNode (m : ℕ) (v : Fin 8 → NodeIndex m) : Fin 8 → ℝ :=
  e8Map (cubeNode 8 m v)

theorem e8TensorNode_injective {m : ℕ} (hm : 8 ≤ m) : Function.Injective (e8TensorNode m) :=
  e8Map_injective.comp (cubeNode_injective 8 m hm)

#print axioms obliqueRieszFour_eq_dist
#print axioms scaledObliqueAnnularRieszFour_sixth_bounded
#print axioms e8AnnularRieszFour_quadrature_bound
#print axioms e8TensorNode_injective

end SphericalRiesz
