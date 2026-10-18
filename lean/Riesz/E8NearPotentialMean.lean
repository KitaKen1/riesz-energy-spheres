import Riesz.E8PotentialAveraging
import Riesz.E8FullRowMean
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The actual near-background averages at fixed radius R

The near potential at radius R/m has the whole-space value at padded
original nodes and, eventually, at every strictly interior cube point.
Its m^4 normalization is uniformly bounded. The good-node fraction and
Lebesgue dominated convergence identify BOTH averages with the same
actual constant. No sixth derivative of the potential is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace SphericalRiesz
open Boundary

theorem cubeQuadrature_const_mul (d m : ℕ) (a : ℝ) (f : (Fin d → ℝ) → ℝ) :
    cubeQuadrature d m (fun x => a*f x) = a*cubeQuadrature d m f := by
  simp only [cubeQuadrature_as_node_sum, ← Finset.mul_sum]
  ring

theorem unitCube_ae_strict (d : ℕ) :
    ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)).restrict (UnitCube d),
      ∀ i, x i ∈ Ioo (0:ℝ) 1 := by
  have heq : (univ.pi (fun _ : Fin d => Ioo (0:ℝ) 1)) =ᵐ[volume] UnitCube d := by
    rw [unitCube_eq_pi]
    exact Measure.pi_Ioo_ae_eq_pi_Icc
  filter_upwards [heq.filter_mono ae_restrict_le,
    ae_restrict_mem (unitCube_measurableSet d)] with x he hx
  have hop : x ∈ univ.pi (fun _ : Fin d => Ioo (0:ℝ) 1) := he.mpr hx
  simpa only [Set.mem_pi, Set.mem_univ, true_imp_iff] using hop

def e8NearPotential (r : ℝ) (x : Fin 8 → ℝ) : ℝ :=
  ∫ y in UnitCube 8, nearObliqueRieszFour 8 e8Map r x y

theorem e8NearPotential_eq (r : ℝ) (hr : 0 < r) (x : Fin 8 → ℝ) :
    e8NearPotential r x = e8Potential x-e8FarPotential (2*r) x := by
  have h := e8Kernel_integral_partition (2*r) (by positivity) x
  rw [show 2*r/2 = r by ring] at h
  change e8Potential x = e8FarPotential (2*r) x+e8NearPotential r x at h
  linarith

theorem e8NearPotential_continuous (r : ℝ) (hr : 0 < r) :
    Continuous (e8NearPotential r) := by
  have heq : e8NearPotential r = fun x => e8Potential x-e8FarPotential (2*r) x :=
    funext (e8NearPotential_eq r hr)
  rw [heq]
  exact e8Potential_continuous.sub (e8FarPotential_continuous _ (by positivity))

theorem e8NearPotential_eq_of_box (r : ℝ) (hr : 0 < r) (x : Fin 8 → ℝ)
    (hx : ∀ i, 2*r ≤ x i ∧ x i+2*r ≤ 1) :
    e8NearPotential r x = e8NearIntegralConstant*r^4 := by
  unfold e8NearPotential
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact e8Near_integral r hr x
  · intro y hy
    apply e8Near_zero_outside_coordinates r hr
    intro hb
    apply hy
    intro i
    have hi := abs_le.mp (hb i)
    change y i ∈ Icc (0:ℝ) 1
    constructor <;> linarith [(hx i).1, (hx i).2]

def e8ScaledNearPotential (R : ℝ) (m : ℕ) (x : Fin 8 → ℝ) : ℝ :=
  (m:ℝ)^4*e8NearPotential (R/(m:ℝ)) x

theorem e8ScaledNearPotential_bound (R : ℝ) (hR : 0 < R) (m : ℕ) (hm : 0 < m)
    (x : Fin 8 → ℝ) :
    |e8ScaledNearPotential R m x| ≤ e8NearIntegralConstant*R^4 := by
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  rw [e8ScaledNearPotential, abs_mul, abs_of_nonneg (pow_nonneg hmr.le 4)]
  calc
    _ ≤ (m:ℝ)^4*(e8NearIntegralConstant*(R/(m:ℝ))^4) :=
      mul_le_mul_of_nonneg_left (e8Near_cubeIntegral_bound _ (div_pos hR hmr) x) (by positivity)
    _ = _ := by field_simp

theorem e8ScaledNearPotential_continuous (R : ℝ) (hR : 0 < R) (m : ℕ) (hm : 0 < m) :
    Continuous (e8ScaledNearPotential R m) := by
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  exact continuous_const.mul (e8NearPotential_continuous _ (div_pos hR hmr))

theorem e8ScaledNearPotential_padded (R : ℝ) (hR : 0 < R) (m : ℕ) (hm : 0 < m)
    (k : ℕ) (hk : 2*R ≤ (k:ℝ)) (w : Fin 8 → Fin (m-8-2*k)) :
    e8ScaledNearPotential R m (cubeNode 8 m (paddedCubeIndex 8 m k w)) =
      e8NearIntegralConstant*R^4 := by
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  have hpad : InteriorPadding 8 m (fun i => paddedInteriorIndex m k (w i)) (2*R) := by
    intro i
    have h := paddedInteriorIndex_padding 8 m k w i
    constructor <;> linarith [h.1,h.2]
  change (m:ℝ)^4*(∫ y in UnitCube 8, nearObliqueRieszFour 8 e8Map (R/(m:ℝ))
    (interiorCenter 8 m (fun i => paddedInteriorIndex m k (w i))) y) = _
  rw [e8Near_interior_cubeIntegral hR m hm _ hpad]
  field_simp

theorem e8ScaledNearPotential_pointwise_limit (R : ℝ) (hR : 0 < R) (x : Fin 8 → ℝ)
    (hx : ∀ i, x i ∈ Ioo (0:ℝ) 1) :
    Tendsto (fun m : ℕ => e8ScaledNearPotential R m x) atTop
      (𝓝 (e8NearIntegralConstant*R^4)) := by
  have hz : Tendsto (fun m : ℕ => 2*(R/(m:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_div_assoc] using tendsto_const_div_atTop_nhds_zero_nat (2*R)
  have hbox : ∀ᶠ m : ℕ in atTop, ∀ i : Fin 8,
      2*(R/(m:ℝ)) ≤ x i ∧ x i+2*(R/(m:ℝ)) ≤ 1 := by
    apply eventually_all.mpr
    intro i
    filter_upwards [hz.eventually (gt_mem_nhds (hx i).1),
      hz.eventually (gt_mem_nhds (by linarith [(hx i).2] : (0:ℝ) < 1-x i))] with m h₁ h₂
    constructor <;> linarith
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ),hbox] with m hm hb
  have hmr : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  rw [e8ScaledNearPotential, e8NearPotential_eq_of_box _ (div_pos hR hmr) x hb]
  field_simp

theorem e8ScaledNearPotential_quadrature_padding_bound (R : ℝ) (hR : 0 < R)
    (m : ℕ) (hm : 8 ≤ m) (k : ℕ) (hk : 2*R ≤ (k:ℝ)) :
    |cubeQuadrature 8 m (e8ScaledNearPotential R m)-e8NearIntegralConstant*R^4| ≤
      (2*e8NearIntegralConstant*R^4)*(1-paddedCubeFraction 8 m k) := by
  classical
  have hm0 : 0 < m := by omega
  have hmr : (0:ℝ) < m := by exact_mod_cast hm0
  have hcard : Fintype.card (Fin 8 → NodeIndex m) = m^8 := cubeNode_card 8 m hm
  have hn : 0 < Fintype.card (Fin 8 → NodeIndex m) := by rw [hcard]; positivity
  have hg (v : Fin 8 → NodeIndex m) (hv : v ∈ paddedCubeSet 8 m k) :
      |e8ScaledNearPotential R m (cubeNode 8 m v)-e8NearIntegralConstant*R^4| ≤ 0 := by
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hv
    rw [e8ScaledNearPotential_padded R hR m hm0 k hk w, sub_self, abs_zero]
  have hb (v : Fin 8 → NodeIndex m) :
      |e8ScaledNearPotential R m (cubeNode 8 m v)-e8NearIntegralConstant*R^4| ≤
        2*e8NearIntegralConstant*R^4 := by
    have h := e8ScaledNearPotential_bound R hR m hm0 (cubeNode 8 m v)
    have hc := e8NearIntegralConstant_nonneg
    have ht := abs_sub (e8ScaledNearPotential R m (cubeNode 8 m v)) (e8NearIntegralConstant*R^4)
    rw [abs_of_nonneg (by positivity : 0 ≤ e8NearIntegralConstant*R^4)] at ht
    linarith
  have h := finite_mean_error_bound (paddedCubeSet 8 m k)
    (fun v => e8ScaledNearPotential R m (cubeNode 8 m v)) (e8NearIntegralConstant*R^4)
    0 (2*e8NearIntegralConstant*R^4) le_rfl hn hg (fun v _ => hb v)
  have hbad : ((Finset.univ \ paddedCubeSet 8 m k).card:ℝ) =
      (m:ℝ)^8-((m-8-2*k:ℕ):ℝ)^8 := by
    have ht := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (paddedCubeSet 8 m k))
    rw [paddedCubeSet_card, Finset.card_univ, hcard] at ht
    have ht' : ((Finset.univ \ paddedCubeSet 8 m k).card:ℝ)+((m-8-2*k:ℕ):ℝ)^8 = (m:ℝ)^8 := by
      exact_mod_cast ht
    linarith
  simp only [hcard,Nat.cast_pow,zero_add] at h
  rw [hbad] at h
  rw [cubeQuadrature_as_node_sum]
  convert h using 1
  unfold paddedCubeFraction
  field_simp

theorem e8ScaledNearPotential_quadrature_limit (R : ℝ) (hR : 0 < R) :
    Tendsto (fun m : ℕ => cubeQuadrature 8 m (e8ScaledNearPotential R m)) atTop
      (𝓝 (e8NearIntegralConstant*R^4)) := by
  obtain ⟨k,hk⟩ := exists_nat_ge (2*R)
  have hf : Tendsto (fun m : ℕ =>
      (2*e8NearIntegralConstant*R^4)*(1-paddedCubeFraction 8 m k)) atTop (𝓝 0) := by
    simpa using ((paddedCubeFraction_limit 8 k).const_sub 1).const_mul
      (2*e8NearIntegralConstant*R^4)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun m => norm_nonneg _)) _ hf
  filter_upwards [eventually_ge_atTop (8:ℕ)] with m hm
  simpa only [Real.norm_eq_abs] using e8ScaledNearPotential_quadrature_padding_bound R hR m hm k hk

theorem e8ScaledNearPotential_integral_limit (R : ℝ) (hR : 0 < R) :
    Tendsto (fun m : ℕ => ∫ x in UnitCube 8, e8ScaledNearPotential R m x) atTop
      (𝓝 (e8NearIntegralConstant*R^4)) := by
  have hmeas : ∀ᶠ m : ℕ in atTop, AEStronglyMeasurable (e8ScaledNearPotential R m)
      (volume.restrict (UnitCube 8)) := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with m hm
    exact (e8ScaledNearPotential_continuous R hR m (by omega)).aestronglyMeasurable.restrict
  have hb : ∀ᶠ m : ℕ in atTop, ∀ᵐ x ∂volume.restrict (UnitCube 8),
      ‖e8ScaledNearPotential R m x‖ ≤ e8NearIntegralConstant*R^4 := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with m hm
    exact Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using e8ScaledNearPotential_bound R hR m (by omega) x)
  have hi : Integrable (fun _ : Fin 8 → ℝ => e8NearIntegralConstant*R^4)
      (volume.restrict (UnitCube 8)) :=
    continuousOn_const.integrableOn_compact (unitCube_isCompact 8)
  have hl : ∀ᵐ x ∂volume.restrict (UnitCube 8),
      Tendsto (fun m : ℕ => e8ScaledNearPotential R m x) atTop
        (𝓝 (e8NearIntegralConstant*R^4)) :=
    (unitCube_ae_strict 8).mono (fun x hx => e8ScaledNearPotential_pointwise_limit R hR x hx)
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun _ : Fin 8 → ℝ => e8NearIntegralConstant*R^4) hmeas hb hi hl
  simpa only [integral_const, Measure.real, Measure.restrict_apply_univ,
    unitCube_volume, ENNReal.toReal_one, smul_eq_mul, one_mul] using h

theorem e8ScaledNearPotential_background_limit (R : ℝ) (hR : 0 < R) :
    Tendsto (fun m : ℕ => cubeQuadrature 8 m (e8ScaledNearPotential R m)-
      ∫ x in UnitCube 8, e8ScaledNearPotential R m x) atTop (𝓝 0) := by
  simpa only [sub_self] using (e8ScaledNearPotential_quadrature_limit R hR).sub
    (e8ScaledNearPotential_integral_limit R hR)

#print axioms cubeQuadrature_const_mul
#print axioms unitCube_ae_strict
#print axioms e8NearPotential_eq
#print axioms e8NearPotential_continuous
#print axioms e8NearPotential_eq_of_box
#print axioms e8ScaledNearPotential_bound
#print axioms e8ScaledNearPotential_continuous
#print axioms e8ScaledNearPotential_padded
#print axioms e8ScaledNearPotential_pointwise_limit
#print axioms e8ScaledNearPotential_quadrature_padding_bound
#print axioms e8ScaledNearPotential_quadrature_limit
#print axioms e8ScaledNearPotential_integral_limit
#print axioms e8ScaledNearPotential_background_limit

end SphericalRiesz
