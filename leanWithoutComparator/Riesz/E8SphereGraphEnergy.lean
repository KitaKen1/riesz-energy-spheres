import Riesz.E8SphereGraph

/-!
# Actual spherical configurations from every original corrected node

This is a SINGLE small spherical patch with exactly m^8 distinct points,
not an asymptotically optimal global configuration. Its chordal pair energy
is exactly the scaled pair kernel of the normalized graph. The near
background estimates here still refer to coordinate Lebesgue measure;
no equality with surface measure is assumed or asserted.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SphericalRiesz
open Boundary

def e8SphereGraphConfiguration (m : ℕ) (hm : 8 ≤ m) (ε : ℝ) (hε : 0 < ε)
    (hsmall : ε*e8GraphRadius ≤ 1/2) : Configuration (m^8) :=
  (Fintype.equivFinOfCardEq (cubeNode_card 8 m hm)).symm.toEmbedding.trans
    (e8SphereGraphNodeEmbedding m hm ε hε hsmall)

theorem e8SphereGraphConfiguration_separated (m : ℕ) (hm : 8 ≤ m) (ε : ℝ) (hε : 0 < ε)
    (hsmall : ε*e8GraphRadius ≤ 1/2) (i j : Fin (m^8)) (hij : i ≠ j) :
    ε*e8SeparationConstant/(m:ℝ) <
      dist (e8SphereGraphConfiguration m hm ε hε hsmall i)
        (e8SphereGraphConfiguration m hm ε hε hsmall j) := by
  exact e8SphereGraphNode_separated m hm ε hε hsmall
    ((Fintype.equivFinOfCardEq (cubeNode_card 8 m hm)).symm i)
    ((Fintype.equivFinOfCardEq (cubeNode_card 8 m hm)).symm j)
    (fun h => hij ((Fintype.equivFinOfCardEq (cubeNode_card 8 m hm)).symm.injective h))

theorem e8SphereGraph_kernel_scaling (ε : ℝ) (hε : 0 < ε)
    (hsmall : ε*e8GraphRadius ≤ 1/2) (x y : UnitCube 8) :
    ε^4*sphereKernel4 (e8SphereGraphCubeEmbedding ε hε hsmall x)
        (e8SphereGraphCubeEmbedding ε hε hsmall y) =
      curvedRieszFour (e8NormalizedSphereGraph ε) x y := by
  unfold sphereKernel4 curvedRieszFour
  change ε^4*(dist (e8SphereGraph ε x) (e8SphereGraph ε y))⁻¹^4 = _
  rw [e8SphereGraph_scaled_distance ε hε,mul_inv,mul_pow]
  field_simp

theorem energy4_eq_sum_all {N : ℕ} (X : Configuration N) :
    energy4 X = ∑ i : Fin N, ∑ j : Fin N, sphereKernel4 (X i) (X j) := by
  unfold energy4 sphereKernel4
  apply Finset.sum_congr rfl
  intro i _
  have h := Finset.sum_erase_add (s := Finset.univ) (a := i)
    (fun j : Fin N => (dist (X i) (X j))⁻¹^4) (Finset.mem_univ i)
  simpa only [dist_self,inv_zero,zero_pow (by decide : (4:ℕ) ≠ 0),add_zero] using h

theorem e8SphereGraphConfiguration_scaled_energy (m : ℕ) (hm : 8 ≤ m) (ε : ℝ) (hε : 0 < ε)
    (hsmall : ε*e8GraphRadius ≤ 1/2) :
    ε^4*energy4 (e8SphereGraphConfiguration m hm ε hε hsmall) =
      ∑ v : Fin 8 → NodeIndex m, ∑ w : Fin 8 → NodeIndex m,
        curvedRieszFour (e8NormalizedSphereGraph ε) (cubeNode 8 m v) (cubeNode 8 m w) := by
  let e := Fintype.equivFinOfCardEq (cubeNode_card 8 m hm)
  rw [energy4_eq_sum_all]
  have hreindex : (∑ i : Fin (m^8), ∑ j : Fin (m^8),
      sphereKernel4 (e8SphereGraphConfiguration m hm ε hε hsmall i)
        (e8SphereGraphConfiguration m hm ε hε hsmall j)) =
      ∑ v : Fin 8 → NodeIndex m, ∑ w : Fin 8 → NodeIndex m,
        sphereKernel4 (e8SphereGraphNodeEmbedding m hm ε hε hsmall v)
          (e8SphereGraphNodeEmbedding m hm ε hε hsmall w) := by
    rw [← e.sum_comp]
    apply Finset.sum_congr rfl
    intro v _
    rw [← e.sum_comp]
    simp only [e8SphereGraphConfiguration,Function.Embedding.trans_apply,
      Equiv.toEmbedding_apply,Equiv.symm_apply_apply,e]
  rw [hreindex,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  let xv : UnitCube 8 := ⟨cubeNode 8 m v,
    fun i => ⟨(cubeNode_mem_open 8 m hm v i).1.le,(cubeNode_mem_open 8 m hm v i).2.le⟩⟩
  let xw : UnitCube 8 := ⟨cubeNode 8 m w,
    fun i => ⟨(cubeNode_mem_open 8 m hm w i).1.le,(cubeNode_mem_open 8 m hm w i).2.le⟩⟩
  exact e8SphereGraph_kernel_scaling ε hε hsmall xv xw

theorem e8SphereGraphConfiguration_energy_quadrature (m : ℕ) (hm : 8 ≤ m)
    (ε : ℝ) (hε : 0 < ε) (hsmall : ε*e8GraphRadius ≤ 1/2) :
    ε^4*energy4 (e8SphereGraphConfiguration m hm ε hε hsmall)/(m:ℝ)^16 =
      cubeQuadrature 8 m (fun x => cubeQuadrature 8 m
        (curvedRieszFour (e8NormalizedSphereGraph ε) x)) := by
  rw [e8SphereGraphConfiguration_scaled_energy m hm ε hε hsmall]
  simp_rw [cubeQuadrature_as_node_sum,← Finset.sum_div]
  rw [div_div,← pow_add]

def e8SphereGraphNearBackground (ε R : ℝ) (m : ℕ) : ℝ :=
  (m:ℝ)^4*(cubeQuadrature 8 m (curvedNearPotential (e8NormalizedSphereGraph ε) (R/(m:ℝ)))-
    ∫ x in UnitCube 8, curvedNearPotential (e8NormalizedSphereGraph ε) (R/(m:ℝ)) x)

theorem e8ScaledNearBackground_eq (R : ℝ) (m : ℕ) :
    cubeQuadrature 8 m (e8ScaledNearPotential R m)-
      (∫ x in UnitCube 8, e8ScaledNearPotential R m x) =
      (m:ℝ)^4*(cubeQuadrature 8 m (e8NearPotential (R/(m:ℝ)))-
        ∫ x in UnitCube 8, e8NearPotential (R/(m:ℝ)) x) := by
  unfold e8ScaledNearPotential
  rw [cubeQuadrature_const_mul,integral_const_mul]
  ring

theorem e8SphereGraphNearBackground_bound (ε : ℝ) (hε : 0 < ε)
    (hsmall : ε*e8GraphRadius ≤ 1/4) (R : ℝ) (hR : 0 < R) (m : ℕ) (hm : 8 ≤ m) :
    |e8SphereGraphNearBackground ε R m| ≤
      |cubeQuadrature 8 m (e8ScaledNearPotential R m)-
        ∫ x in UnitCube 8, e8ScaledNearPotential R m x|+
      512*(ε*e8GraphRadius)^2*e8NearIntegralConstant*R^4 := by
  have h := e8SphereGraph_near_background_error ε hε hsmall R hR m hm
  rw [e8ScaledNearBackground_eq]
  unfold e8SphereGraphNearBackground
  calc
    _ ≤ |(m:ℝ)^4*(cubeQuadrature 8 m (e8NearPotential (R/(m:ℝ)))-
        ∫ x in UnitCube 8, e8NearPotential (R/(m:ℝ)) x)|+
        |(m:ℝ)^4*((cubeQuadrature 8 m (curvedNearPotential (e8NormalizedSphereGraph ε) (R/(m:ℝ)))-
          ∫ x in UnitCube 8, curvedNearPotential (e8NormalizedSphereGraph ε) (R/(m:ℝ)) x)-
          (cubeQuadrature 8 m (e8NearPotential (R/(m:ℝ)))-
          ∫ x in UnitCube 8, e8NearPotential (R/(m:ℝ)) x))| := by
      convert abs_add_le
        ((m:ℝ)^4*(cubeQuadrature 8 m (e8NearPotential (R/(m:ℝ)))-
          ∫ x in UnitCube 8, e8NearPotential (R/(m:ℝ)) x))
        ((m:ℝ)^4*((cubeQuadrature 8 m (curvedNearPotential (e8NormalizedSphereGraph ε) (R/(m:ℝ)))-
          ∫ x in UnitCube 8, curvedNearPotential (e8NormalizedSphereGraph ε) (R/(m:ℝ)) x)-
          (cubeQuadrature 8 m (e8NearPotential (R/(m:ℝ)))-
          ∫ x in UnitCube 8, e8NearPotential (R/(m:ℝ)) x))) using 1
      congr 1
      ring
    _ ≤ _ := add_le_add le_rfl h

theorem e8SphereGraphNearBackground_eventual_bound (ε : ℝ) (hε : 0 < ε)
    (hsmall : ε*e8GraphRadius ≤ 1/4) (R : ℝ) (hR : 0 < R) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, |e8SphereGraphNearBackground ε R m| <
      δ+512*(ε*e8GraphRadius)^2*e8NearIntegralConstant*R^4 := by
  have hlim := (e8ScaledNearPotential_background_limit R hR).norm
  have he : ∀ᶠ m : ℕ in atTop,
      |cubeQuadrature 8 m (e8ScaledNearPotential R m)-
        ∫ x in UnitCube 8, e8ScaledNearPotential R m x| < δ := by
    simpa only [norm_zero,Real.norm_eq_abs] using hlim.eventually (gt_mem_nhds (by simpa using hδ))
  filter_upwards [eventually_ge_atTop (8:ℕ),he] with m hm hh
  exact lt_of_le_of_lt (e8SphereGraphNearBackground_bound ε hε hsmall R hR m hm)
    (add_lt_add_left hh _)

theorem e8SphereGraphNearBackground_limit_along (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0)) (hpos : ∀ᶠ m : ℕ in atTop, 0 < e m)
    (R : ℝ) (hR : 0 < R) :
    Tendsto (fun m : ℕ => e8SphereGraphNearBackground (e m) R m) atTop (𝓝 0) := by
  have hsmall : ∀ᶠ m : ℕ in atTop, e m*e8GraphRadius ≤ 1/4 := by
    have h := he.mul_const e8GraphRadius
    have hh := h.eventually (gt_mem_nhds (by norm_num : (0:ℝ)*e8GraphRadius < 1/4))
    exact hh.mono (fun _ h => h.le)
  have hcurve : Tendsto (fun m : ℕ => 512*(e m*e8GraphRadius)^2*e8NearIntegralConstant*R^4)
      atTop (𝓝 0) := by
    have h := (((he.mul_const e8GraphRadius).pow 2).const_mul 512).mul_const e8NearIntegralConstant
    simpa using h.mul_const (R^4)
  have hnear : Tendsto (fun m : ℕ => |cubeQuadrature 8 m (e8ScaledNearPotential R m)-
      ∫ x in UnitCube 8, e8ScaledNearPotential R m x|) atTop (𝓝 0) := by
    simpa only [Real.norm_eq_abs,norm_zero] using (e8ScaledNearPotential_background_limit R hR).norm
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _
    (by simpa using hnear.add hcurve)
  filter_upwards [eventually_ge_atTop (8:ℕ),hsmall,hpos] with m hm hs hp
  exact e8SphereGraphNearBackground_bound (e m) hp hs R hR m hm

theorem e8SmoothGraphHeight_cube_bound (ε : ℝ) (x : Fin 8 → ℝ) (hx : x ∈ UnitCube 8) :
    |e8SmoothGraphHeight ε x| ≤ |ε| *e8GraphRadius^2 := by
  have hheight : 0 ≤ e8GraphHeight ε x := Real.sqrt_nonneg _
  have hden : 0 < 1+e8GraphHeight ε x := by linarith
  have hb := e8Graph_cube_norm_bound x hx
  unfold e8SmoothGraphHeight
  rw [abs_div,abs_mul,abs_neg,abs_of_nonneg (sq_nonneg ‖e8CoordinateLinearEquiv x‖),abs_of_pos hden]
  calc
    _ ≤ |ε| *‖e8CoordinateLinearEquiv x‖^2 :=
      div_le_self (by positivity) (by linarith)
    _ ≤ _ := by gcongr

theorem e8SmoothNormalizedSphereGraph_cube_bound (ε : ℝ) (x : Fin 8 → ℝ)
    (hx : x ∈ UnitCube 8) :
    dist (e8SmoothNormalizedSphereGraph ε x) (ambientCons9 (0,e8Map x)) ≤
      |ε| *e8GraphRadius^2 := by
  have hs := ambientCons9_dist_sq (e8SmoothGraphHeight ε x,e8Map x) (0,e8Map x)
  simp only [sub_zero,dist_self,zero_pow (by decide : (2:ℕ) ≠ 0),add_zero] at hs
  have he : dist (e8SmoothNormalizedSphereGraph ε x) (ambientCons9 (0,e8Map x)) =
      |e8SmoothGraphHeight ε x| := by
    change dist (ambientCons9 (e8SmoothGraphHeight ε x,e8Map x))
      (ambientCons9 (0,e8Map x)) = _
    nlinarith [sq_abs (e8SmoothGraphHeight ε x),abs_nonneg (e8SmoothGraphHeight ε x),
      (dist_nonneg : 0 ≤ dist (ambientCons9 (e8SmoothGraphHeight ε x,e8Map x))
        (ambientCons9 (0,e8Map x)))]
  rw [he]
  exact e8SmoothGraphHeight_cube_bound ε x hx

theorem e8SmoothNormalizedSphereGraph_uniform_limit :
    TendstoUniformlyOn e8SmoothNormalizedSphereGraph
      (fun x => ambientCons9 (0,e8Map x)) (𝓝 (0:ℝ)) (UnitCube 8) := by
  have hlim : Tendsto (fun ε : ℝ => |ε| *e8GraphRadius^2) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.tendsto (0:ℝ)).mul_const (e8GraphRadius^2)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro δ hδ
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with ε hε x hx
  rw [dist_comm]
  exact (e8SmoothNormalizedSphereGraph_cube_bound ε x hx).trans_lt hε

end SphericalRiesz
