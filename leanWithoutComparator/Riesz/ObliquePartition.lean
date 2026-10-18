import Riesz.ObliqueAnnulus

/-!
# The actual far part in an injective basis

Finite telescoping and the original node rule give a center-uniform far
error for every injective basis, then for the concrete E8 coordinate map.
This removes only the far error. The near lattice coefficient, physical
volume conversion, sphere charts, boundaries and all-N recovery are open.
-/

set_option autoImplicit false
noncomputable section
open scoped ContDiff

namespace SphericalRiesz
open Boundary

def nearObliqueRieszFour (d : ℕ) (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (r : ℝ) (x v : Fin d → ℝ) : ℝ :=
  obliqueRieszFour d A x v*outerUnitBump d (r⁻¹ • (v-x))

def farObliqueRieszFour (d : ℕ) (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (r : ℝ) (x v : Fin d → ℝ) : ℝ :=
  obliqueRieszFour d A x v-nearObliqueRieszFour d A (r/2) x v

theorem scaledObliqueAnnularRieszFour_eq_near_sub (d : ℕ) (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (r : ℝ) (hr : 0 < r)
    (x v : Fin d → ℝ) : scaledObliqueAnnularRieszFour d A r x v =
      nearObliqueRieszFour d A r x v-nearObliqueRieszFour d A (r/2) x v := by
  rw [scaledObliqueAnnularRieszFour_eq_kernel d A r hr, unitAnnularCutoff,
    innerUnitBump_eq_outer_scaled, nearObliqueRieszFour, nearObliqueRieszFour]
  have harg : (2:ℝ) • (r⁻¹ • (v-x)) = (r/2)⁻¹ • (v-x) := by
    rw [smul_smul]
    congr 1
    simp only [div_eq_mul_inv, mul_inv, inv_inv]
    ring
  rw [harg]
  ring

/-- Both endpoints of the finite partition are explicit. -/
theorem oblique_annular_partition_sum (d n : ℕ) (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (r : ℝ) (hr : 0 < r) (x v : Fin d → ℝ) :
    (∑ k ∈ Finset.range n, scaledObliqueAnnularRieszFour d A ((2:ℝ)^k*r) x v) =
      nearObliqueRieszFour d A (((2:ℝ)^n*r)/2) x v-nearObliqueRieszFour d A (r/2) x v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih,
      scaledObliqueAnnularRieszFour_eq_near_sub d A _ (by positivity)]
    have heq : ((2:ℝ)^(n+1)*r)/2 = (2:ℝ)^n*r := by rw [pow_succ]; ring
    rw [heq]
    ring

theorem nearObliqueRieszFour_eq_kernel_of_norm_le (d : ℕ) (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (r : ℝ) (hr : 0 < r)
    (x v : Fin d → ℝ) (hv : ‖v-x‖ ≤ r) :
    nearObliqueRieszFour d A r x v = obliqueRieszFour d A x v := by
  have hb : outerUnitBump d (r⁻¹ • (v-x)) = 1 := by
    apply (outerUnitBump d).one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖r⁻¹ • (v-x)‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), ← div_eq_inv_mul]
    exact (div_le_one hr).mpr hv
  rw [nearObliqueRieszFour, hb, mul_one]

theorem farObliqueRieszFour_eq_annular_sum_on (d n : ℕ) (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (r : ℝ) (hr : 0 < r)
    (x : Fin d → ℝ)
    (hcover : ∀ v ∈ UnitCube d, ‖v-x‖ ≤ ((2:ℝ)^n*r)/2) :
    Set.EqOn (farObliqueRieszFour d A r x)
      (fun v => ∑ k ∈ Finset.range n, scaledObliqueAnnularRieszFour d A ((2:ℝ)^k*r) x v)
      (UnitCube d) := by
  intro v hv
  dsimp only
  rw [oblique_annular_partition_sum d n A r hr x v,
    nearObliqueRieszFour_eq_kernel_of_norm_le d A _ (by positivity) x v (hcover v hv)]
  rfl

theorem farObliqueRieszFour_contDiffOn_cube (d : ℕ) (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (hA : Function.Injective A) (r : ℝ) (hr : 0 < r) (x : Fin d → ℝ) :
    ContDiffOn ℝ 6 (farObliqueRieszFour d A r x) (UnitCube d) := by
  obtain ⟨n, hn⟩ := exists_annular_cover d r hr x
  have h : ContDiffOn ℝ 6
      (fun v => ∑ k ∈ Finset.range n, scaledObliqueAnnularRieszFour d A ((2:ℝ)^k*r) x v)
      (UnitCube d) :=
    ContDiffOn.sum (fun k _ => ((scaledObliqueAnnularRieszFour_contDiff d A hA _ x).of_le (by simp)).contDiffOn)
  exact h.congr (farObliqueRieszFour_eq_annular_sum_on d n A r hr x hn)

theorem oblique_far_near_kernel_partition (d : ℕ) (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (r : ℝ) (x v : Fin d → ℝ) :
    farObliqueRieszFour d A r x v+nearObliqueRieszFour d A (r/2) x v = obliqueRieszFour d A x v := by
  unfold farObliqueRieszFour
  ring

theorem farObliqueRieszFour_zero_inside (d : ℕ) (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (r : ℝ) (hr : 0 < r) (x v : Fin d → ℝ)
    (hv : ‖v-x‖ ≤ r/2) : farObliqueRieszFour d A r x v = 0 := by
  rw [farObliqueRieszFour, nearObliqueRieszFour_eq_kernel_of_norm_le d A _ (by positivity) x v hv, sub_self]

theorem farObliqueRieszFour_eq_kernel_outside (d : ℕ) (A : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) (r : ℝ) (hr : 0 < r)
    (x v : Fin d → ℝ) (hv : r ≤ ‖v-x‖) : farObliqueRieszFour d A r x v = obliqueRieszFour d A x v := by
  have hb : outerUnitBump d ((r/2)⁻¹ • (v-x)) = 0 := by
    apply (outerUnitBump d).zero_of_le_dist
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (r/2)⁻¹),
      ← div_eq_inv_mul]
    change 2 ≤ ‖v-x‖/(r/2)
    apply (le_div_iff₀ (by positivity : 0 < r/2)).mpr
    linarith
  rw [farObliqueRieszFour, nearObliqueRieszFour, hb, mul_zero, sub_zero]

/-- The starting radius is retained, so the far error decreases as r^-2. -/
theorem oblique_annular_error_sum_bound
    (A : (Fin 8 → ℝ) →L[ℝ] (Fin 8 → ℝ)) (hA : Function.Injective A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 8 ≤ m → ∀ r : ℝ, 0 < r → 1/(m:ℝ) ≤ r →
      ∀ n : ℕ, ∀ x : Fin 8 → ℝ,
      |∑ k ∈ Finset.range n,
        (cubeQuadrature 8 m (scaledObliqueAnnularRieszFour 8 A ((2:ℝ)^k*r) x)-
          cubeIntegral 8 (scaledObliqueAnnularRieszFour 8 A ((2:ℝ)^k*r) x))| ≤
        C/((m:ℝ)^6*r^2) := by
  obtain ⟨C, hC, hb⟩ := scaledObliqueAnnularRieszFour_eight_bound A hA
  refine ⟨(4/3:ℝ)*C, by positivity, ?_⟩
  intro m hm r hr hmesh n x
  let e (k : ℕ) := cubeQuadrature 8 m (scaledObliqueAnnularRieszFour 8 A ((2:ℝ)^k*r) x)-
    cubeIntegral 8 (scaledObliqueAnnularRieszFour 8 A ((2:ℝ)^k*r) x)
  have he (k : ℕ) : |e k| ≤ (C/((m:ℝ)^6*r^2))*(1/4:ℝ)^k := by
    have h2 : 0 < (2:ℝ)^k := by positivity
    have hr' : r ≤ (2:ℝ)^k*r := by
      nlinarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := k)]
    have h := hb m hm _ (by positivity) (hmesh.trans hr') x
    have hp : (4:ℝ)^k = ((2:ℝ)^k)^2 := by
      rw [← pow_mul, mul_comm k 2, pow_mul]
      norm_num
    calc
      _ ≤ C/((m:ℝ)^6*((2:ℝ)^k*r)^2) := h
      _ = _ := by
        simp only [div_pow, one_pow, hp, mul_pow]
        field_simp [h2.ne', hr.ne']
  calc
    _ ≤ ∑ k ∈ Finset.range n, |e k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, (C/((m:ℝ)^6*r^2))*(1/4:ℝ)^k :=
      Finset.sum_le_sum (fun k _ => he k)
    _ = (C/((m:ℝ)^6*r^2))*(∑ k ∈ Finset.range n, (1/4:ℝ)^k) := (Finset.mul_sum _ _ _).symm
    _ ≤ (C/((m:ℝ)^6*r^2))*(4/3:ℝ) :=
      mul_le_mul_of_nonneg_left (dyadic_quarter_sum_le n) (by positivity)
    _ = _ := by ring

/-- The actual far kernel, with the near term removed, at the original nodes. -/
theorem farObliqueRieszFour_quadrature_bound
    (A : (Fin 8 → ℝ) →L[ℝ] (Fin 8 → ℝ)) (hA : Function.Injective A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 8 ≤ m → ∀ r : ℝ, 0 < r → 1/(m:ℝ) ≤ r →
      ∀ x : Fin 8 → ℝ,
      |cubeQuadrature 8 m (farObliqueRieszFour 8 A r x)-cubeIntegral 8 (farObliqueRieszFour 8 A r x)| ≤
        C/((m:ℝ)^6*r^2) := by
  obtain ⟨C, hC, hb⟩ := oblique_annular_error_sum_bound A hA
  refine ⟨C, hC, ?_⟩
  intro m hm r hr hmesh x
  obtain ⟨n, hn⟩ := exists_annular_cover 8 r hr x
  have heq := farObliqueRieszFour_eq_annular_sum_on 8 n A r hr x hn
  rw [cubeQuadrature_congr 8 m hm heq, cubeIntegral_congr 8 heq,
    cubeQuadrature_finset_sum, cubeIntegral_finset_sum 8 _ _
      (fun k _ => (scaledObliqueAnnularRieszFour_contDiff 8 A hA _ x).continuous),
    ← Finset.sum_sub_distrib]
  exact hb m hm r hr hmesh n x

/-- Far errors can be made arbitrarily small at the second-term scale.
This leaves the near part, whose lattice coefficient still needs proof. -/
theorem farObliqueRieszFour_error_small
    (A : (Fin 8 → ℝ) →L[ℝ] (Fin 8 → ℝ)) (hA : Function.Injective A) :
    ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, 1 ≤ L ∧ ∀ m : ℕ, 8 ≤ m → ∀ x : Fin 8 → ℝ,
      |cubeQuadrature 8 m (farObliqueRieszFour 8 A (L/(m:ℝ)) x)-
        cubeIntegral 8 (farObliqueRieszFour 8 A (L/(m:ℝ)) x)| ≤ ε/(m:ℝ)^4 := by
  obtain ⟨C, hC, hb⟩ := farObliqueRieszFour_quadrature_bound A hA
  intro ε hε
  let L := 1+C/ε
  have hL : 1 ≤ L := by
    dsimp only [L]
    linarith [div_nonneg hC hε.le]
  have hL0 : 0 < L := by linarith
  refine ⟨L, hL, ?_⟩
  intro m hm x
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hmesh : 1/(m:ℝ) ≤ L/(m:ℝ) := div_le_div_of_nonneg_right hL hm0.le
  have hCε : C ≤ ε*L^2 := by
    have hlin : C ≤ ε*L := by dsimp only [L]; field_simp; nlinarith
    have hs : L ≤ L^2 := by nlinarith
    nlinarith
  calc
    _ ≤ C/((m:ℝ)^6*(L/(m:ℝ))^2) := hb m hm _ (div_pos hL0 hm0) hmesh x
    _ = (C/L^2)/(m:ℝ)^4 := by field_simp [hL0.ne', hm0.ne']
    _ ≤ ε/(m:ℝ)^4 := div_le_div_of_nonneg_right
      ((div_le_iff₀ (sq_pos_of_pos hL0)).mpr hCε) (pow_pos hm0 4).le

/-- Concrete E8 coordinates: the far error is negligible at the m^-4 scale. -/
theorem e8FarRieszFour_error_small :
    ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, 1 ≤ L ∧ ∀ m : ℕ, 8 ≤ m → ∀ x : Fin 8 → ℝ,
      |cubeQuadrature 8 m (farObliqueRieszFour 8 e8Map (L/(m:ℝ)) x)-
        cubeIntegral 8 (farObliqueRieszFour 8 e8Map (L/(m:ℝ)) x)| ≤ ε/(m:ℝ)^4 :=
  farObliqueRieszFour_error_small e8Map e8Map_injective

/-- Independent finite-sum formulation retaining exactly the original nodes. -/
theorem e8FarRieszFour_node_error_small :
    ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, 1 ≤ L ∧ ∀ m : ℕ, 8 ≤ m → ∀ x : Fin 8 → ℝ,
      |(∑ v : Fin 8 → NodeIndex m,
          (dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8))
            (WithLp.toLp 2 (e8TensorNode m v)))⁻¹^4*
            (1-outerUnitBump 8 ((L/(2*(m:ℝ)))⁻¹ • (cubeNode 8 m v-x))))/(m:ℝ)^8-
        cubeIntegral 8 (farObliqueRieszFour 8 e8Map (L/(m:ℝ)) x)| ≤ ε/(m:ℝ)^4 := by
  intro ε hε
  obtain ⟨L, hL, hb⟩ := e8FarRieszFour_error_small ε hε
  refine ⟨L, hL, ?_⟩
  intro m hm x
  have h := hb m hm x
  rw [cubeQuadrature_as_node_sum] at h
  convert h using 1
  congr 3
  apply Finset.sum_congr rfl
  intro v _
  unfold farObliqueRieszFour nearObliqueRieszFour
  rw [obliqueRieszFour_eq_dist]
  change _ = (dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8))
      (WithLp.toLp 2 (e8TensorNode m v)))⁻¹^4-
      (dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8))
      (WithLp.toLp 2 (e8TensorNode m v)))⁻¹^4*
        outerUnitBump 8 (((L/(m:ℝ))/2)⁻¹ • (cubeNode 8 m v-x))
  rw [show (L/(m:ℝ))/2 = L/(2*(m:ℝ)) by ring]
  ring

#print axioms oblique_annular_partition_sum
#print axioms farObliqueRieszFour_quadrature_bound
#print axioms e8FarRieszFour_error_small
#print axioms e8FarRieszFour_node_error_small

end SphericalRiesz
