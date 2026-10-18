import Riesz.AnnularQuadrature
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# The finite annular partition and the actual far part

Two copies of one fixed bump give an exact telescoping partition. An
outer radius can cover the cube, so the actual far kernel is a finite
sum of the already verified smooth annular kernels on that cube.
The near part is retained explicitly; no estimate for it is assumed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff

namespace SphericalRiesz
open Boundary

theorem innerUnitBump_eq_outer_scaled (d : ℕ) (v : Fin d → ℝ) :
    innerUnitBump d v = outerUnitBump d ((2:ℝ) • v) := by
  norm_num [ContDiffBump.apply, innerUnitBump, outerUnitBump]

def nearRieszFour (d : ℕ) (r : ℝ) (x v : Fin d → ℝ) : ℝ :=
  flatRieszFour d x v*outerUnitBump d (r⁻¹ • (v-x))

def farRieszFour (d : ℕ) (r : ℝ) (x v : Fin d → ℝ) : ℝ :=
  flatRieszFour d x v-nearRieszFour d (r/2) x v

theorem scaledAnnularRieszFour_eq_near_sub (d : ℕ) (r : ℝ) (hr : 0 < r)
    (x v : Fin d → ℝ) : scaledAnnularRieszFour d r x v =
      nearRieszFour d r x v-nearRieszFour d (r/2) x v := by
  rw [scaledAnnularRieszFour_eq_kernel d r hr, unitAnnularCutoff,
    innerUnitBump_eq_outer_scaled, nearRieszFour, nearRieszFour]
  have harg : (2:ℝ) • (r⁻¹ • (v-x)) = (r/2)⁻¹ • (v-x) := by
    rw [smul_smul]
    congr 1
    simp only [div_eq_mul_inv, mul_inv, inv_inv]
    ring
  rw [harg]
  ring

/-- Both endpoints of the finite partition are explicit. -/
theorem annular_partition_sum (d n : ℕ) (r : ℝ) (hr : 0 < r) (x v : Fin d → ℝ) :
    (∑ k ∈ Finset.range n, scaledAnnularRieszFour d ((2:ℝ)^k*r) x v) =
      nearRieszFour d (((2:ℝ)^n*r)/2) x v-nearRieszFour d (r/2) x v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih,
      scaledAnnularRieszFour_eq_near_sub d _ (by positivity)]
    have heq : ((2:ℝ)^(n+1)*r)/2 = (2:ℝ)^n*r := by rw [pow_succ]; ring
    rw [heq]
    ring

theorem nearRieszFour_eq_kernel_of_norm_le (d : ℕ) (r : ℝ) (hr : 0 < r)
    (x v : Fin d → ℝ) (hv : ‖v-x‖ ≤ r) :
    nearRieszFour d r x v = flatRieszFour d x v := by
  have hb : outerUnitBump d (r⁻¹ • (v-x)) = 1 := by
    apply (outerUnitBump d).one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖r⁻¹ • (v-x)‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), ← div_eq_inv_mul]
    exact (div_le_one hr).mpr hv
  rw [nearRieszFour, hb, mul_one]

theorem unitCube_norm_le_one (d : ℕ) (v : Fin d → ℝ) (hv : v ∈ UnitCube d) :
    ‖v‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (hv i).1]
  exact (hv i).2

theorem exists_annular_cover (d : ℕ) (r : ℝ) (hr : 0 < r) (x : Fin d → ℝ) :
    ∃ n : ℕ, ∀ v ∈ UnitCube d, ‖v-x‖ ≤ ((2:ℝ)^n*r)/2 := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2*(1+‖x‖)/r) (by norm_num : (1:ℝ) < 2)
  refine ⟨n, ?_⟩
  intro v hv
  have h : 2*(1+‖x‖) < (2:ℝ)^n*r := (div_lt_iff₀ hr).mp hn
  calc
    ‖v-x‖ ≤ ‖v‖+‖x‖ := norm_sub_le _ _
    _ ≤ 1+‖x‖ := by linarith [unitCube_norm_le_one d v hv]
    _ ≤ ((2:ℝ)^n*r)/2 := by linarith

theorem farRieszFour_eq_annular_sum_on (d n : ℕ) (r : ℝ) (hr : 0 < r)
    (x : Fin d → ℝ)
    (hcover : ∀ v ∈ UnitCube d, ‖v-x‖ ≤ ((2:ℝ)^n*r)/2) :
    Set.EqOn (farRieszFour d r x)
      (fun v => ∑ k ∈ Finset.range n, scaledAnnularRieszFour d ((2:ℝ)^k*r) x v)
      (UnitCube d) := by
  intro v hv
  dsimp only
  rw [annular_partition_sum d n r hr x v,
    nearRieszFour_eq_kernel_of_norm_le d _ (by positivity) x v (hcover v hv)]
  rfl

theorem farRieszFour_contDiffOn_cube (d : ℕ) (r : ℝ) (hr : 0 < r) (x : Fin d → ℝ) :
    ContDiffOn ℝ 6 (farRieszFour d r x) (UnitCube d) := by
  obtain ⟨n, hn⟩ := exists_annular_cover d r hr x
  have h : ContDiffOn ℝ 6
      (fun v => ∑ k ∈ Finset.range n, scaledAnnularRieszFour d ((2:ℝ)^k*r) x v)
      (UnitCube d) :=
    ContDiffOn.sum (fun k _ => ((scaledAnnularRieszFour_contDiff d _ x).of_le (by simp)).contDiffOn)
  exact h.congr (farRieszFour_eq_annular_sum_on d n r hr x hn)

theorem cubeQuadrature_finset_sum {ι : Type*} (d m : ℕ) (s : Finset ι)
    (f : ι → (Fin d → ℝ) → ℝ) :
    cubeQuadrature d m (fun v => ∑ k ∈ s, f k v) = ∑ k ∈ s, cubeQuadrature d m (f k) := by
  simp_rw [cubeQuadrature_as_node_sum]
  rw [Finset.sum_comm, Finset.sum_div]

theorem cubeIntegral_finset_sum {ι : Type*} (d : ℕ) (s : Finset ι)
    (f : ι → (Fin d → ℝ) → ℝ) (hf : ∀ k ∈ s, Continuous (f k)) :
    cubeIntegral d (fun v => ∑ k ∈ s, f k v) = ∑ k ∈ s, cubeIntegral d (f k) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    have heq : (fun v : Fin d → ℝ => ∫ t in (0:ℝ)..1, ∑ k ∈ s, f k (Fin.cons t v)) =
        (fun v => ∑ k ∈ s, ∫ t in (0:ℝ)..1, f k (Fin.cons t v)) := by
      funext v
      exact intervalIntegral.integral_finsetSum (fun k hk =>
        ((hf k hk).comp (by fun_prop)).intervalIntegrable _ _)
    simp only [cubeIntegral]
    rw [heq]
    apply ih
    intro k hk
    exact continuous_unitIntegral_param ((hf k hk).comp (by fun_prop))

theorem far_near_kernel_partition (d : ℕ) (r : ℝ) (x v : Fin d → ℝ) :
    farRieszFour d r x v+nearRieszFour d (r/2) x v = flatRieszFour d x v := by
  unfold farRieszFour
  ring

theorem farRieszFour_zero_inside (d : ℕ) (r : ℝ) (hr : 0 < r) (x v : Fin d → ℝ)
    (hv : ‖v-x‖ ≤ r/2) : farRieszFour d r x v = 0 := by
  rw [farRieszFour, nearRieszFour_eq_kernel_of_norm_le d _ (by positivity) x v hv, sub_self]

theorem farRieszFour_eq_kernel_outside (d : ℕ) (r : ℝ) (hr : 0 < r)
    (x v : Fin d → ℝ) (hv : r ≤ ‖v-x‖) : farRieszFour d r x v = flatRieszFour d x v := by
  have hb : outerUnitBump d ((r/2)⁻¹ • (v-x)) = 0 := by
    apply (outerUnitBump d).zero_of_le_dist
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (r/2)⁻¹),
      ← div_eq_inv_mul]
    change 2 ≤ ‖v-x‖/(r/2)
    apply (le_div_iff₀ (by positivity : 0 < r/2)).mpr
    linarith
  rw [farRieszFour, nearRieszFour, hb, mul_zero, sub_zero]

/-- The starting radius is retained, so the far error decreases as r^-2. -/
theorem annular_error_sum_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 8 ≤ m → ∀ r : ℝ, 0 < r → 1/(m:ℝ) ≤ r →
      ∀ n : ℕ, ∀ x : Fin 8 → ℝ,
      |∑ k ∈ Finset.range n,
        (cubeQuadrature 8 m (scaledAnnularRieszFour 8 ((2:ℝ)^k*r) x)-
          cubeIntegral 8 (scaledAnnularRieszFour 8 ((2:ℝ)^k*r) x))| ≤
        C/((m:ℝ)^6*r^2) := by
  obtain ⟨C, hC, hb⟩ := scaledAnnularRieszFour_eight_bound
  refine ⟨(4/3:ℝ)*C, by positivity, ?_⟩
  intro m hm r hr hmesh n x
  let e (k : ℕ) := cubeQuadrature 8 m (scaledAnnularRieszFour 8 ((2:ℝ)^k*r) x)-
    cubeIntegral 8 (scaledAnnularRieszFour 8 ((2:ℝ)^k*r) x)
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
theorem farRieszFour_quadrature_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 8 ≤ m → ∀ r : ℝ, 0 < r → 1/(m:ℝ) ≤ r →
      ∀ x : Fin 8 → ℝ,
      |cubeQuadrature 8 m (farRieszFour 8 r x)-cubeIntegral 8 (farRieszFour 8 r x)| ≤
        C/((m:ℝ)^6*r^2) := by
  obtain ⟨C, hC, hb⟩ := annular_error_sum_bound
  refine ⟨C, hC, ?_⟩
  intro m hm r hr hmesh x
  obtain ⟨n, hn⟩ := exists_annular_cover 8 r hr x
  have heq := farRieszFour_eq_annular_sum_on 8 n r hr x hn
  rw [cubeQuadrature_congr 8 m hm heq, cubeIntegral_congr 8 heq,
    cubeQuadrature_finset_sum, cubeIntegral_finset_sum 8 _ _
      (fun k _ => (scaledAnnularRieszFour_contDiff 8 _ x).continuous),
    ← Finset.sum_sub_distrib]
  exact hb m hm r hr hmesh n x

/-- Far errors can be made arbitrarily small at the second-term scale.
This leaves the near part, whose lattice coefficient still needs proof. -/
theorem farRieszFour_error_small :
    ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, 1 ≤ L ∧ ∀ m : ℕ, 8 ≤ m → ∀ x : Fin 8 → ℝ,
      |cubeQuadrature 8 m (farRieszFour 8 (L/(m:ℝ)) x)-
        cubeIntegral 8 (farRieszFour 8 (L/(m:ℝ)) x)| ≤ ε/(m:ℝ)^4 := by
  obtain ⟨C, hC, hb⟩ := farRieszFour_quadrature_bound
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

#print axioms annular_partition_sum
#print axioms farRieszFour_eq_annular_sum_on
#print axioms farRieszFour_contDiffOn_cube
#print axioms cubeIntegral_finset_sum
#print axioms farRieszFour_quadrature_bound
#print axioms farRieszFour_error_small

end SphericalRiesz
