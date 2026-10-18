import Riesz.InteriorGrid
import Riesz.E8CellLimit
import Riesz.E8FlatPhysicalRow

/-!
# The sharp full singular row at every sufficiently padded interior node

For any original mesh m and any original interior center j, a support
radius R that fits inside its integer padding gives error C/R^2, with
the same constant for every mesh and center. No cutoff remains in the
row being estimated. Averaging boundary layers and curved patches are
not supplied by this module.
-/
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace SphericalRiesz
open Boundary

theorem e8Near_interior_scale {R : ℝ} (hR : 0 < R) (m : ℕ) (hm : 0 < m)
    (j : Fin 8 → Fin (m-8)) (y : Fin 8 → ℝ) :
    nearObliqueRieszFour 8 e8Map (R/(m:ℝ)) (interiorCenter 8 m j) y =
      (m:ℝ)^4 * nearObliqueRieszFour 8 e8Map R 0
        ((m:ℝ) • (y-interiorCenter 8 m j)) := by
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  rw [e8Near_scaled _ (div_pos hR hmr), e8Near_scaled R hR]
  simp only [sub_zero, inv_div, smul_smul]
  rw [show (m:ℝ)/R = R⁻¹*(m:ℝ) by ring]
  ring

theorem e8CompactLatticeSum_eq_interior {R : ℝ} (hR : 0 < R)
    (m : ℕ) (hm : 0 < m) (j : Fin 8 → Fin (m-8))
    (hpad : InteriorPadding 8 m j (2*R)) :
    e8CompactLatticeSum R = ∑ v : Fin 8 → NodeIndex m,
      nearObliqueRieszFour 8 e8Map R 0 (interiorCubeCoordinate 8 m j v) := by
  symm
  apply interiorNodeSum_eq_tsum 8 m hm j (2*R) hpad
  intro y hy
  apply e8Near_zero_outside_coordinates R hR 0 y
  simpa only [Pi.zero_apply, sub_zero] using hy

theorem e8Near_interior_cubeIntegral {R : ℝ} (hR : 0 < R)
    (m : ℕ) (hm : 0 < m) (j : Fin 8 → Fin (m-8))
    (hpad : InteriorPadding 8 m j (2*R)) :
    (∫ y in UnitCube 8, nearObliqueRieszFour 8 e8Map (R/(m:ℝ))
      (interiorCenter 8 m j) y) = e8NearIntegralConstant*(R/(m:ℝ))^4 := by
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact e8Near_integral _ (div_pos hR hmr) _
  · intro y hy
    apply e8Near_zero_outside_coordinates _ (div_pos hR hmr)
    intro hb
    apply hy
    intro i
    have hi := abs_le.mp (hb i)
    have hleft : 2*(R/(m:ℝ)) ≤ interiorCenter 8 m j i := by
      dsimp only [interiorCenter]
      rw [interiorRuleNode, show 2*(R/(m:ℝ)) = (2*R)/(m:ℝ) by ring]
      exact div_le_div_of_nonneg_right (by linarith [(hpad i).1]) hmr.le
    have hright : interiorCenter 8 m j i+2*(R/(m:ℝ)) ≤ 1 := by
      dsimp only [interiorCenter]
      rw [interiorRuleNode, show 2*(R/(m:ℝ)) = (2*R)/(m:ℝ) by ring, ← add_div]
      apply (div_le_one hmr).mpr
      linarith [(hpad i).2]
    change y i ∈ Set.Icc (0:ℝ) 1
    constructor <;> linarith

theorem e8CompactDefect_eq_interior_scaled_row {R : ℝ} (hR : 0 < R)
    (m : ℕ) (hm : 0 < m) (j : Fin 8 → Fin (m-8))
    (hpad : InteriorPadding 8 m j (2*R)) :
    e8CompactDefect R = (m:ℝ)^4 *
      (cubeQuadrature 8 m
        (nearObliqueRieszFour 8 e8Map (R/(m:ℝ)) (interiorCenter 8 m j)) -
       ∫ y in UnitCube 8, nearObliqueRieszFour 8 e8Map (R/(m:ℝ))
        (interiorCenter 8 m j) y) := by
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [cubeQuadrature_as_node_sum, e8Near_interior_cubeIntegral hR m hm j hpad]
  simp_rw [e8Near_interior_scale hR m hm j]
  change e8CompactDefect R = (m:ℝ)^4 *
    ((∑ v : Fin 8 → NodeIndex m, (m:ℝ)^4 *
      nearObliqueRieszFour 8 e8Map R 0 (interiorCubeCoordinate 8 m j v))/(m:ℝ)^8 - _)
  rw [← Finset.mul_sum, ← e8CompactLatticeSum_eq_interior hR m hm j hpad,
    e8CompactDefect, e8Compact_background_value hR]
  field_simp

def e8InteriorFullRow (m : ℕ) (j : Fin 8 → Fin (m-8)) : ℝ :=
  (m:ℝ)^4 *
    (cubeQuadrature 8 m (obliqueRieszFour 8 e8Map (interiorCenter 8 m j)) -
      ∫ y in UnitCube 8, obliqueRieszFour 8 e8Map (interiorCenter 8 m j) y)

def e8InteriorIndex (m : ℕ) (j : Fin 8 → Fin (m-8)) : Fin 8 → NodeIndex m :=
  fun i => interiorNodeIndex (j i)

theorem e8InteriorIndex_node (m : ℕ) (j : Fin 8 → Fin (m-8)) :
    cubeNode 8 m (e8InteriorIndex m j) = interiorCenter 8 m j := rfl

/-- The row is the actual off-diagonal Euclidean energy minus volume background. -/
theorem e8InteriorFullRow_eq_physical (m : ℕ) (j : Fin 8 → Fin (m-8)) :
    e8InteriorFullRow m j = (m:ℝ)^4 *
      ((∑ w ∈ (Finset.univ : Finset (Fin 8 → NodeIndex m)).erase (e8InteriorIndex m j),
        (dist (WithLp.toLp 2 (e8TensorNode m (e8InteriorIndex m j)) : EuclideanSpace ℝ (Fin 8))
          (WithLp.toLp 2 (e8TensorNode m w)))⁻¹^4)/(m:ℝ)^8 -
        ∫ z in e8Map '' UnitCube 8,
          (dist (WithLp.toLp 2 (e8TensorNode m (e8InteriorIndex m j)) : EuclideanSpace ℝ (Fin 8))
            (WithLp.toLp 2 z))⁻¹^4) := by
  classical
  unfold e8InteriorFullRow
  rw [← e8InteriorIndex_node m j, cubeQuadrature_as_node_sum, e8Kernel_imageIntegral]
  simp only [obliqueRieszFour_eq_dist, e8PhysicalKernel]
  change (m:ℝ)^4 *
    ((∑ w : Fin 8 → NodeIndex m,
      (dist (WithLp.toLp 2 (e8TensorNode m (e8InteriorIndex m j)) : EuclideanSpace ℝ (Fin 8))
        (WithLp.toLp 2 (e8TensorNode m w)))⁻¹^4)/(m:ℝ)^8 - _) = _
  have hsum : (∑ w : Fin 8 → NodeIndex m,
      (dist (WithLp.toLp 2 (e8TensorNode m (e8InteriorIndex m j)) : EuclideanSpace ℝ (Fin 8))
        (WithLp.toLp 2 (e8TensorNode m w)))⁻¹^4) =
      ∑ w ∈ (Finset.univ : Finset (Fin 8 → NodeIndex m)).erase (e8InteriorIndex m j),
      (dist (WithLp.toLp 2 (e8TensorNode m (e8InteriorIndex m j)) : EuclideanSpace ℝ (Fin 8))
        (WithLp.toLp 2 (e8TensorNode m w)))⁻¹^4 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro w hw hn
    have he : w = e8InteriorIndex m j := by
      by_contra hne
      exact hn (Finset.mem_erase.mpr ⟨hne, hw⟩)
    subst w
    simp
  rw [hsum]
  rfl

theorem e8InteriorFullRow_radius_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 9 ≤ m → ∀ j : Fin 8 → Fin (m-8),
      ∀ R : ℝ, 1 ≤ R → InteriorPadding 8 m j (2*R) →
      |e8InteriorFullRow m j-(-5*Real.pi^2/6)| ≤ C/R^2 := by
  obtain ⟨Cn, hCn, hnear⟩ := e8CompactDefect_uniform_bound
  obtain ⟨Cf, hCf, hfar⟩ := farObliqueRieszFour_quadrature_bound e8Map e8Map_injective
  refine ⟨Cf/4+Cn, by positivity, ?_⟩
  intro m hm j R hR hpad
  have hm0 : 0 < m := by omega
  have hmr : (0:ℝ) < m := by exact_mod_cast hm0
  have hR0 : 0 < R := by linarith
  let r : ℝ := 2*R/(m:ℝ)
  have hr : 0 < r := by dsimp only [r]; positivity
  have hmesh : 1/(m:ℝ) ≤ r := by
    dsimp only [r]
    exact div_le_div_of_nonneg_right (by linarith) hmr.le
  have hf := hfar m (by omega) r hr hmesh (interiorCenter 8 m j)
  rw [cubeIntegral_eq_setIntegral_on 8 _
    (farObliqueRieszFour_contDiffOn_cube 8 e8Map e8Map_injective r hr _).continuousOn] at hf
  have hscaled :
      |(m:ℝ)^4*(cubeQuadrature 8 m
        (farObliqueRieszFour 8 e8Map r (interiorCenter 8 m j)) -
        ∫ y in UnitCube 8, farObliqueRieszFour 8 e8Map r (interiorCenter 8 m j) y)| ≤
        (Cf/4)/R^2 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hmr.le 4)]
    calc
      _ ≤ (m:ℝ)^4*(Cf/((m:ℝ)^6*r^2)) := mul_le_mul_of_nonneg_left hf (by positivity)
      _ = (Cf/4)/R^2 := by
        dsimp only [r]
        field_simp [hmr.ne', hR0.ne']
        ring
  have hrow := e8CompactDefect_eq_interior_scaled_row hR0 m hm0 j hpad
  have hhalf : r/2 = R/(m:ℝ) := by dsimp only [r]; ring
  have heq : e8InteriorFullRow m j-(-5*Real.pi^2/6) =
      (m:ℝ)^4*(cubeQuadrature 8 m
        (farObliqueRieszFour 8 e8Map r (interiorCenter 8 m j)) -
        ∫ y in UnitCube 8, farObliqueRieszFour 8 e8Map r (interiorCenter 8 m j) y) +
      (e8CompactDefect R-(-5*Real.pi^2/6)) := by
    unfold e8InteriorFullRow
    rw [e8Kernel_quadrature_partition _ r _, e8Kernel_integral_partition r hr _, hhalf, hrow]
    ring
  rw [heq]
  calc
    _ ≤ _ := abs_add_le _ _
    _ ≤ (Cf/4)/R^2+Cn/R^2 := add_le_add hscaled (hnear R hR)
    _ = (Cf/4+Cn)/R^2 := by ring

/-- Fixed depth k gives a uniform O(k^-2) estimate for all padded centers. -/
theorem e8InteriorFullRow_padding_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 9 ≤ m → ∀ j : Fin 8 → Fin (m-8),
      ∀ k : ℝ, 2 ≤ k → InteriorPadding 8 m j k →
      |e8InteriorFullRow m j-(-5*Real.pi^2/6)| ≤ C/k^2 := by
  obtain ⟨C, hC, hb⟩ := e8InteriorFullRow_radius_bound
  refine ⟨4*C, by positivity, ?_⟩
  intro m hm j k hk hpad
  have h := hb m hm j (k/2) (by linarith)
    (by simpa only [show 2*(k/2) = k by ring] using hpad)
  convert h using 1
  field_simp
  ring

/-- Any sequence of original interior centers works once its padding tends to infinity. -/
theorem e8InteriorFullRow_limit (m : ℕ → ℕ) (j : ∀ n, Fin 8 → Fin (m n-8))
    (k : ℕ → ℝ) (hk : Tendsto k atTop atTop)
    (hm : ∀ᶠ n in atTop, 9 ≤ m n)
    (hpad : ∀ᶠ n in atTop, InteriorPadding 8 (m n) (j n) (k n)) :
    Tendsto (fun n => e8InteriorFullRow (m n) (j n)) atTop (𝓝 (-5*Real.pi^2/6)) := by
  obtain ⟨C, _, hb⟩ := e8InteriorFullRow_padding_bound
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _))
    (show ∀ᶠ n in atTop, ‖e8InteriorFullRow (m n) (j n)-(-5*Real.pi^2/6)‖ ≤ C/(k n)^2 from by
      filter_upwards [hm, hpad, hk.eventually (eventually_ge_atTop (2:ℝ))] with n hn hp hkn
      simpa only [Real.norm_eq_abs] using hb (m n) hn (j n) (k n) hkn hp)
  exact ((tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp hk).const_div_atTop C

theorem e8InteriorFullRow_normalized_limit (m : ℕ → ℕ)
    (j : ∀ n, Fin 8 → Fin (m n-8)) (k : ℕ → ℝ) (hk : Tendsto k atTop atTop)
    (hm : ∀ᶠ n in atTop, 9 ≤ m n)
    (hpad : ∀ᶠ n in atTop, InteriorPadding 8 (m n) (j n) (k n)) :
    Tendsto (fun n => e8InteriorFullRow (m n) (j n)/Real.sqrt (sphereArea8.real univ))
      atTop (𝓝 predictedCoefficient) := by
  rw [predictedCoefficient_area_normalization]
  exact (e8InteriorFullRow_limit m j k hk hm hpad).div_const _

#print axioms e8Near_interior_scale
#print axioms e8CompactLatticeSum_eq_interior
#print axioms e8Near_interior_cubeIntegral
#print axioms e8CompactDefect_eq_interior_scaled_row
#print axioms e8InteriorIndex_node
#print axioms e8InteriorFullRow_eq_physical
#print axioms e8InteriorFullRow_radius_bound
#print axioms e8InteriorFullRow_padding_bound
#print axioms e8InteriorFullRow_limit
#print axioms e8InteriorFullRow_normalized_limit

end SphericalRiesz
