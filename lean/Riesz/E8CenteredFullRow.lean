import Riesz.E8CellLimit
import Riesz.E8FlatPhysicalRow

/-!
# The full singular central E8 row at the original corrected nodes

The cutoff radius is free as long as its support lies in the unchanged
interior grid. Choosing R=q/2 gives O(1/q^2) at the second-term scale.
This removes the cutoff from the actual central flat row. Arbitrary
interior centers and curved global rows remain separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace SphericalRiesz
open Boundary

def e8CentralIndex (q : ℕ) : Fin 8 → NodeIndex (centeredMesh q) :=
  fun _ => interiorNodeIndex (centeredInteriorIndex q)

theorem e8CentralIndex_node (q : ℕ) :
    cubeNode 8 (centeredMesh q) (e8CentralIndex q) = (fun _ => (1/2:ℝ)) := by
  funext i
  exact centeredRuleNode q

def e8CenteredFullRow (q : ℕ) : ℝ :=
  (centeredMesh q : ℝ)^4 *
    (cubeQuadrature 8 (centeredMesh q) (obliqueRieszFour 8 e8Map (fun _ => (1/2:ℝ))) -
      ∫ y in UnitCube 8, obliqueRieszFour 8 e8Map (fun _ => (1/2:ℝ)) y)

/-- Use a supplied support radius; no optimization or square-root argument is needed. -/
theorem e8CenteredFullRow_radius_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, ∀ R : ℝ, 1 ≤ R → 2*R ≤ q →
      |e8CenteredFullRow q-(-5*Real.pi^2/6)| ≤ C/R^2 := by
  obtain ⟨Cn, hCn, hnear⟩ := e8CompactDefect_uniform_bound
  obtain ⟨Cf, hCf, hfar⟩ := farObliqueRieszFour_quadrature_bound e8Map e8Map_injective
  refine ⟨Cf/4+Cn, by positivity, ?_⟩
  intro q R hR hcover
  let m : ℝ := centeredMesh q
  let r : ℝ := 2*R/m
  have hm : 0 < m := by dsimp only [m]; positivity
  have hm8 : 8 ≤ centeredMesh q := by simp only [centeredMesh]; omega
  have hR0 : 0 < R := by linarith
  have hr : 0 < r := by dsimp only [r]; positivity
  have hmesh : 1/m ≤ r := by
    dsimp only [r]
    exact div_le_div_of_nonneg_right (by linarith) hm.le
  have hf := hfar (centeredMesh q) hm8 r hr hmesh (fun _ => (1/2:ℝ))
  rw [cubeIntegral_eq_setIntegral_on 8 _
    (farObliqueRieszFour_contDiffOn_cube 8 e8Map e8Map_injective r hr _).continuousOn] at hf
  have hscaled :
      |m^4*(cubeQuadrature 8 (centeredMesh q)
        (farObliqueRieszFour 8 e8Map r (fun _ => (1/2:ℝ))) -
        ∫ y in UnitCube 8, farObliqueRieszFour 8 e8Map r (fun _ => (1/2:ℝ)) y)| ≤
        (Cf/4)/R^2 := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hm.le 4)]
    calc
      _ ≤ m^4*(Cf/(m^6*r^2)) := mul_le_mul_of_nonneg_left hf (by positivity)
      _ = (Cf/4)/R^2 := by
        dsimp only [r]
        field_simp [hm.ne', hR0.ne'] <;> ring
  have hrow := e8CompactDefect_eq_scaled_row hR0 q hcover
  have hhalf : r/2 = R/m := by dsimp only [r]; ring
  have heq : e8CenteredFullRow q-(-5*Real.pi^2/6) =
      m^4*(cubeQuadrature 8 (centeredMesh q)
        (farObliqueRieszFour 8 e8Map r (fun _ => (1/2:ℝ))) -
        ∫ y in UnitCube 8, farObliqueRieszFour 8 e8Map r (fun _ => (1/2:ℝ)) y) +
      (e8CompactDefect R-(-5*Real.pi^2/6)) := by
    unfold e8CenteredFullRow
    rw [e8Kernel_quadrature_partition _ r _, e8Kernel_integral_partition r hr _, hhalf, hrow]
    change m^4*(_+_-(_+_))-_ = _
    ring
  rw [heq]
  calc
    _ ≤ _ := abs_add_le _ _
    _ ≤ (Cf/4)/R^2+Cn/R^2 := add_le_add hscaled (hnear R hR)
    _ = (Cf/4+Cn)/R^2 := by ring

/-- The supplied answer R=q/2 improves the earlier O(q^-1) rate to O(q^-2). -/
theorem e8CenteredFullRow_square_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, 2 ≤ q →
      |e8CenteredFullRow q-(-5*Real.pi^2/6)| ≤ C/(q:ℝ)^2 := by
  obtain ⟨C, hC, hb⟩ := e8CenteredFullRow_radius_bound
  refine ⟨4*C, by positivity, ?_⟩
  intro q hq
  have hqr : (2:ℝ) ≤ q := by exact_mod_cast hq
  have h := hb q ((q:ℝ)/2) (by linarith) (by linarith)
  convert h using 1
  field_simp
  ring

theorem e8CenteredFullRow_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, 4 ≤ q →
      |e8CenteredFullRow q-(-5*Real.pi^2/6)| ≤ C/(q:ℝ) := by
  obtain ⟨Cn, hCn, hnear⟩ := e8CompactDefect_uniform_bound
  obtain ⟨Cf, hCf, hfar⟩ := farObliqueRieszFour_quadrature_bound e8Map e8Map_injective
  refine ⟨Cf/4+Cn, by positivity, ?_⟩
  intro q hq
  let m : ℝ := centeredMesh q
  let R : ℝ := Real.sqrt (q:ℝ)
  let r : ℝ := 2*R/m
  have hm : 0 < m := by dsimp only [m]; positivity
  have hm8 : 8 ≤ centeredMesh q := by simp only [centeredMesh]; omega
  have hqr : (4:ℝ) ≤ q := by exact_mod_cast hq
  have hs : R^2 = (q:ℝ) := Real.sq_sqrt (by positivity)
  have hn : 0 ≤ R := Real.sqrt_nonneg _
  have htwo : (2:ℝ) ≤ R := by nlinarith
  have hR : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  have hcover : 2*R ≤ q := by nlinarith
  have hr : 0 < r := by dsimp only [r]; positivity
  have hmesh : 1/m ≤ r := by
    dsimp only [r]
    exact div_le_div_of_nonneg_right (by linarith) hm.le
  have hf := hfar (centeredMesh q) hm8 r hr hmesh (fun _ => (1/2:ℝ))
  rw [cubeIntegral_eq_setIntegral_on 8 _
    (farObliqueRieszFour_contDiffOn_cube 8 e8Map e8Map_injective r hr _).continuousOn] at hf
  have hscaled :
      |m^4*(cubeQuadrature 8 (centeredMesh q) (farObliqueRieszFour 8 e8Map r (fun _ => (1/2:ℝ))) -
        ∫ y in UnitCube 8, farObliqueRieszFour 8 e8Map r (fun _ => (1/2:ℝ)) y)| ≤
        (Cf/4)/(q:ℝ) := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hm.le 4)]
    calc
      _ ≤ m^4*(Cf/(m^6*r^2)) := mul_le_mul_of_nonneg_left hf (by positivity)
      _ = (Cf/4)/(q:ℝ) := by
        dsimp only [r]
        rw [← hs]
        field_simp [hm.ne', hR0.ne'] <;> ring
  have hrow := e8CompactDefect_eq_scaled_row hR0 q hcover
  have hhalf : r/2 = R/m := by dsimp only [r]; ring
  have heq : e8CenteredFullRow q-(-5*Real.pi^2/6) =
      m^4*(cubeQuadrature 8 (centeredMesh q) (farObliqueRieszFour 8 e8Map r (fun _ => (1/2:ℝ))) -
        ∫ y in UnitCube 8, farObliqueRieszFour 8 e8Map r (fun _ => (1/2:ℝ)) y) +
      (e8CompactDefect R-(-5*Real.pi^2/6)) := by
    unfold e8CenteredFullRow
    rw [e8Kernel_quadrature_partition _ r _, e8Kernel_integral_partition r hr _, hhalf, hrow]
    change m^4*(_+_-(_+_))-_ = _
    ring
  rw [heq]
  calc
    _ ≤ _ := abs_add_le _ _
    _ ≤ (Cf/4)/(q:ℝ)+Cn/R^2 := add_le_add hscaled (hnear R hR)
    _ = (Cf/4+Cn)/(q:ℝ) := by rw [hs]; ring

theorem e8CenteredFullRow_limit :
    Tendsto e8CenteredFullRow atTop (𝓝 (-5*Real.pi^2/6)) := by
  obtain ⟨C, _, hb⟩ := e8CenteredFullRow_bound
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun q => norm_nonneg _))
    (show ∀ᶠ q : ℕ in atTop, ‖e8CenteredFullRow q-(-5*Real.pi^2/6)‖ ≤ C/(q:ℝ) from by
      filter_upwards [eventually_ge_atTop (4:ℕ)] with q hq
      simpa only [Real.norm_eq_abs] using hb q hq)
  exact tendsto_const_div_atTop_nhds_zero_nat C

theorem e8CenteredFullRow_normalized_limit :
    Tendsto (fun q : ℕ => e8CenteredFullRow q/Real.sqrt (sphereArea8.real univ))
      atTop (𝓝 predictedCoefficient) := by
  rw [predictedCoefficient_area_normalization]
  exact e8CenteredFullRow_limit.div_const _

theorem e8CenteredFullRow_eq_physical (q : ℕ) :
    e8CenteredFullRow q = (centeredMesh q : ℝ)^4 *
      ((∑ w ∈ (Finset.univ : Finset (Fin 8 → NodeIndex (centeredMesh q))).erase (e8CentralIndex q),
        (dist (WithLp.toLp 2 (e8TensorNode (centeredMesh q) (e8CentralIndex q)) : EuclideanSpace ℝ (Fin 8))
          (WithLp.toLp 2 (e8TensorNode (centeredMesh q) w)))⁻¹^4)/(centeredMesh q : ℝ)^8 -
        ∫ z in e8Map '' UnitCube 8,
          (dist (WithLp.toLp 2 (e8TensorNode (centeredMesh q) (e8CentralIndex q)) : EuclideanSpace ℝ (Fin 8))
            (WithLp.toLp 2 z))⁻¹^4) := by
  classical
  unfold e8CenteredFullRow
  rw [← e8CentralIndex_node q, cubeQuadrature_as_node_sum, e8Kernel_imageIntegral]
  simp only [obliqueRieszFour_eq_dist, e8PhysicalKernel]
  change (centeredMesh q : ℝ)^4 *
    ((∑ w : Fin 8 → NodeIndex (centeredMesh q),
      (dist (WithLp.toLp 2 (e8TensorNode (centeredMesh q) (e8CentralIndex q)) : EuclideanSpace ℝ (Fin 8))
        (WithLp.toLp 2 (e8TensorNode (centeredMesh q) w)))⁻¹^4)/(centeredMesh q : ℝ)^8 - _) = _
  have hsum : (∑ w : Fin 8 → NodeIndex (centeredMesh q),
      (dist (WithLp.toLp 2 (e8TensorNode (centeredMesh q) (e8CentralIndex q)) : EuclideanSpace ℝ (Fin 8))
        (WithLp.toLp 2 (e8TensorNode (centeredMesh q) w)))⁻¹^4) =
      ∑ w ∈ (Finset.univ : Finset (Fin 8 → NodeIndex (centeredMesh q))).erase (e8CentralIndex q),
      (dist (WithLp.toLp 2 (e8TensorNode (centeredMesh q) (e8CentralIndex q)) : EuclideanSpace ℝ (Fin 8))
        (WithLp.toLp 2 (e8TensorNode (centeredMesh q) w)))⁻¹^4 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro w hw hn
    have he : w = e8CentralIndex q := by
      by_contra hne
      exact hn (Finset.mem_erase.mpr ⟨hne, hw⟩)
    subst w
    simp
  rw [hsum]
  rfl

theorem e8CenteredFullPhysicalRow_limit :
    Tendsto (fun q : ℕ => (centeredMesh q : ℝ)^4 *
      ((∑ w ∈ (Finset.univ : Finset (Fin 8 → NodeIndex (centeredMesh q))).erase (e8CentralIndex q),
        (dist (WithLp.toLp 2 (e8TensorNode (centeredMesh q) (e8CentralIndex q)) : EuclideanSpace ℝ (Fin 8))
          (WithLp.toLp 2 (e8TensorNode (centeredMesh q) w)))⁻¹^4)/(centeredMesh q : ℝ)^8 -
        ∫ z in e8Map '' UnitCube 8,
          (dist (WithLp.toLp 2 (e8TensorNode (centeredMesh q) (e8CentralIndex q)) : EuclideanSpace ℝ (Fin 8))
            (WithLp.toLp 2 z))⁻¹^4)) atTop (𝓝 (-5*Real.pi^2/6)) := by
  apply e8CenteredFullRow_limit.congr'
  exact Eventually.of_forall e8CenteredFullRow_eq_physical

#print axioms e8CentralIndex_node
#print axioms e8CenteredFullRow_radius_bound
#print axioms e8CenteredFullRow_square_bound
#print axioms e8CenteredFullRow_bound
#print axioms e8CenteredFullRow_limit
#print axioms e8CenteredFullRow_normalized_limit
#print axioms e8CenteredFullRow_eq_physical
#print axioms e8CenteredFullPhysicalRow_limit
end SphericalRiesz
