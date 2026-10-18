import Riesz.E8NearPotentialMean

/-!
# Unconditional actual flat E8 neutralized energy

The far-background error is C/R² after multiplication by m^4.
For each fixed R the actual near-background error tends to zero.
First let m grow, then R grow. This proves the required o(m^-4)
without claiming an m^-5 rate or a sixth-derivative face formula.
The unchanged original corrected nodes and actual Lebesgue background
are used throughout. No spherical recovery or curved input is assumed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace SphericalRiesz
open Boundary

theorem e8FlatBackgroundError_partition (R : ℝ) (hR : 0 < R)
    (m : ℕ) (hm : 0 < m) :
    e8FlatBackgroundError m =
      (m:ℝ)^4*(cubeQuadrature 8 m (e8FarPotential (2*R/(m:ℝ)))-
        ∫ x in UnitCube 8, e8FarPotential (2*R/(m:ℝ)) x)+
      (cubeQuadrature 8 m (e8ScaledNearPotential R m)-
        ∫ x in UnitCube 8, e8ScaledNearPotential R m x) := by
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  have hr : 0 < R/(m:ℝ) := div_pos hR hmr
  have hs : 2*(R/(m:ℝ)) = 2*R/(m:ℝ) := by ring
  unfold e8ScaledNearPotential
  simp_rw [e8NearPotential_eq _ hr, hs]
  rw [cubeQuadrature_const_mul, cubeQuadrature_sub, integral_const_mul,
    integral_sub (e8Potential_continuous.continuousOn.integrableOn_compact (unitCube_isCompact 8))
      ((e8FarPotential_continuous _ (by positivity)).continuousOn.integrableOn_compact
        (unitCube_isCompact 8))]
  unfold e8FlatBackgroundError
  ring

theorem e8FlatBackgroundError_radius_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ m : ℕ, 8 ≤ m →
      |e8FlatBackgroundError m| ≤ C/R^2+
        |cubeQuadrature 8 m (e8ScaledNearPotential R m)-
          ∫ x in UnitCube 8, e8ScaledNearPotential R m x| := by
  obtain ⟨C,hC,hb⟩ := e8FarPotential_scaled_quadrature_bound
  refine ⟨C,hC,fun R hR m hm => ?_⟩
  have hR0 : 0 < R := by linarith
  have h := hb m hm (2*R) (by linarith)
  have hc : C/(2*R)^2 ≤ C/R^2 :=
    div_le_div_of_nonneg_left hC (by positivity) (by nlinarith [sq_nonneg R])
  rw [e8FlatBackgroundError_partition R hR0 m (by omega)]
  exact (abs_add_le _ _).trans (add_le_add (h.trans hc) le_rfl)

theorem e8FlatBackgroundError_limit :
    Tendsto e8FlatBackgroundError atTop (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := e8FlatBackgroundError_radius_bound
  have hk : Tendsto (fun k : ℕ => C/(k:ℝ)^2) atTop (𝓝 0) :=
    ((tendsto_pow_atTop (by decide : (2:ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop).const_div_atTop C
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨k,hk1,hka⟩ := ((eventually_ge_atTop (1:ℕ)).and
    (hk.eventually (gt_mem_nhds (by linarith : (0:ℝ) < ε/2)))).exists
  have hkr : (1:ℝ) ≤ k := by exact_mod_cast hk1
  have hnear := e8ScaledNearPotential_background_limit (k:ℝ) (by linarith)
  have he : ∀ᶠ m : ℕ in atTop,
      |cubeQuadrature 8 m (e8ScaledNearPotential (k:ℝ) m)-
        ∫ x in UnitCube 8, e8ScaledNearPotential (k:ℝ) m x| < ε/2 := by
    simpa only [Real.norm_eq_abs] using hnear.norm.eventually
      (gt_mem_nhds (by simpa using (half_pos hε)))
  filter_upwards [eventually_ge_atTop (8:ℕ),he] with m hm hn
  simpa only [Real.dist_eq,sub_zero] using
    lt_of_le_of_lt (hb (k:ℝ) hkr m hm) (by linarith)

theorem e8FlatNeutralizedEnergy_limit :
    Tendsto e8FlatNeutralizedEnergy atTop (𝓝 (-5*Real.pi^2/6)) :=
  e8FlatNeutralizedEnergy_limit_of_background e8FlatBackgroundError_limit

theorem e8FlatNeutralizedEnergy_normalized_limit :
    Tendsto (fun m : ℕ => e8FlatNeutralizedEnergy m/Real.sqrt (sphereArea8.real univ))
      atTop (𝓝 predictedCoefficient) := by
  rw [predictedCoefficient_area_normalization]
  exact e8FlatNeutralizedEnergy_limit.div_const _

#print axioms e8FlatBackgroundError_partition
#print axioms e8FlatBackgroundError_radius_bound
#print axioms e8FlatBackgroundError_limit
#print axioms e8FlatNeutralizedEnergy_limit
#print axioms e8FlatNeutralizedEnergy_normalized_limit

end SphericalRiesz
