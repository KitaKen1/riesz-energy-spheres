import Riesz.EqualAreaInverse8
import Riesz.SphereFiniteCompactCores8
import Riesz.SphereIntegrable8

/-! Quantitative small-ball coverage by explicit rotated equal-area charts.
The near-full compact cores now lie in actual small chart images, with
disjoint open buffers. Equal-scale E8 grid cells remain a separate step. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Metric
open scoped Topology
namespace SphericalRiesz

theorem sphere8_coordinate_difference_le_dist (q p : Sphere8) (i : Fin 9) :
    |(q : Ambient9) i-(p : Ambient9) i| ≤ dist q p := by
  change |(q : Ambient9) i-(p : Ambient9) i| ≤ ‖(q : Ambient9)-(p : Ambient9)‖
  simpa only [PiLp.sub_apply, Real.norm_eq_abs] using
    (PiLp.norm_apply_le ((q : Ambient9)-(p : Ambient9)) i)

theorem northPole8_ball_first_pos (q : Sphere8) (r : ℝ)
    (hr : r ≤ 1/2) (hq : q ∈ ball northPole8 r) :
    1/2 < (q : Ambient9) 0 := by
  have h := (sphere8_coordinate_difference_le_dist q northPole8 0).trans_lt hq
  have hcoord : |(q : Ambient9) 0-1| < r := by
    simpa [northPole8] using h
  linarith [(abs_lt.mp hcoord).1]

theorem equalAreaInverse8_small_ball_norm (q : Sphere8) (r : ℝ) (hr : r ≤ 1/2)
    (hq : q ∈ ball northPole8 r) : ‖equalAreaInverse8 q‖ ≤ 2*r := by
  have hfirst := northPole8_ball_first_pos q r hr hq
  have hrpos : 0 < r := (dist_nonneg : 0 ≤ dist q northPole8).trans_lt hq
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2*r)).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change |Real.arctan ((q : Ambient9) 1/(q : Ambient9) 0)| ≤ 2*r
    have h := (sphere8_coordinate_difference_le_dist q northPole8 1).trans_lt hq
    have hcoord : |(q : Ambient9) 1| < r := by simpa [northPole8] using h
    have hquot : |(q : Ambient9) 1/(q : Ambient9) 0| < 2*r := by
      rw [abs_div,abs_of_pos (by linarith : 0 < (q : Ambient9) 0)]
      apply (div_lt_iff₀ (by linarith : 0 < (q : Ambient9) 0)).mpr
      nlinarith
    exact Real.abs_arctan_le_abs.trans hquot.le
  · change |(q : Ambient9) j.succ.succ| ≤ 2*r
    have h := (sphere8_coordinate_difference_le_dist q northPole8 j.succ.succ).trans_lt hq
    have hcoord : |(q : Ambient9) j.succ.succ| < r := by
      simpa [northPole8] using h
    linarith

theorem northPole8_ball_chart (q : Sphere8) (r : ℝ) (hr : r ≤ 1/2)
    (hq : q ∈ ball northPole8 r) :
    equalAreaInverse8 q ∈ equalAreaChartDomain ∧
      ‖equalAreaInverse8 q‖ ≤ 2*r ∧ equalAreaPhi (equalAreaInverse8 q) = (q : Ambient9) := by
  have hf : 0 < (q : Ambient9) 0 := by
    have h := northPole8_ball_first_pos q r hr hq
    linarith
  exact ⟨equalAreaInverse8_mem_domain q hf,equalAreaInverse8_small_ball_norm q r hr hq,
    equalAreaPhi_inverse8 q hf⟩

theorem sphere8_ball_rotated_chart (p : Sphere8) (r : ℝ) (hr : r ≤ 1/2) :
    ∃ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9, sphereRotation8 g northPole8 = p ∧
      ∀ q ∈ ball p r, ∃ u ∈ equalAreaChartDomain, ‖u‖ ≤ 2*r ∧
        g (equalAreaPhi u) = (q : Ambient9) := by
  obtain ⟨g,hg⟩ := sphereRotation8_transitive northPole8 p
  refine ⟨g,hg,?_⟩
  intro q hq
  let z : Sphere8 := sphereRotation8 g.symm q
  have hgz : sphereRotation8 g z = q := by
    apply Subtype.ext
    exact g.apply_symm_apply q
  have hz : z ∈ ball northPole8 r := by
    rw [mem_ball,← sphereRotation8_dist g z northPole8,hgz,hg]
    exact hq
  obtain ⟨hu,hn,hphi⟩ := northPole8_ball_chart z r hr hz
  refine ⟨equalAreaInverse8 z,hu,hn,?_⟩
  rw [hphi]
  exact g.apply_symm_apply q

theorem sphere8_finite_small_chart_buffered_cores (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ K : ℕ, ∃ g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9,
      ∃ k : Fin K → Set Sphere8, ∃ ρ > 0,
      (∀ i, IsCompact (k i) ∧ IsOpen (thickening ρ (k i)) ∧
        k i ⊆ thickening ρ (k i) ∧
        ∀ q ∈ thickening ρ (k i), ∃ u ∈ equalAreaChartDomain,
          ‖u‖ < a ∧ g i (equalAreaPhi u) = (q : Ambient9)) ∧
      1-b < sphereProbability8.real (⋃ i, k i) ∧
      Pairwise (fun i j => Disjoint (thickening ρ (k i)) (thickening ρ (k j))) := by
  classical
  let r : ℝ := min (a/4) (1/4)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hrhalf : r ≤ 1/2 := (min_le_right _ _).trans (by norm_num)
  have hra : 2*r < a := by
    have h := min_le_left (a/4) (1/4)
    change r ≤ a/4 at h
    linarith
  obtain ⟨K,p,k,ρ,hρ,hk,hmass,hd⟩ := sphere8_finite_ball_buffered_cores_mass r b hr hb
  have h : ∀ i, ∃ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9, sphereRotation8 g northPole8 = p i ∧
      ∀ q ∈ ball (p i) r, ∃ u ∈ equalAreaChartDomain, ‖u‖ ≤ 2*r ∧
        g (equalAreaPhi u) = (q : Ambient9) :=
    fun i => sphere8_ball_rotated_chart (p i) r hrhalf
  choose g hg hchart using h
  refine ⟨K,g,k,ρ,hρ,?_,hmass,hd⟩
  intro i
  refine ⟨(hk i).1,(hk i).2.2.1,(hk i).2.2.2.1,?_⟩
  intro q hq
  obtain ⟨u,hu,hn,he⟩ := hchart i q ((hk i).2.2.2.2 hq)
  exact ⟨u,hu,hn.trans_lt hra,he⟩

end SphericalRiesz
