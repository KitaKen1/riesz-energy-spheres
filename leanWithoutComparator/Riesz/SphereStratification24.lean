import Riesz.CarryOverSlices
import Riesz.SphereResidualCells24
import Riesz.SphereRieszNeg24
import Riesz.LeechProfileLower24
import Riesz.EqualAreaMeasureD
import Riesz.SphereChartPool8
import Riesz.SphereRieszLower24
import Riesz.LeechForegroundBump24
import Riesz.EqualAreaFinitePatchGeometry24
import Riesz.CubeLebesgue

/-! # Exact-mass stratifications of `S²⁴` with small cells

The dimension-24 form of the checked dimension-8 stratification chain (`SphereGridPool8`,
`SphereChartBiLip8`, `ChartGridBoxes8`, `ChartBoundaryMinkowski8`, `SphereChartRegions8`,
`SphereChartPool8`, `SphereStratification8`, `PatchBoundaryMinkowski8` and the stratification
part of `ResidualStratification8`).  The parts keep the order and the statements of that chain,
with `S⁸`, the `E8` map and the dimension 8 replaced by `S²⁴`, the Leech map and the dimension 24.
The results are

* `sphere24_stratifiable`: for every `r` the sphere splits into `r` measurable cells of
  probability exactly `1/r` with `Σ_j c_r d_j² ≤ B r` for one absolute `B`
  (`SphereStratifiable24 B`);
* `negStratifiable24_patch_complement`: the complement of any finite union of small Leech cube
  patches splits, for `r = N σ(A)`, into `r` cells of probability exactly `1/N` with
  `Σ_j c_N d_j² ≤ 96π r + ε N` for every large `N` (`NegStratifiable24 A (96π)`);
* `sphere24_stratification_hypotheses`: both hold with one absolute constant.

Here `c_N = π (N/area)^(1/12)` is `sphereGaussianDensityFactor24 N` and `d_j` bounds the diameter
of the `j`-th cell.  No point configurations, energies or asymptotics are asserted. -/

section

/-! Pools of small mass on `S²⁴` split into exact-mass cells of coarse diameter (stage NEG,
stratification; dimension-24 port of `SphereGridPool8`).

* The level sets of the first coordinate are null for the sphere probability
  (`sphereProbability24_coord_level_null`, already in `SphereResidualCells24`).
* The ambient grid of side `H` cuts the sphere into `(2⌈1/H⌉+1)^25` measurable disjoint pieces of
  diameter at most `5H` (`√25 = 5`).
* Pool partition: any measurable `P` splits into `n` cells of mass exactly `σ(P)/n` with
  `Σ_j d_j² ≤ n (5H)² + 4 (2⌈1/H⌉+1)^25` (carry-over slicing along the grid; at most one cell per
  grid piece straddles, with diameter at most 2 by `sphere24_dist_le_two` of `SphereRieszNeg24`). -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped Pointwise
namespace SphericalRiesz

theorem sphere24_abs_coord_le_one (x : SphereD 24) (i : Fin 25) : |(x : AmbientD 24) i| ≤ 1 := by
  have hx : ‖(x : AmbientD 24)‖ = 1 := norm_eq_of_mem_sphere x
  calc |(x : AmbientD 24) i| = ‖(x : AmbientD 24) i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖(x : AmbientD 24)‖ := PiLp.norm_apply_le _ i
    _ = 1 := hx

/-- The cells of the ambient grid of side `H` met by the sphere. -/
def ambientGridCell24 (H : ℝ) (m : ℕ) (k : Fin 25 → Fin (2*m+1)) : Set (SphereD 24) :=
  {x | ∀ i, ⌊(x : AmbientD 24) i/H⌋+(m:ℤ) = ((k i : ℕ) : ℤ)}

theorem ambientGridCell24_measurable (H : ℝ) (m : ℕ) (k : Fin 25 → Fin (2*m+1)) :
    MeasurableSet (ambientGridCell24 H m k) := by
  have : ambientGridCell24 H m k =
      ⋂ i, {x : SphereD 24 | ⌊(x : AmbientD 24) i/H⌋+(m:ℤ) = ((k i : ℕ) : ℤ)} := by
    ext x
    simp [ambientGridCell24]
  rw [this]
  refine MeasurableSet.iInter fun i => ?_
  have hm : Measurable (fun x : SphereD 24 => ⌊(x : AmbientD 24) i/H⌋+(m:ℤ)) :=
    (Int.measurable_floor.comp (by fun_prop)).add_const _
  exact hm (measurableSet_singleton _)

theorem ambientGridCell24_disjoint (H : ℝ) (m : ℕ) :
    Pairwise (fun k k' : Fin 25 → Fin (2*m+1) =>
      Disjoint (ambientGridCell24 H m k) (ambientGridCell24 H m k')) := by
  intro k k' hkk
  rw [Set.disjoint_left]
  intro x hx hx'
  apply hkk
  funext i
  have h1 := hx i
  have h2 := hx' i
  apply Fin.ext
  exact_mod_cast h1.symm.trans h2

theorem ambientGridCell24_cover {H : ℝ} (hH : 0 < H) (x : SphereD 24) :
    ∃ k, x ∈ ambientGridCell24 H ⌈1/H⌉₊ k := by
  set m := ⌈1/H⌉₊ with hmdef
  have hmH : 1/H ≤ (m:ℝ) := Nat.le_ceil _
  have hb : ∀ i, 0 ≤ ⌊(x : AmbientD 24) i/H⌋+(m:ℤ) ∧
      ⌊(x : AmbientD 24) i/H⌋+(m:ℤ) < 2*(m:ℤ)+1 := by
    intro i
    have hxi := abs_le.mp (sphere24_abs_coord_le_one x i)
    have hlo : -(1/H) ≤ (x : AmbientD 24) i/H := by
      rw [← neg_div]
      exact div_le_div_of_nonneg_right hxi.1 hH.le
    have hhi : (x : AmbientD 24) i/H ≤ 1/H := div_le_div_of_nonneg_right hxi.2 hH.le
    have h1 : -((m:ℤ)) ≤ ⌊(x : AmbientD 24) i/H⌋ := by
      rw [Int.le_floor]
      push_cast
      linarith
    have h2 : ⌊(x : AmbientD 24) i/H⌋ ≤ (m:ℤ) := by
      have h3 : ((⌊(x : AmbientD 24) i/H⌋ : ℤ) : ℝ) ≤ (m:ℝ) :=
        (Int.floor_le _).trans (hhi.trans hmH)
      exact_mod_cast h3
    constructor <;> omega
  refine ⟨fun i => ⟨(⌊(x : AmbientD 24) i/H⌋+(m:ℤ)).toNat, ?_⟩, ?_⟩
  · have := hb i
    omega
  · intro i
    have := hb i
    simp only
    rw [Int.toNat_of_nonneg this.1]

/-- Diameter of an ambient grid cell: `√25 H = 5H`. -/
theorem ambientGridCell24_dist_le {H : ℝ} (hH : 0 < H) (m : ℕ) (k : Fin 25 → Fin (2*m+1))
    {x y : SphereD 24} (hx : x ∈ ambientGridCell24 H m k) (hy : y ∈ ambientGridCell24 H m k) :
    dist x y ≤ 5*H := by
  have hi : ∀ i, |(x : AmbientD 24) i-(y : AmbientD 24) i| < H := by
    intro i
    have h := (hx i).trans (hy i).symm
    have hfl : ⌊(x : AmbientD 24) i/H⌋ = ⌊(y : AmbientD 24) i/H⌋ := by linarith
    have h1 := Int.abs_sub_lt_one_of_floor_eq_floor hfl
    rw [← sub_div, abs_div, abs_of_pos hH, div_lt_one hH] at h1
    exact h1
  have hsq : dist x y^2 ≤ (5*H)^2 := by
    rw [Subtype.dist_eq, EuclideanSpace.dist_eq,
      Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    calc ∑ i, dist ((x : AmbientD 24) i) ((y : AmbientD 24) i)^2 ≤ ∑ _i : Fin 25, H^2 := by
          apply Finset.sum_le_sum
          intro i _
          rw [Real.dist_eq]
          have := hi i
          have h0 := abs_nonneg ((x : AmbientD 24) i-(y : AmbientD 24) i)
          nlinarith
      _ = (5*H)^2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have h0 : 0 ≤ 5*H := by positivity
  nlinarith [dist_nonneg (x := x) (y := y)]

/-- Pool partition: exact-mass cells whose diameters are controlled by the grid scale, up to at
most `(2⌈1/H⌉+1)^25` straddling cells. -/
theorem sphere24_pool_partition {P : Set (SphereD 24)} (hP : MeasurableSet P) {H : ℝ} (hH : 0 < H)
    {n : ℕ} (hn : 0 < n) :
    ∃ C : Fin n → Set (SphereD 24), ∃ dm : Fin n → ℝ, (∀ j, MeasurableSet (C j)) ∧
      Pairwise (fun i j => Disjoint (C i) (C j)) ∧ (⋃ j, C j) = P ∧
      (∀ j, (sphereProbabilityD 24).real (C j) = (sphereProbabilityD 24).real P/n) ∧
      (∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y ≤ dm j) ∧
      ∑ j, (dm j)^2 ≤ n*(5*H)^2+4*(2*⌈1/H⌉₊+1)^25 := by
  classical
  set m := ⌈1/H⌉₊ with hmdef
  let e := Fintype.equivFin (Fin 25 → Fin (2*m+1))
  set M := Fintype.card (Fin 25 → Fin (2*m+1)) with hMdef
  have hMval : M = (2*m+1)^25 := by
    rw [hMdef, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  let Q : Fin M → Set (SphereD 24) := fun j => ambientGridCell24 H m (e.symm j)
  have hQm : ∀ j, MeasurableSet (Q j) := fun j => ambientGridCell24_measurable H m _
  have hQd : Pairwise (fun i j => Disjoint (Q i) (Q j)) := by
    intro i j hij
    exact ambientGridCell24_disjoint H m (fun h => hij (e.symm.injective h))
  have hPQ : P ⊆ ⋃ j, Q j := by
    intro x _
    obtain ⟨k, hk⟩ := ambientGridCell24_cover hH x
    exact mem_iUnion.mpr ⟨e k, by simp only [Q, e.symm_apply_apply]; exact hk⟩
  have hg : Measurable (fun x : SphereD 24 => (x : AmbientD 24) 0) := by fun_prop
  have hgnull : ∀ c, (sphereProbabilityD 24)
      ((fun x : SphereD 24 => (x : AmbientD 24) 0) ⁻¹' {c} ∩ P) = 0 :=
    fun c => measure_mono_null inter_subset_left (sphereProbability24_coord_level_null c)
  obtain ⟨C, hCm, hCd, hCu, hCmass, T, hT, hTsub⟩ := exists_exact_mass_carry_slices
    (sphereProbabilityD 24) hP Q hQm hQd hPQ hg (fun x => sphere24_abs_coord_le_one x 0) hgnull hn
  refine ⟨C, fun j => if j ∈ T then 2 else 5*H, hCm, hCd, hCu, hCmass, ?_, ?_⟩
  · intro j x hx y hy
    by_cases hj : j ∈ T
    · simp only [ite_eq_left hj]
      exact sphere24_dist_le_two x y
    · simp only [ite_eq_right hj]
      obtain ⟨k, hxk, hyk⟩ := hTsub j hj x hx y hy
      exact ambientGridCell24_dist_le hH m (e.symm k) hxk hyk
  · have hsplit : ∑ j, (if j ∈ T then (2:ℝ) else 5*H)^2 ≤
        ∑ j : Fin n, ((5*H)^2+(if j ∈ T then 4 else 0)) := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j ∈ T
      · simp only [ite_eq_left hj]
        have h22 : (2:ℝ)^2 = 4 := by norm_num
        rw [h22]
        exact le_add_of_nonneg_left (sq_nonneg (5*H))
      · simp only [ite_eq_right hj]
        exact (add_zero _).ge
    have hcount : ∑ j : Fin n, (if j ∈ T then (4:ℝ) else 0) = 4*T.card := by
      rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      ring
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hcount] at hsplit
    have hT' : T.card ≤ (2*m+1)^25 := hMval ▸ hT
    have hTM : (T.card:ℝ) ≤ (2*(m:ℝ)+1)^25 := by exact_mod_cast hT'
    have h4 : (4:ℝ)*T.card ≤ 4*(2*(m:ℝ)+1)^25 := mul_le_mul_of_nonneg_left hTM (by norm_num)
    exact hsplit.trans (add_le_add le_rfl h4)

end SphericalRiesz
end
end

section

/-! Bi-Lipschitz equal-area charts and the spherical cap bound on `S²⁴` (stage NEG,
stratification; dimension-24 port of `SphereChartBiLip8`).

The equal-area chart `Φ` has an isometric derivative at the centre (`‖DΦ(0) v‖ = ‖v‖`) and is
strictly differentiable there, so `Φ - DΦ(0)` is `1/2`-Lipschitz near `0`; hence
`|u - v| ≤ 2 |Φu - Φv| ≤ 4 |u - v|` near the centre. Consequently a small spherical cap around
any point is the rotated chart image of a small coordinate set: `area(B(x,R)) ≤ (4R)^24` for
`R ≤ R₀` (rotate `x` to the north pole, pull back by the chart, compare with a coordinate cube;
the chart is exactly equal-area). The coordinate cube `[-2R,2R]^24` lies in the chart domain as
soon as `23 (2R)² < 1`, which is why `R₀ ≤ 1/16` here (`1/8` suffices in dimension 8). -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
namespace SphericalRiesz

theorem equalAreaPhiEuclidean24_near_biLipschitz :
    ∃ ρ > 0, ρ ≤ 1/8 ∧ ∀ u ∈ ball (0 : EuclideanSpace ℝ (Fin 24)) ρ,
      ∀ v ∈ ball (0 : EuclideanSpace ℝ (Fin 24)) ρ,
        dist u v ≤ 2*dist (equalAreaPhiEuclidean24 u) (equalAreaPhiEuclidean24 v) ∧
        dist (equalAreaPhiEuclidean24 u) (equalAreaPhiEuclidean24 v) ≤ 2*dist u v := by
  set D := equalAreaEuclideanDerivative24 with hDdef
  have hD := equalAreaPhiEuclidean24_hasStrictFDerivAt_zero
  have hsub : HasStrictFDerivAt (fun u => equalAreaPhiEuclidean24 u-D u) (D-D) 0 :=
    hD.sub D.hasStrictFDerivAt
  rw [sub_self] at hsub
  have hk : ‖(0 : EuclideanSpace ℝ (Fin 24) →L[ℝ] AmbientD 24)‖₊ < Real.toNNReal (1/2) := by
    simp
  obtain ⟨s, hs, hLip⟩ := hsub.exists_lipschitzOnWith_of_nnnorm_lt (Real.toNNReal (1/2)) hk
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨min δ (1/8), lt_min hδ (by norm_num), min_le_right _ _, ?_⟩
  intro u hu v hv
  have hu' := hball (ball_subset_ball (min_le_left δ (1/8)) hu)
  have hv' := hball (ball_subset_ball (min_le_left δ (1/8)) hv)
  have h := hLip.dist_le_mul u hu' v hv'
  rw [Real.coe_toNNReal _ (by norm_num)] at h
  set E := (equalAreaPhiEuclidean24 u-D u)-(equalAreaPhiEuclidean24 v-D v) with hEdef
  have hE : ‖E‖ ≤ 1/2*‖u-v‖ := by
    rw [hEdef, ← dist_eq_norm, ← dist_eq_norm]
    exact h
  have hDn : ‖D (u-v)‖ = ‖u-v‖ := equalAreaEuclideanDerivative24_norm (u-v)
  have hdecomp : equalAreaPhiEuclidean24 u-equalAreaPhiEuclidean24 v = D (u-v)+E := by
    rw [hEdef, map_sub]
    abel
  rw [dist_eq_norm, dist_eq_norm, hdecomp]
  constructor
  · have h4 := norm_sub_le (D (u-v)+E) E
    have h2 : D (u-v)+E-E = D (u-v) := by abel
    rw [h2, hDn] at h4
    linarith
  · have h1 := norm_add_le (D (u-v)) E
    rw [hDn] at h1
    nlinarith [norm_nonneg (u-v)]

theorem equalAreaPhiEuclidean24_zero :
    equalAreaPhiEuclidean24 0 = (northPole24 : AmbientD 24) := by
  have h := equalAreaPhiEuclidean24_inverse northPole24 (by simp [northPole24])
  rwa [sphereEqualAreaCoordinates24_northPole] at h

theorem sphere24_coord0_gt_of_dist_northPole (y : SphereD 24) (hy : dist y northPole24 < 1/2) :
    1/2 < (y : AmbientD 24) 0 := by
  have h1 : |((y : AmbientD 24)-(northPole24 : AmbientD 24)) 0| ≤
      ‖(y : AmbientD 24)-(northPole24 : AmbientD 24)‖ := by
    have := PiLp.norm_apply_le ((y : AmbientD 24)-(northPole24 : AmbientD 24)) (0 : Fin 25)
    rwa [Real.norm_eq_abs] at this
  have h2 : ((y : AmbientD 24)-(northPole24 : AmbientD 24)) 0 = (y : AmbientD 24) 0-1 := by
    simp [northPole24]
  rw [h2] at h1
  have h3 : dist y northPole24 = ‖(y : AmbientD 24)-(northPole24 : AmbientD 24)‖ := by
    rw [Subtype.dist_eq, dist_eq_norm]
  rw [← h3] at h1
  have := (abs_lt.mp (lt_of_le_of_lt h1 hy)).1
  linarith

/-- The spherical cap bound: `area(B(x,R)) ≤ (4R)^24` for small `R`. -/
theorem sphereArea24_ball_le : ∃ R₀ > 0, ∀ x : SphereD 24, ∀ R : ℝ, 0 < R → R ≤ R₀ →
    (sphereAreaD 24) {y : SphereD 24 | dist y x < R} ≤ ENNReal.ofReal ((4*R)^24) := by
  obtain ⟨ρ, hρ, _hρ8, hbi⟩ := equalAreaPhiEuclidean24_near_biLipschitz
  have hc := sphereEqualAreaCoordinates24_continuousAt northPole24 (by simp [northPole24])
  obtain ⟨R₁, hR₁, hR₁c⟩ := Metric.continuousAt_iff.mp hc ρ hρ
  refine ⟨min R₁ (1/16), lt_min hR₁ (by norm_num), fun x R hR hRR => ?_⟩
  have hR1 : R ≤ R₁ := hRR.trans (min_le_left _ _)
  have hR16 : R ≤ 1/16 := hRR.trans (min_le_right _ _)
  obtain ⟨g, hg⟩ := sphereRotation24_transitive northPole24 x
  have hpre : (sphereRotationD g) ⁻¹' {y : SphereD 24 | dist y x < R} =
      {y : SphereD 24 | dist y northPole24 < R} := by
    ext y
    simp only [mem_preimage, mem_ofPred_eq, ← hg]
    have : dist (sphereRotationD g y) (sphereRotationD g northPole24) = dist y northPole24 :=
      sphereRotationD_dist g y northPole24
    rw [this]
  have hm := (sphereAreaD_rotation_preserving g).measure_preimage_emb
    (sphereRotationD g).measurableEmbedding {y : SphereD 24 | dist y x < R}
  rw [hpre] at hm
  rw [← hm]
  set cube : Set (Fin 24 → ℝ) := Set.pi univ (fun _ => Icc (-(2*R)) (2*R)) with hcube
  have hcm : MeasurableSet cube := MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hcd : cube ⊆ equalAreaChartDomainD := by
    intro p hp
    have hpi : ∀ i, |p i| ≤ 2*R := fun i => abs_le.mpr (hp i (mem_univ i))
    refine ⟨?_, ?_⟩
    · unfold equalAreaSquaredNormD
      calc ∑ j : Fin 23, p j.succ^2 ≤ ∑ _j : Fin 23, (2*R)^2 := by
            apply Finset.sum_le_sum
            intro j _
            have := hpi j.succ
            nlinarith [abs_nonneg (p j.succ), sq_abs (p j.succ)]
        _ < 1 := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            have hR2 : R^2 ≤ 1/256 := by nlinarith
            push_cast
            nlinarith
    · have h0 := abs_le.mp (hpi 0)
      have hpi3 := Real.pi_gt_three
      constructor <;> linarith
  have hsub : {y : SphereD 24 | dist y northPole24 < R} ⊆ equalAreaSpherePatchD cube := by
    intro y hy
    simp only [mem_ofPred_eq] at hy
    have hy0 : 0 < (y : AmbientD 24) 0 :=
      lt_trans (by norm_num)
        (sphere24_coord0_gt_of_dist_northPole y (lt_of_lt_of_le hy (by linarith)))
    set u := sphereEqualAreaCoordinates24 y with hudef
    have hu : dist u 0 < ρ := by
      rw [← sphereEqualAreaCoordinates24_northPole]
      exact hR₁c (lt_of_lt_of_le hy hR1)
    have hΦu : equalAreaPhiEuclidean24 u = (y : AmbientD 24) :=
      equalAreaPhiEuclidean24_inverse y hy0
    have hb := (hbi u (mem_ball.mpr hu) 0 (mem_ball_self hρ)).1
    rw [hΦu, equalAreaPhiEuclidean24_zero] at hb
    have hyd : dist (y : AmbientD 24) (northPole24 : AmbientD 24) = dist y northPole24 :=
      (Subtype.dist_eq _ _).symm
    rw [hyd] at hb
    have hun : ‖u‖ < 2*R := by
      rw [← dist_zero_right]
      linarith
    refine ⟨WithLp.ofLp u, ?_, hΦu⟩
    intro i _
    have := (PiLp.norm_apply_le u i).trans hun.le
    exact abs_le.mp this
  calc (sphereAreaD 24) {y : SphereD 24 | dist y northPole24 < R}
      ≤ (sphereAreaD 24) (equalAreaSpherePatchD cube) := measure_mono hsub
    _ = (volume : Measure (Fin 24 → ℝ)) cube := sphereAreaD_equalAreaSpherePatch cube hcm hcd
    _ = ENNReal.ofReal ((4*R)^24) := by
        rw [hcube, volume_pi_pi]
        simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [← ENNReal.ofReal_pow (by linarith)]
        congr 1
        ring

end SphericalRiesz
end
end

section

/-! Grid boxes in chart coordinates of `S²⁴` (stage NEG, stratification; dimension-24 port of
`ChartGridBoxes8`).

Half-open boxes `∏ [h z_i, h(z_i+1))` of side `h` tile `ℝ^24`: they are measurable, pairwise
disjoint, have volume `h^24` and Euclidean diameter at most `√24 h`, and every point lies in the
box of its floor index. Counting by volume: any finite family of distinct boxes inside a
measurable set `U` has at most `vol(U)/h^24` members; for the boxes meeting the boundary layer of
the cube `[-δ,δ]^24` this gives `O(h^(-23))`, the count behind the Minkowski estimate of chart
images of cube boundaries. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal
namespace SphericalRiesz

def gridBox24 (h : ℝ) (z : Fin 24 → ℤ) : Set (Fin 24 → ℝ) :=
  Set.pi univ (fun i => Ico (h*(z i)) (h*((z i)+1)))

theorem gridBox24_measurable (h : ℝ) (z : Fin 24 → ℤ) : MeasurableSet (gridBox24 h z) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ico)

theorem gridBox24_volume {h : ℝ} (hh : 0 < h) (z : Fin 24 → ℤ) :
    (volume : Measure (Fin 24 → ℝ)) (gridBox24 h z) = ENNReal.ofReal (h^24) := by
  rw [gridBox24, volume_pi_pi]
  simp only [Real.volume_Ico]
  have he : ∀ i, h*((z i:ℝ)+1)-h*(z i) = h := fun i => by ring
  simp only [he, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow hh.le]

theorem gridBox24_disjoint {h : ℝ} (hh : 0 < h) :
    Pairwise (fun z z' : Fin 24 → ℤ => Disjoint (gridBox24 h z) (gridBox24 h z')) := by
  intro z z' hzz
  rw [Set.disjoint_left]
  intro p hp hp'
  apply hzz
  funext i
  have h1 := hp i (mem_univ i)
  have h2 := hp' i (mem_univ i)
  have a1 : (z i:ℝ) ≤ p i/h := by rw [le_div_iff₀ hh]; linarith [h1.1]
  have a2 : p i/h < (z i:ℝ)+1 := by rw [div_lt_iff₀ hh]; linarith [h1.2]
  have b1 : (z' i:ℝ) ≤ p i/h := by rw [le_div_iff₀ hh]; linarith [h2.1]
  have b2 : p i/h < (z' i:ℝ)+1 := by rw [div_lt_iff₀ hh]; linarith [h2.2]
  have c1 : (z i:ℝ) < (z' i:ℝ)+1 := lt_of_le_of_lt a1 b2
  have c2 : (z' i:ℝ) < (z i:ℝ)+1 := lt_of_le_of_lt b1 a2
  have d1 : z i < z' i+1 := by exact_mod_cast c1
  have d2 : z' i < z i+1 := by exact_mod_cast c2
  omega

/-- The floor index of a point. -/
def gridIndex24 (h : ℝ) (p : Fin 24 → ℝ) : Fin 24 → ℤ := fun i => ⌊p i/h⌋

theorem mem_gridBox24_gridIndex24 {h : ℝ} (hh : 0 < h) (p : Fin 24 → ℝ) :
    p ∈ gridBox24 h (gridIndex24 h p) := by
  intro i _
  simp only [gridIndex24]
  constructor
  · have := Int.floor_le (p i/h)
    rw [le_div_iff₀ hh] at this
    linarith
  · have := Int.lt_floor_add_one (p i/h)
    rw [div_lt_iff₀ hh] at this
    linarith

theorem gridBox24_abs_sub_lt {h : ℝ} {z : Fin 24 → ℤ} {p q : Fin 24 → ℝ}
    (hp : p ∈ gridBox24 h z) (hq : q ∈ gridBox24 h z) (i : Fin 24) : |p i-q i| < h := by
  have h1 := hp i (mem_univ i)
  have h2 := hq i (mem_univ i)
  rw [abs_lt]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Euclidean diameter of a grid box. -/
theorem gridBox24_dist_le {h : ℝ} (hh : 0 < h) {z : Fin 24 → ℤ} {p q : Fin 24 → ℝ}
    (hp : p ∈ gridBox24 h z) (hq : q ∈ gridBox24 h z) :
    dist (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 24)) (WithLp.toLp 2 q) ≤ Real.sqrt 24*h := by
  rw [EuclideanSpace.dist_eq]
  have hsum : ∑ i, dist ((WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 24)) i)
      ((WithLp.toLp 2 q : EuclideanSpace ℝ (Fin 24)) i)^2 ≤ 24*h^2 := by
    calc ∑ i, dist ((WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 24)) i)
          ((WithLp.toLp 2 q : EuclideanSpace ℝ (Fin 24)) i)^2 ≤ ∑ _i : Fin 24, h^2 := by
          apply Finset.sum_le_sum
          intro i _
          rw [Real.dist_eq]
          have := gridBox24_abs_sub_lt hp hq i
          have h0 := abs_nonneg (p i-q i)
          nlinarith
      _ = 24*h^2 := by simp
  calc Real.sqrt (∑ i, dist ((WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 24)) i)
        ((WithLp.toLp 2 q : EuclideanSpace ℝ (Fin 24)) i)^2) ≤ Real.sqrt (24*h^2) :=
        Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 24*h := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hh.le]

/-- Counting by volume: distinct grid boxes inside `U`. -/
theorem gridBox24_card_le {h : ℝ} (hh : 0 < h) (Z : Finset (Fin 24 → ℤ))
    {U : Set (Fin 24 → ℝ)} (hU : ∀ z ∈ Z, gridBox24 h z ⊆ U) :
    (Z.card:ℝ≥0∞)*ENNReal.ofReal (h^24) ≤ (volume : Measure (Fin 24 → ℝ)) U := by
  have hdisj : Set.PairwiseDisjoint (↑Z) (gridBox24 h) :=
    fun z _ z' _ hzz => gridBox24_disjoint hh hzz
  have hm := measure_biUnion_finset hdisj (fun z _ => gridBox24_measurable h z)
    (μ := (volume : Measure (Fin 24 → ℝ)))
  have hsub : (⋃ z ∈ Z, gridBox24 h z) ⊆ U := iUnion₂_subset hU
  calc (Z.card:ℝ≥0∞)*ENNReal.ofReal (h^24) =
        ∑ z ∈ Z, (volume : Measure (Fin 24 → ℝ)) (gridBox24 h z) := by
        rw [Finset.sum_congr rfl (fun z _ => gridBox24_volume hh z), Finset.sum_const, nsmul_eq_mul]
    _ = (volume : Measure (Fin 24 → ℝ)) (⋃ z ∈ Z, gridBox24 h z) := hm.symm
    _ ≤ (volume : Measure (Fin 24 → ℝ)) U := measure_mono hsub

end SphericalRiesz
end
end

section

/-! Minkowski estimate for chart images of cube boundaries on `S²⁴` (stage NEG, stratification;
dimension-24 port of `ChartBoundaryMinkowski8`).

Fix the chart cube `[-δ,δ]^24` with `δ = ρ_b/12`, where `ρ_b` is the radius on which the
equal-area chart is bi-Lipschitz with constants `1/2, 2` (`2√24 δ < ρ_b` since `√24 < 5`). Grid
boxes of side `ρ` meeting the cube boundary lie in the `48 = 2·24` boundary slabs, of total volume
`48·2ρ·(2(δ+ρ))^23`, so there are at most `96 (2(δ+ρ))^23/ρ^23` of them (counting by volume).
Every point within `ρ` of a rotated chart image of the boundary is within `(2√24+1)ρ < 11ρ` of the
image of such a box corner, and spherical caps of radius `R` have area at most `(4R)^24`: the
neighbourhood has area `O(ρ)`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal
namespace SphericalRiesz

/-- The boundary of the chart cube `[-δ,δ]^24`. -/
def cubeBdry24 (δ : ℝ) : Set (Fin 24 → ℝ) := {w | (∀ i, |w i| ≤ δ) ∧ ∃ i, |w i| = δ}

/-- The boundary slab of the cube in direction `i` and sign `s`. -/
def cubeSlab24 (δ ρ : ℝ) (i : Fin 24) (s : Bool) : Set (Fin 24 → ℝ) :=
  Set.pi univ (fun j => if j = i then Icc ((if s then δ else -δ)-ρ) ((if s then δ else -δ)+ρ)
    else Icc (-(δ+ρ)) (δ+ρ))

theorem cubeSlab24_volume (δ ρ : ℝ) (i : Fin 24) (s : Bool) :
    (volume : Measure (Fin 24 → ℝ)) (cubeSlab24 δ ρ i s) =
      ENNReal.ofReal (2*ρ)*ENNReal.ofReal (2*(δ+ρ))^23 := by
  rw [cubeSlab24, volume_pi_pi]
  have hj : ∀ j, (volume : Measure ℝ) (if j = i then Icc ((if s then δ else -δ)-ρ)
      ((if s then δ else -δ)+ρ) else Icc (-(δ+ρ)) (δ+ρ)) =
      if j = i then ENNReal.ofReal (2*ρ) else ENNReal.ofReal (2*(δ+ρ)) := by
    intro j
    split_ifs <;> rw [Real.volume_Icc] <;> congr 1 <;> ring
  simp only [hj]
  rw [Fintype.prod_eq_mul_prod_compl i]
  simp only [ite_true]
  congr 1
  rw [Finset.prod_congr rfl (fun j hj => ite_eq_right (by simpa using hj))]
  simp [Finset.card_compl]

theorem gridBox24_subset_slab {δ ρ : ℝ} {z : Fin 24 → ℤ}
    (hz : (gridBox24 ρ z ∩ cubeBdry24 δ).Nonempty) :
    ∃ i s, gridBox24 ρ z ⊆ cubeSlab24 δ ρ i s := by
  obtain ⟨w, hwb, hw, i, hi⟩ := hz
  have hs : w i = δ ∨ w i = -δ := by
    rcases le_or_gt 0 (w i) with h | h
    · left; rw [abs_of_nonneg h] at hi; exact hi
    · right; rw [abs_of_neg h] at hi; linarith
  refine ⟨i, decide (w i = δ), ?_⟩
  intro p hp j _
  have hpw := gridBox24_abs_sub_lt hp hwb j
  by_cases hji : j = i
  · subst hji
    simp only [ite_true]
    rcases hs with h | h
    · have hd : decide (w j = δ) = true := decide_eq_true h
      simp only [hd, ite_true]
      rw [abs_lt] at hpw
      constructor <;> linarith
    · by_cases hδ0 : w j = δ
      · have hd : decide (w j = δ) = true := decide_eq_true hδ0
        simp only [hd, ite_true]
        rw [abs_lt] at hpw
        constructor <;> linarith
      · have hd : decide (w j = δ) = false := decide_eq_false hδ0
        simp only [hd]
        simp only [Bool.false_eq_true, ite_false]
        rw [abs_lt] at hpw
        constructor <;> linarith
  · simp only [ite_eq_right hji]
    have hwj := abs_le.mp (hw j)
    rw [abs_lt] at hpw
    constructor <;> linarith

theorem cubeBdry24_box_finite {δ ρ : ℝ} (hρ : 0 < ρ) :
    {z : Fin 24 → ℤ | (gridBox24 ρ z ∩ cubeBdry24 δ).Nonempty}.Finite := by
  set K : ℤ := ⌈|δ|/ρ⌉+1 with hK
  apply (Set.finite_Icc (fun _ : Fin 24 => -K) (fun _ => K)).subset
  intro z hz
  obtain ⟨w, hwb, hw, _⟩ := hz
  have hb : ∀ i, -K ≤ z i ∧ z i ≤ K := by
    intro i
    have h1 := (hwb i (mem_univ i)).1
    have h2 := (hwb i (mem_univ i)).2
    have hwi := abs_le.mp ((hw i).trans (le_abs_self δ))
    have hc := Int.le_ceil (|δ|/ρ)
    have hKr : (K:ℝ) = ((⌈|δ|/ρ⌉:ℤ):ℝ)+1 := by rw [hK]; push_cast; ring
    have hzu : (z i:ℝ) ≤ |δ|/ρ := by rw [le_div_iff₀ hρ]; linarith
    have h5 : (-|δ|)/ρ < (z i:ℝ)+1 := by rw [div_lt_iff₀ hρ]; linarith
    rw [neg_div] at h5
    have hl : (-(K:ℝ)) < (z i:ℝ) := by linarith
    have hu : (z i:ℝ) ≤ (K:ℝ) := by linarith
    have hl' : -K < z i := by exact_mod_cast hl
    have hu' : z i ≤ K := by exact_mod_cast hu
    exact ⟨hl'.le, hu'⟩
  exact ⟨fun i => (hb i).1, fun i => (hb i).2⟩

/-- Sup-norm bounds give Euclidean bounds in `ℝ^24` with the factor `√24`. -/
theorem toLp24_norm_le_of_abs_le {p : Fin 24 → ℝ} {a : ℝ} (ha : 0 ≤ a) (hp : ∀ i, |p i| ≤ a) :
    ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 24))‖ ≤ Real.sqrt 24*a := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i, ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 24)) i‖^2 ≤ 24*a^2 := by
    calc ∑ i, ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 24)) i‖^2 ≤ ∑ _i : Fin 24, a^2 := by
          apply Finset.sum_le_sum
          intro i _
          rw [Real.norm_eq_abs, sq_abs]
          have := hp i
          have h0 := abs_nonneg (p i)
          nlinarith [sq_abs (p i)]
      _ = 24*a^2 := by simp
  calc Real.sqrt (∑ i, ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 24)) i‖^2) ≤
        Real.sqrt (24*a^2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt 24*a := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq ha]

/-- The chart parameters: a cube `[-2δ,2δ]^24` inside the chart domain on which the chart is
bi-Lipschitz, and the Minkowski estimate for rotated images of the boundary of `[-δ,δ]^24`. -/
theorem chart_boundary_minkowski24 :
    ∃ δ > 0, ∃ C : ℝ, 0 ≤ C ∧ ∃ ρ₁ > 0,
      (∀ p : Fin 24 → ℝ, (∀ i, |p i| ≤ 2*δ) → p ∈ equalAreaChartDomainD) ∧
      (∀ p q : Fin 24 → ℝ, (∀ i, |p i| ≤ 2*δ) → (∀ i, |q i| ≤ 2*δ) →
        dist (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 24)) (WithLp.toLp 2 q) ≤
          2*dist (equalAreaPhiD p) (equalAreaPhiD q) ∧
        dist (equalAreaPhiD p) (equalAreaPhiD q) ≤
          2*dist (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 24)) (WithLp.toLp 2 q)) ∧
      ∀ g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24, ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₁ →
        (sphereAreaD 24) {x : SphereD 24 | ∃ w ∈ cubeBdry24 δ,
            dist (x : AmbientD 24) (g (equalAreaPhiD w)) ≤ ρ} ≤
          ENNReal.ofReal (C*ρ) := by
  obtain ⟨ρb, hρb, hρb8, hbi⟩ := equalAreaPhiEuclidean24_near_biLipschitz
  obtain ⟨R₀, hR₀, hcap⟩ := sphereArea24_ball_le
  set δ := ρb/12 with hδdef
  have hδ : 0 < δ := by positivity
  have hs24 : Real.sqrt 24 < 5 := by
    rw [show (5:ℝ) = Real.sqrt 25 by
      rw [show (25:ℝ) = 5^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs240 : 0 ≤ Real.sqrt 24 := Real.sqrt_nonneg 24
  have hball : ∀ p : Fin 24 → ℝ, (∀ i, |p i| ≤ 2*δ) →
      (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 24)) ∈
        ball (0 : EuclideanSpace ℝ (Fin 24)) ρb := by
    intro p hp
    rw [mem_ball, dist_zero_right]
    have := toLp24_norm_le_of_abs_le (by positivity) hp
    nlinarith [mul_pos (sub_pos.mpr hs24) hδ]
  have hdom : ∀ p : Fin 24 → ℝ, (∀ i, |p i| ≤ 2*δ) → p ∈ equalAreaChartDomainD := by
    intro p hp
    have h1 := toLp24_norm_le_of_abs_le (by positivity) hp
    have h2 : ‖(WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 24))‖ ≤ 1/8 := by
      nlinarith [mul_pos (sub_pos.mpr hs24) hδ]
    simpa using equalAreaEuclidean24_small_norm_domain (WithLp.toLp 2 p) h2
  have hΦ : ∀ p : Fin 24 → ℝ, equalAreaPhiD p = equalAreaPhiEuclidean24 (WithLp.toLp 2 p) := by
    intro p
    simp [equalAreaPhiEuclidean24]
  have hbi' : ∀ p q : Fin 24 → ℝ, (∀ i, |p i| ≤ 2*δ) → (∀ i, |q i| ≤ 2*δ) →
      dist (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 24)) (WithLp.toLp 2 q) ≤
        2*dist (equalAreaPhiD p) (equalAreaPhiD q) ∧
      dist (equalAreaPhiD p) (equalAreaPhiD q) ≤
        2*dist (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 24)) (WithLp.toLp 2 q) := by
    intro p q hp hq
    rw [hΦ p, hΦ q]
    exact hbi _ (hball p hp) _ (hball q hq)
  refine ⟨δ, hδ, 96*(44:ℝ)^24*(4*δ)^23, by positivity, min δ (R₀/11), lt_min hδ (by positivity),
    hdom, hbi', ?_⟩
  intro g ρ hρ hρ1
  have hρδ : ρ ≤ δ := hρ1.trans (min_le_left _ _)
  have hρR : 11*ρ ≤ R₀ := by have := hρ1.trans (min_le_right _ _); linarith
  set Z := (cubeBdry24_box_finite (δ := δ) hρ).toFinset with hZdef
  -- the number of boundary boxes
  have hcard : (Z.card:ℝ≥0∞)*ENNReal.ofReal (ρ^24) ≤ ENNReal.ofReal (96*ρ*(4*δ)^23) := by
    have hsub : ∀ z ∈ Z, gridBox24 ρ z ⊆ ⋃ (is : Fin 24 × Bool), cubeSlab24 δ ρ is.1 is.2 := by
      intro z hz
      rw [Set.Finite.mem_toFinset] at hz
      obtain ⟨i, s, hi⟩ := gridBox24_subset_slab hz
      exact hi.trans (subset_iUnion_of_subset (i, s) subset_rfl)
    have h1 := gridBox24_card_le hρ Z hsub
    have h2 : (volume : Measure (Fin 24 → ℝ))
        (⋃ (is : Fin 24 × Bool), cubeSlab24 δ ρ is.1 is.2) ≤
        ∑ is : Fin 24 × Bool, (volume : Measure (Fin 24 → ℝ)) (cubeSlab24 δ ρ is.1 is.2) :=
      measure_iUnion_fintype_le _ _
    have h3 : ∑ is : Fin 24 × Bool, (volume : Measure (Fin 24 → ℝ)) (cubeSlab24 δ ρ is.1 is.2) =
        48*(ENNReal.ofReal (2*ρ)*ENNReal.ofReal (2*(δ+ρ))^23) := by
      simp only [cubeSlab24_volume, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
      norm_num
    have h4 : 48*(ENNReal.ofReal (2*ρ)*ENNReal.ofReal (2*(δ+ρ))^23) ≤
        ENNReal.ofReal (96*ρ*(4*δ)^23) := by
      rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
        show (48:ℝ≥0∞) = ENNReal.ofReal 48 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      have h5 : (2*(δ+ρ))^23 ≤ (4*δ)^23 := pow_le_pow_left₀ (by positivity) (by linarith) 23
      have h6 : 0 ≤ 2*ρ := by positivity
      have h7 := mul_le_mul_of_nonneg_left h5 h6
      linarith
    exact h1.trans (h2.trans (h3.le.trans h4))
  -- the covering by caps
  have hpt : ∀ z : Fin 24 → ℤ, z ∈ Z →
      equalAreaPhiD (fun i => ρ*(z i)) ∈ sphere (0 : AmbientD 24) 1 := by
    intro z hz
    rw [Set.Finite.mem_toFinset] at hz
    obtain ⟨w, hwb, hw, _⟩ := hz
    have hc : ∀ i, |ρ*(z i)| ≤ 2*δ := by
      intro i
      have h1 := (hwb i (mem_univ i)).1
      have h2 := (hwb i (mem_univ i)).2
      have hwi := abs_le.mp (hw i)
      rw [abs_le]
      constructor <;> nlinarith
    exact equalAreaPhiD_mem_sphere _ (hdom _ hc).1
  let q : (Fin 24 → ℤ) → SphereD 24 := fun z =>
    if hz : z ∈ Z then ⟨g (equalAreaPhiD (fun i => ρ*(z i))), by
      have := hpt z hz
      simp only [mem_sphere_zero_iff_norm] at this ⊢
      rw [g.norm_map]; exact this⟩
    else northPole24
  have hcover : {x : SphereD 24 | ∃ w ∈ cubeBdry24 δ,
        dist (x : AmbientD 24) (g (equalAreaPhiD w)) ≤ ρ} ⊆
      ⋃ z ∈ Z, {x : SphereD 24 | dist x (q z) < 11*ρ} := by
    intro x hx
    obtain ⟨w, hw, hxw⟩ := hx
    set z := gridIndex24 ρ w with hzdef
    have hwz : w ∈ gridBox24 ρ z := mem_gridBox24_gridIndex24 hρ w
    have hzZ : z ∈ Z := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨w, hwz, hw⟩
    have hcz : (fun i => ρ*(z i)) ∈ gridBox24 ρ z := by
      intro i _
      constructor
      · exact le_rfl
      · nlinarith
    have hwabs : ∀ i, |w i| ≤ 2*δ := fun i => (hw.1 i).trans (by linarith)
    have hcabs : ∀ i, |ρ*(z i)| ≤ 2*δ := by
      intro i
      have h1 := (hwz i (mem_univ i)).1
      have h2 := (hwz i (mem_univ i)).2
      have hwi := abs_le.mp (hw.1 i)
      rw [abs_le]
      constructor <;> nlinarith
    have hd := gridBox24_dist_le hρ hwz hcz
    have hb := (hbi' w (fun i => ρ*(z i)) hwabs hcabs).2
    refine mem_iUnion₂.mpr ⟨z, hzZ, ?_⟩
    simp only [mem_ofPred_eq, q, dite_eq_left hzZ]
    rw [Subtype.dist_eq]
    change dist (x : AmbientD 24) (g (equalAreaPhiD (fun i => ρ*(z i)))) < 11*ρ
    have hrot : dist (g (equalAreaPhiD w)) (g (equalAreaPhiD (fun i => ρ*(z i)))) =
        dist (equalAreaPhiD w) (equalAreaPhiD (fun i => ρ*(z i))) := g.dist_map _ _
    calc dist (x : AmbientD 24) (g (equalAreaPhiD (fun i => ρ*(z i))))
        ≤ dist (x : AmbientD 24) (g (equalAreaPhiD w))+
          dist (g (equalAreaPhiD w)) (g (equalAreaPhiD (fun i => ρ*(z i)))) :=
          dist_triangle _ _ _
      _ ≤ ρ+2*(Real.sqrt 24*ρ) := by rw [hrot]; linarith
      _ < 11*ρ := by nlinarith [mul_pos (sub_pos.mpr hs24) hρ]
  calc (sphereAreaD 24) {x : SphereD 24 | ∃ w ∈ cubeBdry24 δ,
        dist (x : AmbientD 24) (g (equalAreaPhiD w)) ≤ ρ}
      ≤ (sphereAreaD 24) (⋃ z ∈ Z, {x : SphereD 24 | dist x (q z) < 11*ρ}) :=
        measure_mono hcover
    _ ≤ ∑ z ∈ Z, (sphereAreaD 24) {x : SphereD 24 | dist x (q z) < 11*ρ} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _z ∈ Z, ENNReal.ofReal ((4*(11*ρ))^24) :=
        Finset.sum_le_sum fun z _ => hcap (q z) (11*ρ) (by positivity) hρR
    _ = (Z.card:ℝ≥0∞)*ENNReal.ofReal (ρ^24)*ENNReal.ofReal ((44:ℝ)^24) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring
    _ ≤ ENNReal.ofReal (96*ρ*(4*δ)^23)*ENNReal.ofReal ((44:ℝ)^24) := by gcongr
    _ = ENNReal.ofReal (96*(44:ℝ)^24*(4*δ)^23*ρ) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end SphericalRiesz
end
end

section

/-! Rotated chart regions on `S²⁴` (stage NEG, stratification; dimension-24 port of
`SphereChartRegions8`).

`chartImage24 g S` is the image of the coordinate set `S` under the rotated equal-area chart.
For `S` measurable inside the chart domain its area is the Lebesgue volume of `S`; the image of
the closed chart cube is closed, the image of the open cube is open, and the frontier of the
image of the closed cube lies in the image of the cube boundary. By compactness finitely many
rotations of the open cube cover the sphere (`SphereChartPool24`). The dimension-free
topological lemma `isPreconnected_inter_frontier` of `SphereChartRegions8` is not repeated
here. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric Topology
namespace SphericalRiesz

/-- The image of a coordinate set under the rotated equal-area chart. -/
def chartImage24 (g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24) (S : Set (Fin 24 → ℝ)) :
    Set (SphereD 24) :=
  {x | ∃ p ∈ S, (x : AmbientD 24) = g (equalAreaPhiD p)}

theorem chartImage24_eq_preimage (g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24) (S : Set (Fin 24 → ℝ)) :
    chartImage24 g S = (sphereRotationD g.symm) ⁻¹' equalAreaSpherePatchD S := by
  ext x
  simp only [chartImage24, mem_ofPred_eq, mem_preimage, equalAreaSpherePatchD, mem_image]
  constructor
  · rintro ⟨p, hp, hx⟩
    refine ⟨p, hp, ?_⟩
    change equalAreaPhiD p = g.symm (x : AmbientD 24)
    rw [hx, g.symm_apply_apply]
  · rintro ⟨p, hp, hx⟩
    refine ⟨p, hp, ?_⟩
    change equalAreaPhiD p = g.symm (x : AmbientD 24) at hx
    rw [hx, g.apply_symm_apply]

theorem chartImage24_measurable (g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24) {S : Set (Fin 24 → ℝ)}
    (hS : MeasurableSet S) (hsub : S ⊆ equalAreaChartDomainD) :
    MeasurableSet (chartImage24 g S) := by
  rw [chartImage24_eq_preimage]
  exact (equalAreaSpherePatchD_measurable S hS hsub).preimage (sphereRotationD g.symm).measurable

theorem chartImage24_area (g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24) {S : Set (Fin 24 → ℝ)}
    (hS : MeasurableSet S) (hsub : S ⊆ equalAreaChartDomainD) :
    (sphereAreaD 24) (chartImage24 g S) = (volume : Measure (Fin 24 → ℝ)) S := by
  rw [chartImage24_eq_preimage, (sphereAreaD_rotation_preserving g.symm).measure_preimage_emb
    (sphereRotationD g.symm).measurableEmbedding, sphereAreaD_equalAreaSpherePatch S hS hsub]

theorem chartImage24_mono (g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24) {S T : Set (Fin 24 → ℝ)}
    (h : S ⊆ T) : chartImage24 g S ⊆ chartImage24 g T := by
  rintro x ⟨p, hp, hx⟩
  exact ⟨p, h hp, hx⟩

theorem chartImage24_disjoint (g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24) {S T : Set (Fin 24 → ℝ)}
    (hS : S ⊆ equalAreaChartDomainD) (hT : T ⊆ equalAreaChartDomainD) (hST : Disjoint S T) :
    Disjoint (chartImage24 g S) (chartImage24 g T) := by
  rw [Set.disjoint_left]
  rintro x ⟨p, hp, hx⟩ ⟨q, hq, hx'⟩
  have : equalAreaPhiD p = equalAreaPhiD q := g.injective (hx.symm.trans hx')
  have hpq := equalAreaPhiD_injOn (hS hp) (hT hq) this
  subst hpq
  exact Set.disjoint_left.mp hST hp hq

/-- The image of a compact coordinate set is closed. -/
theorem chartImage24_isClosed (g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24) {S : Set (Fin 24 → ℝ)}
    (hS : IsCompact S) : IsClosed (chartImage24 g S) := by
  have hc : IsCompact ((fun p : Fin 24 → ℝ => g (equalAreaPhiD p)) '' S) :=
    hS.image (g.continuous.comp equalAreaPhiD_continuous)
  have he : chartImage24 g S =
      Subtype.val ⁻¹' ((fun p : Fin 24 → ℝ => g (equalAreaPhiD p)) '' S) := by
    ext x
    simp only [chartImage24, mem_ofPred_eq, mem_preimage, mem_image]
    constructor
    · rintro ⟨p, hp, hx⟩; exact ⟨p, hp, hx.symm⟩
    · rintro ⟨p, hp, hx⟩; exact ⟨p, hp, hx.symm⟩
  rw [he]
  exact hc.isClosed.preimage continuous_subtype_val

/-- The image of an open coordinate set inside the chart domain is open. -/
theorem chartImage24_isOpen (g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24) {S : Set (Fin 24 → ℝ)}
    (hS : IsOpen S) (hsub : S ⊆ equalAreaChartDomainD) : IsOpen (chartImage24 g S) := by
  rw [chartImage24_eq_preimage]
  apply IsOpen.preimage (sphereRotationD g.symm).continuous
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨p, hp, hx⟩
  have hx0 : 0 < (x : AmbientD 24) 0 := by
    rw [← hx]
    exact equalAreaPhiD_first_pos p (hsub hp)
  have hcoord : WithLp.ofLp (sphereEqualAreaCoordinates24 x) = p := by
    have h := equalAreaInverseD_phi p (hsub hp)
    rw [hx] at h
    simpa [sphereEqualAreaCoordinates24] using h
  have hca := sphereEqualAreaCoordinates24_continuousAt x hx0
  have hS' : IsOpen ((fun u : EuclideanSpace ℝ (Fin 24) => WithLp.ofLp u) ⁻¹' S) :=
    hS.preimage (PiLp.continuous_ofLp 2 _)
  have hnb : (fun u : EuclideanSpace ℝ (Fin 24) => WithLp.ofLp u) ⁻¹' S ∈
      𝓝 (sphereEqualAreaCoordinates24 x) := by
    apply hS'.mem_nhds
    simp only [mem_preimage]
    rw [hcoord]; exact hp
  have hpos : {y : SphereD 24 | 0 < (y : AmbientD 24) 0} ∈ 𝓝 x :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds hx0
  filter_upwards [hca hnb, hpos] with y hy hy0
  refine ⟨WithLp.ofLp (sphereEqualAreaCoordinates24 y), hy, ?_⟩
  have h := equalAreaPhiD_inverse8 y hy0
  simpa [sphereEqualAreaCoordinates24] using h

end SphericalRiesz
end
end

section

/-! The pool of a chart grid on `S²⁴` lies near the chart-cube boundaries (stage NEG,
stratification; dimension-24 port of `SphereChartPool8`).

With the closed chart cube `C₀ = [-δ,δ]^24`, the open cube `I₀`, finitely many rotations covering
the sphere by `chartImage24 (g k) I₀`, and the first-come regions, a grid box `b` of side `h` in
chart `k` is *good* if `b ⊆ C₀` and its image misses the images of `C₀` in the earlier charts.
Every point outside the good cells lies within `2√24 h` of the image of the cube boundary in some
chart: either its box leaves `C₀` (the segment to an outside point crosses the cube boundary),
or the image of its box meets an earlier chart image without being inside it (a connected set
meeting a closed set and its complement meets its frontier, and the frontier of a chart image of
`C₀` lies in the image of the cube boundary).

The dimension-free topological lemmas `isPreconnected_inter_frontier` and
`frontier_biUnion_closed_subset` are the ones of `SphereChartRegions8` and `SphereChartPool8`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric Topology
namespace SphericalRiesz

/-- The closed and the open chart cube. -/
def chartCube24 (δ : ℝ) : Set (Fin 24 → ℝ) := {p | ∀ i, |p i| ≤ δ}
def chartCubeOpen24 (δ : ℝ) : Set (Fin 24 → ℝ) := {p | ∀ i, |p i| < δ}

theorem chartCube24_eq (δ : ℝ) : chartCube24 δ = Set.pi univ (fun _ => Icc (-δ) δ) := by
  ext p
  simp only [chartCube24, mem_ofPred_eq, mem_pi, mem_univ, true_implies, mem_Icc, abs_le]

theorem chartCubeOpen24_eq (δ : ℝ) : chartCubeOpen24 δ = Set.pi univ (fun _ => Ioo (-δ) δ) := by
  ext p
  simp only [chartCubeOpen24, mem_ofPred_eq, mem_pi, mem_univ, true_implies, mem_Ioo, abs_lt]

theorem chartCube24_isCompact (δ : ℝ) : IsCompact (chartCube24 δ) := by
  rw [chartCube24_eq]
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

theorem chartCube24_measurable (δ : ℝ) : MeasurableSet (chartCube24 δ) := by
  rw [chartCube24_eq]
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

theorem chartCubeOpen24_isOpen (δ : ℝ) : IsOpen (chartCubeOpen24 δ) := by
  rw [chartCubeOpen24_eq]
  exact isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)

theorem chartCubeOpen24_subset (δ : ℝ) : chartCubeOpen24 δ ⊆ chartCube24 δ :=
  fun _ hp i => (hp i).le

theorem chartCube24_sdiff_open (δ : ℝ) : chartCube24 δ \ chartCubeOpen24 δ ⊆ cubeBdry24 δ := by
  rintro p ⟨hp, hpo⟩
  refine ⟨hp, ?_⟩
  by_contra hne
  simp only [not_exists] at hne
  exact hpo (fun i => lt_of_le_of_ne (hp i) (hne i))

theorem chartCube24_frontier (δ : ℝ) : frontier (chartCube24 δ) ⊆ cubeBdry24 δ := by
  intro p hp
  have hcl : IsClosed (chartCube24 δ) := (chartCube24_isCompact δ).isClosed
  rw [frontier, hcl.closure_eq] at hp
  refine chartCube24_sdiff_open δ ⟨hp.1, fun ho => hp.2 ?_⟩
  exact interior_maximal (chartCubeOpen24_subset δ) (chartCubeOpen24_isOpen δ) ho

/-- The frontier of the chart image of the closed cube lies in the image of its boundary. -/
theorem chartImage24_frontier (g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24) {δ : ℝ}
    (hdom : chartCube24 δ ⊆ equalAreaChartDomainD) :
    frontier (chartImage24 g (chartCube24 δ)) ⊆ chartImage24 g (cubeBdry24 δ) := by
  intro x hx
  have hcl := chartImage24_isClosed g (chartCube24_isCompact δ)
  rw [frontier, hcl.closure_eq] at hx
  obtain ⟨⟨p, hp, hxp⟩, hxi⟩ := hx
  have hopen := chartImage24_isOpen g (chartCubeOpen24_isOpen δ)
    ((chartCubeOpen24_subset δ).trans hdom)
  have hsub : chartImage24 g (chartCubeOpen24 δ) ⊆ interior (chartImage24 g (chartCube24 δ)) :=
    interior_maximal (chartImage24_mono g (chartCubeOpen24_subset δ)) hopen
  have hpo : p ∉ chartCubeOpen24 δ := fun hpo => hxi (hsub ⟨p, hpo, hxp⟩)
  exact ⟨p, chartCube24_sdiff_open δ ⟨hp, hpo⟩, hxp⟩

/-- Finitely many rotated open chart cubes cover the sphere. -/
theorem sphere24_finite_chart_cover {δ : ℝ} (hδ : 0 < δ)
    (hdom : chartCube24 δ ⊆ equalAreaChartDomainD) :
    ∃ K : ℕ, ∃ g : Fin K → AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24,
      ∀ x : SphereD 24, ∃ k, x ∈ chartImage24 (g k) (chartCubeOpen24 δ) := by
  classical
  let : CompactSpace (SphereD 24) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : AmbientD 24) 1)
  have ht : ∀ p : SphereD 24, ∃ g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24,
      sphereRotationD g northPole24 = p :=
    fun p => sphereRotation24_transitive northPole24 p
  choose g hg using ht
  let U : SphereD 24 → Set (SphereD 24) := fun p => chartImage24 (g p) (chartCubeOpen24 δ)
  have hU : ∀ p, IsOpen (U p) := fun p =>
    chartImage24_isOpen (g p) (chartCubeOpen24_isOpen δ) ((chartCubeOpen24_subset δ).trans hdom)
  have hcenter : ∀ p, p ∈ U p := by
    intro p
    refine ⟨0, fun i => by simpa using hδ, ?_⟩
    have h1 : (p : AmbientD 24) = (sphereRotationD (g p) northPole24 : AmbientD 24) := by
      rw [hg p]
    rw [h1]
    change (g p) (northPole24 : AmbientD 24) = (g p) (equalAreaPhiD (0 : Fin 24 → ℝ))
    congr 1
    have h0 := equalAreaPhiEuclidean24_zero
    simp only [equalAreaPhiEuclidean24] at h0
    rw [← h0]
    simp
  obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (univ : Set (SphereD 24))).elim_finite_subcover
    U hU (fun p _ => mem_iUnion.mpr ⟨p, hcenter p⟩)
  refine ⟨t.card, fun i => g (t.equivFin.symm i).val, ?_⟩
  intro x
  obtain ⟨p, hp⟩ := mem_iUnion.mp (ht (mem_univ x))
  obtain ⟨hpt, hxp⟩ := mem_iUnion.mp hp
  refine ⟨t.equivFin ⟨p, hpt⟩, ?_⟩
  simpa only [Equiv.symm_apply_apply] using hxp

/-- Chart images of convex coordinate sets are preconnected. -/
theorem chartImage24_isPreconnected (g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24) {S : Set (Fin 24 → ℝ)}
    (hS : Convex ℝ S) (hsub : S ⊆ equalAreaChartDomainD) :
    IsPreconnected (chartImage24 g S) := by
  have himg : Subtype.val '' chartImage24 g S =
      (fun p : Fin 24 → ℝ => g (equalAreaPhiD p)) '' S := by
    ext y
    simp only [chartImage24, mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨x, ⟨p, hp, hxp⟩, rfl⟩
      exact ⟨p, hp, hxp.symm⟩
    · rintro ⟨p, hp, rfl⟩
      have hm : g (equalAreaPhiD p) ∈ sphere (0 : AmbientD 24) 1 := by
        rw [mem_sphere_zero_iff_norm, g.norm_map]
        have := equalAreaPhiD_mem_sphere p (hsub hp).1
        rwa [mem_sphere_zero_iff_norm] at this
      exact ⟨⟨g (equalAreaPhiD p), hm⟩, ⟨p, hp, rfl⟩, rfl⟩
  rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, himg]
  exact hS.isPreconnected.image _ (g.continuous.comp equalAreaPhiD_continuous).continuousOn

theorem gridBox24_convex (h : ℝ) (z : Fin 24 → ℤ) : Convex ℝ (gridBox24 h z) :=
  convex_pi (fun _ _ => convex_Ico _ _)

/-- Points outside the good cells lie near the image of a chart-cube boundary. -/
theorem chart_pool_near_boundary24 {δ h : ℝ} (hδ : 0 < δ) (hh : 0 < h)
    (hdom2 : ∀ p : Fin 24 → ℝ, (∀ i, |p i| ≤ 2*δ) → p ∈ equalAreaChartDomainD)
    (hbi : ∀ p q : Fin 24 → ℝ, (∀ i, |p i| ≤ 2*δ) → (∀ i, |q i| ≤ 2*δ) →
      dist (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 24)) (WithLp.toLp 2 q) ≤
        2*dist (equalAreaPhiD p) (equalAreaPhiD q) ∧
      dist (equalAreaPhiD p) (equalAreaPhiD q) ≤
        2*dist (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 24)) (WithLp.toLp 2 q))
    {K : ℕ} (g : Fin K → AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24)
    (hcover : ∀ x : SphereD 24, ∃ k, x ∈ chartImage24 (g k) (chartCubeOpen24 δ))
    (x : SphereD 24)
    (hx : ∀ k : Fin K, ∀ z : Fin 24 → ℤ, gridBox24 h z ⊆ chartCube24 δ →
      Disjoint (chartImage24 (g k) (gridBox24 h z))
        (⋃ j ∈ Finset.univ.filter (fun j : Fin K => j < k), chartImage24 (g j) (chartCube24 δ)) →
      x ∉ chartImage24 (g k) (gridBox24 h z)) :
    ∃ k : Fin K, ∃ w ∈ cubeBdry24 δ,
      dist (x : AmbientD 24) (g k (equalAreaPhiD w)) ≤ 2*(Real.sqrt 24*h) := by
  classical
  have hC2 : ∀ p ∈ chartCube24 δ, ∀ i, |p i| ≤ 2*δ := fun p hp i => (hp i).trans (by linarith)
  have hCdom : chartCube24 δ ⊆ equalAreaChartDomainD := fun p hp => hdom2 p (hC2 p hp)
  -- the first chart containing x
  set Sx := Finset.univ.filter (fun k : Fin K => x ∈ chartImage24 (g k) (chartCube24 δ)) with hSx
  have hSne : Sx.Nonempty := by
    obtain ⟨k, hk⟩ := hcover x
    exact ⟨k, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, chartImage24_mono (g k) (chartCubeOpen24_subset δ) hk⟩⟩
  set k₀ := Sx.min' hSne with hk₀
  have hk₀S : k₀ ∈ Sx := Finset.min'_mem Sx hSne
  have hxk₀ : x ∈ chartImage24 (g k₀) (chartCube24 δ) := (Finset.mem_filter.mp hk₀S).2
  have hxF : x ∉ ⋃ j ∈ Finset.univ.filter (fun j : Fin K => j < k₀),
      chartImage24 (g j) (chartCube24 δ) := by
    intro hxF
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxF
    have hjS : j ∈ Sx := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxj⟩
    have := Finset.min'_le Sx j hjS
    have hjlt := (Finset.mem_filter.mp hj).2
    rw [← hk₀] at this
    exact absurd hjlt (not_lt.mpr this)
  obtain ⟨p, hp, hxp⟩ := hxk₀
  set z := gridIndex24 h p with hzdef
  have hpb : p ∈ gridBox24 h z := mem_gridBox24_gridIndex24 hh p
  have hdist : ∀ k : Fin K, ∀ q r : Fin 24 → ℝ, q ∈ gridBox24 h z → r ∈ gridBox24 h z →
      (∀ i, |q i| ≤ 2*δ) → (∀ i, |r i| ≤ 2*δ) →
      dist (g k (equalAreaPhiD q)) (g k (equalAreaPhiD r)) ≤ 2*(Real.sqrt 24*h) := by
    intro k q r hq hr hq2 hr2
    rw [(g k).dist_map]
    have h1 := (hbi q r hq2 hr2).2
    have h2 := gridBox24_dist_le hh hq hr
    linarith
  by_cases hb : gridBox24 h z ⊆ chartCube24 δ
  · -- the box image meets an earlier chart image: it crosses that image's frontier
    have hnd : ¬Disjoint (chartImage24 (g k₀) (gridBox24 h z))
        (⋃ j ∈ Finset.univ.filter (fun j : Fin K => j < k₀),
          chartImage24 (g j) (chartCube24 δ)) :=
      fun hd => hx k₀ z hb hd ⟨p, hpb, hxp⟩
    rw [Set.not_disjoint_iff] at hnd
    obtain ⟨y, hyY, hyF⟩ := hnd
    have hpre := chartImage24_isPreconnected (g k₀) (gridBox24_convex h z) (hb.trans hCdom)
    obtain ⟨y', hy'Y, hy'f⟩ := isPreconnected_inter_frontier hpre ⟨y, hyY, hyF⟩
      ⟨x, ⟨p, hpb, hxp⟩, hxF⟩
    have hfr := frontier_biUnion_closed_subset (Finset.univ.filter (fun j : Fin K => j < k₀))
      (fun j => chartImage24 (g j) (chartCube24 δ))
      (fun j _ => chartImage24_isClosed (g j) (chartCube24_isCompact δ)) hy'f
    obtain ⟨j, _, hj⟩ := mem_iUnion₂.mp hfr
    obtain ⟨w, hw, hyw⟩ := chartImage24_frontier (g j) hCdom hj
    obtain ⟨p', hp', hyp'⟩ := hy'Y
    refine ⟨j, w, hw, ?_⟩
    rw [hxp, ← hyw, hyp']
    exact hdist k₀ p p' hpb hp' (hC2 p hp) (hC2 p' (hb hp'))
  · -- the box leaves the cube: the segment to an outside point crosses the cube boundary
    rw [Set.not_subset] at hb
    obtain ⟨q, hqb, hqC⟩ := hb
    have hseg : segment ℝ p q ⊆ gridBox24 h z := (gridBox24_convex h z).segment_subset hpb hqb
    obtain ⟨w, hwseg, hwf⟩ := isPreconnected_inter_frontier (convex_segment p q).isPreconnected
      ⟨p, left_mem_segment ℝ p q, hp⟩ ⟨q, right_mem_segment ℝ p q, hqC⟩
    have hw := chartCube24_frontier δ hwf
    refine ⟨k₀, w, hw, ?_⟩
    rw [hxp]
    exact hdist k₀ p w hpb (hseg hwseg) (hC2 p hp) (fun i => (hw.1 i).trans (by linarith))

end SphericalRiesz
end
end

section

/-! Exact-mass stratification of the whole sphere `S²⁴` at every scale (stage NEG; dimension-24
port of `SphereStratification8`).

For `r` points take chart grid boxes of side `h`, `h^24 = A/r` (`A` the area of `S²⁴`), so that
their rotated equal-area images have probability exactly `1/r`. Good cells (box inside the chart
cube, image missing the earlier charts) are pairwise disjoint with diameter at most `2√24 h`; at
most `r - 1` of them are kept. The rest of the sphere (the pool) lies within `2√24 h` of the chart
images of the cube boundaries, so it has probability at most `K C 2√24 h/A + 1/r`; it is split by
the pool partition at scale `√h` into exact-mass cells of diameter at most `5√h`. With
`c_r h² = π` (`c_r = π (r/A)^(1/12)`) this gives `Σ_j c_r d_j² ≤ B r` for an absolute `B`
(`SphereStratifiable24`). -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal
namespace SphericalRiesz

/-- Exact-mass stratifications of the whole sphere `S²⁴` at every scale: `r` cells of mass `1/r`
with `Σ_j c_r d_j² ≤ B r` (cells at the density scale `r^(-1/24)`). -/
def SphereStratifiable24 (B : ℝ) : Prop :=
  ∀ r : ℕ, 0 < r → ∃ C : Fin r → Set (SphereD 24), ∃ dm : Fin r → ℝ,
    (∀ j, MeasurableSet (C j)) ∧ Pairwise (fun i j => Disjoint (C i) (C j)) ∧
    (⋃ j, C j) = univ ∧
    (∀ j, sphereProbabilityD 24 (C j) = sphereProbabilityD 24 univ/(r:ℝ≥0∞)) ∧
    (∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y ≤ dm j) ∧
    ∑ j, sphereGaussianDensityFactor24 r*(dm j)^2 ≤ B*r

theorem gridBox24_inside_cube_finite {δ h : ℝ} (hh : 0 < h) :
    {z : Fin 24 → ℤ | gridBox24 h z ⊆ chartCube24 δ}.Finite := by
  set K : ℤ := ⌈|δ|/h⌉ with hK
  apply (Set.finite_Icc (fun _ : Fin 24 => -K) (fun _ => K)).subset
  intro z hz
  have hc : (fun i => h*(z i)) ∈ gridBox24 h z := by
    intro i _
    constructor
    · exact le_rfl
    · nlinarith
  have hcube := hz hc
  have hb : ∀ i, -K ≤ z i ∧ z i ≤ K := by
    intro i
    have hi := abs_le.mp ((hcube i).trans (le_abs_self δ))
    simp only at hi
    have hceil := Int.le_ceil (|δ|/h)
    have h1 : (z i:ℝ) ≤ |δ|/h := by rw [le_div_iff₀ hh]; linarith
    have h2 : -(|δ|/h) ≤ (z i:ℝ) := by
      rw [neg_le, le_div_iff₀ hh]
      linarith
    have hu : (z i:ℝ) ≤ (K:ℝ) := by rw [hK]; linarith
    have hl : (-(K:ℝ)) ≤ (z i:ℝ) := by rw [hK]; linarith
    exact ⟨by exact_mod_cast hl, by exact_mod_cast hu⟩
  exact ⟨fun i => (hb i).1, fun i => (hb i).2⟩

theorem sphereProbability24_real_eq_area (s : Set (SphereD 24)) :
    (sphereProbabilityD 24).real s = (sphereAreaD 24).real s/(sphereAreaD 24).real univ := by
  simp only [Measure.real, sphereProbabilityD, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  ring


/-- The chart partition of the whole sphere into `r` exact-mass cells, for small `h`. -/
theorem sphere24_chart_partition_large {δ C ρ₁ : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hdom2 : ∀ p : Fin 24 → ℝ, (∀ i, |p i| ≤ 2*δ) → p ∈ equalAreaChartDomainD)
    (hbi : ∀ p q : Fin 24 → ℝ, (∀ i, |p i| ≤ 2*δ) → (∀ i, |q i| ≤ 2*δ) →
      dist (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 24)) (WithLp.toLp 2 q) ≤
        2*dist (equalAreaPhiD p) (equalAreaPhiD q) ∧
      dist (equalAreaPhiD p) (equalAreaPhiD q) ≤
        2*dist (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 24)) (WithLp.toLp 2 q))
    (hmink : ∀ g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24, ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₁ →
      (sphereAreaD 24) {x : SphereD 24 | ∃ w ∈ cubeBdry24 δ, dist (x : AmbientD 24) (g (equalAreaPhiD w)) ≤ ρ} ≤
        ENNReal.ofReal (C*ρ))
    {K : ℕ} (g : Fin K → AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24)
    (hcover : ∀ x : SphereD 24, ∃ k, x ∈ chartImage24 (g k) (chartCubeOpen24 δ))
    {r : ℕ} (hr : 0 < r) {h : ℝ} (hh : 0 < h)
    (hh24 : h^24 = (sphereAreaD 24).real univ/r) (hρ : 2*(Real.sqrt 24*h) ≤ ρ₁) :
    ∃ Cl : Fin r → Set (SphereD 24), ∃ dm : Fin r → ℝ,
      (∀ j, MeasurableSet (Cl j)) ∧ Pairwise (fun i j => Disjoint (Cl i) (Cl j)) ∧
      (⋃ j, Cl j) = univ ∧ (∀ j, (sphereProbabilityD 24).real (Cl j) = 1/r) ∧
      (∀ j, ∀ x ∈ Cl j, ∀ y ∈ Cl j, dist x y ≤ dm j) ∧
      ∑ j, (dm j)^2 ≤ 96*h^2*r+
        25*h*(r*(K*(C*(2*(Real.sqrt 24*h))))/(sphereAreaD 24).real univ+1)+
        4*(2*⌈1/Real.sqrt h⌉₊+1)^25 := by
  classical
  set A := (sphereAreaD 24).real univ with hAdef
  have hA : 0 < A := sphereAreaD_univ_pos 24
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hC2 : ∀ p ∈ chartCube24 δ, ∀ i, |p i| ≤ 2*δ := fun p hp i => (hp i).trans (by linarith)
  have hCdom : chartCube24 δ ⊆ equalAreaChartDomainD := fun p hp => hdom2 p (hC2 p hp)
  set Zall := (gridBox24_inside_cube_finite (δ := δ) hh).toFinset with hZall
  have hZmem : ∀ z, z ∈ Zall ↔ gridBox24 h z ⊆ chartCube24 δ := fun z => by
    rw [hZall, Set.Finite.mem_toFinset]; rfl
  let earlier : Fin K → Set (SphereD 24) := fun k =>
    ⋃ j ∈ Finset.univ.filter (fun j : Fin K => j < k), chartImage24 (g j) (chartCube24 δ)
  let cell : Fin K × (Fin 24 → ℤ) → Set (SphereD 24) := fun q => chartImage24 (g q.1) (gridBox24 h q.2)
  set G₀ := (Finset.univ ×ˢ Zall).filter (fun q => Disjoint (cell q) (earlier q.1)) with hG₀
  have hG₀box : ∀ q ∈ G₀, gridBox24 h q.2 ⊆ chartCube24 δ := by
    intro q hq
    rw [hG₀, Finset.mem_filter, Finset.mem_product] at hq
    exact (hZmem q.2).mp hq.1.2
  have hG₀good : ∀ q ∈ G₀, Disjoint (cell q) (earlier q.1) := by
    intro q hq
    rw [hG₀, Finset.mem_filter] at hq
    exact hq.2
  -- the good cells
  have hcm : ∀ q ∈ G₀, MeasurableSet (cell q) := fun q hq =>
    chartImage24_measurable (g q.1) (gridBox24_measurable h q.2) ((hG₀box q hq).trans hCdom)
  have hcprob : ∀ q ∈ G₀, (sphereProbabilityD 24).real (cell q) = 1/r := by
    intro q hq
    rw [sphereProbability24_real_eq_area, Measure.real, chartImage24_area (g q.1)
      (gridBox24_measurable h q.2) ((hG₀box q hq).trans hCdom), gridBox24_volume hh,
      ENNReal.toReal_ofReal (by positivity), hh24, ← hAdef]
    field_simp
  have hcdisj : Set.PairwiseDisjoint (↑G₀) cell := by
    intro q hq q' hq' hne
    show Disjoint (cell q) (cell q')
    by_cases hk : q.1 = q'.1
    · have hz : q.2 ≠ q'.2 := fun hz => hne (Prod.ext hk hz)
      show Disjoint (chartImage24 (g q.1) (gridBox24 h q.2)) (chartImage24 (g q'.1) (gridBox24 h q'.2))
      rw [← hk]
      exact chartImage24_disjoint (g q.1) ((hG₀box q hq).trans hCdom)
        ((hG₀box q' hq').trans hCdom) (gridBox24_disjoint hh hz)
    · rcases lt_or_gt_of_ne hk with hlt | hlt
      · -- cell q lies in the earlier charts of q'
        have hsub : cell q ⊆ earlier q'.1 := by
          intro x hx
          refine mem_iUnion₂.mpr ⟨q.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, ?_⟩
          exact chartImage24_mono (g q.1) (hG₀box q hq) hx
        exact (hG₀good q' hq').symm.mono_left hsub
      · have hsub : cell q' ⊆ earlier q.1 := by
          intro x hx
          refine mem_iUnion₂.mpr ⟨q'.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, ?_⟩
          exact chartImage24_mono (g q'.1) (hG₀box q' hq') hx
        exact (hG₀good q hq).mono_right hsub
  have hcdiam : ∀ q ∈ G₀, ∀ x ∈ cell q, ∀ y ∈ cell q, dist x y ≤ 2*(Real.sqrt 24*h) := by
    intro q hq x hx y hy
    obtain ⟨p, hp, hxp⟩ := hx
    obtain ⟨p', hp', hyp'⟩ := hy
    rw [Subtype.dist_eq, hxp, hyp', (g q.1).dist_map]
    have h1 := (hbi p p' (hC2 p (hG₀box q hq hp)) (hC2 p' (hG₀box q hq hp'))).2
    have h2 := gridBox24_dist_le hh hp hp'
    linarith
  -- at most r good cells
  have hcard₀ : G₀.card ≤ r := by
    have hm := measureReal_biUnion_finset hcdisj hcm (μ := (sphereProbabilityD 24))
    have hle : (sphereProbabilityD 24).real (⋃ q ∈ G₀, cell q) ≤ 1 := measureReal_le_one
    rw [hm, Finset.sum_congr rfl hcprob, Finset.sum_const, nsmul_eq_mul] at hle
    have : (G₀.card:ℝ) ≤ r := by
      rw [mul_one_div, div_le_one hrR] at hle
      exact hle
    exact_mod_cast this
  obtain ⟨G, hGsub, hGcard⟩ := Finset.exists_subset_card_eq (s := G₀) (n := min G₀.card (r-1))
    (min_le_left _ _)
  set n := r-G.card with hndef
  have hGr : G.card ≤ r-1 := hGcard ▸ min_le_right _ _
  have hn : 0 < n := by omega
  -- the pool
  set P := (⋃ q ∈ G, cell q)ᶜ with hPdef
  have hGm : MeasurableSet (⋃ q ∈ G, cell q) :=
    Finset.measurableSet_biUnion G (fun q hq => hcm q (hGsub hq))
  have hPm : MeasurableSet P := hGm.compl
  have hGdisj : Set.PairwiseDisjoint (↑G) cell := hcdisj.subset (by exact_mod_cast hGsub)
  have hPprob : (sphereProbabilityD 24).real P = n/r := by
    rw [hPdef, measureReal_compl hGm, probReal_univ,
      measureReal_biUnion_finset hGdisj (fun q hq => hcm q (hGsub hq)),
      Finset.sum_congr rfl (fun q hq => hcprob q (hGsub hq)), Finset.sum_const, nsmul_eq_mul]
    have : ((r-G.card : ℕ):ℝ) = (r:ℝ)-G.card := by
      rw [Nat.cast_sub (by omega)]
    rw [hndef, this]
    field_simp
  -- the pool lies near the chart cube boundaries
  set N₀ := ⋃ k : Fin K, {x : SphereD 24 | ∃ w ∈ cubeBdry24 δ,
    dist (x : AmbientD 24) (g k (equalAreaPhiD w)) ≤ 2*(Real.sqrt 24*h)} with hN₀
  have hP₀ : (⋃ q ∈ G₀, cell q)ᶜ ⊆ N₀ := by
    intro x hx
    rw [mem_compl_iff] at hx
    obtain ⟨k, w, hw, hd⟩ := chart_pool_near_boundary24 hδ hh hdom2 hbi g hcover x
      (fun k z hz hdisj hxk => hx (mem_iUnion₂.mpr ⟨(k, z), by
        rw [hG₀, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨Finset.mem_univ _, (hZmem z).mpr hz⟩, hdisj⟩, hxk⟩))
    exact mem_iUnion.mpr ⟨k, w, hw, hd⟩
  have hN₀area : (sphereAreaD 24) N₀ ≤ ENNReal.ofReal (K*(C*(2*(Real.sqrt 24*h)))) := by
    calc (sphereAreaD 24) N₀ ≤ ∑ k : Fin K, (sphereAreaD 24) {x : SphereD 24 | ∃ w ∈ cubeBdry24 δ,
          dist (x : AmbientD 24) (g k (equalAreaPhiD w)) ≤ 2*(Real.sqrt 24*h)} := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _k : Fin K, ENNReal.ofReal (C*(2*(Real.sqrt 24*h))) :=
          Finset.sum_le_sum fun k _ => hmink (g k) _ (by positivity) hρ
      _ = ENNReal.ofReal (K*(C*(2*(Real.sqrt 24*h)))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  -- the pool probability
  have hPbound : (sphereProbabilityD 24).real P ≤ K*(C*(2*(Real.sqrt 24*h)))/A+1/r := by
    have hsub : P ⊆ (⋃ q ∈ G₀, cell q)ᶜ ∪ ⋃ q ∈ G₀ \ G, cell q := by
      intro x hx
      by_cases hx0 : x ∈ ⋃ q ∈ G₀, cell q
      · right
        obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp hx0
        refine mem_iUnion₂.mpr ⟨q, Finset.mem_sdiff.mpr ⟨hq, fun hqG => hx ?_⟩, hxq⟩
        exact mem_iUnion₂.mpr ⟨q, hqG, hxq⟩
      · left; exact hx0
    have hdiff : (G₀ \ G).card ≤ 1 := by
      rw [Finset.card_sdiff_of_subset hGsub, hGcard]
      omega
    have h1 : (sphereProbabilityD 24).real P ≤ (sphereProbabilityD 24).real ((⋃ q ∈ G₀, cell q)ᶜ)+
        (sphereProbabilityD 24).real (⋃ q ∈ G₀ \ G, cell q) :=
      (measureReal_mono hsub).trans (measureReal_union_le _ _)
    have h2 : (sphereProbabilityD 24).real ((⋃ q ∈ G₀, cell q)ᶜ) ≤ K*(C*(2*(Real.sqrt 24*h)))/A := by
      rw [sphereProbability24_real_eq_area, ← hAdef]
      apply div_le_div_of_nonneg_right _ hA.le
      have hm := (measure_mono (μ := (sphereAreaD 24)) hP₀).trans hN₀area
      calc (sphereAreaD 24).real ((⋃ q ∈ G₀, cell q)ᶜ) ≤ (ENNReal.ofReal (K*(C*(2*(Real.sqrt 24*h))))).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
        _ = K*(C*(2*(Real.sqrt 24*h))) := ENNReal.toReal_ofReal (by positivity)
    have h3 : (sphereProbabilityD 24).real (⋃ q ∈ G₀ \ G, cell q) ≤ 1/r := by
      have hdj : Set.PairwiseDisjoint (↑(G₀ \ G)) cell :=
        hcdisj.subset (by exact_mod_cast Finset.sdiff_subset)
      rw [measureReal_biUnion_finset hdj (fun q hq => hcm q (Finset.mem_sdiff.mp hq).1),
        Finset.sum_congr rfl (fun q hq => hcprob q (Finset.mem_sdiff.mp hq).1),
        Finset.sum_const, nsmul_eq_mul]
      have : ((G₀ \ G).card:ℝ) ≤ 1 := by exact_mod_cast hdiff
      have h0 : (0:ℝ) ≤ 1/r := by positivity
      nlinarith
    linarith
  have hnbound : (n:ℝ) ≤ r*(K*(C*(2*(Real.sqrt 24*h))))/A+1 := by
    have h1 : (n:ℝ)/r ≤ K*(C*(2*(Real.sqrt 24*h)))/A+1/r := hPprob ▸ hPbound
    rw [div_le_iff₀ hrR] at h1
    have : (K*(C*(2*(Real.sqrt 24*h)))/A+1/r)*r = r*(K*(C*(2*(Real.sqrt 24*h))))/A+1 := by
      field_simp
    linarith
  -- split the pool
  have hsh : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  obtain ⟨PC, dmP, hPCm, hPCd, hPCu, hPCmass, hPCdiam, hPCsum⟩ :=
    sphere24_pool_partition hPm hsh hn
  -- assemble
  have hcardG : Fintype.card (↥G ⊕ Fin n) = r := by
    rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin, hndef]
    omega
  let e := Fintype.equivFinOfCardEq hcardG
  let Cl : Fin r → Set (SphereD 24) := fun j => Sum.elim (fun q : ↥G => cell q.1) PC (e.symm j)
  let dm : Fin r → ℝ := fun j => Sum.elim (fun _ : ↥G => 2*(Real.sqrt 24*h)) dmP (e.symm j)
  have hPCsub : ∀ i, PC i ⊆ P := fun i x hx => hPCu ▸ mem_iUnion.mpr ⟨i, hx⟩
  refine ⟨Cl, dm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    simp only [Cl]
    cases e.symm j with
    | inl q => exact hcm q.1 (hGsub q.2)
    | inr i => exact hPCm i
  · intro i j hij
    simp only [Cl]
    have hne : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
    revert hne
    cases e.symm i with
    | inl q =>
      cases e.symm j with
      | inl q' =>
        intro hne
        have hqq : q.1 ≠ q'.1 := fun h => hne (by rw [Subtype.ext h])
        exact hGdisj q.2 q'.2 hqq
      | inr i' =>
        intro _
        apply Disjoint.mono_right (hPCsub i')
        rw [hPdef]
        exact disjoint_compl_right.mono_left (subset_biUnion_of_mem (u := cell) q.2)
    | inr i' =>
      cases e.symm j with
      | inl q =>
        intro _
        apply Disjoint.mono_left (hPCsub i')
        rw [hPdef]
        exact disjoint_compl_left.mono_right (subset_biUnion_of_mem (u := cell) q.2)
      | inr j' =>
        intro hne
        have : i' ≠ j' := fun h => hne (by rw [h])
        exact hPCd this
  · apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ ⋃ q ∈ G, cell q
    · obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp hx
      refine mem_iUnion.mpr ⟨e (Sum.inl ⟨q, hq⟩), ?_⟩
      simp only [Cl, Equiv.symm_apply_apply, Sum.elim_inl]
      exact hxq
    · have hxP : x ∈ P := hx
      rw [← hPCu] at hxP
      obtain ⟨i, hi⟩ := mem_iUnion.mp hxP
      refine mem_iUnion.mpr ⟨e (Sum.inr i), ?_⟩
      simp only [Cl, Equiv.symm_apply_apply, Sum.elim_inr]
      exact hi
  · intro j
    simp only [Cl]
    cases e.symm j with
    | inl q => exact hcprob q.1 (hGsub q.2)
    | inr i =>
      simp only [Sum.elim_inr]
      rw [hPCmass i, hPprob]
      field_simp
  · intro j x hx y hy
    simp only [Cl, dm] at hx hy ⊢
    cases hj : e.symm j with
    | inl q =>
      rw [hj] at hx hy
      exact hcdiam q.1 (hGsub q.2) x hx y hy
    | inr i =>
      rw [hj] at hx hy
      exact hPCdiam i x hx y hy
  · have hsum : ∑ j, (dm j)^2 = ∑ u : ↥G ⊕ Fin n,
        (Sum.elim (fun _ : ↥G => 2*(Real.sqrt 24*h)) dmP u)^2 := by
      rw [← e.symm.sum_comp]
    rw [hsum, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
      nsmul_eq_mul]
    have hs24 : Real.sqrt 24^2 = 24 := Real.sq_sqrt (by norm_num)
    have hgood : (G.card:ℝ)*(2*(Real.sqrt 24*h))^2 ≤ 96*h^2*r := by
      have : (G.card:ℝ) ≤ r := by exact_mod_cast (hGr.trans (Nat.sub_le r 1))
      have e1 : (2*(Real.sqrt 24*h))^2 = 96*h^2 := by rw [mul_pow, mul_pow, hs24]; ring
      rw [e1]
      have h96 : (0:ℝ) ≤ 96*h^2 := by positivity
      calc (G.card:ℝ)*(96*h^2) ≤ r*(96*h^2) := mul_le_mul_of_nonneg_right this h96
        _ = 96*h^2*r := by ring
    have hpool : ∑ i, (dmP i)^2 ≤ 25*h*(r*(K*(C*(2*(Real.sqrt 24*h))))/A+1)+
        4*(2*⌈1/Real.sqrt h⌉₊+1)^25 := by
      have h1 := hPCsum
      have e2 : (n:ℝ)*(5*Real.sqrt h)^2 = 25*h*n := by
        rw [mul_pow, Real.sq_sqrt hh.le]; ring
      rw [e2] at h1
      have h3 : 25*h*(n:ℝ) ≤ 25*h*(r*(K*(C*(2*(Real.sqrt 24*h))))/A+1) :=
        mul_le_mul_of_nonneg_left hnbound (by positivity)
      linarith
    linarith


theorem sphereProbability24_eq_inv_of_real {s : Set (SphereD 24)} {r : ℕ} (hr : 0 < r)
    (hs : (sphereProbabilityD 24).real s = 1/r) :
    (sphereProbabilityD 24) s = (sphereProbabilityD 24) univ/(r:ℝ≥0∞) := by
  rw [measure_univ, ← ofReal_measureReal (measure_ne_top _ _), hs, one_div, one_div,
    ENNReal.ofReal_inv_of_pos (by exact_mod_cast hr), ENNReal.ofReal_natCast]

/-- The twelfth power of the density factor: `c_N^12 = π^12 N/A`. -/
theorem sphereGaussianDensityFactor24_pow_twelve {N : ℕ} (hN : 0 < N) :
    (sphereGaussianDensityFactor24 N)^12 = Real.pi^12*((N:ℝ)/(sphereAreaD 24).real univ) := by
  unfold sphereGaussianDensityFactor24
  rw [sphereGaussianScale24_pow_twelve hN]
  ring

theorem sphereGaussianDensityFactor24_mul_sq {r : ℕ} (hr : 0 < r) {h : ℝ} (hh : 0 < h)
    (hh24 : h^24 = (sphereAreaD 24).real univ/r) :
    sphereGaussianDensityFactor24 r*h^2 = Real.pi := by
  have hc0 := sphereGaussianDensityFactor24_pos hr
  have h12 := sphereGaussianDensityFactor24_pow_twelve hr
  have hA : 0 < (sphereAreaD 24).real univ := sphereAreaD_univ_pos 24
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hpow : (sphereGaussianDensityFactor24 r*h^2)^12 = Real.pi^12 := by
    rw [mul_pow, h12, ← pow_mul, show 2*12 = 24 by norm_num, hh24]
    field_simp
  exact (pow_left_inj₀ (by positivity) Real.pi_pos.le (by norm_num)).mp hpow

/-- The scale arithmetic of the chart construction: with `c h² = π` and `h^24 = A/r` the bound
`96h²r + 25h(rQh/A + 1) + 4(2⌈1/√h⌉+1)^25` on `Σ d_j²` becomes `O(r)` after multiplying by `c`. -/
theorem stratification_large_arith24 {A Q c h r S : ℝ} (hA : 0 < A) (hh : 0 < h) (hh1 : h ≤ 1)
    (hr : 0 < r) (hh24 : h^24 = A/r) (hch : c*h^2 = Real.pi)
    (hS : S ≤ 96*h^2*r+25*h*(r*(Q*h)/A+1)+4*(2*(⌈1/Real.sqrt h⌉₊:ℝ)+1)^25) :
    c*S ≤ (96*Real.pi+25*Real.pi*Q/A+25*Real.pi/A+4*5^25*Real.pi/A)*r := by
  have hcval : c = Real.pi/h^2 := (eq_div_iff (by positivity)).mpr hch
  have hc0 : 0 < c := by rw [hcval]; positivity
  have hsh : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  have hsh1 : Real.sqrt h ≤ 1 := by
    have := Real.sqrt_le_sqrt hh1
    rwa [Real.sqrt_one] at this
  have hsq : Real.sqrt h^2 = h := Real.sq_sqrt hh.le
  have hhsh : h ≤ Real.sqrt h := by
    nlinarith [mul_nonneg hsh.le (sub_nonneg.mpr hsh1)]
  have hceil : 2*(⌈1/Real.sqrt h⌉₊:ℝ)+1 ≤ 5/Real.sqrt h := by
    have h1 := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 1/Real.sqrt h by positivity)
    have h2 : (1:ℝ) ≤ 1/Real.sqrt h := by rw [le_div_iff₀ hsh]; linarith
    have : (5:ℝ)/Real.sqrt h = 5*(1/Real.sqrt h) := by ring
    rw [this]
    linarith
  have h24le : h^24 ≤ h := by
    calc h^24 ≤ h^1 := pow_le_pow_of_le_one hh.le hh1 (by norm_num)
      _ = h := pow_one h
  have hinv : 1/h ≤ r/A := by
    rw [div_le_div_iff₀ hh hA, one_mul]
    rw [hh24, div_le_iff₀ hr] at h24le
    linarith
  have hT1 : c*(96*h^2*r) = 96*Real.pi*r := by rw [← hch]; ring
  have hT2 : c*(25*h*(r*(Q*h)/A+1)) ≤ 25*Real.pi*Q/A*r+25*Real.pi/A*r := by
    have e1 : c*(25*h*(r*(Q*h)/A+1)) = 25*Real.pi*Q/A*r+25*Real.pi*(1/h) := by
      rw [hcval]
      field_simp
    rw [e1]
    have h1 : 25*Real.pi*(1/h) ≤ 25*Real.pi*(r/A) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    have e2 : 25*Real.pi*(r/A) = 25*Real.pi/A*r := by ring
    linarith
  have hT3 : c*(4*(2*(⌈1/Real.sqrt h⌉₊:ℝ)+1)^25) ≤ 4*5^25*Real.pi/A*r := by
    have h1 : (2*(⌈1/Real.sqrt h⌉₊:ℝ)+1)^25 ≤ (5/Real.sqrt h)^25 :=
      pow_le_pow_left₀ (by positivity) hceil 25
    have hs25 : Real.sqrt h^25 = h^12*Real.sqrt h := by
      rw [show 25 = 2*12+1 by norm_num, pow_succ, pow_mul, hsq]
    have hh10 : h^10 ≤ Real.sqrt h := by
      have : h^10 ≤ h := by
        calc h^10 ≤ h^1 := pow_le_pow_of_le_one hh.le hh1 (by norm_num)
          _ = h := pow_one h
      linarith
    have hden : h^24 ≤ h^2*(h^12*Real.sqrt h) := by
      have := mul_le_mul_of_nonneg_left hh10 (show 0 ≤ h^14 by positivity)
      calc h^24 = h^14*h^10 := by ring
        _ ≤ h^14*Real.sqrt h := this
        _ = h^2*(h^12*Real.sqrt h) := by ring
    have e : c*(5/Real.sqrt h)^25 = 5^25*Real.pi/(h^2*(h^12*Real.sqrt h)) := by
      rw [hcval, div_pow, hs25]
      field_simp
    have h2 : c*(5/Real.sqrt h)^25 ≤ 5^25*Real.pi/h^24 := by
      rw [e]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    have h3 : 5^25*Real.pi/h^24 = 5^25*Real.pi/A*r := by
      rw [hh24, div_div_eq_mul_div]
      ring
    have h4 : c*(2*(⌈1/Real.sqrt h⌉₊:ℝ)+1)^25 ≤ c*(5/Real.sqrt h)^25 :=
      mul_le_mul_of_nonneg_left h1 hc0.le
    calc c*(4*(2*(⌈1/Real.sqrt h⌉₊:ℝ)+1)^25) = 4*(c*(2*(⌈1/Real.sqrt h⌉₊:ℝ)+1)^25) := by ring
      _ ≤ 4*(5^25*Real.pi/h^24) := by linarith
      _ = 4*5^25*Real.pi/A*r := by rw [h3]; ring
  have hexp : c*(96*h^2*r+25*h*(r*(Q*h)/A+1)+4*(2*(⌈1/Real.sqrt h⌉₊:ℝ)+1)^25) =
      c*(96*h^2*r)+c*(25*h*(r*(Q*h)/A+1))+c*(4*(2*(⌈1/Real.sqrt h⌉₊:ℝ)+1)^25) := by ring
  have hcS := mul_le_mul_of_nonneg_left hS hc0.le
  have hBr : (96*Real.pi+25*Real.pi*Q/A+25*Real.pi/A+4*5^25*Real.pi/A)*r =
      96*Real.pi*r+(25*Real.pi*Q/A*r+25*Real.pi/A*r)+4*5^25*Real.pi/A*r := by ring
  rw [hBr]
  linarith

/-- The whole sphere `S²⁴` is stratifiable at every scale with one absolute constant. -/
theorem sphere24_stratifiable : ∃ B : ℝ, 0 ≤ B ∧ SphereStratifiable24 B := by
  classical
  obtain ⟨δ, hδ, C, hC, ρ₁, hρ₁, hdom2, hbi, hmink⟩ := chart_boundary_minkowski24
  have hCdom : chartCube24 δ ⊆ equalAreaChartDomainD := fun p hp =>
    hdom2 p (fun i => (hp i).trans (by linarith))
  obtain ⟨K, g, hcover⟩ := sphere24_finite_chart_cover hδ hCdom
  have hA : 0 < (sphereAreaD 24).real univ := sphereAreaD_univ_pos 24
  have hs24 : 0 < Real.sqrt 24 := by positivity
  obtain ⟨h₀, hh₀pos, hh₀1, hh₀ρ⟩ : ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ 2*(Real.sqrt 24*h₀) ≤ ρ₁ := by
    refine ⟨min (ρ₁/(2*Real.sqrt 24)) 1, lt_min (by positivity) one_pos, min_le_right _ _, ?_⟩
    have h1 := min_le_left (ρ₁/(2*Real.sqrt 24)) 1
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  obtain ⟨BL, hBL⟩ : ∃ BL : ℝ, BL = 96*Real.pi+
      25*Real.pi*((K:ℝ)*(C*(2*Real.sqrt 24)))/(sphereAreaD 24).real univ+
      25*Real.pi/(sphereAreaD 24).real univ+4*5^25*Real.pi/(sphereAreaD 24).real univ := ⟨_, rfl⟩
  obtain ⟨BS, hBS⟩ : ∃ BS : ℝ, BS = Real.pi/h₀^2*(25+4*3^25) := ⟨_, rfl⟩
  have hBL0 : 0 ≤ BL := by rw [hBL]; positivity
  refine ⟨max BL BS, le_max_of_le_left hBL0, ?_⟩
  intro r hr
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  obtain ⟨h, hh, hh24⟩ : ∃ h : ℝ, 0 < h ∧ h^24 = (sphereAreaD 24).real univ/r := by
    refine ⟨((sphereAreaD 24).real univ/r)^((1:ℝ)/24), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hch := sphereGaussianDensityFactor24_mul_sq hr hh hh24
  by_cases hsmall : h ≤ h₀
  · -- the chart construction
    have hh1 : h ≤ 1 := hsmall.trans hh₀1
    have hρ : 2*(Real.sqrt 24*h) ≤ ρ₁ := by
      have := mul_le_mul_of_nonneg_left hsmall hs24.le
      linarith
    obtain ⟨Cl, dm, hm, hd, hu, hmass, hdiam, hsum⟩ := sphere24_chart_partition_large hδ hC hdom2
      hbi hmink g hcover hr hh hh24 hρ
    refine ⟨Cl, dm, hm, hd, hu, fun j => sphereProbability24_eq_inv_of_real hr (hmass j),
      hdiam, ?_⟩
    rw [← Finset.mul_sum]
    have hsum2 : ∑ j, (dm j)^2 ≤ 96*h^2*r+
        25*h*(r*(((K:ℝ)*(C*(2*Real.sqrt 24)))*h)/(sphereAreaD 24).real univ+1)+
        4*(2*(⌈1/Real.sqrt h⌉₊:ℝ)+1)^25 := by
      have e : (r:ℝ)*(((K:ℝ)*(C*(2*Real.sqrt 24)))*h) = r*(K*(C*(2*(Real.sqrt 24*h)))) := by ring
      rw [e]
      exact hsum
    have hfin : sphereGaussianDensityFactor24 r*∑ j, (dm j)^2 ≤ BL*r := by
      rw [hBL]
      exact stratification_large_arith24 hA hh hh1 hrR hh24 hch hsum2
    exact hfin.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hrR.le)
  · -- small r: the pool partition of the whole sphere at scale 1
    have hsmall' : h₀ < h := lt_of_not_ge hsmall
    obtain ⟨Cl, dm, hm, hd, hu, hmass, hdiam, hsum⟩ :=
      sphere24_pool_partition (P := univ) MeasurableSet.univ one_pos hr
    refine ⟨Cl, dm, hm, hd, hu, fun j => sphereProbability24_eq_inv_of_real hr ?_, hdiam, ?_⟩
    · rw [hmass j, probReal_univ]
    · rw [← Finset.mul_sum]
      have hcval : sphereGaussianDensityFactor24 r = Real.pi/h^2 :=
        (eq_div_iff (by positivity)).mpr hch
      have hc : sphereGaussianDensityFactor24 r ≤ Real.pi/h₀^2 := by
        rw [hcval]
        exact div_le_div_of_nonneg_left Real.pi_pos.le (by positivity)
          (pow_le_pow_left₀ hh₀pos.le hsmall'.le 2)
      have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hr
      have hs : ∑ j, (dm j)^2 ≤ (25+4*3^25)*r := by
        have hb : (r:ℝ)*(5*1)^2+4*(2*(⌈(1:ℝ)/1⌉₊:ℝ)+1)^25 ≤ (25+4*3^25)*r := by
          norm_num
          linarith
        exact hsum.trans hb
      have h1 : sphereGaussianDensityFactor24 r*(∑ j, (dm j)^2) ≤
          Real.pi/h₀^2*((25+4*3^25)*r) :=
        mul_le_mul hc hs (Finset.sum_nonneg fun j _ => sq_nonneg _) (by positivity)
      calc sphereGaussianDensityFactor24 r*∑ j, (dm j)^2 ≤ Real.pi/h₀^2*((25+4*3^25)*r) := h1
        _ = BS*r := by rw [hBS]; ring
        _ ≤ max BL BS*r := mul_le_mul_of_nonneg_right (le_max_right _ _) hrR.le

end SphericalRiesz
end
end

section

/-! Minkowski bounds for the frontiers of Leech cube patches on `S²⁴` (stage NEG, residual
stratification; dimension-24 port of `PatchBoundaryMinkowski8`).

If `F` is Lipschitz on the unit cube `[0,1]^24`, the `ρ`-neighbourhood on `S²⁴` of the image of
the cube boundary has area `O(ρ)`: the boundary is covered by the `48 (m+1)^23` face grid points
of mesh `1/m ≤ ρ`, and each neighbourhood piece lies in a spherical cap of radius `O(ρ)`, of area
`O(ρ^24)`. Every small Leech cube patch map is `C^∞` on the closed cube, hence Lipschitz there;
the image of the open cube is open in the sphere, so the frontier of a patch lies in the image of
the cube boundary. Hence the frontier of the complement of any finite union of patches has a
linear Minkowski bound. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal NNReal ContDiff
namespace SphericalRiesz
open Boundary

/-- Small Leech cube patch maps are smooth at every point of the closed unit cube. -/
theorem smallLeechCubeMap24_contDiffAt (p : SmallLeechCubePatch24) (x : Fin 24 → ℝ)
    (hx : x ∈ UnitCube 24) : ContDiffAt ℝ ∞ (smallLeechCubeMap24 p) x := by
  have hdom := equalAreaLeechAffine24_cube_domain p.v p.c p.ε p.ε_pos p.c_mem p.small
    ⟨x, hx, rfl⟩
  have hshift : ContDiffAt ℝ ∞ (fun y : Fin 24 → ℝ => y-p.c) x := by fun_prop
  have hf : ContDiffAt ℝ ∞ (fun y => equalAreaMovingLeechChart p.v p.ε (y-p.c)) x :=
    ContDiffAt.comp (g := equalAreaMovingLeechChart p.v p.ε)
      (f := fun y : Fin 24 → ℝ => y-p.c) x
      (equalAreaMovingLeechChart_contDiffAt p.v p.ε (x-p.c) hdom.1) hshift
  exact p.g.toContinuousLinearMap.contDiff.contDiffAt.comp x hf

/-- The physical sphere patch of a small Leech cube patch is compact. -/
theorem smallLeechSpherePatch24_isCompact (p : SmallLeechCubePatch24) :
    IsCompact (smallLeechSpherePatch24 p) :=
  equalAreaLeechSpherePatch24_cube_isCompact p.g p.v p.c p.ε p.ε_pos p.c_mem p.small

/-- The boundary of the unit cube `[0,1]^24`. -/
def unitCubeBdry24 : Set (Fin 24 → ℝ) := {w | w ∈ UnitCube 24 ∧ ∃ i, w i = 0 ∨ w i = 1}

/-- The open unit cube `(0,1)^24`. -/
def unitCubeOpen24 : Set (Fin 24 → ℝ) := Set.pi univ (fun _ => Ioo (0:ℝ) 1)

theorem unitCubeOpen24_isOpen : IsOpen unitCubeOpen24 :=
  isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)

theorem unitCubeOpen24_subset : unitCubeOpen24 ⊆ UnitCube 24 := by
  intro w hw i
  have := hw i (mem_univ i)
  exact ⟨this.1.le, this.2.le⟩

/-- Grid points on the faces of the unit cube: coordinate `i` is `0` or `1`, the others are
multiples of `1/m`. -/
def cubeFacePoint24 (m : ℕ) (q : Fin 24 × Bool × (Fin 23 → Fin (m+1))) : Fin 24 → ℝ :=
  Fin.insertNth (α := fun _ => ℝ) q.1 (if q.2.1 then (1:ℝ) else 0) (fun j => ((q.2.2 j : ℕ):ℝ)/m)

theorem cubeFacePoint24_mem {m : ℕ} (hm : 0 < m) (q : Fin 24 × Bool × (Fin 23 → Fin (m+1))) :
    cubeFacePoint24 m q ∈ UnitCube 24 := by
  intro j
  rcases Fin.eq_self_or_eq_succAbove q.1 j with h | ⟨j', rfl⟩
  · subst h
    simp only [cubeFacePoint24, Fin.insertNth_apply_same]
    split_ifs <;> norm_num
  · simp only [cubeFacePoint24, Fin.insertNth_apply_succAbove]
    have hmR : (0:ℝ) < m := by exact_mod_cast hm
    have hk : ((q.2.2 j' : ℕ):ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp (q.2.2 j').isLt
    exact ⟨by positivity, (div_le_one hmR).mpr hk⟩

theorem exists_cubeFacePoint24_near {m : ℕ} (hm : 0 < m) {w : Fin 24 → ℝ}
    (hw : w ∈ unitCubeBdry24) :
    ∃ q : Fin 24 × Bool × (Fin 23 → Fin (m+1)), dist w (cubeFacePoint24 m q) ≤ 1/m := by
  obtain ⟨hwc, i, hi⟩ := hw
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hk : ∀ j : Fin 23, ⌊(m:ℝ)*w (i.succAbove j)⌋₊ < m+1 := by
    intro j
    have h1 : (m:ℝ)*w (i.succAbove j) ≤ m := by
      have := (hwc (i.succAbove j)).2
      nlinarith
    have := Nat.floor_le_floor (a := (m:ℝ)*w (i.succAbove j)) h1
    rw [Nat.floor_natCast] at this
    omega
  refine ⟨(i, decide (w i = 1), fun j => ⟨⌊(m:ℝ)*w (i.succAbove j)⌋₊, hk j⟩), ?_⟩
  rw [dist_pi_le_iff (by positivity)]
  intro j
  rcases Fin.eq_self_or_eq_succAbove i j with h | ⟨j', rfl⟩
  · subst h
    simp only [cubeFacePoint24, Fin.insertNth_apply_same]
    rcases hi with h0 | h1
    · have hd : decide (w j = 1) = false := decide_eq_false (by rw [h0]; norm_num)
      rw [hd, ite_eq_right (by decide), h0, dist_self]
      positivity
    · have hd : decide (w j = 1) = true := decide_eq_true h1
      rw [hd, ite_eq_left rfl, h1, dist_self]
      positivity
  · simp only [cubeFacePoint24, Fin.insertNth_apply_succAbove]
    rw [Real.dist_eq]
    have h0 : 0 ≤ (m:ℝ)*w (i.succAbove j') := by
      have := (hwc (i.succAbove j')).1
      positivity
    have hf1 := Nat.floor_le h0
    have hf2 := Nat.lt_floor_add_one ((m:ℝ)*w (i.succAbove j'))
    have e : w (i.succAbove j')-(⌊(m:ℝ)*w (i.succAbove j')⌋₊:ℝ)/m =
        ((m:ℝ)*w (i.succAbove j')-⌊(m:ℝ)*w (i.succAbove j')⌋₊)/m := by
      field_simp
    rw [e, abs_div, abs_of_pos hmR, div_le_div_iff_of_pos_right hmR, abs_le]
    constructor <;> linarith

/-- Minkowski bound for Lipschitz images of the boundary of the unit cube. -/
theorem lipschitz_cubeBdry_minkowski24 {F : (Fin 24 → ℝ) → AmbientD 24} {L : ℝ≥0}
    (hF : LipschitzOnWith L F (UnitCube 24)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ →
      (sphereAreaD 24) {x : SphereD 24 | ∃ w ∈ unitCubeBdry24, dist (x : AmbientD 24) (F w) ≤ ρ} ≤
        ENNReal.ofReal (C*ρ) := by
  classical
  obtain ⟨R₀, hR₀, hcap⟩ := sphereArea24_ball_le
  obtain ⟨L', hL'⟩ : ∃ L' : ℝ, L' = (L:ℝ)+1 := ⟨_, rfl⟩
  have hL'pos : 0 < L' := by rw [hL']; positivity
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀ : ℝ, ρ₀ = min 1 (R₀/(3*L')) := ⟨_, rfl⟩
  have hρ₀pos : 0 < ρ₀ := by rw [hρ₀]; exact lt_min one_pos (by positivity)
  have hρ₀1 : ρ₀ ≤ 1 := by rw [hρ₀]; exact min_le_left _ _
  have hρ₀R : 3*L'*ρ₀ ≤ R₀ := by
    have h := min_le_right 1 (R₀/(3*L'))
    rw [← hρ₀, le_div_iff₀ (by positivity)] at h
    linarith
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (sphereAreaD 24).real univ := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; exact measureReal_nonneg
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = 48*3^23*(12*L')^24 := ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  refine ⟨max C₁ (A/ρ₀), le_max_of_le_left hC₁0, fun ρ hρ => ?_⟩
  by_cases hbig : ρ₀ < ρ
  · calc (sphereAreaD 24) _ ≤ (sphereAreaD 24) univ := measure_mono (subset_univ _)
      _ = ENNReal.ofReal A := by rw [hA, ofReal_measureReal (measure_ne_top _ _)]
      _ ≤ ENNReal.ofReal (max C₁ (A/ρ₀)*ρ) := by
          apply ENNReal.ofReal_le_ofReal
          calc A = A/ρ₀*ρ₀ := by field_simp
            _ ≤ A/ρ₀*ρ := mul_le_mul_of_nonneg_left hbig.le (by positivity)
            _ ≤ max C₁ (A/ρ₀)*ρ := mul_le_mul_of_nonneg_right (le_max_right _ _) hρ.le
  have hρρ₀ : ρ ≤ ρ₀ := not_lt.mp hbig
  have hρ1 : ρ ≤ 1 := hρρ₀.trans hρ₀1
  set m := ⌈1/ρ⌉₊ with hm
  have hmpos : 0 < m := Nat.ceil_pos.mpr (by positivity)
  have hmR : (0:ℝ) < m := by exact_mod_cast hmpos
  have hm1 : 1/(m:ℝ) ≤ ρ := (one_div_le hmR hρ).mpr (Nat.le_ceil _)
  have hm2 : ((m:ℝ)+1)*ρ ≤ 3 := by
    have h1 := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 1/ρ by positivity)
    rw [← hm] at h1
    have h2 : (1/ρ)*ρ = 1 := by field_simp
    nlinarith
  -- the cover by caps around the images of face grid points
  let T : Fin 24 × Bool × (Fin 23 → Fin (m+1)) → Set (SphereD 24) := fun q =>
    {x : SphereD 24 | dist (x : AmbientD 24) (F (cubeFacePoint24 m q)) ≤ L'*ρ}
  have hsub : {x : SphereD 24 | ∃ w ∈ unitCubeBdry24, dist (x : AmbientD 24) (F w) ≤ ρ} ⊆
      ⋃ q, T q := by
    rintro x ⟨w, hw, hxw⟩
    obtain ⟨q, hq⟩ := exists_cubeFacePoint24_near hmpos hw
    refine mem_iUnion.mpr ⟨q, ?_⟩
    show dist (x : AmbientD 24) (F (cubeFacePoint24 m q)) ≤ L'*ρ
    have hFw := hF.dist_le_mul w hw.1 (cubeFacePoint24 m q) (cubeFacePoint24_mem hmpos q)
    have hwq : dist w (cubeFacePoint24 m q) ≤ ρ := hq.trans hm1
    have hL0 : (0:ℝ) ≤ L := L.2
    have : (L:ℝ)*dist w (cubeFacePoint24 m q) ≤ L*ρ := mul_le_mul_of_nonneg_left hwq hL0
    calc dist (x : AmbientD 24) (F (cubeFacePoint24 m q)) ≤ dist (x : AmbientD 24) (F w)+
          dist (F w) (F (cubeFacePoint24 m q)) := dist_triangle _ _ _
      _ ≤ ρ+L*ρ := by linarith
      _ = L'*ρ := by rw [hL']; ring
  have hT : ∀ q, (sphereAreaD 24) (T q) ≤ ENNReal.ofReal ((12*L'*ρ)^24) := by
    intro q
    rcases (T q).eq_empty_or_nonempty with he | ⟨x₀, hx₀⟩
    · rw [he, measure_empty]; exact zero_le
    · have hsub' : T q ⊆ {y : SphereD 24 | dist y x₀ < 3*L'*ρ} := by
        intro y hy
        show dist y x₀ < 3*L'*ρ
        have h1 : dist (y : AmbientD 24) (F (cubeFacePoint24 m q)) ≤ L'*ρ := hy
        have h2 : dist (x₀ : AmbientD 24) (F (cubeFacePoint24 m q)) ≤ L'*ρ := hx₀
        have h3 : dist (y : AmbientD 24) (x₀ : AmbientD 24) ≤
            dist (y : AmbientD 24) (F (cubeFacePoint24 m q))+
            dist (x₀ : AmbientD 24) (F (cubeFacePoint24 m q)) := dist_triangle_right _ _ _
        have h4 : 0 < L'*ρ := by positivity
        rw [Subtype.dist_eq]
        linarith
      have h3R : 3*L'*ρ ≤ R₀ :=
        (mul_le_mul_of_nonneg_left hρρ₀ (by positivity)).trans hρ₀R
      calc (sphereAreaD 24) (T q) ≤ (sphereAreaD 24) {y : SphereD 24 | dist y x₀ < 3*L'*ρ} :=
            measure_mono hsub'
        _ ≤ ENNReal.ofReal ((4*(3*L'*ρ))^24) := hcap x₀ _ (by positivity) h3R
        _ = ENNReal.ofReal ((12*L'*ρ)^24) := by
            congr 1
            ring
  have hcard : Fintype.card (Fin 24 × Bool × (Fin 23 → Fin (m+1))) = 48*(m+1)^23 := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Fintype.card_fun]
    ring
  calc (sphereAreaD 24) {x : SphereD 24 | ∃ w ∈ unitCubeBdry24, dist (x : AmbientD 24) (F w) ≤ ρ}
      ≤ (sphereAreaD 24) (⋃ q, T q) := measure_mono hsub
    _ ≤ ∑ q, (sphereAreaD 24) (T q) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _q : Fin 24 × Bool × (Fin 23 → Fin (m+1)), ENNReal.ofReal ((12*L'*ρ)^24) :=
        Finset.sum_le_sum fun q _ => hT q
    _ = ENNReal.ofReal ((48*((m:ℝ)+1)^23)*(12*L'*ρ)^24) := by
        rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [← ENNReal.ofReal_natCast]
        congr 1
        push_cast
        ring
    _ ≤ ENNReal.ofReal (max C₁ (A/ρ₀)*ρ) := by
        apply ENNReal.ofReal_le_ofReal
        have e : ∀ M : ℝ, (48*M^23)*(12*L'*ρ)^24 = 48*(12*L')^24*(M*ρ)^23*ρ := fun M => by ring
        rw [e ((m:ℝ)+1)]
        have h7 : (((m:ℝ)+1)*ρ)^23 ≤ 3^23 := pow_le_pow_left₀ (by positivity) hm2 23
        have h8 : 48*(12*L')^24*(((m:ℝ)+1)*ρ)^23 ≤ C₁ := by
          rw [hC₁]
          have h0 : (0:ℝ) ≤ 48*(12*L')^24 := by positivity
          calc 48*(12*L')^24*(((m:ℝ)+1)*ρ)^23 ≤ 48*(12*L')^24*3^23 :=
                mul_le_mul_of_nonneg_left h7 h0
            _ = 48*3^23*(12*L')^24 := by ring
        calc 48*(12*L')^24*(((m:ℝ)+1)*ρ)^23*ρ ≤ C₁*ρ := mul_le_mul_of_nonneg_right h8 hρ.le
          _ ≤ max C₁ (A/ρ₀)*ρ := mul_le_mul_of_nonneg_right (le_max_left _ _) hρ.le

/-- Small Leech cube patch maps are Lipschitz on the closed unit cube. -/
theorem smallLeechCubeMap24_lipschitz (p : SmallLeechCubePatch24) :
    ∃ L : ℝ≥0, LipschitzOnWith L (smallLeechCubeMap24 p) (UnitCube 24) := by
  have hloc : LocallyLipschitzOn (UnitCube 24) (smallLeechCubeMap24 p) := by
    intro x hx
    obtain ⟨K, t, ht, hK⟩ :=
      ((smallLeechCubeMap24_contDiffAt p x hx).of_le (by simp)).exists_lipschitzOnWith
    exact ⟨K, t, nhdsWithin_le_nhds ht, hK⟩
  exact hloc.exists_lipschitzOnWith_of_compact (unitCube_isCompact 24)

theorem smallLeechSpherePatch24_eq (p : SmallLeechCubePatch24) :
    smallLeechSpherePatch24 p =
      {x : SphereD 24 | ∃ w ∈ UnitCube 24, (x : AmbientD 24) = smallLeechCubeMap24 p w} := by
  ext x
  simp only [smallLeechSpherePatch24, equalAreaLeechSpherePatch24, mem_preimage, mem_image,
    mem_ofPred_eq, smallLeechCubeMap24]
  constructor
  · rintro ⟨w, hw, hx⟩; exact ⟨w, hw, hx.symm⟩
  · rintro ⟨w, hw, hx⟩; exact ⟨w, hw, hx.symm⟩

theorem equalAreaLeechAffine24_isOpenMap (v c : Fin 24 → ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    IsOpenMap (equalAreaLeechAffine24 v c ε) := by
  have he : IsOpenMap leechMap :=
    (leechBasis.equivFun.symm.toContinuousLinearEquiv :
      (Fin 24 → ℝ) ≃L[ℝ] (Fin 24 → ℝ)).isOpenMap
  have hcomp : equalAreaLeechAffine24 v c ε =
      (fun y => v+y) ∘ (fun y => ε • y) ∘ leechMap ∘ (fun x => x-c) := by
    funext x; rfl
  rw [hcomp]
  exact (isOpenMap_add_left v).comp ((isOpenMap_smul₀ hε).comp (he.comp (isOpenMap_sub_right c)))

/-- The image of the open cube under a patch map is open in the sphere. -/
theorem smallLeech_openImage_isOpen (p : SmallLeechCubePatch24) :
    IsOpen {x : SphereD 24 | ∃ w ∈ unitCubeOpen24, (x : AmbientD 24) = smallLeechCubeMap24 p w} := by
  have hset : {x : SphereD 24 | ∃ w ∈ unitCubeOpen24,
        (x : AmbientD 24) = smallLeechCubeMap24 p w} =
      chartImage24 p.g (equalAreaLeechAffine24 p.v p.c p.ε '' unitCubeOpen24) := by
    ext x
    simp only [mem_ofPred_eq, chartImage24, mem_image]
    constructor
    · rintro ⟨w, hw, hx⟩; exact ⟨_, ⟨w, hw, rfl⟩, hx⟩
    · rintro ⟨_, ⟨w, hw, rfl⟩, hx⟩; exact ⟨w, hw, hx⟩
  rw [hset]
  apply chartImage24_isOpen
  · exact equalAreaLeechAffine24_isOpenMap p.v p.c p.ε_pos.ne' _ unitCubeOpen24_isOpen
  · exact (image_mono unitCubeOpen24_subset).trans
      (equalAreaLeechAffine24_cube_domain p.v p.c p.ε p.ε_pos p.c_mem p.small)

/-- The frontier of a patch lies in the image of the cube boundary. -/
theorem smallLeechSpherePatch24_frontier (p : SmallLeechCubePatch24) :
    frontier (smallLeechSpherePatch24 p) ⊆
      {x : SphereD 24 | ∃ w ∈ unitCubeBdry24, (x : AmbientD 24) = smallLeechCubeMap24 p w} := by
  intro x hx
  have hcl := (smallLeechSpherePatch24_isCompact p).isClosed
  rw [frontier, hcl.closure_eq] at hx
  obtain ⟨hxS, hxi⟩ := hx
  have hxS' := hxS
  rw [smallLeechSpherePatch24_eq] at hxS'
  obtain ⟨w, hw, hxw⟩ := hxS'
  refine ⟨w, ⟨hw, ?_⟩, hxw⟩
  by_contra hne
  have hwo : w ∈ unitCubeOpen24 := by
    intro i _
    have hi := hw i
    have h01 : ¬ (w i = 0 ∨ w i = 1) := fun h => hne ⟨i, h⟩
    rw [not_or] at h01
    exact ⟨lt_of_le_of_ne hi.1 (Ne.symm h01.1), lt_of_le_of_ne hi.2 h01.2⟩
  apply hxi
  rw [mem_interior]
  refine ⟨_, ?_, smallLeech_openImage_isOpen p, ⟨w, hwo, hxw⟩⟩
  rw [smallLeechSpherePatch24_eq]
  rintro y ⟨w', hw', hy⟩
  exact ⟨w', unitCubeOpen24_subset hw', hy⟩

/-- Linear Minkowski bound for the frontier of the complement of finitely many patches. -/
theorem patchComplement_frontier_minkowski24 {K : ℕ} (P : Fin K → SmallLeechCubePatch24) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ →
      (sphereAreaD 24) {x : SphereD 24 |
          ∃ y ∈ frontier (⋃ i, smallLeechSpherePatch24 (P i))ᶜ, dist x y ≤ ρ} ≤
        ENNReal.ofReal (C*ρ) := by
  classical
  have hL : ∀ i, ∃ L : ℝ≥0, LipschitzOnWith L (smallLeechCubeMap24 (P i)) (UnitCube 24) :=
    fun i => smallLeechCubeMap24_lipschitz (P i)
  choose L hL using hL
  have hM : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ →
      (sphereAreaD 24) {x : SphereD 24 | ∃ w ∈ unitCubeBdry24,
        dist (x : AmbientD 24) (smallLeechCubeMap24 (P i) w) ≤ ρ} ≤ ENNReal.ofReal (C*ρ) :=
    fun i => lipschitz_cubeBdry_minkowski24 (hL i)
  choose C hC0 hC using hM
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC0 i), fun ρ hρ => ?_⟩
  have hsub : {x : SphereD 24 |
        ∃ y ∈ frontier (⋃ i, smallLeechSpherePatch24 (P i))ᶜ, dist x y ≤ ρ} ⊆
      ⋃ i, {x : SphereD 24 | ∃ w ∈ unitCubeBdry24,
        dist (x : AmbientD 24) (smallLeechCubeMap24 (P i) w) ≤ ρ} := by
    rintro x ⟨y, hy, hxy⟩
    rw [frontier_compl] at hy
    have hy' : y ∈ ⋃ i ∈ (Finset.univ : Finset (Fin K)),
        frontier (smallLeechSpherePatch24 (P i)) := by
      apply frontier_biUnion_closed_subset Finset.univ (fun i => smallLeechSpherePatch24 (P i))
        (fun i _ => (smallLeechSpherePatch24_isCompact (P i)).isClosed)
      simpa using hy
    obtain ⟨i, _, hyi⟩ := mem_iUnion₂.mp hy'
    obtain ⟨w, hw, hyw⟩ := smallLeechSpherePatch24_frontier (P i) hyi
    refine mem_iUnion.mpr ⟨i, w, hw, ?_⟩
    rw [← hyw]
    exact hxy
  calc (sphereAreaD 24) {x : SphereD 24 |
        ∃ y ∈ frontier (⋃ i, smallLeechSpherePatch24 (P i))ᶜ, dist x y ≤ ρ}
      ≤ (sphereAreaD 24) (⋃ i, {x : SphereD 24 | ∃ w ∈ unitCubeBdry24,
          dist (x : AmbientD 24) (smallLeechCubeMap24 (P i) w) ≤ ρ}) := measure_mono hsub
    _ ≤ ∑ i, (sphereAreaD 24) {x : SphereD 24 | ∃ w ∈ unitCubeBdry24,
          dist (x : AmbientD 24) (smallLeechCubeMap24 (P i) w) ≤ ρ} :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ i, ENNReal.ofReal (C i*ρ) := Finset.sum_le_sum fun i _ => hC i ρ hρ
    _ = ENNReal.ofReal ((∑ i, C i)*ρ) := by
        rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hC0 i) hρ.le)]

end SphericalRiesz
end
end

section

/-! Exact-mass stratification of residual regions on `S²⁴` (stage NEG; dimension-24 port of
`ResidualStratification8`, without the three concluding asymptotic theorems).

For a measurable region `R ⊆ S²⁴` whose frontier has a linear Minkowski bound, and `r = N σ(R)`,
take the rotated chart grid boxes of side `h`, `h^24 = A/N`, whose images lie inside `R`: they
have mass exactly `1/N` and diameter at most `2√24 h`; at most `r - 1` are kept. A box image
meeting both `R` and its complement meets the frontier of `R` (it is preconnected), so the rest of
`R` lies within `2√24 h` of the chart cube boundaries or of the frontier of `R`, and has mass
`O(h)`. It is split into exact-mass cells by the pool partition at scale `τ√h` (cells of diameter
at most `5τ√h`). With `c_N h² = π`, the good cells cost at most `4·24·π r = 96π r`, and for fixed
`τ` with `25πτ²Q/A ≤ ε/3` the pool costs at most `ε N` once `N` is large:
`NegStratifiable24 R (96π)`. The complement of any finite union of small Leech cube patches
qualifies, so both stratification hypotheses hold with one absolute constant. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal
namespace SphericalRiesz

/-- Exact-mass stratifications of a region `A ⊆ S²⁴` at the density scale: for every large `N`
and every `r = N σ(A)`, cells of mass `σ(A)/r = 1/N` with diameters `d_j` and
`Σ_j c_N d_j² ≤ B r + ε N`. -/
def NegStratifiable24 (A : Set (SphereD 24)) (B : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N r : ℕ, N₀ ≤ N → 0 < r →
    (r:ℝ) = (N:ℝ)*(sphereProbabilityD 24).real A →
    ∃ C : Fin r → Set (SphereD 24), ∃ dm : Fin r → ℝ,
      (∀ j, MeasurableSet (C j)) ∧ Pairwise (fun i j => Disjoint (C i) (C j)) ∧
      (⋃ j, C j) = A ∧
      (∀ j, sphereProbabilityD 24 (C j) = sphereProbabilityD 24 A/(r:ℝ≥0∞)) ∧
      (∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y ≤ dm j) ∧
      ∑ j, sphereGaussianDensityFactor24 N*(dm j)^2 ≤ B*r+ε*N

set_option maxHeartbeats 1000000 in
/-- The chart partition of a measurable region `R` into `r` cells of mass `1/N`, for small `h`. -/
theorem sphere24_region_chart_partition {δ C ρ₁ : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hdom2 : ∀ p : Fin 24 → ℝ, (∀ i, |p i| ≤ 2*δ) → p ∈ equalAreaChartDomainD)
    (hbi : ∀ p q : Fin 24 → ℝ, (∀ i, |p i| ≤ 2*δ) → (∀ i, |q i| ≤ 2*δ) →
      dist (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 24)) (WithLp.toLp 2 q) ≤
        2*dist (equalAreaPhiD p) (equalAreaPhiD q) ∧
      dist (equalAreaPhiD p) (equalAreaPhiD q) ≤
        2*dist (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 24)) (WithLp.toLp 2 q))
    (hmink : ∀ g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24, ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₁ →
      (sphereAreaD 24) {x : SphereD 24 | ∃ w ∈ cubeBdry24 δ, dist (x : AmbientD 24) (g (equalAreaPhiD w)) ≤ ρ} ≤
        ENNReal.ofReal (C*ρ))
    {K : ℕ} (g : Fin K → AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24)
    (hcover : ∀ x : SphereD 24, ∃ k, x ∈ chartImage24 (g k) (chartCubeOpen24 δ))
    {R : Set (SphereD 24)} (hRm : MeasurableSet R) {h : ℝ} (hh : 0 < h) {MR : ℝ} (hMR : 0 ≤ MR)
    (hRmink : (sphereAreaD 24) {x : SphereD 24 | ∃ y ∈ frontier R, dist x y ≤ 2*(Real.sqrt 24*h)} ≤
      ENNReal.ofReal MR)
    {N r : ℕ} (hN : 0 < N) (hr : 0 < r) (hrN : (r:ℝ) = N*(sphereProbabilityD 24).real R)
    (hh24 : h^24 = (sphereAreaD 24).real univ/N) (hρ : 2*(Real.sqrt 24*h) ≤ ρ₁) {H : ℝ} (hH : 0 < H) :
    ∃ Cl : Fin r → Set (SphereD 24), ∃ dm : Fin r → ℝ,
      (∀ j, MeasurableSet (Cl j)) ∧ Pairwise (fun i j => Disjoint (Cl i) (Cl j)) ∧
      (⋃ j, Cl j) = R ∧ (∀ j, (sphereProbabilityD 24).real (Cl j) = 1/N) ∧
      (∀ j, ∀ x ∈ Cl j, ∀ y ∈ Cl j, dist x y ≤ dm j) ∧
      ∑ j, (dm j)^2 ≤ 96*h^2*r+
        (5*H)^2*(N*(K*(C*(2*(Real.sqrt 24*h)))+MR)/(sphereAreaD 24).real univ+1)+
        4*(2*⌈1/H⌉₊+1)^25 := by
  classical
  set A := (sphereAreaD 24).real univ with hAdef
  have hA : 0 < A := sphereAreaD_univ_pos 24
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hC2 : ∀ p ∈ chartCube24 δ, ∀ i, |p i| ≤ 2*δ := fun p hp i => (hp i).trans (by linarith)
  have hCdom : chartCube24 δ ⊆ equalAreaChartDomainD := fun p hp => hdom2 p (hC2 p hp)
  set Zall := (gridBox24_inside_cube_finite (δ := δ) hh).toFinset with hZall
  have hZmem : ∀ z, z ∈ Zall ↔ gridBox24 h z ⊆ chartCube24 δ := fun z => by
    rw [hZall, Set.Finite.mem_toFinset]; rfl
  let earlier : Fin K → Set (SphereD 24) := fun k =>
    ⋃ j ∈ Finset.univ.filter (fun j : Fin K => j < k), chartImage24 (g j) (chartCube24 δ)
  let cell : Fin K × (Fin 24 → ℤ) → Set (SphereD 24) := fun q => chartImage24 (g q.1) (gridBox24 h q.2)
  set G₀ := (Finset.univ ×ˢ Zall).filter (fun q => Disjoint (cell q) (earlier q.1) ∧ cell q ⊆ R)
    with hG₀
  have hG₀box : ∀ q ∈ G₀, gridBox24 h q.2 ⊆ chartCube24 δ := by
    intro q hq
    rw [hG₀, Finset.mem_filter, Finset.mem_product] at hq
    exact (hZmem q.2).mp hq.1.2
  have hG₀good : ∀ q ∈ G₀, Disjoint (cell q) (earlier q.1) := by
    intro q hq
    rw [hG₀, Finset.mem_filter] at hq
    exact hq.2.1
  have hG₀R : ∀ q ∈ G₀, cell q ⊆ R := by
    intro q hq
    rw [hG₀, Finset.mem_filter] at hq
    exact hq.2.2
  -- the good cells
  have hcm : ∀ q ∈ G₀, MeasurableSet (cell q) := fun q hq =>
    chartImage24_measurable (g q.1) (gridBox24_measurable h q.2) ((hG₀box q hq).trans hCdom)
  have hcprob : ∀ q ∈ G₀, (sphereProbabilityD 24).real (cell q) = 1/N := by
    intro q hq
    rw [sphereProbability24_real_eq_area, Measure.real, chartImage24_area (g q.1)
      (gridBox24_measurable h q.2) ((hG₀box q hq).trans hCdom), gridBox24_volume hh,
      ENNReal.toReal_ofReal (by positivity), hh24, ← hAdef]
    field_simp
  have hcdisj : Set.PairwiseDisjoint (↑G₀) cell := by
    intro q hq q' hq' hne
    show Disjoint (cell q) (cell q')
    by_cases hk : q.1 = q'.1
    · have hz : q.2 ≠ q'.2 := fun hz => hne (Prod.ext hk hz)
      show Disjoint (chartImage24 (g q.1) (gridBox24 h q.2)) (chartImage24 (g q'.1) (gridBox24 h q'.2))
      rw [← hk]
      exact chartImage24_disjoint (g q.1) ((hG₀box q hq).trans hCdom)
        ((hG₀box q' hq').trans hCdom) (gridBox24_disjoint hh hz)
    · rcases lt_or_gt_of_ne hk with hlt | hlt
      · have hsub : cell q ⊆ earlier q'.1 := by
          intro x hx
          refine mem_iUnion₂.mpr ⟨q.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, ?_⟩
          exact chartImage24_mono (g q.1) (hG₀box q hq) hx
        exact (hG₀good q' hq').symm.mono_left hsub
      · have hsub : cell q' ⊆ earlier q.1 := by
          intro x hx
          refine mem_iUnion₂.mpr ⟨q'.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, ?_⟩
          exact chartImage24_mono (g q'.1) (hG₀box q' hq') hx
        exact (hG₀good q hq).mono_right hsub
  have hcdiam' : ∀ k : Fin K, ∀ z, gridBox24 h z ⊆ chartCube24 δ →
      ∀ x ∈ chartImage24 (g k) (gridBox24 h z), ∀ y ∈ chartImage24 (g k) (gridBox24 h z),
        dist x y ≤ 2*(Real.sqrt 24*h) := by
    intro k z hz x hx y hy
    obtain ⟨p, hp, hxp⟩ := hx
    obtain ⟨p', hp', hyp'⟩ := hy
    rw [Subtype.dist_eq, hxp, hyp', (g k).dist_map]
    have h1 := (hbi p p' (hC2 p (hz hp)) (hC2 p' (hz hp'))).2
    have h2 := gridBox24_dist_le hh hp hp'
    linarith
  have hcdiam : ∀ q ∈ G₀, ∀ x ∈ cell q, ∀ y ∈ cell q, dist x y ≤ 2*(Real.sqrt 24*h) :=
    fun q hq => hcdiam' q.1 q.2 (hG₀box q hq)
  -- at most r good cells
  have hcard₀ : G₀.card ≤ r := by
    have hm := measureReal_biUnion_finset hcdisj hcm (μ := (sphereProbabilityD 24))
    have hsubR : (⋃ q ∈ G₀, cell q) ⊆ R := iUnion₂_subset hG₀R
    have hle : (sphereProbabilityD 24).real (⋃ q ∈ G₀, cell q) ≤ (sphereProbabilityD 24).real R :=
      measureReal_mono hsubR
    rw [hm, Finset.sum_congr rfl hcprob, Finset.sum_const, nsmul_eq_mul] at hle
    have : (G₀.card:ℝ) ≤ r := by
      have h2 : (G₀.card:ℝ)*(1/N)*N ≤ (sphereProbabilityD 24).real R*N :=
        mul_le_mul_of_nonneg_right hle hNR.le
      have e : (G₀.card:ℝ)*(1/N)*N = G₀.card := by field_simp
      rw [e] at h2
      linarith
    exact_mod_cast this
  obtain ⟨G, hGsub, hGcard⟩ := Finset.exists_subset_card_eq (s := G₀) (n := min G₀.card (r-1))
    (min_le_left _ _)
  set n := r-G.card with hndef
  have hGr : G.card ≤ r-1 := hGcard ▸ min_le_right _ _
  have hn : 0 < n := by omega
  -- the pool
  set U := ⋃ q ∈ G, cell q with hUdef
  have hUm : MeasurableSet U := Finset.measurableSet_biUnion G (fun q hq => hcm q (hGsub hq))
  have hUR : U ⊆ R := iUnion₂_subset fun q hq => hG₀R q (hGsub hq)
  set P := R \ U with hPdef
  have hPm : MeasurableSet P := hRm.diff hUm
  have hGdisj : Set.PairwiseDisjoint (↑G) cell := hcdisj.subset (by exact_mod_cast hGsub)
  have hUprob : (sphereProbabilityD 24).real U = G.card/N := by
    rw [hUdef, measureReal_biUnion_finset hGdisj (fun q hq => hcm q (hGsub hq)),
      Finset.sum_congr rfl (fun q hq => hcprob q (hGsub hq)), Finset.sum_const, nsmul_eq_mul]
    ring
  have hPprob : (sphereProbabilityD 24).real P = n/N := by
    have h1 := measureReal_inter_add_sdiff (μ := (sphereProbabilityD 24)) (s := R) hUm
    rw [inter_eq_right.mpr hUR, hUprob] at h1
    have hR : (sphereProbabilityD 24).real R = r/N := by
      field_simp
      linarith
    have : ((r-G.card : ℕ):ℝ) = (r:ℝ)-G.card := by
      rw [Nat.cast_sub (by omega)]
    rw [hR] at h1
    rw [hPdef, hndef, this, sub_div]
    linarith
  -- the pool lies near the chart cube boundaries or the frontier of `R`
  set N₀ := ⋃ k : Fin K, {x : SphereD 24 | ∃ w ∈ cubeBdry24 δ,
    dist (x : AmbientD 24) (g k (equalAreaPhiD w)) ≤ 2*(Real.sqrt 24*h)} with hN₀
  set NR := {x : SphereD 24 | ∃ y ∈ frontier R, dist x y ≤ 2*(Real.sqrt 24*h)} with hNRdef
  have hP₀ : R \ (⋃ q ∈ G₀, cell q) ⊆ N₀ ∪ NR := by
    rintro x ⟨hxR, hx⟩
    by_cases hgood : ∃ k : Fin K, ∃ z : Fin 24 → ℤ, gridBox24 h z ⊆ chartCube24 δ ∧
        Disjoint (chartImage24 (g k) (gridBox24 h z))
          (⋃ j ∈ Finset.univ.filter (fun j : Fin K => j < k), chartImage24 (g j) (chartCube24 δ)) ∧
        x ∈ chartImage24 (g k) (gridBox24 h z)
    · right
      obtain ⟨k, z, hz, hdisj, hxk⟩ := hgood
      have hnot : ¬ chartImage24 (g k) (gridBox24 h z) ⊆ R := by
        intro hsub
        apply hx
        refine mem_iUnion₂.mpr ⟨(k, z), ?_, hxk⟩
        rw [hG₀, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨Finset.mem_univ _, (hZmem z).mpr hz⟩, hdisj, hsub⟩
      obtain ⟨y, hy, hyR⟩ := not_subset.mp hnot
      have hpc := chartImage24_isPreconnected (g k) (gridBox24_convex h z) (hz.trans hCdom)
      obtain ⟨y', hy', hy'f⟩ := isPreconnected_inter_frontier hpc ⟨x, hxk, hxR⟩ ⟨y, hy, hyR⟩
      exact ⟨y', hy'f, hcdiam' k z hz x hxk y' hy'⟩
    · left
      obtain ⟨k, w, hw, hd⟩ := chart_pool_near_boundary24 hδ hh hdom2 hbi g hcover x
        (fun k z hz hdisj hxk => hgood ⟨k, z, hz, hdisj, hxk⟩)
      exact mem_iUnion.mpr ⟨k, w, hw, hd⟩
  have hN₀area : (sphereAreaD 24) N₀ ≤ ENNReal.ofReal (K*(C*(2*(Real.sqrt 24*h)))) := by
    calc (sphereAreaD 24) N₀ ≤ ∑ k : Fin K, (sphereAreaD 24) {x : SphereD 24 | ∃ w ∈ cubeBdry24 δ,
          dist (x : AmbientD 24) (g k (equalAreaPhiD w)) ≤ 2*(Real.sqrt 24*h)} := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _k : Fin K, ENNReal.ofReal (C*(2*(Real.sqrt 24*h))) :=
          Finset.sum_le_sum fun k _ => hmink (g k) _ (by positivity) hρ
      _ = ENNReal.ofReal (K*(C*(2*(Real.sqrt 24*h)))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  -- the pool probability
  have hPbound : (sphereProbabilityD 24).real P ≤ (K*(C*(2*(Real.sqrt 24*h)))+MR)/A+1/N := by
    have hsub : P ⊆ (R \ ⋃ q ∈ G₀, cell q) ∪ ⋃ q ∈ G₀ \ G, cell q := by
      rintro x ⟨hxR, hxU⟩
      by_cases hx0 : x ∈ ⋃ q ∈ G₀, cell q
      · right
        obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp hx0
        refine mem_iUnion₂.mpr ⟨q, Finset.mem_sdiff.mpr ⟨hq, fun hqG => hxU ?_⟩, hxq⟩
        exact mem_iUnion₂.mpr ⟨q, hqG, hxq⟩
      · left; exact ⟨hxR, hx0⟩
    have hdiff : (G₀ \ G).card ≤ 1 := by
      rw [Finset.card_sdiff_of_subset hGsub, hGcard]
      omega
    have h1 : (sphereProbabilityD 24).real P ≤ (sphereProbabilityD 24).real (R \ ⋃ q ∈ G₀, cell q)+
        (sphereProbabilityD 24).real (⋃ q ∈ G₀ \ G, cell q) :=
      (measureReal_mono hsub).trans (measureReal_union_le _ _)
    have h2 : (sphereProbabilityD 24).real (R \ ⋃ q ∈ G₀, cell q) ≤
        (K*(C*(2*(Real.sqrt 24*h)))+MR)/A := by
      rw [sphereProbability24_real_eq_area, ← hAdef]
      apply div_le_div_of_nonneg_right _ hA.le
      have hm : (sphereAreaD 24) (R \ ⋃ q ∈ G₀, cell q) ≤
          ENNReal.ofReal (K*(C*(2*(Real.sqrt 24*h)))+MR) := by
        calc (sphereAreaD 24) (R \ ⋃ q ∈ G₀, cell q) ≤ (sphereAreaD 24) (N₀ ∪ NR) := measure_mono hP₀
          _ ≤ (sphereAreaD 24) N₀+(sphereAreaD 24) NR := measure_union_le _ _
          _ ≤ ENNReal.ofReal (K*(C*(2*(Real.sqrt 24*h))))+ENNReal.ofReal MR := add_le_add hN₀area hRmink
          _ = ENNReal.ofReal (K*(C*(2*(Real.sqrt 24*h)))+MR) :=
              (ENNReal.ofReal_add (by positivity) hMR).symm
      calc (sphereAreaD 24).real (R \ ⋃ q ∈ G₀, cell q) ≤
            (ENNReal.ofReal (K*(C*(2*(Real.sqrt 24*h)))+MR)).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
        _ = K*(C*(2*(Real.sqrt 24*h)))+MR := ENNReal.toReal_ofReal (by positivity)
    have h3 : (sphereProbabilityD 24).real (⋃ q ∈ G₀ \ G, cell q) ≤ 1/N := by
      have hdj : Set.PairwiseDisjoint (↑(G₀ \ G)) cell :=
        hcdisj.subset (by exact_mod_cast Finset.sdiff_subset)
      rw [measureReal_biUnion_finset hdj (fun q hq => hcm q (Finset.mem_sdiff.mp hq).1),
        Finset.sum_congr rfl (fun q hq => hcprob q (Finset.mem_sdiff.mp hq).1),
        Finset.sum_const, nsmul_eq_mul]
      have : ((G₀ \ G).card:ℝ) ≤ 1 := by exact_mod_cast hdiff
      have h0 : (0:ℝ) ≤ 1/N := by positivity
      nlinarith
    linarith
  have hnbound : (n:ℝ) ≤ N*(K*(C*(2*(Real.sqrt 24*h)))+MR)/A+1 := by
    have h1 : (n:ℝ)/N ≤ (K*(C*(2*(Real.sqrt 24*h)))+MR)/A+1/N := hPprob ▸ hPbound
    rw [div_le_iff₀ hNR] at h1
    have : ((K*(C*(2*(Real.sqrt 24*h)))+MR)/A+1/N)*N = N*(K*(C*(2*(Real.sqrt 24*h)))+MR)/A+1 := by
      field_simp
    linarith
  -- split the pool
  obtain ⟨PC, dmP, hPCm, hPCd, hPCu, hPCmass, hPCdiam, hPCsum⟩ :=
    sphere24_pool_partition hPm hH hn
  -- assemble
  have hcardG : Fintype.card (↥G ⊕ Fin n) = r := by
    rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin, hndef]
    omega
  let e := Fintype.equivFinOfCardEq hcardG
  let Cl : Fin r → Set (SphereD 24) := fun j => Sum.elim (fun q : ↥G => cell q.1) PC (e.symm j)
  let dm : Fin r → ℝ := fun j => Sum.elim (fun _ : ↥G => 2*(Real.sqrt 24*h)) dmP (e.symm j)
  have hPCsub : ∀ i, PC i ⊆ P := fun i x hx => hPCu ▸ mem_iUnion.mpr ⟨i, hx⟩
  refine ⟨Cl, dm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    simp only [Cl]
    cases e.symm j with
    | inl q => exact hcm q.1 (hGsub q.2)
    | inr i => exact hPCm i
  · intro i j hij
    simp only [Cl]
    have hne : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
    revert hne
    cases e.symm i with
    | inl q =>
      cases e.symm j with
      | inl q' =>
        intro hne
        have hqq : q.1 ≠ q'.1 := fun h => hne (by rw [Subtype.ext h])
        exact hGdisj q.2 q'.2 hqq
      | inr i' =>
        intro _
        apply Disjoint.mono_right (hPCsub i')
        rw [hPdef]
        exact (disjoint_sdiff_right).mono_left (subset_biUnion_of_mem (u := cell) q.2)
    | inr i' =>
      cases e.symm j with
      | inl q =>
        intro _
        apply Disjoint.mono_left (hPCsub i')
        rw [hPdef]
        exact (disjoint_sdiff_left).mono_right (subset_biUnion_of_mem (u := cell) q.2)
      | inr j' =>
        intro hne
        have : i' ≠ j' := fun h => hne (by rw [h])
        exact hPCd this
  · apply Subset.antisymm
    · apply iUnion_subset
      intro j
      simp only [Cl]
      cases e.symm j with
      | inl q => exact hG₀R q.1 (hGsub q.2)
      | inr i => exact (hPCsub i).trans sdiff_subset
    · intro x hxR
      by_cases hx : x ∈ U
      · obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp hx
        refine mem_iUnion.mpr ⟨e (Sum.inl ⟨q, hq⟩), ?_⟩
        simp only [Cl, Equiv.symm_apply_apply, Sum.elim_inl]
        exact hxq
      · have hxP : x ∈ P := ⟨hxR, hx⟩
        rw [← hPCu] at hxP
        obtain ⟨i, hi⟩ := mem_iUnion.mp hxP
        refine mem_iUnion.mpr ⟨e (Sum.inr i), ?_⟩
        simp only [Cl, Equiv.symm_apply_apply, Sum.elim_inr]
        exact hi
  · intro j
    simp only [Cl]
    cases e.symm j with
    | inl q => exact hcprob q.1 (hGsub q.2)
    | inr i =>
      simp only [Sum.elim_inr]
      rw [hPCmass i, hPprob]
      have hnR : (0:ℝ) < n := by exact_mod_cast hn
      field_simp
  · intro j x hx y hy
    simp only [Cl, dm] at hx hy ⊢
    cases hj : e.symm j with
    | inl q =>
      rw [hj] at hx hy
      exact hcdiam q.1 (hGsub q.2) x hx y hy
    | inr i =>
      rw [hj] at hx hy
      exact hPCdiam i x hx y hy
  · have hsum : ∑ j, (dm j)^2 = ∑ u : ↥G ⊕ Fin n,
        (Sum.elim (fun _ : ↥G => 2*(Real.sqrt 24*h)) dmP u)^2 := by
      rw [← e.symm.sum_comp]
    rw [hsum, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
      nsmul_eq_mul]
    have hs24 : Real.sqrt 24^2 = 24 := Real.sq_sqrt (by norm_num)
    have hgood : (G.card:ℝ)*(2*(Real.sqrt 24*h))^2 ≤ 96*h^2*r := by
      have : (G.card:ℝ) ≤ r := by exact_mod_cast (hGr.trans (Nat.sub_le r 1))
      have e1 : (2*(Real.sqrt 24*h))^2 = 96*h^2 := by rw [mul_pow, mul_pow, hs24]; ring
      rw [e1]
      have h96 : (0:ℝ) ≤ 96*h^2 := by positivity
      calc (G.card:ℝ)*(96*h^2) ≤ r*(96*h^2) := mul_le_mul_of_nonneg_right this h96
        _ = 96*h^2*r := by ring
    have hpool : ∑ i, (dmP i)^2 ≤ (5*H)^2*(N*(K*(C*(2*(Real.sqrt 24*h)))+MR)/A+1)+
        4*(2*⌈1/H⌉₊+1)^25 := by
      have h3 : (n:ℝ)*(5*H)^2 ≤ (5*H)^2*(N*(K*(C*(2*(Real.sqrt 24*h)))+MR)/A+1) := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left hnbound (by positivity)
      linarith
    linarith

set_option maxHeartbeats 1000000 in
/-- The scale arithmetic of the residual construction: with `c h² = π`, `h^24 = A/N`, pool scale
`τ√h` and `h` small in terms of `ε` and `τ`, the cost is at most `96π r + ε N`. -/
theorem residual_stratification_arith24 {A Q c h N r S τ ε : ℝ} (hA : 0 < A) (hQ : 0 ≤ Q)
    (hh : 0 < h) (hh1 : h ≤ 1) (hN : 0 < N) (hh24 : h^24 = A/N) (hch : c*h^2 = Real.pi)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (_hε : 0 < ε)
    (hτQ : 25*Real.pi*τ^2*Q/A ≤ ε/3) (hh2 : h ≤ ε*A/(75*Real.pi))
    (hh3 : h ≤ ε*A*τ^25/(12*5^25*Real.pi))
    (hS : S ≤ 96*h^2*r+(5*(τ*Real.sqrt h))^2*(N*(Q*h)/A+1)+
      4*(2*(⌈1/(τ*Real.sqrt h)⌉₊:ℝ)+1)^25) :
    c*S ≤ 96*Real.pi*r+ε*N := by
  have hcval : c = Real.pi/h^2 := (eq_div_iff (by positivity)).mpr hch
  have hc0 : 0 < c := by rw [hcval]; positivity
  have hsh : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  have hsh1 : Real.sqrt h ≤ 1 := by
    have := Real.sqrt_le_sqrt hh1
    rwa [Real.sqrt_one] at this
  have hsq : Real.sqrt h^2 = h := Real.sq_sqrt hh.le
  have hNh24 : N*h^24 = A := by rw [hh24]; field_simp
  -- the good cells
  have hT1 : c*(96*h^2*r) = 96*Real.pi*r := by rw [← hch]; ring
  -- the pool cells
  have hT2 : c*((5*(τ*Real.sqrt h))^2*(N*(Q*h)/A+1)) ≤ ε/3*N+ε/3*N := by
    have e1 : c*((5*(τ*Real.sqrt h))^2*(N*(Q*h)/A+1)) =
        25*Real.pi*τ^2*Q/A*N+25*Real.pi*τ^2/h := by
      rw [mul_pow, mul_pow, hsq, hcval]
      field_simp
      norm_num
    rw [e1]
    have h1 : 25*Real.pi*τ^2*Q/A*N ≤ ε/3*N := mul_le_mul_of_nonneg_right hτQ hN.le
    have hτ2 : τ^2 ≤ 1 := by nlinarith
    have h2 : 25*Real.pi*τ^2/h ≤ 25*Real.pi/h := by
      apply div_le_div_of_nonneg_right _ hh.le
      nlinarith [Real.pi_pos]
    have h23 : h^23 ≤ h := by
      calc h^23 ≤ h^1 := pow_le_pow_of_le_one hh.le hh1 (by norm_num)
        _ = h := pow_one h
    have h3 : 25*Real.pi*h^23 ≤ ε/3*N*h*h^23 := by
      have e2 : ε/3*N*h*h^23 = ε/3*(N*h^24) := by ring
      rw [e2, hNh24]
      have h75 : 75*Real.pi*h ≤ ε*A := by
        rw [le_div_iff₀ (by positivity)] at hh2
        linarith
      calc 25*Real.pi*h^23 ≤ 25*Real.pi*h := mul_le_mul_of_nonneg_left h23 (by positivity)
        _ ≤ ε/3*A := by linarith
    have h4 : 25*Real.pi ≤ ε/3*N*h := le_of_mul_le_mul_right h3 (pow_pos hh 23)
    have h5 : 25*Real.pi/h ≤ ε/3*N := by
      rw [div_le_iff₀ hh]
      linarith
    linarith
  -- the coarse grid term
  have hT3 : c*(4*(2*(⌈1/(τ*Real.sqrt h)⌉₊:ℝ)+1)^25) ≤ ε/3*N := by
    have hx : 0 < τ*Real.sqrt h := by positivity
    have hx1 : τ*Real.sqrt h ≤ 1 := by nlinarith
    have hceil : 2*(⌈1/(τ*Real.sqrt h)⌉₊:ℝ)+1 ≤ 5/(τ*Real.sqrt h) := by
      have h1 := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 1/(τ*Real.sqrt h) by positivity)
      have h2 : (1:ℝ) ≤ 1/(τ*Real.sqrt h) := by rw [le_div_iff₀ hx]; linarith
      have : (5:ℝ)/(τ*Real.sqrt h) = 5*(1/(τ*Real.sqrt h)) := by ring
      rw [this]
      linarith
    have h1 : (2*(⌈1/(τ*Real.sqrt h)⌉₊:ℝ)+1)^25 ≤ (5/(τ*Real.sqrt h))^25 :=
      pow_le_pow_left₀ (by positivity) hceil 25
    have hs25 : Real.sqrt h^25 = h^12*Real.sqrt h := by
      rw [show 25 = 2*12+1 by norm_num, pow_succ, pow_mul, hsq]
    have e : c*(5/(τ*Real.sqrt h))^25 = 5^25*Real.pi/(h^14*τ^25*Real.sqrt h) := by
      rw [hcval, div_pow, mul_pow, hs25]
      field_simp
    have key : 4*(5^25*Real.pi)*h^24 ≤ ε/3*A*(h^14*τ^25*Real.sqrt h) := by
      have hh3' : 12*5^25*Real.pi*h ≤ ε*A*τ^25 := by
        rw [le_div_iff₀ (by positivity)] at hh3
        linarith
      have hh2s : h^2 ≤ h*Real.sqrt h := by
        have : h^2 = h*(Real.sqrt h*Real.sqrt h) := by rw [← sq, hsq]; ring
        rw [this]
        have : Real.sqrt h*Real.sqrt h ≤ Real.sqrt h := by nlinarith
        exact mul_le_mul_of_nonneg_left this hh.le
      have hh10s : h^10 ≤ h*Real.sqrt h := by
        have : h^10 ≤ h^2 := pow_le_pow_of_le_one hh.le hh1 (by norm_num)
        linarith
      have e3 : 4*(5^25*Real.pi)*h^24 = h^14*(4*(5^25*Real.pi)*h^10) := by ring
      have e4 : ε/3*A*(h^14*τ^25*Real.sqrt h) = h^14*(ε/3*A*τ^25*Real.sqrt h) := by ring
      rw [e3, e4]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc 4*(5^25*Real.pi)*h^10 ≤ 4*(5^25*Real.pi)*(h*Real.sqrt h) :=
            mul_le_mul_of_nonneg_left hh10s (by positivity)
        _ = (12*5^25*Real.pi*h)/3*Real.sqrt h := by ring
        _ ≤ (ε*A*τ^25)/3*Real.sqrt h := by
            apply mul_le_mul_of_nonneg_right _ hsh.le
            linarith
        _ = ε/3*A*τ^25*Real.sqrt h := by ring
    have h2 : 4*(c*(5/(τ*Real.sqrt h))^25) ≤ ε/3*N := by
      rw [e]
      have hD : 0 < h^14*τ^25*Real.sqrt h := by positivity
      have e5 : 4*(5^25*Real.pi/(h^14*τ^25*Real.sqrt h)) =
          4*(5^25*Real.pi)/(h^14*τ^25*Real.sqrt h) := by
        ring
      rw [e5, div_le_iff₀ hD]
      have e6 : ε/3*N*(h^14*τ^25*Real.sqrt h)*h^24 = ε/3*A*(h^14*τ^25*Real.sqrt h) := by
        rw [← hNh24]; ring
      exact le_of_mul_le_mul_right (by rw [e6]; exact key) (pow_pos hh 24)
    have h3 : c*(2*(⌈1/(τ*Real.sqrt h)⌉₊:ℝ)+1)^25 ≤ c*(5/(τ*Real.sqrt h))^25 :=
      mul_le_mul_of_nonneg_left h1 hc0.le
    calc c*(4*(2*(⌈1/(τ*Real.sqrt h)⌉₊:ℝ)+1)^25) =
          4*(c*(2*(⌈1/(τ*Real.sqrt h)⌉₊:ℝ)+1)^25) := by
          ring
      _ ≤ ε/3*N := by linarith
  have hexp : c*(96*h^2*r+(5*(τ*Real.sqrt h))^2*(N*(Q*h)/A+1)+
      4*(2*(⌈1/(τ*Real.sqrt h)⌉₊:ℝ)+1)^25) = c*(96*h^2*r)+
        c*((5*(τ*Real.sqrt h))^2*(N*(Q*h)/A+1))+c*(4*(2*(⌈1/(τ*Real.sqrt h)⌉₊:ℝ)+1)^25) := by
    ring
  have hcS := mul_le_mul_of_nonneg_left hS hc0.le
  linarith

theorem sphereProbability24_eq_div_of_real {s R : Set (SphereD 24)} {N r : ℕ} (hN : 0 < N)
    (hr : 0 < r) (hrN : (r:ℝ) = N*(sphereProbabilityD 24).real R)
    (hs : (sphereProbabilityD 24).real s = 1/N) :
    (sphereProbabilityD 24) s = (sphereProbabilityD 24) R/(r:ℝ≥0∞) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hσR : 0 < (sphereProbabilityD 24).real R := by
    by_contra hle
    have h0 : (sphereProbabilityD 24).real R ≤ 0 := not_lt.mp hle
    nlinarith
  have hfin1 : (sphereProbabilityD 24) s ≠ ⊤ := measure_ne_top _ _
  have hfin2 : (sphereProbabilityD 24) R/(r:ℝ≥0∞) ≠ ⊤ :=
    ENNReal.div_ne_top (measure_ne_top _ _) (by exact_mod_cast hr.ne')
  rw [← ENNReal.toReal_eq_toReal_iff' hfin1 hfin2, ENNReal.toReal_div, ENNReal.toReal_natCast]
  change (sphereProbabilityD 24).real s = (sphereProbabilityD 24).real R/r
  rw [hs, hrN]
  field_simp

set_option maxHeartbeats 1000000 in
/-- A measurable region of `S²⁴` whose frontier has a linear Minkowski bound is stratifiable at
the density scale with the absolute constant `96π = 4·24·π`. -/
theorem negStratifiable24_of_frontier_minkowski {R : Set (SphereD 24)} (hRm : MeasurableSet R)
    {CR : ℝ} (hCR : 0 ≤ CR)
    (hRmink : ∀ ρ : ℝ, 0 < ρ →
      (sphereAreaD 24) {x : SphereD 24 | ∃ y ∈ frontier R, dist x y ≤ ρ} ≤
        ENNReal.ofReal (CR*ρ)) :
    NegStratifiable24 R (96*Real.pi) := by
  classical
  obtain ⟨δ, hδ, C, hC, ρ₁, hρ₁, hdom2, hbi, hmink⟩ := chart_boundary_minkowski24
  have hCdom : chartCube24 δ ⊆ equalAreaChartDomainD := fun p hp =>
    hdom2 p (fun i => (hp i).trans (by linarith))
  obtain ⟨K, g, hcover⟩ := sphere24_finite_chart_cover hδ hCdom
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = (sphereAreaD 24).real univ := ⟨_, rfl⟩
  have hA : 0 < A := by rw [hAdef]; exact sphereAreaD_univ_pos 24
  have hs24 : 0 < Real.sqrt 24 := by positivity
  intro ε hε
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = ((K:ℝ)*C+CR)*(2*Real.sqrt 24) := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  -- the pool scale factor
  obtain ⟨τ, hτ0, hτ1, hτQ⟩ : ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ 25*Real.pi*τ^2*Q/A ≤ ε/3 := by
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = min 1 (ε*A/(75*Real.pi*(Q+1))) := ⟨_, rfl⟩
    have ht0 : 0 < t := by rw [ht]; exact lt_min one_pos (by positivity)
    have ht1 : t ≤ 1 := by rw [ht]; exact min_le_left _ _
    have ht2 : t ≤ ε*A/(75*Real.pi*(Q+1)) := by rw [ht]; exact min_le_right _ _
    refine ⟨Real.sqrt t, Real.sqrt_pos.mpr ht0, ?_, ?_⟩
    · have := Real.sqrt_le_sqrt ht1
      rwa [Real.sqrt_one] at this
    · rw [Real.sq_sqrt ht0.le, div_le_iff₀ hA]
      rw [le_div_iff₀ (by positivity)] at ht2
      have hQQ : Q ≤ Q+1 := by linarith
      have h1 : 75*Real.pi*(t*Q) ≤ 75*Real.pi*(t*(Q+1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQQ ht0.le) (by positivity)
      nlinarith [Real.pi_pos]
  -- the threshold scale
  obtain ⟨h₁, hh₁⟩ : ∃ h₁ : ℝ, h₁ = min (min 1 (ρ₁/(2*Real.sqrt 24)))
      (min (ε*A/(75*Real.pi)) (ε*A*τ^25/(12*5^25*Real.pi))) := ⟨_, rfl⟩
  have hh₁pos : 0 < h₁ := by
    rw [hh₁]
    exact lt_min (lt_min one_pos (by positivity)) (lt_min (by positivity) (by positivity))
  refine ⟨⌈A/h₁^24⌉₊, fun N r hN hr hrN => ?_⟩
  have hNle : A/h₁^24 ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hNpos : 0 < N := by
    have : (0:ℝ) < N := lt_of_lt_of_le (by positivity) hNle
    exact_mod_cast this
  have hNR : (0:ℝ) < N := by exact_mod_cast hNpos
  obtain ⟨h, hh, hh24⟩ : ∃ h : ℝ, 0 < h ∧ h^24 = A/N := by
    refine ⟨(A/N)^((1:ℝ)/24), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hhh₁ : h ≤ h₁ := by
    have h24 : h^24 ≤ h₁^24 := by
      rw [hh24, div_le_iff₀ hNR]
      rw [div_le_iff₀ (by positivity)] at hNle
      linarith
    exact le_of_pow_le_pow_left₀ (by norm_num) hh₁pos.le h24
  have hh1 : h ≤ 1 := hhh₁.trans (by rw [hh₁]; exact (min_le_left _ _).trans (min_le_left _ _))
  have hhρ : h ≤ ρ₁/(2*Real.sqrt 24) :=
    hhh₁.trans (by rw [hh₁]; exact (min_le_left _ _).trans (min_le_right _ _))
  have hh2 : h ≤ ε*A/(75*Real.pi) :=
    hhh₁.trans (by rw [hh₁]; exact (min_le_right _ _).trans (min_le_left _ _))
  have hh3 : h ≤ ε*A*τ^25/(12*5^25*Real.pi) :=
    hhh₁.trans (by rw [hh₁]; exact (min_le_right _ _).trans (min_le_right _ _))
  have hρ : 2*(Real.sqrt 24*h) ≤ ρ₁ := by
    rw [le_div_iff₀ (by positivity)] at hhρ
    linarith
  have hh24' : h^24 = (sphereAreaD 24).real univ/N := by rw [hh24, hAdef]
  have hch := sphereGaussianDensityFactor24_mul_sq hNpos hh hh24'
  have hRm' := hRmink (2*(Real.sqrt 24*h)) (by positivity)
  obtain ⟨Cl, dm, hm, hd, hu, hmass, hdiam, hsum⟩ := sphere24_region_chart_partition hδ hC hdom2
    hbi hmink g hcover hRm hh (by positivity : 0 ≤ CR*(2*(Real.sqrt 24*h))) hRm' hNpos hr hrN
    hh24' hρ (by positivity : 0 < τ*Real.sqrt h)
  refine ⟨Cl, dm, hm, hd, hu,
    fun j => sphereProbability24_eq_div_of_real hNpos hr hrN (hmass j), hdiam, ?_⟩
  rw [← Finset.mul_sum]
  have hsum2 : ∑ j, (dm j)^2 ≤ 96*h^2*r+(5*(τ*Real.sqrt h))^2*(N*(Q*h)/A+1)+
      4*(2*(⌈1/(τ*Real.sqrt h)⌉₊:ℝ)+1)^25 := by
    have e : (N:ℝ)*(Q*h) = N*(K*(C*(2*(Real.sqrt 24*h)))+CR*(2*(Real.sqrt 24*h))) := by
      rw [hQ]; ring
    rw [e, hAdef]
    exact hsum
  have := residual_stratification_arith24 hA hQ0 hh hh1 hNR hh24 hch hτ0 hτ1 hε hτQ hh2 hh3 hsum2
  linarith

/-- The complement of any finite union of small Leech cube patches is stratifiable at the density
scale with the absolute constant `96π`. -/
theorem negStratifiable24_patch_complement {K : ℕ} (P : Fin K → SmallLeechCubePatch24) :
    NegStratifiable24 (⋃ i, smallLeechSpherePatch24 (P i))ᶜ (96*Real.pi) := by
  obtain ⟨C, hC, hmink⟩ := patchComplement_frontier_minkowski24 P
  have hm : MeasurableSet (⋃ i, smallLeechSpherePatch24 (P i))ᶜ :=
    (MeasurableSet.iUnion fun i =>
      (smallLeechSpherePatch24_isCompact (P i)).isClosed.measurableSet).compl
  exact negStratifiable24_of_frontier_minkowski hm hC hmink

theorem NegStratifiable24.mono {A : Set (SphereD 24)} {B B' : ℝ} (h : NegStratifiable24 A B)
    (hB : B ≤ B') : NegStratifiable24 A B' := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := h ε hε
  refine ⟨N₀, fun N r hN hr hrN => ?_⟩
  obtain ⟨C, dm, h1, h2, h3, h4, h5, h6⟩ := hN₀ N r hN hr hrN
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  exact ⟨C, dm, h1, h2, h3, h4, h5, h6.trans (by nlinarith)⟩

theorem SphereStratifiable24.mono {B B' : ℝ} (h : SphereStratifiable24 B) (hB : B ≤ B') :
    SphereStratifiable24 B' := by
  intro r hr
  obtain ⟨C, dm, h1, h2, h3, h4, h5, h6⟩ := h r hr
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  exact ⟨C, dm, h1, h2, h3, h4, h5, h6.trans (by nlinarith)⟩

/-- Both stratification hypotheses hold on `S²⁴` with one absolute constant. -/
theorem sphere24_stratification_hypotheses : ∃ B : ℝ, 0 ≤ B ∧
    (∀ {K : ℕ} (P : Fin K → SmallLeechCubePatch24),
      NegStratifiable24 (⋃ i, smallLeechSpherePatch24 (P i))ᶜ B) ∧ SphereStratifiable24 B := by
  obtain ⟨B₁, hB₁, hsph⟩ := sphere24_stratifiable
  exact ⟨max (96*Real.pi) B₁, le_max_of_le_right hB₁,
    fun P => (negStratifiable24_patch_complement P).mono (le_max_left _ _),
    hsph.mono (le_max_right _ _)⟩

end SphericalRiesz
end
end
