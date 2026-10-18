import Riesz.SphereStratification8
import Riesz.PatchBoundaryMinkowski8
import Riesz.SphereCapDiscrepancyUpper8
import Riesz.SphereLogUpper8

/-! Exact-mass stratification of residual regions (stage NEG).

For a measurable region `R ⊆ S⁸` whose frontier has a linear Minkowski bound, and `r = N σ(R)`,
take the rotated chart grid boxes of side `h`, `h^8 = A/N`, whose images lie inside `R`: they
have mass exactly `1/N` and diameter at most `2√8 h`; at most `r - 1` are kept. A box image meeting
both `R` and its complement meets the frontier of `R` (it is preconnected), so the rest of `R`
lies within `2√8 h` of the chart cube boundaries or of the frontier of `R`, and has mass `O(h)`.
It is split into exact-mass cells by the pool partition at scale `τ√h`. With `c_N h² = π`, the
good cells cost at most `32π r`, and for fixed `τ` with `9πτ²Q/A ≤ ε/3` the pool costs at most
`ε N` once `N` is large: `NegStratifiable8 R (32π)`. The complement of any finite union of small
E8 cube patches qualifies, so both stratification hypotheses of the negative-exponent,
discrepancy and logarithmic theorems are discharged. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal
namespace SphericalRiesz

set_option maxHeartbeats 1000000 in
/-- The chart partition of a measurable region `R` into `r` cells of mass `1/N`, for small `h`. -/
theorem sphere8_region_chart_partition {δ C ρ₁ : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (hdom2 : ∀ p : Fin 8 → ℝ, (∀ i, |p i| ≤ 2*δ) → p ∈ equalAreaChartDomain)
    (hbi : ∀ p q : Fin 8 → ℝ, (∀ i, |p i| ≤ 2*δ) → (∀ i, |q i| ≤ 2*δ) →
      dist (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 q) ≤
        2*dist (equalAreaPhi p) (equalAreaPhi q) ∧
      dist (equalAreaPhi p) (equalAreaPhi q) ≤
        2*dist (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 q))
    (hmink : ∀ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9, ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₁ →
      sphereArea8 {x : Sphere8 | ∃ w ∈ cubeBdry8 δ, dist (x:Ambient9) (g (equalAreaPhi w)) ≤ ρ} ≤
        ENNReal.ofReal (C*ρ))
    {K : ℕ} (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (hcover : ∀ x : Sphere8, ∃ k, x ∈ chartImage8 (g k) (chartCubeOpen8 δ))
    {R : Set Sphere8} (hRm : MeasurableSet R) {h : ℝ} (hh : 0 < h) {MR : ℝ} (hMR : 0 ≤ MR)
    (hRmink : sphereArea8 {x : Sphere8 | ∃ y ∈ frontier R, dist x y ≤ 2*(Real.sqrt 8*h)} ≤
      ENNReal.ofReal MR)
    {N r : ℕ} (hN : 0 < N) (hr : 0 < r) (hrN : (r:ℝ) = N*sphereProbability8.real R)
    (hh8 : h^8 = sphereArea8.real univ/N) (hρ : 2*(Real.sqrt 8*h) ≤ ρ₁) {H : ℝ} (hH : 0 < H) :
    ∃ Cl : Fin r → Set Sphere8, ∃ dm : Fin r → ℝ,
      (∀ j, MeasurableSet (Cl j)) ∧ Pairwise (fun i j => Disjoint (Cl i) (Cl j)) ∧
      (⋃ j, Cl j) = R ∧ (∀ j, sphereProbability8.real (Cl j) = 1/N) ∧
      (∀ j, ∀ x ∈ Cl j, ∀ y ∈ Cl j, dist x y ≤ dm j) ∧
      ∑ j, (dm j)^2 ≤ 32*h^2*r+(3*H)^2*(N*(K*(C*(2*(Real.sqrt 8*h)))+MR)/sphereArea8.real univ+1)+
        4*(2*⌈1/H⌉₊+1)^9 := by
  classical
  set A := sphereArea8.real univ with hAdef
  have hA : 0 < A := by rw [hAdef, sphereArea8_mass_real]; positivity
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hC2 : ∀ p ∈ chartCube8 δ, ∀ i, |p i| ≤ 2*δ := fun p hp i => (hp i).trans (by linarith)
  have hCdom : chartCube8 δ ⊆ equalAreaChartDomain := fun p hp => hdom2 p (hC2 p hp)
  set Zall := (gridBox8_inside_cube_finite (δ := δ) hh).toFinset with hZall
  have hZmem : ∀ z, z ∈ Zall ↔ gridBox8 h z ⊆ chartCube8 δ := fun z => by
    rw [hZall, Set.Finite.mem_toFinset]; rfl
  let earlier : Fin K → Set Sphere8 := fun k =>
    ⋃ j ∈ Finset.univ.filter (fun j : Fin K => j < k), chartImage8 (g j) (chartCube8 δ)
  let cell : Fin K × (Fin 8 → ℤ) → Set Sphere8 := fun q => chartImage8 (g q.1) (gridBox8 h q.2)
  set G₀ := (Finset.univ ×ˢ Zall).filter (fun q => Disjoint (cell q) (earlier q.1) ∧ cell q ⊆ R)
    with hG₀
  have hG₀box : ∀ q ∈ G₀, gridBox8 h q.2 ⊆ chartCube8 δ := by
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
    chartImage8_measurable (g q.1) (gridBox8_measurable h q.2) ((hG₀box q hq).trans hCdom)
  have hcprob : ∀ q ∈ G₀, sphereProbability8.real (cell q) = 1/N := by
    intro q hq
    rw [sphereProbability8_real_eq_area, Measure.real, chartImage8_area (g q.1)
      (gridBox8_measurable h q.2) ((hG₀box q hq).trans hCdom), gridBox8_volume hh,
      ENNReal.toReal_ofReal (by positivity), hh8, ← hAdef]
    field_simp
  have hcdisj : Set.PairwiseDisjoint (↑G₀) cell := by
    intro q hq q' hq' hne
    show Disjoint (cell q) (cell q')
    by_cases hk : q.1 = q'.1
    · have hz : q.2 ≠ q'.2 := fun hz => hne (Prod.ext hk hz)
      show Disjoint (chartImage8 (g q.1) (gridBox8 h q.2)) (chartImage8 (g q'.1) (gridBox8 h q'.2))
      rw [← hk]
      exact chartImage8_disjoint (g q.1) ((hG₀box q hq).trans hCdom)
        ((hG₀box q' hq').trans hCdom) (gridBox8_disjoint hh hz)
    · rcases lt_or_gt_of_ne hk with hlt | hlt
      · have hsub : cell q ⊆ earlier q'.1 := by
          intro x hx
          refine mem_iUnion₂.mpr ⟨q.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, ?_⟩
          exact chartImage8_mono (g q.1) (hG₀box q hq) hx
        exact (hG₀good q' hq').symm.mono_left hsub
      · have hsub : cell q' ⊆ earlier q.1 := by
          intro x hx
          refine mem_iUnion₂.mpr ⟨q'.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, ?_⟩
          exact chartImage8_mono (g q'.1) (hG₀box q' hq') hx
        exact (hG₀good q hq).mono_right hsub
  have hcdiam' : ∀ k : Fin K, ∀ z, gridBox8 h z ⊆ chartCube8 δ →
      ∀ x ∈ chartImage8 (g k) (gridBox8 h z), ∀ y ∈ chartImage8 (g k) (gridBox8 h z),
        dist x y ≤ 2*(Real.sqrt 8*h) := by
    intro k z hz x hx y hy
    obtain ⟨p, hp, hxp⟩ := hx
    obtain ⟨p', hp', hyp'⟩ := hy
    rw [Subtype.dist_eq, hxp, hyp', (g k).dist_map]
    have h1 := (hbi p p' (hC2 p (hz hp)) (hC2 p' (hz hp'))).2
    have h2 := gridBox8_dist_le hh hp hp'
    linarith
  have hcdiam : ∀ q ∈ G₀, ∀ x ∈ cell q, ∀ y ∈ cell q, dist x y ≤ 2*(Real.sqrt 8*h) :=
    fun q hq => hcdiam' q.1 q.2 (hG₀box q hq)
  -- at most r good cells
  have hcard₀ : G₀.card ≤ r := by
    have hm := measureReal_biUnion_finset hcdisj hcm (μ := sphereProbability8)
    have hsubR : (⋃ q ∈ G₀, cell q) ⊆ R := iUnion₂_subset hG₀R
    have hle : sphereProbability8.real (⋃ q ∈ G₀, cell q) ≤ sphereProbability8.real R :=
      measureReal_mono hsubR
    rw [hm, Finset.sum_congr rfl hcprob, Finset.sum_const, nsmul_eq_mul] at hle
    have : (G₀.card:ℝ) ≤ r := by
      have h2 : (G₀.card:ℝ)*(1/N)*N ≤ sphereProbability8.real R*N :=
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
  have hUprob : sphereProbability8.real U = G.card/N := by
    rw [hUdef, measureReal_biUnion_finset hGdisj (fun q hq => hcm q (hGsub hq)),
      Finset.sum_congr rfl (fun q hq => hcprob q (hGsub hq)), Finset.sum_const, nsmul_eq_mul]
    ring
  have hPprob : sphereProbability8.real P = n/N := by
    have h1 := measureReal_inter_add_sdiff (μ := sphereProbability8) (s := R) hUm
    rw [inter_eq_right.mpr hUR, hUprob] at h1
    have hR : sphereProbability8.real R = r/N := by
      field_simp
      linarith
    have : ((r-G.card : ℕ):ℝ) = (r:ℝ)-G.card := by
      rw [Nat.cast_sub (by omega)]
    rw [hR] at h1
    rw [hPdef, hndef, this, sub_div]
    linarith
  -- the pool lies near the chart cube boundaries or the frontier of `R`
  set N₀ := ⋃ k : Fin K, {x : Sphere8 | ∃ w ∈ cubeBdry8 δ,
    dist (x:Ambient9) (g k (equalAreaPhi w)) ≤ 2*(Real.sqrt 8*h)} with hN₀
  set NR := {x : Sphere8 | ∃ y ∈ frontier R, dist x y ≤ 2*(Real.sqrt 8*h)} with hNRdef
  have hP₀ : R \ (⋃ q ∈ G₀, cell q) ⊆ N₀ ∪ NR := by
    rintro x ⟨hxR, hx⟩
    by_cases hgood : ∃ k : Fin K, ∃ z : Fin 8 → ℤ, gridBox8 h z ⊆ chartCube8 δ ∧
        Disjoint (chartImage8 (g k) (gridBox8 h z))
          (⋃ j ∈ Finset.univ.filter (fun j : Fin K => j < k), chartImage8 (g j) (chartCube8 δ)) ∧
        x ∈ chartImage8 (g k) (gridBox8 h z)
    · right
      obtain ⟨k, z, hz, hdisj, hxk⟩ := hgood
      have hnot : ¬ chartImage8 (g k) (gridBox8 h z) ⊆ R := by
        intro hsub
        apply hx
        refine mem_iUnion₂.mpr ⟨(k, z), ?_, hxk⟩
        rw [hG₀, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨Finset.mem_univ _, (hZmem z).mpr hz⟩, hdisj, hsub⟩
      obtain ⟨y, hy, hyR⟩ := not_subset.mp hnot
      have hpc := chartImage8_isPreconnected (g k) (gridBox8_convex h z) (hz.trans hCdom)
      obtain ⟨y', hy', hy'f⟩ := isPreconnected_inter_frontier hpc ⟨x, hxk, hxR⟩ ⟨y, hy, hyR⟩
      exact ⟨y', hy'f, hcdiam' k z hz x hxk y' hy'⟩
    · left
      obtain ⟨k, w, hw, hd⟩ := chart_pool_near_boundary hδ hh hdom2 hbi g hcover x
        (fun k z hz hdisj hxk => hgood ⟨k, z, hz, hdisj, hxk⟩)
      exact mem_iUnion.mpr ⟨k, w, hw, hd⟩
  have hN₀area : sphereArea8 N₀ ≤ ENNReal.ofReal (K*(C*(2*(Real.sqrt 8*h)))) := by
    calc sphereArea8 N₀ ≤ ∑ k : Fin K, sphereArea8 {x : Sphere8 | ∃ w ∈ cubeBdry8 δ,
          dist (x:Ambient9) (g k (equalAreaPhi w)) ≤ 2*(Real.sqrt 8*h)} := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _k : Fin K, ENNReal.ofReal (C*(2*(Real.sqrt 8*h))) :=
          Finset.sum_le_sum fun k _ => hmink (g k) _ (by positivity) hρ
      _ = ENNReal.ofReal (K*(C*(2*(Real.sqrt 8*h)))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  -- the pool probability
  have hPbound : sphereProbability8.real P ≤ (K*(C*(2*(Real.sqrt 8*h)))+MR)/A+1/N := by
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
    have h1 : sphereProbability8.real P ≤ sphereProbability8.real (R \ ⋃ q ∈ G₀, cell q)+
        sphereProbability8.real (⋃ q ∈ G₀ \ G, cell q) :=
      (measureReal_mono hsub).trans (measureReal_union_le _ _)
    have h2 : sphereProbability8.real (R \ ⋃ q ∈ G₀, cell q) ≤
        (K*(C*(2*(Real.sqrt 8*h)))+MR)/A := by
      rw [sphereProbability8_real_eq_area, ← hAdef]
      apply div_le_div_of_nonneg_right _ hA.le
      have hm : sphereArea8 (R \ ⋃ q ∈ G₀, cell q) ≤
          ENNReal.ofReal (K*(C*(2*(Real.sqrt 8*h)))+MR) := by
        calc sphereArea8 (R \ ⋃ q ∈ G₀, cell q) ≤ sphereArea8 (N₀ ∪ NR) := measure_mono hP₀
          _ ≤ sphereArea8 N₀+sphereArea8 NR := measure_union_le _ _
          _ ≤ ENNReal.ofReal (K*(C*(2*(Real.sqrt 8*h))))+ENNReal.ofReal MR := add_le_add hN₀area hRmink
          _ = ENNReal.ofReal (K*(C*(2*(Real.sqrt 8*h)))+MR) :=
              (ENNReal.ofReal_add (by positivity) hMR).symm
      calc sphereArea8.real (R \ ⋃ q ∈ G₀, cell q) ≤
            (ENNReal.ofReal (K*(C*(2*(Real.sqrt 8*h)))+MR)).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
        _ = K*(C*(2*(Real.sqrt 8*h)))+MR := ENNReal.toReal_ofReal (by positivity)
    have h3 : sphereProbability8.real (⋃ q ∈ G₀ \ G, cell q) ≤ 1/N := by
      have hdj : Set.PairwiseDisjoint (↑(G₀ \ G)) cell :=
        hcdisj.subset (by exact_mod_cast Finset.sdiff_subset)
      rw [measureReal_biUnion_finset hdj (fun q hq => hcm q (Finset.mem_sdiff.mp hq).1),
        Finset.sum_congr rfl (fun q hq => hcprob q (Finset.mem_sdiff.mp hq).1),
        Finset.sum_const, nsmul_eq_mul]
      have : ((G₀ \ G).card:ℝ) ≤ 1 := by exact_mod_cast hdiff
      have h0 : (0:ℝ) ≤ 1/N := by positivity
      nlinarith
    linarith
  have hnbound : (n:ℝ) ≤ N*(K*(C*(2*(Real.sqrt 8*h)))+MR)/A+1 := by
    have h1 : (n:ℝ)/N ≤ (K*(C*(2*(Real.sqrt 8*h)))+MR)/A+1/N := hPprob ▸ hPbound
    rw [div_le_iff₀ hNR] at h1
    have : ((K*(C*(2*(Real.sqrt 8*h)))+MR)/A+1/N)*N = N*(K*(C*(2*(Real.sqrt 8*h)))+MR)/A+1 := by
      field_simp
    linarith
  -- split the pool
  obtain ⟨PC, dmP, hPCm, hPCd, hPCu, hPCmass, hPCdiam, hPCsum⟩ :=
    sphere8_pool_partition hPm hH hn
  -- assemble
  have hcardG : Fintype.card (↥G ⊕ Fin n) = r := by
    rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin, hndef]
    omega
  let e := Fintype.equivFinOfCardEq hcardG
  let Cl : Fin r → Set Sphere8 := fun j => Sum.elim (fun q : ↥G => cell q.1) PC (e.symm j)
  let dm : Fin r → ℝ := fun j => Sum.elim (fun _ : ↥G => 2*(Real.sqrt 8*h)) dmP (e.symm j)
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
      | inr i => exact (hPCsub i).trans diff_subset
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
        (Sum.elim (fun _ : ↥G => 2*(Real.sqrt 8*h)) dmP u)^2 := by
      rw [← e.symm.sum_comp]
    rw [hsum, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
      nsmul_eq_mul]
    have hs8 : Real.sqrt 8^2 = 8 := Real.sq_sqrt (by norm_num)
    have hgood : (G.card:ℝ)*(2*(Real.sqrt 8*h))^2 ≤ 32*h^2*r := by
      have : (G.card:ℝ) ≤ r := by exact_mod_cast (hGr.trans (Nat.sub_le r 1))
      have e1 : (2*(Real.sqrt 8*h))^2 = 32*h^2 := by rw [mul_pow, mul_pow, hs8]; ring
      rw [e1]
      have h32 : (0:ℝ) ≤ 32*h^2 := by positivity
      calc (G.card:ℝ)*(32*h^2) ≤ r*(32*h^2) := mul_le_mul_of_nonneg_right this h32
        _ = 32*h^2*r := by ring
    have hpool : ∑ i, (dmP i)^2 ≤ (3*H)^2*(N*(K*(C*(2*(Real.sqrt 8*h)))+MR)/A+1)+
        4*(2*⌈1/H⌉₊+1)^9 := by
      have h3 : (n:ℝ)*(3*H)^2 ≤ (3*H)^2*(N*(K*(C*(2*(Real.sqrt 8*h)))+MR)/A+1) := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left hnbound (by positivity)
      linarith
    linarith

set_option maxHeartbeats 1000000 in
/-- The scale arithmetic of the residual construction: with `c h² = π`, `h^8 = A/N`, pool scale
`τ√h` and `h` small in terms of `ε` and `τ`, the cost is at most `32π r + ε N`. -/
theorem residual_stratification_arith {A Q c h N r S τ ε : ℝ} (hA : 0 < A) (hQ : 0 ≤ Q)
    (hh : 0 < h) (hh1 : h ≤ 1) (hN : 0 < N) (hh8 : h^8 = A/N) (hch : c*h^2 = Real.pi)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hε : 0 < ε)
    (hτQ : 9*Real.pi*τ^2*Q/A ≤ ε/3) (hh2 : h ≤ ε*A/(27*Real.pi))
    (hh3 : h ≤ ε*A*τ^9/(12*5^9*Real.pi))
    (hS : S ≤ 32*h^2*r+(3*(τ*Real.sqrt h))^2*(N*(Q*h)/A+1)+
      4*(2*(⌈1/(τ*Real.sqrt h)⌉₊:ℝ)+1)^9) :
    c*S ≤ 32*Real.pi*r+ε*N := by
  have hcval : c = Real.pi/h^2 := (eq_div_iff (by positivity)).mpr hch
  have hc0 : 0 < c := by rw [hcval]; positivity
  have hsh : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  have hsh1 : Real.sqrt h ≤ 1 := by
    have := Real.sqrt_le_sqrt hh1
    rwa [Real.sqrt_one] at this
  have hsq : Real.sqrt h^2 = h := Real.sq_sqrt hh.le
  have hNh8 : N*h^8 = A := by rw [hh8]; field_simp
  -- the good cells
  have hT1 : c*(32*h^2*r) = 32*Real.pi*r := by rw [← hch]; ring
  -- the pool cells
  have hT2 : c*((3*(τ*Real.sqrt h))^2*(N*(Q*h)/A+1)) ≤ ε/3*N+ε/3*N := by
    have e1 : c*((3*(τ*Real.sqrt h))^2*(N*(Q*h)/A+1)) =
        9*Real.pi*τ^2*Q/A*N+9*Real.pi*τ^2/h := by
      rw [mul_pow, mul_pow, hsq, hcval]
      field_simp
      norm_num
    rw [e1]
    have h1 : 9*Real.pi*τ^2*Q/A*N ≤ ε/3*N := mul_le_mul_of_nonneg_right hτQ hN.le
    have hτ2 : τ^2 ≤ 1 := by nlinarith
    have h2 : 9*Real.pi*τ^2/h ≤ 9*Real.pi/h := by
      apply div_le_div_of_nonneg_right _ hh.le
      nlinarith [Real.pi_pos]
    have h7 : h^7 ≤ h := by
      calc h^7 ≤ h^1 := pow_le_pow_of_le_one hh.le hh1 (by norm_num)
        _ = h := pow_one h
    have h3 : 9*Real.pi*h^7 ≤ ε/3*N*h*h^7 := by
      have e2 : ε/3*N*h*h^7 = ε/3*(N*h^8) := by ring
      rw [e2, hNh8]
      have : 27*Real.pi*h ≤ ε*A := by
        rw [le_div_iff₀ (by positivity)] at hh2
        linarith
      nlinarith [Real.pi_pos]
    have h4 : 9*Real.pi ≤ ε/3*N*h := le_of_mul_le_mul_right h3 (pow_pos hh 7)
    have h5 : 9*Real.pi/h ≤ ε/3*N := by
      rw [div_le_iff₀ hh]
      linarith
    linarith
  -- the coarse grid term
  have hT3 : c*(4*(2*(⌈1/(τ*Real.sqrt h)⌉₊:ℝ)+1)^9) ≤ ε/3*N := by
    have hx : 0 < τ*Real.sqrt h := by positivity
    have hx1 : τ*Real.sqrt h ≤ 1 := by nlinarith
    have hceil : 2*(⌈1/(τ*Real.sqrt h)⌉₊:ℝ)+1 ≤ 5/(τ*Real.sqrt h) := by
      have h1 := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 1/(τ*Real.sqrt h) by positivity)
      have h2 : (1:ℝ) ≤ 1/(τ*Real.sqrt h) := by rw [le_div_iff₀ hx]; linarith
      have : (5:ℝ)/(τ*Real.sqrt h) = 5*(1/(τ*Real.sqrt h)) := by ring
      rw [this]
      linarith
    have h1 : (2*(⌈1/(τ*Real.sqrt h)⌉₊:ℝ)+1)^9 ≤ (5/(τ*Real.sqrt h))^9 :=
      pow_le_pow_left₀ (by positivity) hceil 9
    have hs9 : Real.sqrt h^9 = h^4*Real.sqrt h := by
      rw [show 9 = 2*4+1 by norm_num, pow_succ, pow_mul, hsq]
    have e : c*(5/(τ*Real.sqrt h))^9 = 5^9*Real.pi/(h^6*τ^9*Real.sqrt h) := by
      rw [hcval, div_pow, mul_pow, hs9]
      field_simp
    have key : 4*(5^9*Real.pi)*h^8 ≤ ε/3*A*(h^6*τ^9*Real.sqrt h) := by
      have hh3' : 12*5^9*Real.pi*h ≤ ε*A*τ^9 := by
        rw [le_div_iff₀ (by positivity)] at hh3
        linarith
      have hh2s : h^2 ≤ h*Real.sqrt h := by
        have : h^2 = h*(Real.sqrt h*Real.sqrt h) := by rw [← sq, hsq]; ring
        rw [this]
        have : Real.sqrt h*Real.sqrt h ≤ Real.sqrt h := by nlinarith
        exact mul_le_mul_of_nonneg_left this hh.le
      have e3 : 4*(5^9*Real.pi)*h^8 = h^6*(4*(5^9*Real.pi)*h^2) := by ring
      have e4 : ε/3*A*(h^6*τ^9*Real.sqrt h) = h^6*(ε/3*A*τ^9*Real.sqrt h) := by ring
      rw [e3, e4]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc 4*(5^9*Real.pi)*h^2 ≤ 4*(5^9*Real.pi)*(h*Real.sqrt h) :=
            mul_le_mul_of_nonneg_left hh2s (by positivity)
        _ = (12*5^9*Real.pi*h)/3*Real.sqrt h := by ring
        _ ≤ (ε*A*τ^9)/3*Real.sqrt h := by
            apply mul_le_mul_of_nonneg_right _ hsh.le
            linarith
        _ = ε/3*A*τ^9*Real.sqrt h := by ring
    have h2 : 4*(c*(5/(τ*Real.sqrt h))^9) ≤ ε/3*N := by
      rw [e]
      have hD : 0 < h^6*τ^9*Real.sqrt h := by positivity
      have e5 : 4*(5^9*Real.pi/(h^6*τ^9*Real.sqrt h)) = 4*(5^9*Real.pi)/(h^6*τ^9*Real.sqrt h) := by
        ring
      rw [e5, div_le_iff₀ hD]
      have e6 : ε/3*N*(h^6*τ^9*Real.sqrt h)*h^8 = ε/3*A*(h^6*τ^9*Real.sqrt h) := by
        rw [← hNh8]; ring
      exact le_of_mul_le_mul_right (by rw [e6]; exact key) (pow_pos hh 8)
    have h3 : c*(2*(⌈1/(τ*Real.sqrt h)⌉₊:ℝ)+1)^9 ≤ c*(5/(τ*Real.sqrt h))^9 :=
      mul_le_mul_of_nonneg_left h1 hc0.le
    calc c*(4*(2*(⌈1/(τ*Real.sqrt h)⌉₊:ℝ)+1)^9) = 4*(c*(2*(⌈1/(τ*Real.sqrt h)⌉₊:ℝ)+1)^9) := by
          ring
      _ ≤ ε/3*N := by linarith
  have hexp : c*(32*h^2*r+(3*(τ*Real.sqrt h))^2*(N*(Q*h)/A+1)+
      4*(2*(⌈1/(τ*Real.sqrt h)⌉₊:ℝ)+1)^9) = c*(32*h^2*r)+
        c*((3*(τ*Real.sqrt h))^2*(N*(Q*h)/A+1))+c*(4*(2*(⌈1/(τ*Real.sqrt h)⌉₊:ℝ)+1)^9) := by
    ring
  have hcS := mul_le_mul_of_nonneg_left hS hc0.le
  linarith

theorem sphereProbability8_eq_div_of_real {s R : Set Sphere8} {N r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (hrN : (r:ℝ) = N*sphereProbability8.real R) (hs : sphereProbability8.real s = 1/N) :
    sphereProbability8 s = sphereProbability8 R/(r:ℝ≥0∞) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hσR : 0 < sphereProbability8.real R := by
    by_contra hle
    have h0 : sphereProbability8.real R ≤ 0 := not_lt.mp hle
    nlinarith
  have hfin1 : sphereProbability8 s ≠ ⊤ := measure_ne_top _ _
  have hfin2 : sphereProbability8 R/(r:ℝ≥0∞) ≠ ⊤ :=
    ENNReal.div_ne_top (measure_ne_top _ _) (by exact_mod_cast hr.ne')
  rw [← ENNReal.toReal_eq_toReal_iff' hfin1 hfin2, ENNReal.toReal_div, ENNReal.toReal_natCast]
  change sphereProbability8.real s = sphereProbability8.real R/r
  rw [hs, hrN]
  field_simp

set_option maxHeartbeats 1000000 in
/-- A measurable region whose frontier has a linear Minkowski bound is stratifiable at the
density scale with the absolute constant `32π`. -/
theorem negStratifiable8_of_frontier_minkowski {R : Set Sphere8} (hRm : MeasurableSet R)
    {CR : ℝ} (hCR : 0 ≤ CR)
    (hRmink : ∀ ρ : ℝ, 0 < ρ →
      sphereArea8 {x : Sphere8 | ∃ y ∈ frontier R, dist x y ≤ ρ} ≤ ENNReal.ofReal (CR*ρ)) :
    NegStratifiable8 R (32*Real.pi) := by
  classical
  obtain ⟨δ, hδ, C, hC, ρ₁, hρ₁, hdom2, hbi, hmink⟩ := chart_boundary_minkowski8
  have hCdom : chartCube8 δ ⊆ equalAreaChartDomain := fun p hp =>
    hdom2 p (fun i => (hp i).trans (by linarith))
  obtain ⟨K, g, hcover⟩ := sphere8_finite_chart_cover hδ hCdom
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = sphereArea8.real univ := ⟨_, rfl⟩
  have hA : 0 < A := by rw [hAdef, sphereArea8_mass_real]; positivity
  have hs8 : 0 < Real.sqrt 8 := by positivity
  intro ε hε
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = ((K:ℝ)*C+CR)*(2*Real.sqrt 8) := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  -- the pool scale factor
  obtain ⟨τ, hτ0, hτ1, hτQ⟩ : ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ 9*Real.pi*τ^2*Q/A ≤ ε/3 := by
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = min 1 (ε*A/(27*Real.pi*(Q+1))) := ⟨_, rfl⟩
    have ht0 : 0 < t := by rw [ht]; exact lt_min one_pos (by positivity)
    have ht1 : t ≤ 1 := by rw [ht]; exact min_le_left _ _
    have ht2 : t ≤ ε*A/(27*Real.pi*(Q+1)) := by rw [ht]; exact min_le_right _ _
    refine ⟨Real.sqrt t, Real.sqrt_pos.mpr ht0, ?_, ?_⟩
    · have := Real.sqrt_le_sqrt ht1
      rwa [Real.sqrt_one] at this
    · rw [Real.sq_sqrt ht0.le, div_le_iff₀ hA]
      rw [le_div_iff₀ (by positivity)] at ht2
      have hQQ : Q ≤ Q+1 := by linarith
      have h1 : 27*Real.pi*(t*Q) ≤ 27*Real.pi*(t*(Q+1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQQ ht0.le) (by positivity)
      nlinarith [Real.pi_pos]
  -- the threshold scale
  obtain ⟨h₁, hh₁⟩ : ∃ h₁ : ℝ, h₁ = min (min 1 (ρ₁/(2*Real.sqrt 8)))
      (min (ε*A/(27*Real.pi)) (ε*A*τ^9/(12*5^9*Real.pi))) := ⟨_, rfl⟩
  have hh₁pos : 0 < h₁ := by
    rw [hh₁]
    exact lt_min (lt_min one_pos (by positivity)) (lt_min (by positivity) (by positivity))
  refine ⟨⌈A/h₁^8⌉₊, fun N r hN hr hrN => ?_⟩
  have hNle : A/h₁^8 ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hNpos : 0 < N := by
    have : (0:ℝ) < N := lt_of_lt_of_le (by positivity) hNle
    exact_mod_cast this
  have hNR : (0:ℝ) < N := by exact_mod_cast hNpos
  obtain ⟨h, hh, hh8⟩ : ∃ h : ℝ, 0 < h ∧ h^8 = A/N := by
    refine ⟨(A/N)^((1:ℝ)/8), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hhh₁ : h ≤ h₁ := by
    have h8 : h^8 ≤ h₁^8 := by
      rw [hh8, div_le_iff₀ hNR]
      rw [div_le_iff₀ (by positivity)] at hNle
      linarith
    exact le_of_pow_le_pow_left₀ (by norm_num) hh₁pos.le h8
  have hh1 : h ≤ 1 := hhh₁.trans (by rw [hh₁]; exact (min_le_left _ _).trans (min_le_left _ _))
  have hhρ : h ≤ ρ₁/(2*Real.sqrt 8) :=
    hhh₁.trans (by rw [hh₁]; exact (min_le_left _ _).trans (min_le_right _ _))
  have hh2 : h ≤ ε*A/(27*Real.pi) :=
    hhh₁.trans (by rw [hh₁]; exact (min_le_right _ _).trans (min_le_left _ _))
  have hh3 : h ≤ ε*A*τ^9/(12*5^9*Real.pi) :=
    hhh₁.trans (by rw [hh₁]; exact (min_le_right _ _).trans (min_le_right _ _))
  have hρ : 2*(Real.sqrt 8*h) ≤ ρ₁ := by
    rw [le_div_iff₀ (by positivity)] at hhρ
    linarith
  have hh8' : h^8 = sphereArea8.real univ/N := by rw [hh8, hAdef]
  have hch := sphereGaussianDensityFactor8_mul_sq hNpos hh hh8'
  have hRm' := hRmink (2*(Real.sqrt 8*h)) (by positivity)
  obtain ⟨Cl, dm, hm, hd, hu, hmass, hdiam, hsum⟩ := sphere8_region_chart_partition hδ hC hdom2
    hbi hmink g hcover hRm hh (by positivity : 0 ≤ CR*(2*(Real.sqrt 8*h))) hRm' hNpos hr hrN hh8'
    hρ (by positivity : 0 < τ*Real.sqrt h)
  refine ⟨Cl, dm, hm, hd, hu,
    fun j => sphereProbability8_eq_div_of_real hNpos hr hrN (hmass j), hdiam, ?_⟩
  rw [← Finset.mul_sum]
  have hsum2 : ∑ j, (dm j)^2 ≤ 32*h^2*r+(3*(τ*Real.sqrt h))^2*(N*(Q*h)/A+1)+
      4*(2*(⌈1/(τ*Real.sqrt h)⌉₊:ℝ)+1)^9 := by
    have e : (N:ℝ)*(Q*h) = N*(K*(C*(2*(Real.sqrt 8*h)))+CR*(2*(Real.sqrt 8*h))) := by
      rw [hQ]; ring
    rw [e, hAdef]
    exact hsum
  have := residual_stratification_arith hA hQ0 hh hh1 hNR hh8 hch hτ0 hτ1 hε hτQ hh2 hh3 hsum2
  linarith

/-- The complement of any finite union of small E8 cube patches is stratifiable at the density
scale with the absolute constant `32π`. -/
theorem negStratifiable8_patch_complement {K : ℕ} (P : Fin K → SmallE8CubePatch8) :
    NegStratifiable8 (⋃ i, smallE8CubeSet8 (P i))ᶜ (32*Real.pi) := by
  obtain ⟨C, hC, hmink⟩ := patchComplement_frontier_minkowski8 P
  have hm : MeasurableSet (⋃ i, smallE8CubeSet8 (P i))ᶜ :=
    (MeasurableSet.iUnion fun i => (smallE8CubeSet8_isCompact (P i)).isClosed.measurableSet).compl
  exact negStratifiable8_of_frontier_minkowski hm hC hmink

theorem NegStratifiable8.mono {A : Set Sphere8} {B B' : ℝ} (h : NegStratifiable8 A B)
    (hB : B ≤ B') : NegStratifiable8 A B' := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := h ε hε
  refine ⟨N₀, fun N r hN hr hrN => ?_⟩
  obtain ⟨C, dm, h1, h2, h3, h4, h5, h6⟩ := hN₀ N r hN hr hrN
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  exact ⟨C, dm, h1, h2, h3, h4, h5, h6.trans (by nlinarith)⟩

theorem SphereStratifiable8.mono {B B' : ℝ} (h : SphereStratifiable8 B) (hB : B ≤ B') :
    SphereStratifiable8 B' := by
  intro r hr
  obtain ⟨C, dm, h1, h2, h3, h4, h5, h6⟩ := h r hr
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg r
  exact ⟨C, dm, h1, h2, h3, h4, h5, h6.trans (by nlinarith)⟩

/-- Both stratification hypotheses hold with one absolute constant. -/
theorem sphere8_stratification_hypotheses : ∃ B : ℝ, 0 ≤ B ∧
    (∀ {K : ℕ} (P : Fin K → SmallE8CubePatch8),
      NegStratifiable8 (⋃ i, smallE8CubeSet8 (P i))ᶜ B) ∧ SphereStratifiable8 B := by
  obtain ⟨B₁, hB₁, hsph⟩ := sphere8_stratifiable
  exact ⟨max (32*Real.pi) B₁, le_max_of_le_right hB₁,
    fun P => (negStratifiable8_patch_complement P).mono (le_max_left _ _),
    hsph.mono (le_max_right _ _)⟩

/-- NEG, two-sided, under the CKMRV contract alone: for every `-2 < s < 0` the sharp asymptotics
of the Riesz `|s|`-energy on `S⁸` in conjecture form, with the E8 Epstein coefficient. -/
theorem sphere8_riesz_neg_sharp (D : E8LaplaceSineData8) {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Configuration N,
      (energyRpow s X-(∫ p : Sphere8 × Sphere8, (dist p.1 p.2)^(-s)
          ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2)/(N:ℝ)^(1+s/8) ≤
        (sphereArea8.real univ)^(-(s/8))*(e8EpsteinCandidate ((s/2:ℝ):ℂ)).re+η) ∧
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : Configuration N,
      (sphereArea8.real univ)^(-(s/8))*(e8EpsteinCandidate ((s/2:ℝ):ℂ)).re-η ≤
        (energyRpow s Y-(∫ p : Sphere8 × Sphere8, (dist p.1 p.2)^(-s)
          ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2)/(N:ℝ)^(1+s/8)) := by
  obtain ⟨B, hB, hstrat, hsph⟩ := sphere8_stratification_hypotheses
  exact sphere8_riesz_neg_sharp_asymptotic D hB hstrat hsph hs hs0

/-- DISC, two-sided, under the CKMRV contract alone: `N^(1/2+1/16) D_L2 → c₈`. -/
theorem sphere8_cap_discrepancy_sharp_ckmrv (D : E8LaplaceSineData8) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (∀ X : Configuration N, sphereCapDiscrepancyConst8-η ≤
        (N:ℝ)^((1:ℝ)/2+1/16)*Real.sqrt (capDiscrepancyL2Sq8 X)) ∧
      ∃ X : Configuration N,
        (N:ℝ)^((1:ℝ)/2+1/16)*Real.sqrt (capDiscrepancyL2Sq8 X) ≤ sphereCapDiscrepancyConst8+η := by
  obtain ⟨B, hB, hstrat, hsph⟩ := sphere8_stratification_hypotheses
  exact sphere8_cap_discrepancy_sharp D hB hstrat hsph

/-- LOG, two-sided, under the CKMRV contract alone. -/
theorem sphere8_log_sharp (D : E8LaplaceSineData8) :
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Configuration N,
      -60*(deriv riemannZeta (-3)).re+(5/8)*Real.log 2-(1/8)*Real.log 105-η ≤
        (energyLog X-(∫ p : Sphere8 × Sphere8, -Real.log (dist p.1 p.2)
          ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2+(N:ℝ)/8*Real.log N)/(N:ℝ)) ∧
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : Configuration N,
      (energyLog Y-(∫ p : Sphere8 × Sphere8, -Real.log (dist p.1 p.2)
          ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2+(N:ℝ)/8*Real.log N)/(N:ℝ) ≤
        -60*(deriv riemannZeta (-3)).re+(5/8)*Real.log 2-(1/8)*Real.log 105+η) := by
  obtain ⟨B, hB, hstrat, hsph⟩ := sphere8_stratification_hypotheses
  exact sphere8_log_sharp_asymptotic D hB hstrat hsph

#print axioms sphere8_region_chart_partition
#print axioms residual_stratification_arith
#print axioms sphereProbability8_eq_div_of_real
#print axioms negStratifiable8_of_frontier_minkowski
#print axioms negStratifiable8_patch_complement
#print axioms NegStratifiable8.mono
#print axioms SphereStratifiable8.mono
#print axioms sphere8_stratification_hypotheses
#print axioms sphere8_riesz_neg_sharp
#print axioms sphere8_cap_discrepancy_sharp_ckmrv
#print axioms sphere8_log_sharp

end SphericalRiesz
