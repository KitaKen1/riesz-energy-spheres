import Riesz.SphereChartPool8
import Riesz.NegAllN8

/-! Exact-mass stratification of the whole sphere at every scale (stage NEG).

For `r` points take chart grid boxes of side `h`, `h^8 = A/r` (`A` the area of `S⁸`), so that
their rotated equal-area images have probability exactly `1/r`. Good cells (box inside the chart
cube, image missing the earlier charts) are pairwise disjoint with diameter at most `2√8 h`; at
most `r - 1` of them are kept. The rest of the sphere (the pool) lies within `2√8 h` of the chart
images of the cube boundaries, so it has probability at most `K C 2√8 h/A + 1/r`; it is split by
the pool partition at scale `√h` into exact-mass cells. With `c_r h² = π` this gives
`Σ_j c_r d_j² ≤ B r` for an absolute `B` (`SphereStratifiable8`). -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal
namespace SphericalRiesz

theorem gridBox8_inside_cube_finite {δ h : ℝ} (hh : 0 < h) :
    {z : Fin 8 → ℤ | gridBox8 h z ⊆ chartCube8 δ}.Finite := by
  set K : ℤ := ⌈|δ|/h⌉ with hK
  apply (Set.finite_Icc (fun _ : Fin 8 => -K) (fun _ => K)).subset
  intro z hz
  have hc : (fun i => h*(z i)) ∈ gridBox8 h z := by
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

theorem sphereProbability8_real_eq_area (s : Set Sphere8) :
    sphereProbability8.real s = sphereArea8.real s/sphereArea8.real univ := by
  simp only [Measure.real, sphereProbability8, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  ring


/-- The chart partition of the whole sphere into `r` exact-mass cells, for small `h`. -/
theorem sphere8_chart_partition_large {δ C ρ₁ : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
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
    {r : ℕ} (hr : 0 < r) {h : ℝ} (hh : 0 < h)
    (hh8 : h^8 = sphereArea8.real univ/r) (hρ : 2*(Real.sqrt 8*h) ≤ ρ₁) :
    ∃ Cl : Fin r → Set Sphere8, ∃ dm : Fin r → ℝ,
      (∀ j, MeasurableSet (Cl j)) ∧ Pairwise (fun i j => Disjoint (Cl i) (Cl j)) ∧
      (⋃ j, Cl j) = univ ∧ (∀ j, sphereProbability8.real (Cl j) = 1/r) ∧
      (∀ j, ∀ x ∈ Cl j, ∀ y ∈ Cl j, dist x y ≤ dm j) ∧
      ∑ j, (dm j)^2 ≤ 32*h^2*r+9*h*(r*(K*(C*(2*(Real.sqrt 8*h))))/sphereArea8.real univ+1)+
        4*(2*⌈1/Real.sqrt h⌉₊+1)^9 := by
  classical
  set A := sphereArea8.real univ with hAdef
  have hA : 0 < A := by rw [hAdef, sphereArea8_mass_real]; positivity
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hC2 : ∀ p ∈ chartCube8 δ, ∀ i, |p i| ≤ 2*δ := fun p hp i => (hp i).trans (by linarith)
  have hCdom : chartCube8 δ ⊆ equalAreaChartDomain := fun p hp => hdom2 p (hC2 p hp)
  set Zall := (gridBox8_inside_cube_finite (δ := δ) hh).toFinset with hZall
  have hZmem : ∀ z, z ∈ Zall ↔ gridBox8 h z ⊆ chartCube8 δ := fun z => by
    rw [hZall, Set.Finite.mem_toFinset]; rfl
  let earlier : Fin K → Set Sphere8 := fun k =>
    ⋃ j ∈ Finset.univ.filter (fun j : Fin K => j < k), chartImage8 (g j) (chartCube8 δ)
  let cell : Fin K × (Fin 8 → ℤ) → Set Sphere8 := fun q => chartImage8 (g q.1) (gridBox8 h q.2)
  set G₀ := (Finset.univ ×ˢ Zall).filter (fun q => Disjoint (cell q) (earlier q.1)) with hG₀
  have hG₀box : ∀ q ∈ G₀, gridBox8 h q.2 ⊆ chartCube8 δ := by
    intro q hq
    rw [hG₀, Finset.mem_filter, Finset.mem_product] at hq
    exact (hZmem q.2).mp hq.1.2
  have hG₀good : ∀ q ∈ G₀, Disjoint (cell q) (earlier q.1) := by
    intro q hq
    rw [hG₀, Finset.mem_filter] at hq
    exact hq.2
  -- the good cells
  have hcm : ∀ q ∈ G₀, MeasurableSet (cell q) := fun q hq =>
    chartImage8_measurable (g q.1) (gridBox8_measurable h q.2) ((hG₀box q hq).trans hCdom)
  have hcprob : ∀ q ∈ G₀, sphereProbability8.real (cell q) = 1/r := by
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
      · -- cell q lies in the earlier charts of q'
        have hsub : cell q ⊆ earlier q'.1 := by
          intro x hx
          refine mem_iUnion₂.mpr ⟨q.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, ?_⟩
          exact chartImage8_mono (g q.1) (hG₀box q hq) hx
        exact (hG₀good q' hq').symm.mono_left hsub
      · have hsub : cell q' ⊆ earlier q.1 := by
          intro x hx
          refine mem_iUnion₂.mpr ⟨q'.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, ?_⟩
          exact chartImage8_mono (g q'.1) (hG₀box q' hq') hx
        exact (hG₀good q hq).mono_right hsub
  have hcdiam : ∀ q ∈ G₀, ∀ x ∈ cell q, ∀ y ∈ cell q, dist x y ≤ 2*(Real.sqrt 8*h) := by
    intro q hq x hx y hy
    obtain ⟨p, hp, hxp⟩ := hx
    obtain ⟨p', hp', hyp'⟩ := hy
    rw [Subtype.dist_eq, hxp, hyp', (g q.1).dist_map]
    have h1 := (hbi p p' (hC2 p (hG₀box q hq hp)) (hC2 p' (hG₀box q hq hp'))).2
    have h2 := gridBox8_dist_le hh hp hp'
    linarith
  -- at most r good cells
  have hcard₀ : G₀.card ≤ r := by
    have hm := measureReal_biUnion_finset hcdisj hcm (μ := sphereProbability8)
    have hle : sphereProbability8.real (⋃ q ∈ G₀, cell q) ≤ 1 := measureReal_le_one
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
  have hPprob : sphereProbability8.real P = n/r := by
    rw [hPdef, measureReal_compl hGm, probReal_univ,
      measureReal_biUnion_finset hGdisj (fun q hq => hcm q (hGsub hq)),
      Finset.sum_congr rfl (fun q hq => hcprob q (hGsub hq)), Finset.sum_const, nsmul_eq_mul]
    have : ((r-G.card : ℕ):ℝ) = (r:ℝ)-G.card := by
      rw [Nat.cast_sub (by omega)]
    rw [hndef, this]
    field_simp
  -- the pool lies near the chart cube boundaries
  set N₀ := ⋃ k : Fin K, {x : Sphere8 | ∃ w ∈ cubeBdry8 δ,
    dist (x:Ambient9) (g k (equalAreaPhi w)) ≤ 2*(Real.sqrt 8*h)} with hN₀
  have hP₀ : (⋃ q ∈ G₀, cell q)ᶜ ⊆ N₀ := by
    intro x hx
    rw [mem_compl_iff] at hx
    obtain ⟨k, w, hw, hd⟩ := chart_pool_near_boundary hδ hh hdom2 hbi g hcover x
      (fun k z hz hdisj hxk => hx (mem_iUnion₂.mpr ⟨(k, z), by
        rw [hG₀, Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨Finset.mem_univ _, (hZmem z).mpr hz⟩, hdisj⟩, hxk⟩))
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
  have hPbound : sphereProbability8.real P ≤ K*(C*(2*(Real.sqrt 8*h)))/A+1/r := by
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
    have h1 : sphereProbability8.real P ≤ sphereProbability8.real ((⋃ q ∈ G₀, cell q)ᶜ)+
        sphereProbability8.real (⋃ q ∈ G₀ \ G, cell q) :=
      (measureReal_mono hsub).trans (measureReal_union_le _ _)
    have h2 : sphereProbability8.real ((⋃ q ∈ G₀, cell q)ᶜ) ≤ K*(C*(2*(Real.sqrt 8*h)))/A := by
      rw [sphereProbability8_real_eq_area, ← hAdef]
      apply div_le_div_of_nonneg_right _ hA.le
      have hm := (measure_mono (μ := sphereArea8) hP₀).trans hN₀area
      calc sphereArea8.real ((⋃ q ∈ G₀, cell q)ᶜ) ≤ (ENNReal.ofReal (K*(C*(2*(Real.sqrt 8*h))))).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
        _ = K*(C*(2*(Real.sqrt 8*h))) := ENNReal.toReal_ofReal (by positivity)
    have h3 : sphereProbability8.real (⋃ q ∈ G₀ \ G, cell q) ≤ 1/r := by
      have hdj : Set.PairwiseDisjoint (↑(G₀ \ G)) cell :=
        hcdisj.subset (by exact_mod_cast Finset.sdiff_subset)
      rw [measureReal_biUnion_finset hdj (fun q hq => hcm q (Finset.mem_sdiff.mp hq).1),
        Finset.sum_congr rfl (fun q hq => hcprob q (Finset.mem_sdiff.mp hq).1),
        Finset.sum_const, nsmul_eq_mul]
      have : ((G₀ \ G).card:ℝ) ≤ 1 := by exact_mod_cast hdiff
      have h0 : (0:ℝ) ≤ 1/r := by positivity
      nlinarith
    linarith
  have hnbound : (n:ℝ) ≤ r*(K*(C*(2*(Real.sqrt 8*h))))/A+1 := by
    have h1 : (n:ℝ)/r ≤ K*(C*(2*(Real.sqrt 8*h)))/A+1/r := hPprob ▸ hPbound
    rw [div_le_iff₀ hrR] at h1
    have : (K*(C*(2*(Real.sqrt 8*h)))/A+1/r)*r = r*(K*(C*(2*(Real.sqrt 8*h))))/A+1 := by
      field_simp
    linarith
  -- split the pool
  have hsh : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  obtain ⟨PC, dmP, hPCm, hPCd, hPCu, hPCmass, hPCdiam, hPCsum⟩ :=
    sphere8_pool_partition hPm hsh hn
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
      nlinarith [sq_nonneg h]
    have hpool : ∑ i, (dmP i)^2 ≤ 9*h*(r*(K*(C*(2*(Real.sqrt 8*h))))/A+1)+
        4*(2*⌈1/Real.sqrt h⌉₊+1)^9 := by
      have h1 := hPCsum
      have e2 : (n:ℝ)*(3*Real.sqrt h)^2 = 9*h*n := by
        rw [mul_pow, Real.sq_sqrt hh.le]; ring
      rw [e2] at h1
      have h3 : 9*h*(n:ℝ) ≤ 9*h*(r*(K*(C*(2*(Real.sqrt 8*h))))/A+1) :=
        mul_le_mul_of_nonneg_left hnbound (by positivity)
      linarith
    linarith


theorem sphereProbability8_eq_inv_of_real {s : Set Sphere8} {r : ℕ} (hr : 0 < r)
    (hs : sphereProbability8.real s = 1/r) :
    sphereProbability8 s = sphereProbability8 univ/(r:ℝ≥0∞) := by
  rw [measure_univ, ← ofReal_measureReal (measure_ne_top _ _), hs, one_div, one_div,
    ENNReal.ofReal_inv_of_pos (by exact_mod_cast hr), ENNReal.ofReal_natCast]

theorem sphereGaussianDensityFactor8_mul_sq {r : ℕ} (hr : 0 < r) {h : ℝ} (hh : 0 < h)
    (hh8 : h^8 = sphereArea8.real univ/r) : sphereGaussianDensityFactor8 r*h^2 = Real.pi := by
  have hc0 := sphereGaussianDensityFactor8_pos hr
  have h4 := sphereGaussianDensityFactor8_pow_four hr
  have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hpow : (sphereGaussianDensityFactor8 r*h^2)^4 = Real.pi^4 := by
    rw [mul_pow, h4, ← pow_mul, show 2*4 = 8 by norm_num, hh8]
    field_simp
  exact (pow_left_inj₀ (by positivity) Real.pi_pos.le (by norm_num)).mp hpow

/-- The scale arithmetic of the chart construction: with `c h² = π` and `h^8 = A/r` the bound
`32h²r + 9h(rQh/A + 1) + 4(2⌈1/√h⌉+1)^9` on `Σ d_j²` becomes `O(r)` after multiplying by `c`. -/
theorem stratification_large_arith {A Q c h r S : ℝ} (hA : 0 < A) (hh : 0 < h) (hh1 : h ≤ 1)
    (hr : 0 < r) (hh8 : h^8 = A/r) (hch : c*h^2 = Real.pi)
    (hS : S ≤ 32*h^2*r+9*h*(r*(Q*h)/A+1)+4*(2*(⌈1/Real.sqrt h⌉₊:ℝ)+1)^9) :
    c*S ≤ (32*Real.pi+9*Real.pi*Q/A+9*Real.pi/A+4*5^9*Real.pi/A)*r := by
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
  have h8le : h^8 ≤ h := by
    calc h^8 ≤ h^1 := pow_le_pow_of_le_one hh.le hh1 (by norm_num)
      _ = h := pow_one h
  have hinv : 1/h ≤ r/A := by
    rw [div_le_div_iff₀ hh hA, one_mul]
    rw [hh8, div_le_iff₀ hr] at h8le
    linarith
  have hT1 : c*(32*h^2*r) = 32*Real.pi*r := by rw [← hch]; ring
  have hT2 : c*(9*h*(r*(Q*h)/A+1)) ≤ 9*Real.pi*Q/A*r+9*Real.pi/A*r := by
    have e1 : c*(9*h*(r*(Q*h)/A+1)) = 9*Real.pi*Q/A*r+9*Real.pi*(1/h) := by
      rw [hcval]
      field_simp
    rw [e1]
    have h1 : 9*Real.pi*(1/h) ≤ 9*Real.pi*(r/A) := mul_le_mul_of_nonneg_left hinv (by positivity)
    have e2 : 9*Real.pi*(r/A) = 9*Real.pi/A*r := by ring
    linarith
  have hT3 : c*(4*(2*(⌈1/Real.sqrt h⌉₊:ℝ)+1)^9) ≤ 4*5^9*Real.pi/A*r := by
    have h1 : (2*(⌈1/Real.sqrt h⌉₊:ℝ)+1)^9 ≤ (5/Real.sqrt h)^9 :=
      pow_le_pow_left₀ (by positivity) hceil 9
    have hs9 : Real.sqrt h^9 = h^4*Real.sqrt h := by
      rw [show 9 = 2*4+1 by norm_num, pow_succ, pow_mul, hsq]
    have hh2 : h^2 ≤ Real.sqrt h := by
      have : h^2 ≤ h := by nlinarith [mul_nonneg hh.le (sub_nonneg.mpr hh1)]
      linarith
    have hden : h^8 ≤ h^2*(h^4*Real.sqrt h) := by
      have := mul_le_mul_of_nonneg_left hh2 (show 0 ≤ h^6 by positivity)
      calc h^8 = h^6*h^2 := by ring
        _ ≤ h^6*Real.sqrt h := this
        _ = h^2*(h^4*Real.sqrt h) := by ring
    have e : c*(5/Real.sqrt h)^9 = 5^9*Real.pi/(h^2*(h^4*Real.sqrt h)) := by
      rw [hcval, div_pow, hs9]
      field_simp
    have h2 : c*(5/Real.sqrt h)^9 ≤ 5^9*Real.pi/h^8 := by
      rw [e]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    have h3 : 5^9*Real.pi/h^8 = 5^9*Real.pi/A*r := by
      rw [hh8, div_div_eq_mul_div]
      ring
    have h4 : c*(2*(⌈1/Real.sqrt h⌉₊:ℝ)+1)^9 ≤ c*(5/Real.sqrt h)^9 :=
      mul_le_mul_of_nonneg_left h1 hc0.le
    calc c*(4*(2*(⌈1/Real.sqrt h⌉₊:ℝ)+1)^9) = 4*(c*(2*(⌈1/Real.sqrt h⌉₊:ℝ)+1)^9) := by ring
      _ ≤ 4*(5^9*Real.pi/h^8) := by linarith
      _ = 4*5^9*Real.pi/A*r := by rw [h3]; ring
  have hexp : c*(32*h^2*r+9*h*(r*(Q*h)/A+1)+4*(2*(⌈1/Real.sqrt h⌉₊:ℝ)+1)^9) =
      c*(32*h^2*r)+c*(9*h*(r*(Q*h)/A+1))+c*(4*(2*(⌈1/Real.sqrt h⌉₊:ℝ)+1)^9) := by ring
  have hcS := mul_le_mul_of_nonneg_left hS hc0.le
  have hBr : (32*Real.pi+9*Real.pi*Q/A+9*Real.pi/A+4*5^9*Real.pi/A)*r =
      32*Real.pi*r+(9*Real.pi*Q/A*r+9*Real.pi/A*r)+4*5^9*Real.pi/A*r := by ring
  rw [hBr]
  linarith

/-- The whole sphere is stratifiable at every scale with one absolute constant. -/
theorem sphere8_stratifiable : ∃ B : ℝ, 0 ≤ B ∧ SphereStratifiable8 B := by
  classical
  obtain ⟨δ, hδ, C, hC, ρ₁, hρ₁, hdom2, hbi, hmink⟩ := chart_boundary_minkowski8
  have hCdom : chartCube8 δ ⊆ equalAreaChartDomain := fun p hp =>
    hdom2 p (fun i => (hp i).trans (by linarith))
  obtain ⟨K, g, hcover⟩ := sphere8_finite_chart_cover hδ hCdom
  have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
  have hs8 : 0 < Real.sqrt 8 := by positivity
  obtain ⟨h₀, hh₀pos, hh₀1, hh₀ρ⟩ : ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ 2*(Real.sqrt 8*h₀) ≤ ρ₁ := by
    refine ⟨min (ρ₁/(2*Real.sqrt 8)) 1, lt_min (by positivity) one_pos, min_le_right _ _, ?_⟩
    have h1 := min_le_left (ρ₁/(2*Real.sqrt 8)) 1
    rw [le_div_iff₀ (by positivity)] at h1
    linarith
  obtain ⟨BL, hBL⟩ : ∃ BL : ℝ, BL = 32*Real.pi+9*Real.pi*((K:ℝ)*(C*(2*Real.sqrt 8)))/sphereArea8.real univ+
      9*Real.pi/sphereArea8.real univ+4*5^9*Real.pi/sphereArea8.real univ := ⟨_, rfl⟩
  obtain ⟨BS, hBS⟩ : ∃ BS : ℝ, BS = Real.pi/h₀^2*(9+4*3^9) := ⟨_, rfl⟩
  have hBL0 : 0 ≤ BL := by rw [hBL]; positivity
  refine ⟨max BL BS, le_max_of_le_left hBL0, ?_⟩
  intro r hr
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  obtain ⟨h, hh, hh8⟩ : ∃ h : ℝ, 0 < h ∧ h^8 = sphereArea8.real univ/r := by
    refine ⟨(sphereArea8.real univ/r)^((1:ℝ)/8), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hch := sphereGaussianDensityFactor8_mul_sq hr hh hh8
  by_cases hsmall : h ≤ h₀
  · -- the chart construction
    have hh1 : h ≤ 1 := hsmall.trans hh₀1
    have hρ : 2*(Real.sqrt 8*h) ≤ ρ₁ := by
      have := mul_le_mul_of_nonneg_left hsmall hs8.le
      linarith
    obtain ⟨Cl, dm, hm, hd, hu, hmass, hdiam, hsum⟩ := sphere8_chart_partition_large hδ hC hdom2
      hbi hmink g hcover hr hh hh8 hρ
    refine ⟨Cl, dm, hm, hd, hu, fun j => sphereProbability8_eq_inv_of_real hr (hmass j), hdiam, ?_⟩
    rw [← Finset.mul_sum]
    have hsum2 : ∑ j, (dm j)^2 ≤ 32*h^2*r+9*h*(r*(((K:ℝ)*(C*(2*Real.sqrt 8)))*h)/sphereArea8.real univ+1)+
        4*(2*(⌈1/Real.sqrt h⌉₊:ℝ)+1)^9 := by
      have e : (r:ℝ)*(((K:ℝ)*(C*(2*Real.sqrt 8)))*h) = r*(K*(C*(2*(Real.sqrt 8*h)))) := by ring
      rw [e]
      exact hsum
    have hfin : sphereGaussianDensityFactor8 r*∑ j, (dm j)^2 ≤ BL*r := by
      rw [hBL]
      exact stratification_large_arith hA hh hh1 hrR hh8 hch hsum2
    exact hfin.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hrR.le)
  · -- small r: the pool partition of the whole sphere at scale 1
    have hsmall' : h₀ < h := lt_of_not_ge hsmall
    obtain ⟨Cl, dm, hm, hd, hu, hmass, hdiam, hsum⟩ :=
      sphere8_pool_partition (P := univ) MeasurableSet.univ one_pos hr
    refine ⟨Cl, dm, hm, hd, hu, fun j => sphereProbability8_eq_inv_of_real hr ?_, hdiam, ?_⟩
    · rw [hmass j, probReal_univ]
    · rw [← Finset.mul_sum]
      have hcval : sphereGaussianDensityFactor8 r = Real.pi/h^2 :=
        (eq_div_iff (by positivity)).mpr hch
      have hc : sphereGaussianDensityFactor8 r ≤ Real.pi/h₀^2 := by
        rw [hcval]
        exact div_le_div_of_nonneg_left Real.pi_pos.le (by positivity)
          (pow_le_pow_left₀ hh₀pos.le hsmall'.le 2)
      have hr1 : (1:ℝ) ≤ r := by exact_mod_cast hr
      have hs : ∑ j, (dm j)^2 ≤ (9+4*3^9)*r := by
        have hb : (r:ℝ)*(3*1)^2+4*(2*(⌈(1:ℝ)/1⌉₊:ℝ)+1)^9 ≤ (9+4*3^9)*r := by
          norm_num
          linarith
        exact hsum.trans hb
      have h1 : sphereGaussianDensityFactor8 r*(∑ j, (dm j)^2) ≤ Real.pi/h₀^2*((9+4*3^9)*r) :=
        mul_le_mul hc hs (Finset.sum_nonneg fun j _ => sq_nonneg _) (by positivity)
      calc sphereGaussianDensityFactor8 r*∑ j, (dm j)^2 ≤ Real.pi/h₀^2*((9+4*3^9)*r) := h1
        _ = BS*r := by rw [hBS]; ring
        _ ≤ max BL BS*r := mul_le_mul_of_nonneg_right (le_max_right _ _) hrR.le

#print axioms gridBox8_inside_cube_finite
#print axioms sphereProbability8_real_eq_area
#print axioms sphere8_chart_partition_large
#print axioms sphereProbability8_eq_inv_of_real
#print axioms sphereGaussianDensityFactor8_mul_sq
#print axioms stratification_large_arith
#print axioms sphere8_stratifiable

end SphericalRiesz
