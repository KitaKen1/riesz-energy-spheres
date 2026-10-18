import Riesz.SphereChartRegions8

/-! The pool of a chart grid lies near the chart-cube boundaries (stage NEG, stratification).

With the closed chart cube `C₀ = [-δ,δ]^8`, the open cube `I₀`, finitely many rotations covering
the sphere by `chartImage8 (g k) I₀`, and the first-come regions, a grid box `b` of side `h` in
chart `k` is *good* if `b ⊆ C₀` and its image misses the images of `C₀` in the earlier charts.
Every point outside the good cells lies within `2√8 h` of the image of the cube boundary in some
chart: either its box leaves `C₀` (the segment to an outside point crosses the cube boundary),
or the image of its box meets an earlier chart image without being inside it (a connected set
meeting a closed set and its complement meets its frontier, and the frontier of a chart image of
`C₀` lies in the image of the cube boundary). -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric Topology
namespace SphericalRiesz

/-- The closed and the open chart cube. -/
def chartCube8 (δ : ℝ) : Set (Fin 8 → ℝ) := {p | ∀ i, |p i| ≤ δ}
def chartCubeOpen8 (δ : ℝ) : Set (Fin 8 → ℝ) := {p | ∀ i, |p i| < δ}

theorem chartCube8_eq (δ : ℝ) : chartCube8 δ = Set.pi univ (fun _ => Icc (-δ) δ) := by
  ext p
  simp only [chartCube8, mem_setOf_eq, mem_pi, mem_univ, true_implies, mem_Icc, abs_le]

theorem chartCubeOpen8_eq (δ : ℝ) : chartCubeOpen8 δ = Set.pi univ (fun _ => Ioo (-δ) δ) := by
  ext p
  simp only [chartCubeOpen8, mem_setOf_eq, mem_pi, mem_univ, true_implies, mem_Ioo, abs_lt]

theorem chartCube8_isCompact (δ : ℝ) : IsCompact (chartCube8 δ) := by
  rw [chartCube8_eq]
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

theorem chartCube8_measurable (δ : ℝ) : MeasurableSet (chartCube8 δ) := by
  rw [chartCube8_eq]
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

theorem chartCubeOpen8_isOpen (δ : ℝ) : IsOpen (chartCubeOpen8 δ) := by
  rw [chartCubeOpen8_eq]
  exact isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo)

theorem chartCubeOpen8_subset (δ : ℝ) : chartCubeOpen8 δ ⊆ chartCube8 δ :=
  fun _ hp i => (hp i).le

theorem chartCube8_sdiff_open (δ : ℝ) : chartCube8 δ \ chartCubeOpen8 δ ⊆ cubeBdry8 δ := by
  rintro p ⟨hp, hpo⟩
  refine ⟨hp, ?_⟩
  by_contra hne
  simp only [not_exists] at hne
  exact hpo (fun i => lt_of_le_of_ne (hp i) (hne i))

theorem chartCube8_frontier (δ : ℝ) : frontier (chartCube8 δ) ⊆ cubeBdry8 δ := by
  intro p hp
  have hcl : IsClosed (chartCube8 δ) := (chartCube8_isCompact δ).isClosed
  rw [frontier, hcl.closure_eq] at hp
  refine chartCube8_sdiff_open δ ⟨hp.1, fun ho => hp.2 ?_⟩
  exact interior_maximal (chartCubeOpen8_subset δ) (chartCubeOpen8_isOpen δ) ho

/-- The frontier of the chart image of the closed cube lies in the image of its boundary. -/
theorem chartImage8_frontier (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) {δ : ℝ}
    (hdom : chartCube8 δ ⊆ equalAreaChartDomain) :
    frontier (chartImage8 g (chartCube8 δ)) ⊆ chartImage8 g (cubeBdry8 δ) := by
  intro x hx
  have hcl := chartImage8_isClosed g (chartCube8_isCompact δ)
  rw [frontier, hcl.closure_eq] at hx
  obtain ⟨⟨p, hp, hxp⟩, hxi⟩ := hx
  have hopen := chartImage8_isOpen g (chartCubeOpen8_isOpen δ)
    ((chartCubeOpen8_subset δ).trans hdom)
  have hsub : chartImage8 g (chartCubeOpen8 δ) ⊆ interior (chartImage8 g (chartCube8 δ)) :=
    interior_maximal (chartImage8_mono g (chartCubeOpen8_subset δ)) hopen
  have hpo : p ∉ chartCubeOpen8 δ := fun hpo => hxi (hsub ⟨p, hpo, hxp⟩)
  exact ⟨p, chartCube8_sdiff_open δ ⟨hp, hpo⟩, hxp⟩

/-- Finitely many rotated open chart cubes cover the sphere. -/
theorem sphere8_finite_chart_cover {δ : ℝ} (hδ : 0 < δ)
    (hdom : chartCube8 δ ⊆ equalAreaChartDomain) :
    ∃ K : ℕ, ∃ g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9,
      ∀ x : Sphere8, ∃ k, x ∈ chartImage8 (g k) (chartCubeOpen8 δ) := by
  classical
  let : CompactSpace Sphere8 := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : Ambient9) 1)
  have ht : ∀ p : Sphere8, ∃ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9, sphereRotation8 g northPole8 = p :=
    fun p => sphereRotation8_transitive northPole8 p
  choose g hg using ht
  let U : Sphere8 → Set Sphere8 := fun p => chartImage8 (g p) (chartCubeOpen8 δ)
  have hU : ∀ p, IsOpen (U p) := fun p =>
    chartImage8_isOpen (g p) (chartCubeOpen8_isOpen δ) ((chartCubeOpen8_subset δ).trans hdom)
  have hcenter : ∀ p, p ∈ U p := by
    intro p
    refine ⟨0, fun i => by simpa using hδ, ?_⟩
    have h1 : (p:Ambient9) = (sphereRotation8 (g p) northPole8 : Ambient9) := by rw [hg p]
    rw [h1]
    change (g p) (northPole8 : Ambient9) = (g p) (equalAreaPhi 0)
    congr 1
    have h0 := equalAreaPhiEuclidean8_zero
    simp only [equalAreaPhiEuclidean8] at h0
    rw [← h0]
    simp
  obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (univ : Set Sphere8)).elim_finite_subcover
    U hU (fun p _ => mem_iUnion.mpr ⟨p, hcenter p⟩)
  refine ⟨t.card, fun i => g (t.equivFin.symm i).val, ?_⟩
  intro x
  obtain ⟨p, hp⟩ := mem_iUnion.mp (ht (mem_univ x))
  obtain ⟨hpt, hxp⟩ := mem_iUnion.mp hp
  refine ⟨t.equivFin ⟨p, hpt⟩, ?_⟩
  simpa only [Equiv.symm_apply_apply] using hxp

/-- Chart images of convex coordinate sets are preconnected. -/
theorem chartImage8_isPreconnected (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) {S : Set (Fin 8 → ℝ)}
    (hS : Convex ℝ S) (hsub : S ⊆ equalAreaChartDomain) :
    IsPreconnected (chartImage8 g S) := by
  have himg : Subtype.val '' chartImage8 g S = (fun p => g (equalAreaPhi p)) '' S := by
    ext y
    simp only [chartImage8, mem_image, mem_setOf_eq]
    constructor
    · rintro ⟨x, ⟨p, hp, hxp⟩, rfl⟩
      exact ⟨p, hp, hxp.symm⟩
    · rintro ⟨p, hp, rfl⟩
      have hm : g (equalAreaPhi p) ∈ sphere (0:Ambient9) 1 := by
        rw [mem_sphere_zero_iff_norm, g.norm_map]
        have := equalAreaPhi_mem_sphere p (hsub hp).1
        rwa [mem_sphere_zero_iff_norm] at this
      exact ⟨⟨g (equalAreaPhi p), hm⟩, ⟨p, hp, rfl⟩, rfl⟩
  rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, himg]
  exact hS.isPreconnected.image _ (g.continuous.comp equalAreaPhi_continuous).continuousOn

/-- The frontier of a finite union of closed sets lies in the union of their frontiers. -/
theorem frontier_biUnion_closed_subset {X : Type*} [TopologicalSpace X] {ι : Type*}
    (s : Finset ι) (E : ι → Set X) (hE : ∀ i ∈ s, IsClosed (E i)) :
    frontier (⋃ i ∈ s, E i) ⊆ ⋃ i ∈ s, frontier (E i) := by
  intro x hx
  have hcl : IsClosed (⋃ i ∈ s, E i) := by
    have := (s.finite_toSet).isClosed_biUnion (f := E) (fun i hi => hE i hi)
    simpa using this
  rw [frontier, hcl.closure_eq] at hx
  obtain ⟨hxu, hxi⟩ := hx
  obtain ⟨i, hi, hxe⟩ := mem_iUnion₂.mp hxu
  refine mem_iUnion₂.mpr ⟨i, hi, ?_⟩
  rw [frontier, (hE i hi).closure_eq]
  refine ⟨hxe, fun hxie => hxi ?_⟩
  exact interior_mono (subset_biUnion_of_mem hi) hxie


theorem gridBox8_convex (h : ℝ) (z : Fin 8 → ℤ) : Convex ℝ (gridBox8 h z) :=
  convex_pi (fun _ _ => convex_Ico _ _)

/-- Points outside the good cells lie near the image of a chart-cube boundary. -/
theorem chart_pool_near_boundary {δ h : ℝ} (hδ : 0 < δ) (hh : 0 < h)
    (hdom2 : ∀ p : Fin 8 → ℝ, (∀ i, |p i| ≤ 2*δ) → p ∈ equalAreaChartDomain)
    (hbi : ∀ p q : Fin 8 → ℝ, (∀ i, |p i| ≤ 2*δ) → (∀ i, |q i| ≤ 2*δ) →
      dist (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 q) ≤
        2*dist (equalAreaPhi p) (equalAreaPhi q) ∧
      dist (equalAreaPhi p) (equalAreaPhi q) ≤
        2*dist (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 q))
    {K : ℕ} (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9)
    (hcover : ∀ x : Sphere8, ∃ k, x ∈ chartImage8 (g k) (chartCubeOpen8 δ)) (x : Sphere8)
    (hx : ∀ k : Fin K, ∀ z : Fin 8 → ℤ, gridBox8 h z ⊆ chartCube8 δ →
      Disjoint (chartImage8 (g k) (gridBox8 h z))
        (⋃ j ∈ Finset.univ.filter (fun j : Fin K => j < k), chartImage8 (g j) (chartCube8 δ)) →
      x ∉ chartImage8 (g k) (gridBox8 h z)) :
    ∃ k : Fin K, ∃ w ∈ cubeBdry8 δ, dist (x:Ambient9) (g k (equalAreaPhi w)) ≤ 2*(Real.sqrt 8*h) := by
  classical
  have hC2 : ∀ p ∈ chartCube8 δ, ∀ i, |p i| ≤ 2*δ := fun p hp i => (hp i).trans (by linarith)
  have hCdom : chartCube8 δ ⊆ equalAreaChartDomain := fun p hp => hdom2 p (hC2 p hp)
  -- the first chart containing x
  set Sx := Finset.univ.filter (fun k : Fin K => x ∈ chartImage8 (g k) (chartCube8 δ)) with hSx
  have hSne : Sx.Nonempty := by
    obtain ⟨k, hk⟩ := hcover x
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, chartImage8_mono (g k) (chartCubeOpen8_subset δ) hk⟩⟩
  set k₀ := Sx.min' hSne with hk₀
  have hk₀S : k₀ ∈ Sx := Finset.min'_mem Sx hSne
  have hxk₀ : x ∈ chartImage8 (g k₀) (chartCube8 δ) := (Finset.mem_filter.mp hk₀S).2
  have hxF : x ∉ ⋃ j ∈ Finset.univ.filter (fun j : Fin K => j < k₀), chartImage8 (g j) (chartCube8 δ) := by
    intro hxF
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxF
    have hjS : j ∈ Sx := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxj⟩
    have := Finset.min'_le Sx j hjS
    have hjlt := (Finset.mem_filter.mp hj).2
    rw [← hk₀] at this
    exact absurd hjlt (not_lt.mpr this)
  obtain ⟨p, hp, hxp⟩ := hxk₀
  set z := gridIndex8 h p with hzdef
  have hpb : p ∈ gridBox8 h z := mem_gridBox8_gridIndex8 hh p
  have hdist : ∀ k : Fin K, ∀ q r : Fin 8 → ℝ, q ∈ gridBox8 h z → r ∈ gridBox8 h z →
      (∀ i, |q i| ≤ 2*δ) → (∀ i, |r i| ≤ 2*δ) →
      dist (g k (equalAreaPhi q)) (g k (equalAreaPhi r)) ≤ 2*(Real.sqrt 8*h) := by
    intro k q r hq hr hq2 hr2
    rw [(g k).dist_map]
    have h1 := (hbi q r hq2 hr2).2
    have h2 := gridBox8_dist_le hh hq hr
    linarith
  by_cases hb : gridBox8 h z ⊆ chartCube8 δ
  · -- the box image meets an earlier chart image: it crosses that image's frontier
    have hnd : ¬Disjoint (chartImage8 (g k₀) (gridBox8 h z))
        (⋃ j ∈ Finset.univ.filter (fun j : Fin K => j < k₀), chartImage8 (g j) (chartCube8 δ)) :=
      fun hd => hx k₀ z hb hd ⟨p, hpb, hxp⟩
    rw [Set.not_disjoint_iff] at hnd
    obtain ⟨y, hyY, hyF⟩ := hnd
    have hpre := chartImage8_isPreconnected (g k₀) (gridBox8_convex h z) (hb.trans hCdom)
    obtain ⟨y', hy'Y, hy'f⟩ := isPreconnected_inter_frontier hpre ⟨y, hyY, hyF⟩
      ⟨x, ⟨p, hpb, hxp⟩, hxF⟩
    have hfr := frontier_biUnion_closed_subset (Finset.univ.filter (fun j : Fin K => j < k₀))
      (fun j => chartImage8 (g j) (chartCube8 δ))
      (fun j _ => chartImage8_isClosed (g j) (chartCube8_isCompact δ)) hy'f
    obtain ⟨j, _, hj⟩ := mem_iUnion₂.mp hfr
    obtain ⟨w, hw, hyw⟩ := chartImage8_frontier (g j) hCdom hj
    obtain ⟨p', hp', hyp'⟩ := hy'Y
    refine ⟨j, w, hw, ?_⟩
    rw [hxp, ← hyw, hyp']
    exact hdist k₀ p p' hpb hp' (hC2 p hp) (hC2 p' (hb hp'))
  · -- the box leaves the cube: the segment to an outside point crosses the cube boundary
    rw [Set.not_subset] at hb
    obtain ⟨q, hqb, hqC⟩ := hb
    have hseg : segment ℝ p q ⊆ gridBox8 h z := (gridBox8_convex h z).segment_subset hpb hqb
    obtain ⟨w, hwseg, hwf⟩ := isPreconnected_inter_frontier (convex_segment p q).isPreconnected
      ⟨p, left_mem_segment ℝ p q, hp⟩ ⟨q, right_mem_segment ℝ p q, hqC⟩
    have hw := chartCube8_frontier δ hwf
    refine ⟨k₀, w, hw, ?_⟩
    rw [hxp]
    exact hdist k₀ p w hpb (hseg hwseg) (hC2 p hp) (fun i => (hw.1 i).trans (by linarith))

#print axioms chartCube8_eq
#print axioms chartCubeOpen8_eq
#print axioms chartCube8_isCompact
#print axioms chartCube8_measurable
#print axioms chartCubeOpen8_isOpen
#print axioms chartCubeOpen8_subset
#print axioms chartCube8_sdiff_open
#print axioms chartCube8_frontier
#print axioms chartImage8_frontier
#print axioms sphere8_finite_chart_cover
#print axioms chartImage8_isPreconnected
#print axioms frontier_biUnion_closed_subset
#print axioms gridBox8_convex
#print axioms chart_pool_near_boundary

end SphericalRiesz
