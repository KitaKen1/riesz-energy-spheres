import Riesz.ChartBoundaryMinkowski8

/-! Rotated chart regions on the sphere (stage NEG, stratification).

`chartImage8 g S` is the image of the coordinate set `S` under the rotated equal-area chart.
For `S` measurable inside the chart domain its area is the Lebesgue volume of `S`; the image of
the closed chart cube is closed, the image of the open cube is open, and the frontier of the
image of the closed cube lies in the image of the cube boundary. By compactness finitely many
rotations of the open cube cover the sphere. A preconnected set meeting `t` and `tᶜ` meets the
frontier of `t`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric Topology
namespace SphericalRiesz

theorem isPreconnected_inter_frontier {X : Type*} [TopologicalSpace X] {s t : Set X}
    (hs : IsPreconnected s) (h1 : (s ∩ t).Nonempty) (h2 : (s \ t).Nonempty) :
    (s ∩ frontier t).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hnf : ∀ x ∈ s, x ∉ frontier t := by
    intro x hx hf
    have : x ∈ s ∩ frontier t := ⟨hx, hf⟩
    rw [hne] at this
    exact this
  have hsub : s ⊆ interior t ∪ interior tᶜ := by
    intro x hx
    by_cases hxt : x ∈ interior t
    · exact Or.inl hxt
    · right
      rw [interior_compl]
      intro hxc
      exact hnf x hx ⟨hxc, hxt⟩
  obtain ⟨x, hxs, hxt⟩ := h1
  obtain ⟨y, hys, hyt⟩ := h2
  have hx : x ∈ interior t := by
    by_contra hxi
    exact hnf x hxs ⟨subset_closure hxt, hxi⟩
  have hy : y ∈ interior tᶜ := by
    rcases hsub hys with h | h
    · exact absurd (interior_subset h) hyt
    · exact h
  obtain ⟨z, _, hzu, hzv⟩ := hs _ _ isOpen_interior isOpen_interior hsub ⟨x, hxs, hx⟩ ⟨y, hys, hy⟩
  exact (interior_subset hzv) (interior_subset hzu)

/-- The image of a coordinate set under the rotated equal-area chart. -/
def chartImage8 (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) (S : Set (Fin 8 → ℝ)) : Set Sphere8 :=
  {x | ∃ p ∈ S, (x:Ambient9) = g (equalAreaPhi p)}

theorem chartImage8_eq_preimage (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) (S : Set (Fin 8 → ℝ)) :
    chartImage8 g S = (sphereRotation8 g.symm) ⁻¹' equalAreaSpherePatch S := by
  ext x
  simp only [chartImage8, mem_setOf_eq, mem_preimage, equalAreaSpherePatch, mem_image]
  constructor
  · rintro ⟨p, hp, hx⟩
    refine ⟨p, hp, ?_⟩
    change equalAreaPhi p = g.symm (x:Ambient9)
    rw [hx, g.symm_apply_apply]
  · rintro ⟨p, hp, hx⟩
    refine ⟨p, hp, ?_⟩
    change equalAreaPhi p = g.symm (x:Ambient9) at hx
    rw [hx, g.apply_symm_apply]

theorem chartImage8_measurable (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) {S : Set (Fin 8 → ℝ)}
    (hS : MeasurableSet S) (hsub : S ⊆ equalAreaChartDomain) : MeasurableSet (chartImage8 g S) := by
  rw [chartImage8_eq_preimage]
  exact (equalAreaSpherePatch_measurable S hS hsub).preimage (sphereRotation8 g.symm).measurable

theorem chartImage8_area (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) {S : Set (Fin 8 → ℝ)}
    (hS : MeasurableSet S) (hsub : S ⊆ equalAreaChartDomain) :
    sphereArea8 (chartImage8 g S) = (volume : Measure (Fin 8 → ℝ)) S := by
  rw [chartImage8_eq_preimage, (sphereArea8_rotation_preserving g.symm).measure_preimage_emb
    (sphereRotation8 g.symm).measurableEmbedding, sphereArea8_equalAreaSpherePatch S hS hsub]

theorem chartImage8_mono (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) {S T : Set (Fin 8 → ℝ)} (h : S ⊆ T) :
    chartImage8 g S ⊆ chartImage8 g T := by
  rintro x ⟨p, hp, hx⟩
  exact ⟨p, h hp, hx⟩

theorem chartImage8_disjoint (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) {S T : Set (Fin 8 → ℝ)}
    (hS : S ⊆ equalAreaChartDomain) (hT : T ⊆ equalAreaChartDomain) (hST : Disjoint S T) :
    Disjoint (chartImage8 g S) (chartImage8 g T) := by
  rw [Set.disjoint_left]
  rintro x ⟨p, hp, hx⟩ ⟨q, hq, hx'⟩
  have : equalAreaPhi p = equalAreaPhi q := g.injective (hx.symm.trans hx')
  have hpq := equalAreaPhi_injOn (hS hp) (hT hq) this
  subst hpq
  exact Set.disjoint_left.mp hST hp hq

/-- The image of a compact coordinate set is closed. -/
theorem chartImage8_isClosed (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) {S : Set (Fin 8 → ℝ)}
    (hS : IsCompact S) : IsClosed (chartImage8 g S) := by
  have hc : IsCompact ((fun p => g (equalAreaPhi p)) '' S) :=
    hS.image (g.continuous.comp equalAreaPhi_continuous)
  have he : chartImage8 g S = Subtype.val ⁻¹' ((fun p => g (equalAreaPhi p)) '' S) := by
    ext x
    simp only [chartImage8, mem_setOf_eq, mem_preimage, mem_image]
    constructor
    · rintro ⟨p, hp, hx⟩; exact ⟨p, hp, hx.symm⟩
    · rintro ⟨p, hp, hx⟩; exact ⟨p, hp, hx.symm⟩
  rw [he]
  exact hc.isClosed.preimage continuous_subtype_val

/-- The image of an open coordinate set inside the chart domain is open. -/
theorem chartImage8_isOpen (g : Ambient9 ≃ₗᵢ[ℝ] Ambient9) {S : Set (Fin 8 → ℝ)}
    (hS : IsOpen S) (hsub : S ⊆ equalAreaChartDomain) : IsOpen (chartImage8 g S) := by
  rw [chartImage8_eq_preimage]
  apply IsOpen.preimage (sphereRotation8 g.symm).continuous
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨p, hp, hx⟩
  have hx0 : 0 < (x:Ambient9) 0 := by
    rw [← hx]
    exact equalAreaPhi_first_pos p (hsub hp)
  have hcoord : WithLp.ofLp (sphereEqualAreaCoordinates8 x) = p := by
    have h := equalAreaInverse8_phi p (hsub hp)
    rw [hx] at h
    simpa [sphereEqualAreaCoordinates8] using h
  have hca := sphereEqualAreaCoordinates8_continuousAt x hx0
  have hS' : IsOpen ((fun u : EuclideanSpace ℝ (Fin 8) => WithLp.ofLp u) ⁻¹' S) :=
    hS.preimage (PiLp.continuous_ofLp 2 _)
  have hnb : (fun u : EuclideanSpace ℝ (Fin 8) => WithLp.ofLp u) ⁻¹' S ∈ 𝓝 (sphereEqualAreaCoordinates8 x) := by
    apply hS'.mem_nhds
    simp only [mem_preimage]
    rw [hcoord]; exact hp
  have hpos : {y : Sphere8 | 0 < (y:Ambient9) 0} ∈ 𝓝 x :=
    (isOpen_lt continuous_const (by fun_prop)).mem_nhds hx0
  filter_upwards [hca hnb, hpos] with y hy hy0
  refine ⟨WithLp.ofLp (sphereEqualAreaCoordinates8 y), hy, ?_⟩
  have h := equalAreaPhi_inverse8 y hy0
  simpa [sphereEqualAreaCoordinates8] using h

#print axioms isPreconnected_inter_frontier
#print axioms chartImage8_eq_preimage
#print axioms chartImage8_measurable
#print axioms chartImage8_area
#print axioms chartImage8_mono
#print axioms chartImage8_disjoint
#print axioms chartImage8_isClosed
#print axioms chartImage8_isOpen

end SphericalRiesz
