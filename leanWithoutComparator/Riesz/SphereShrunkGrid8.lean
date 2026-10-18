import Riesz.SphereGridMass8
import Riesz.EqualAreaFinitePatchGeometry8

/-! Construct a near-full separated compact interval-cell family on the actual
unit sphere. A common shrink parameter gives exact physical mass accounting.
This does not yet identify the cells with the uniform affine unit-cube class. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
namespace SphericalRiesz

theorem e8GridSphereSigma8_disjoint {K : ℕ}
    (g : Fin K → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (U : Fin K → Set Sphere8)
    (h : ℝ) (hh : 0 < h) (Z : Fin K → Finset (Fin 8 → ℤ))
    (hdom : ∀ i z, z ∈ Z i → e8Map '' gridClosedCell8 h z ⊆ equalAreaChartDomain)
    (hU : ∀ i z, z ∈ Z i → equalAreaE8SpherePatch8 (g i) 0 0 1
      (gridClosedCell8 h z) ⊆ U i)
    (hd : Pairwise (fun i j => Disjoint (U i) (U j))) :
    Pairwise (fun p q : (Σ i : Fin K, Z i) => Disjoint
      (equalAreaE8SpherePatch8 (g p.1) 0 0 1 (gridHalfOpenCell8 h p.2.val))
      (equalAreaE8SpherePatch8 (g q.1) 0 0 1 (gridHalfOpenCell8 h q.2.val))) := by
  classical
  rintro ⟨i,z⟩ ⟨j,w⟩ hpq
  by_cases hij : i = j
  · subst j
    have hzw : z.val ≠ w.val := by
      intro he
      exact hpq (by congr 1; exact Subtype.ext he)
    exact e8GridSpherePatch8_disjoint (g i) _ _
      ((image_mono (gridHalfOpenCell8_subset_closed h z.val)).trans (hdom i z.val z.property))
      ((image_mono (gridHalfOpenCell8_subset_closed h w.val)).trans (hdom i w.val w.property))
      (gridHalfOpenCell8_pairwise_disjoint h hh hzw)
  · exact (hd hij).mono
      ((e8GridSpherePatch8_mono _ (gridHalfOpenCell8_subset_closed h z.val)).trans
        (hU i z.val z.property))
      ((e8GridSpherePatch8_mono _ (gridHalfOpenCell8_subset_closed h w.val)).trans
        (hU j w.val w.property))

theorem sphere8_finite_small_chart_grid_flat (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ L : ℕ, ∃ g : Fin L → Ambient9 ≃ₗᵢ[ℝ] Ambient9,
      ∃ z : Fin L → Fin 8 → ℤ, ∃ h > 0,
      (∀ i, e8Map '' gridClosedCell8 h (z i) ⊆ equalAreaChartDomain ∧
        ∀ x ∈ gridClosedCell8 h (z i), ‖e8Map x‖ < a) ∧
      Pairwise (fun i j => Disjoint
        (equalAreaE8SpherePatch8 (g i) 0 0 1 (gridHalfOpenCell8 h (z i)))
        (equalAreaE8SpherePatch8 (g j) 0 0 1 (gridHalfOpenCell8 h (z j)))) ∧
      1-b < sphereProbability8.real
        (⋃ i, equalAreaE8SpherePatch8 (g i) 0 0 1 (gridHalfOpenCell8 h (z i))) := by
  classical
  obtain ⟨K,g,U,h,hh,Z,hcell,hmass,hd⟩ := sphere8_finite_small_chart_grid a b ha hb
  let I := Σ i : Fin K, Z i
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let g' := fun j => g (e.symm j).1
  let z' := fun j => (e.symm j).2.val
  have hdI := e8GridSphereSigma8_disjoint g U h hh Z
    (fun i z hz => ((hcell i).2 z hz).1)
    (fun i z hz => ((hcell i).2 z hz).2.2) hd
  have heq : (⋃ j, equalAreaE8SpherePatch8 (g' j) 0 0 1 (gridHalfOpenCell8 h (z' j))) =
      ⋃ i, ⋃ z ∈ Z i, equalAreaE8SpherePatch8 (g i) 0 0 1 (gridHalfOpenCell8 h z) := by
    ext q
    constructor
    · intro hq
      obtain ⟨j,hj⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨(e.symm j).1,mem_iUnion₂.mpr
        ⟨(e.symm j).2.val,(e.symm j).2.property,hj⟩⟩
    · intro hq
      obtain ⟨i,hi⟩ := mem_iUnion.mp hq
      obtain ⟨z,hz,hzq⟩ := mem_iUnion₂.mp hi
      refine mem_iUnion.mpr ⟨e ⟨i,⟨z,hz⟩⟩,?_⟩
      change q ∈ equalAreaE8SpherePatch8 (g (e.symm (e ⟨i,⟨z,hz⟩⟩)).1) 0 0 1
        (gridHalfOpenCell8 h (e.symm (e ⟨i,⟨z,hz⟩⟩)).2.val)
      rw [e.symm_apply_apply]
      exact hzq
  refine ⟨Fintype.card I,g',z',h,hh,?_,?_,?_⟩
  · intro j
    exact ⟨((hcell (e.symm j).1).2 _ (e.symm j).2.property).1,
      ((hcell (e.symm j).1).2 _ (e.symm j).2.property).2.1⟩
  · intro i j hij
    exact hdI (e.symm.injective.ne hij)
  · simpa only [heq] using hmass

theorem shrinkMass8_loss_budget (b m : ℝ) (hb : 0 < b)
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hm : 1-min (b/4) (1/4) < m) :
    ∃ γ > 0, γ < 1 ∧ 1-b < (1-γ)^8*m ∧ (1-γ)^8*m < 1 := by
  let β := min (b/4) (1/4)
  have hβ : 0 < β := lt_min (by positivity) (by norm_num)
  have hβb : β ≤ b/4 := min_le_left _ _
  have hβ1 : β ≤ 1/4 := min_le_right _ _
  let γ := β/16
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hγ1 : γ < 1 := by dsimp [γ]; linarith
  have hf0 : 0 ≤ (1-γ)^8 := pow_nonneg (by linarith) _
  have hf1 : (1-γ)^8 < 1 := pow_lt_one₀ (by linarith) (by linarith) (by decide)
  have hber : 1-8*γ ≤ (1-γ)^8 := by
    have h := one_add_mul_le_pow (a := -γ) (by linarith : -2 ≤ -γ) 8
    simpa only [Nat.cast_ofNat,mul_neg,← sub_eq_add_neg] using h
  have hproduct := mul_le_mul_of_nonneg_right hber hm0
  have hmul := mul_le_mul_of_nonneg_left hm1 (show 0 ≤ 8*γ by positivity)
  have hm' : 1-β < m := hm
  refine ⟨γ,hγ,hγ1,?_,?_⟩
  · dsimp [γ] at hproduct hmul ⊢
    nlinarith
  · exact (mul_le_mul_of_nonneg_left hm1 hf0).trans_lt (by simpa using hf1)

theorem sphere8_near_full_separated_shrunk_grid (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ L : ℕ, ∃ g : Fin L → Ambient9 ≃ₗᵢ[ℝ] Ambient9,
      ∃ z : Fin L → Fin 8 → ℤ, ∃ h > 0, ∃ γ > 0, γ < 1 ∧
      (∀ i, e8Map '' gridShrunkCell8 h γ (z i) ⊆ equalAreaChartDomain ∧
        (∀ x ∈ gridShrunkCell8 h γ (z i), ‖e8Map x‖ < a) ∧
        IsCompact (equalAreaE8SpherePatch8 (g i) 0 0 1 (gridShrunkCell8 h γ (z i)))) ∧
      Pairwise (fun i j => Disjoint
        (equalAreaE8SpherePatch8 (g i) 0 0 1 (gridShrunkCell8 h γ (z i)))
        (equalAreaE8SpherePatch8 (g j) 0 0 1 (gridShrunkCell8 h γ (z j)))) ∧
      (∃ δ > 0, ∀ i j, i ≠ j →
        ∀ x ∈ equalAreaE8SpherePatch8 (g i) 0 0 1 (gridShrunkCell8 h γ (z i)),
        ∀ y ∈ equalAreaE8SpherePatch8 (g j) 0 0 1 (gridShrunkCell8 h γ (z j)), δ < dist x y) ∧
      1-b < sphereProbability8.real
        (⋃ i, equalAreaE8SpherePatch8 (g i) 0 0 1 (gridShrunkCell8 h γ (z i))) ∧
      sphereProbability8.real
        (⋃ i, equalAreaE8SpherePatch8 (g i) 0 0 1 (gridShrunkCell8 h γ (z i))) < 1 := by
  classical
  obtain ⟨L,g,z,h,hh,hcell,hd,hm⟩ := sphere8_finite_small_chart_grid_flat a
    (min (b/4) (1/4)) ha (lt_min (by positivity) (by norm_num))
  let H := ⋃ i, equalAreaE8SpherePatch8 (g i) 0 0 1 (gridHalfOpenCell8 h (z i))
  obtain ⟨γ,hγ,hγ1,hl,hu⟩ := shrinkMass8_loss_budget b (sphereProbability8.real H) hb
    measureReal_nonneg measureReal_le_one hm
  have hs : ∀ i, gridShrunkCell8 h γ (z i) ⊆ gridClosedCell8 h (z i) := fun i =>
    (gridShrunkCell8_subset_halfOpen h γ hh hγ (z i)).trans
      (gridHalfOpenCell8_subset_closed h (z i))
  have hcompact : ∀ i, IsCompact
      (equalAreaE8SpherePatch8 (g i) 0 0 1 (gridShrunkCell8 h γ (z i))) := fun i =>
    e8GridSpherePatch8_isCompact _ _ (gridShrunkCell8_isCompact h γ (z i))
  have hd' := e8GridShrunkSphereFamily8_disjoint g z h γ hh hγ hd
  have heq := e8GridShrunkSphereFamily8_probability_real_factor g z h γ hh hγ hγ1.le
    (fun i => (hcell i).1) hd
  refine ⟨L,g,z,h,hh,γ,hγ,hγ1,?_,hd',
    finite_compact_disjoint_distance8 _ hcompact hd',?_,?_⟩
  · intro i
    exact ⟨(image_mono (hs i)).trans (hcell i).1,
      fun x hx => (hcell i).2 x (hs i hx),hcompact i⟩
  · rw [heq]; exact hl
  · rw [heq]; exact hu

end SphericalRiesz
