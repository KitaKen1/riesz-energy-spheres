import Riesz.ExactMassCut

/-! Exact-mass slicing (stage NEG, stratification).

A measurable region `S` of a finite measure, cut by a bounded measurable function `f` whose level
sets meet `S` in null sets, splits into `n` slices of mass exactly `μ(S)/n`: cut at levels `c_k`
where the cumulative mass `μ({f ≤ c_k} ∩ S)` is `(k+1) μ(S)/n` (intermediate value theorem for
the distribution function, `exists_cut_measure_eq_restrict`), with the last cumulative set equal
to `S`, and take the disjointed differences. For `μ(S) > 0` the cut levels increase, so each
slice is `{c_{k-1} < f ≤ c_k} ∩ S` and has mass `μ(S)/n`; for `μ(S) = 0` every slice is null.
This is the one-dimensional step of the exact-mass stratifications (fine cells inside a coarse
cell are obtained by slicing in successive coordinates). -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz

theorem exists_exact_mass_slices {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] {S : Set X} (hS : MeasurableSet S) {f : X → ℝ} (hf : Measurable f)
    {R : ℝ} (hR : ∀ x, |f x| ≤ R) (hnull : ∀ c, μ (f ⁻¹' {c} ∩ S) = 0) {n : ℕ} (hn : 0 < n) :
    ∃ C : Fin n → Set X, (∀ j, MeasurableSet (C j)) ∧
      Pairwise (fun i j => Disjoint (C i) (C j)) ∧ (⋃ j, C j) = S ∧
      ∀ j, μ.real (C j) = μ.real S/n := by
  classical
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  set m := μ.real S/n with hmdef
  have hm0 : 0 ≤ m := div_nonneg measureReal_nonneg hn'.le
  have hSm : μ.real S = n*m := by
    rw [hmdef]
    field_simp
  have hcut : ∀ k : ℕ, ∃ c : ℝ, k+1 < n → μ.real (f ⁻¹' Iic c ∩ S) = ((k:ℝ)+1)*m := by
    intro k
    by_cases hk : k+1 < n
    · have hk' : ((k:ℝ)+1) ≤ n := by exact_mod_cast hk.le
      obtain ⟨c, hc⟩ := exists_cut_measure_eq_restrict μ S hf hR hnull (m := ((k:ℝ)+1)*m)
        (mul_nonneg (by positivity) hm0) (by rw [hSm]; exact mul_le_mul_of_nonneg_right hk' hm0)
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose c hc using hcut
  set A : ℕ → Set X := fun k => if k+1 < n then f ⁻¹' Iic (c k) ∩ S else S with hAdef
  have hAm : ∀ k, MeasurableSet (A k) := by
    intro k
    simp only [hAdef]
    split_ifs
    · exact (hf measurableSet_Iic).inter hS
    · exact hS
  have hAS : ∀ k, A k ⊆ S := by
    intro k
    simp only [hAdef]
    split_ifs
    · exact inter_subset_right
    · exact subset_rfl
  have hAlast : A (n-1) = S := by
    simp only [hAdef]
    rw [if_neg (by omega)]
  have hAmass : ∀ k, k < n → μ.real (A k) = ((k:ℝ)+1)*m := by
    intro k hk
    simp only [hAdef]
    split_ifs with h
    · exact hc k h
    · have hkn : k+1 = n := by omega
      have hkn' : (n:ℝ) = (k:ℝ)+1 := by exact_mod_cast hkn.symm
      rw [hSm, hkn']
  refine ⟨fun j => disjointed A j, fun j => MeasurableSet.disjointed hAm j, ?_, ?_, ?_⟩
  · intro i j hij
    exact disjoint_disjointed A (fun h => hij (Fin.ext h))
  · apply Subset.antisymm
    · exact iUnion_subset fun j => (disjointed_subset A j).trans (hAS j)
    · intro x hx
      have hxA : x ∈ ⋃ k, A k := mem_iUnion.mpr ⟨n-1, by rw [hAlast]; exact hx⟩
      rw [← iUnion_disjointed] at hxA
      obtain ⟨k, hk⟩ := mem_iUnion.mp hxA
      by_cases hkn : k < n
      · exact mem_iUnion.mpr ⟨⟨k, hkn⟩, hk⟩
      · exfalso
        rw [disjointed_apply] at hk
        apply hk.2
        have hmem : n-1 ∈ Finset.Iio k := Finset.mem_Iio.mpr (by omega)
        have hle : A (n-1) ≤ (Finset.Iio k).sup A := Finset.le_sup (f := A) hmem
        exact hle (by rw [hAlast]; exact hx)
  · intro j
    by_cases hm : m = 0
    · have hS0 : μ.real S = 0 := by rw [hSm, hm, mul_zero]
      have h1 : μ.real (disjointed A j) ≤ μ.real S :=
        measureReal_mono ((disjointed_subset A j).trans (hAS j))
      have h2 : 0 ≤ μ.real (disjointed A j) := measureReal_nonneg
      show μ.real (disjointed A j) = m
      linarith
    · have hmpos : 0 < m := lt_of_le_of_ne hm0 (Ne.symm hm)
      have hmono : Monotone A := by
        apply monotone_nat_of_le_succ
        intro k
        by_cases hk : k+1+1 < n
        · have hk1 : k+1 < n := by omega
          simp only [hAdef, if_pos hk, if_pos hk1]
          apply inter_subset_inter_left
          apply preimage_mono
          apply Iic_subset_Iic.mpr
          by_contra hlt
          have hlt' := lt_of_not_ge hlt
          have hsub : f ⁻¹' Iic (c (k+1)) ∩ S ⊆ f ⁻¹' Iic (c k) ∩ S :=
            inter_subset_inter_left _ (preimage_mono (Iic_subset_Iic.mpr hlt'.le))
          have hle := measureReal_mono (μ := μ) hsub
          rw [hc k hk1, hc (k+1) hk] at hle
          push_cast at hle
          nlinarith
        · show A k ⊆ A (k+1)
          have hA1 : A (k+1) = S := by
            simp only [hAdef]
            rw [if_neg hk]
          rw [hA1]
          exact hAS k
      obtain ⟨k, hk⟩ := j
      show μ.real (disjointed A k) = m
      cases k with
      | zero =>
        rw [disjointed_zero, hAmass 0 hk]
        push_cast
        ring
      | succ k =>
        have hs := hmono.disjointed_succ (i := k) (not_isMax k)
        rw [Order.succ_eq_add_one] at hs
        rw [hs, measureReal_sdiff (hmono (by omega : k ≤ k+1)) (hAm k) (measure_ne_top μ _), hAmass (k+1) hk,
          hAmass k (by omega)]
        push_cast
        ring

#print axioms exists_exact_mass_slices

end SphericalRiesz
