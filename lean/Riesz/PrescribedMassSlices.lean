import Riesz.ExactMassCut

/-! Slicing with prescribed masses (stage NEG, stratification).

A measurable region `S` of a finite measure, cut by a bounded measurable function `f` whose level
sets meet `S` in null sets, splits into `n` slices with any prescribed nonnegative masses
`w_0, …, w_{n-1}` summing to `μ(S)`: cut at levels `c_k` where the cumulative mass is
`w_0 + … + w_k` (intermediate value theorem), replace the levels by their running maxima (the
cumulative mass is unchanged, since the cumulative masses are nondecreasing), and take the
disjointed differences. This is the uneven step of the exact-mass stratifications: a piece that
must contain `q` cells is cut into pieces containing `⌊q/2⌋` and `⌈q/2⌉` cells. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz

theorem exists_prescribed_mass_slices {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] {S : Set X} (hS : MeasurableSet S) {f : X → ℝ} (hf : Measurable f)
    {R : ℝ} (hR : ∀ x, |f x| ≤ R) (hnull : ∀ c, μ (f ⁻¹' {c} ∩ S) = 0) {n : ℕ} (hn : 0 < n)
    (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = μ.real S) :
    ∃ C : Fin n → Set X, (∀ j, MeasurableSet (C j)) ∧
      Pairwise (fun i j => Disjoint (C i) (C j)) ∧ (⋃ j, C j) = S ∧
      ∀ j, μ.real (C j) = w j := by
  classical
  -- weights on ℕ and cumulative masses
  set w' : ℕ → ℝ := fun k => if h : k < n then w ⟨k, h⟩ else 0 with hw'def
  have hw'0 : ∀ k, 0 ≤ w' k := by
    intro k
    simp only [hw'def]
    split_ifs
    · exact hw _
    · exact le_rfl
  set P : ℕ → ℝ := fun k => ∑ i ∈ Finset.range (k+1), w' i with hPdef
  have hPsucc : ∀ k, P (k+1) = P k+w' (k+1) := by
    intro k
    simp only [hPdef]
    rw [Finset.sum_range_succ]
  have hPmono : Monotone P := by
    apply monotone_nat_of_le_succ
    intro k
    rw [hPsucc]
    linarith [hw'0 (k+1)]
  have hPlast : P (n-1) = μ.real S := by
    rw [← hsum]
    simp only [hPdef]
    have hn1 : n-1+1 = n := by omega
    rw [hn1, Finset.sum_range (fun i => w' i)]
    apply Finset.sum_congr rfl
    intro j _
    simp only [hw'def, dif_pos j.2]
  have hP0 : ∀ k, 0 ≤ P k := fun k => Finset.sum_nonneg fun i _ => hw'0 i
  -- cut levels
  have hcut : ∀ k : ℕ, ∃ c : ℝ, k+1 < n → μ.real (f ⁻¹' Iic c ∩ S) = P k := by
    intro k
    by_cases hk : k+1 < n
    · obtain ⟨c, hc⟩ := exists_cut_measure_eq_restrict μ S hf hR hnull (m := P k) (hP0 k)
        (by rw [← hPlast]; exact hPmono (by omega))
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose c hc using hcut
  -- running maxima of the levels
  let c' : ℕ → ℝ := fun k => Nat.rec (c 0) (fun k ck => max ck (c (k+1))) k
  have hc'succ : ∀ k, c' (k+1) = max (c' k) (c (k+1)) := fun k => rfl
  have hc'mono : Monotone c' := by
    apply monotone_nat_of_le_succ
    intro k
    rw [hc'succ]
    exact le_max_left _ _
  have hc'ge : ∀ k, c k ≤ c' k := by
    intro k
    cases k with
    | zero => exact le_rfl
    | succ k => rw [hc'succ]; exact le_max_right _ _
  have hc'eq : ∀ k, ∃ i ≤ k, c' k = c i := by
    intro k
    induction k with
    | zero => exact ⟨0, le_rfl, rfl⟩
    | succ k ih =>
      obtain ⟨i, hi, hci⟩ := ih
      rw [hc'succ]
      rcases le_total (c' k) (c (k+1)) with h | h
      · exact ⟨k+1, le_rfl, max_eq_right h⟩
      · exact ⟨i, by omega, by rw [max_eq_left h, hci]⟩
  have hc'mass : ∀ k, k+1 < n → μ.real (f ⁻¹' Iic (c' k) ∩ S) = P k := by
    intro k hk
    obtain ⟨i, hi, hci⟩ := hc'eq k
    apply le_antisymm
    · rw [hci, hc i (by omega)]
      exact hPmono hi
    · rw [← hc k hk]
      exact measureReal_mono (inter_subset_inter_left _ (preimage_mono (Iic_subset_Iic.mpr (hc'ge k))))
  -- cumulative sets
  set A : ℕ → Set X := fun k => if k+1 < n then f ⁻¹' Iic (c' k) ∩ S else S with hAdef
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
  have hAmass : ∀ k, k < n → μ.real (A k) = P k := by
    intro k hk
    simp only [hAdef]
    split_ifs with h
    · exact hc'mass k h
    · have hkn : k = n-1 := by omega
      rw [hkn, hPlast]
  have hmono : Monotone A := by
    apply monotone_nat_of_le_succ
    intro k
    by_cases hk : k+1+1 < n
    · have hk1 : k+1 < n := by omega
      simp only [hAdef, if_pos hk, if_pos hk1]
      exact inter_subset_inter_left _ (preimage_mono (Iic_subset_Iic.mpr (hc'mono (show k ≤ k+1 by omega))))
    · show A k ⊆ A (k+1)
      have hA1 : A (k+1) = S := by
        simp only [hAdef]
        rw [if_neg hk]
      rw [hA1]
      exact hAS k
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
    obtain ⟨k, hk⟩ := j
    show μ.real (disjointed A k) = w ⟨k, hk⟩
    have hwk : w ⟨k, hk⟩ = w' k := by simp only [hw'def, dif_pos hk]
    rw [hwk]
    cases k with
    | zero =>
      rw [disjointed_zero, hAmass 0 hk]
      simp only [hPdef, zero_add, Finset.sum_range_one]
    | succ k =>
      have hs := hmono.disjointed_succ (i := k) (not_isMax k)
      rw [Order.succ_eq_add_one] at hs
      have hd : μ.real (A (k+1) \ A k) = μ.real (A (k+1))-μ.real (A k) :=
        measureReal_sdiff (hmono (show k ≤ k+1 by omega)) (hAm k) (measure_ne_top μ _)
      rw [hs]
      refine hd.trans ?_
      rw [hAmass (k+1) hk, hAmass k (by omega), hPsucc]
      ring

#print axioms exists_prescribed_mass_slices

end SphericalRiesz
