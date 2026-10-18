import Riesz.PrescribedMassSlices

/-! Carry-over slicing over coarse sets (stage NEG, stratification).

`exists_exact_mass_slices_Ioc`: the exact-mass slices of `S` by a bounded measurable `f` with null
level sets can be taken inside consecutive `f`-intervals `(t_j, t_(j+1)]` with `t` monotone (the
cut levels are replaced by their running maxima and clamped below `-R-1`, which does not change
the cumulative sets).

`exists_exact_mass_carry_slices`: if `P` is covered by `M` pairwise disjoint coarse sets `Q_k`,
slicing `P` by `Φ = 3 k(x) + g(x)` (`|g| ≤ 1`) gives `n` cells of mass exactly `μ(P)/n` such that,
outside a set of at most `M` straddling cells, every cell lies in a single coarse set: a slice
meeting two coarse sets contains a separator `3k + 3/2` in its `Φ`-interval, and the intervals
are disjoint. This is the step that turns a pool of small mass into exact-mass cells whose
diameters are controlled by the coarse scale, up to `M` cells. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz

theorem exists_exact_mass_slices_Ioc {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] {S : Set X} (hS : MeasurableSet S) {f : X → ℝ} (hf : Measurable f)
    {R : ℝ} (hR : ∀ x, |f x| ≤ R) (hnull : ∀ c, μ (f ⁻¹' {c} ∩ S) = 0) {n : ℕ} (hn : 0 < n) :
    ∃ C : Fin n → Set X, ∃ t : ℕ → ℝ, Monotone t ∧ (∀ j, MeasurableSet (C j)) ∧
      Pairwise (fun i j => Disjoint (C i) (C j)) ∧ (⋃ j, C j) = S ∧
      (∀ j, μ.real (C j) = μ.real S/n) ∧
      ∀ j : Fin n, C j ⊆ f ⁻¹' Ioc (t j) (t (j+1)) := by
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
  have hfR : ∀ x, -R ≤ f x ∧ f x ≤ R := fun x => abs_le.mp (hR x)
  -- running maxima, clamped below
  let c' : ℕ → ℝ := fun k => Nat.rec (max (-R-1) (c 0)) (fun k ck => max ck (c (k+1))) k
  have hc'succ : ∀ k, c' (k+1) = max (c' k) (c (k+1)) := fun k => rfl
  have hc'0 : c' 0 = max (-R-1) (c 0) := rfl
  have hc'mono : Monotone c' := by
    apply monotone_nat_of_le_succ
    intro k
    rw [hc'succ]
    exact le_max_left _ _
  have hc'low : ∀ k, -R-1 ≤ c' k := by
    intro k
    induction k with
    | zero => rw [hc'0]; exact le_max_left _ _
    | succ k ih => rw [hc'succ]; exact ih.trans (le_max_left _ _)
  have hc'ge : ∀ k, c k ≤ c' k := by
    intro k
    cases k with
    | zero => rw [hc'0]; exact le_max_right _ _
    | succ k => rw [hc'succ]; exact le_max_right _ _
  have hc'eq : ∀ k, (∃ i ≤ k, c' k = c i) ∨ c' k = -R-1 := by
    intro k
    induction k with
    | zero =>
      rcases le_total (-R-1) (c 0) with h | h
      · exact Or.inl ⟨0, le_rfl, by rw [hc'0, max_eq_right h]⟩
      · exact Or.inr (by rw [hc'0, max_eq_left h])
    | succ k ih =>
      rw [hc'succ]
      rcases le_total (c' k) (c (k+1)) with h | h
      · exact Or.inl ⟨k+1, le_rfl, max_eq_right h⟩
      · rcases ih with ⟨i, hi, hci⟩ | hci
        · exact Or.inl ⟨i, by omega, by rw [max_eq_left h, hci]⟩
        · exact Or.inr (by rw [max_eq_left h, hci])
  have hset : ∀ k, k+1 < n → f ⁻¹' Iic (c' k) ∩ S = f ⁻¹' Iic (c k) ∩ S ∨
      μ.real (f ⁻¹' Iic (c' k) ∩ S) = ((k:ℝ)+1)*m := by
    intro k hk
    right
    rcases hc'eq k with ⟨i, hi, hci⟩ | hci
    · apply le_antisymm
      · rw [hci, hc i (by omega)]
        have : ((i:ℝ)+1) ≤ (k:ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hi 1
        exact mul_le_mul_of_nonneg_right this hm0
      · rw [← hc k hk]
        exact measureReal_mono (inter_subset_inter_left _ (preimage_mono (Iic_subset_Iic.mpr (hc'ge k))))
    · -- the clamped level is below every value, so the cut level is too
      have hempty : f ⁻¹' Iic (c' k) ∩ S = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_and]
        intro hx _
        have := (hfR x).1
        rw [hci] at hx
        linarith
      have hempty2 : f ⁻¹' Iic (c k) ∩ S = ∅ := by
        apply Set.eq_empty_of_subset_empty
        rw [← hempty]
        exact inter_subset_inter_left _ (preimage_mono (Iic_subset_Iic.mpr (hc'ge k)))
      have h0 := hc k hk
      rw [hempty2, measureReal_empty] at h0
      rw [hempty, measureReal_empty, ← h0]
  have hc'mass : ∀ k, k+1 < n → μ.real (f ⁻¹' Iic (c' k) ∩ S) = ((k:ℝ)+1)*m := by
    intro k hk
    rcases hset k hk with h | h
    · rw [h]; exact hc k hk
    · exact h
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
  have hAmass : ∀ k, k < n → μ.real (A k) = ((k:ℝ)+1)*m := by
    intro k hk
    simp only [hAdef]
    split_ifs with h
    · exact hc'mass k h
    · have hkn : k+1 = n := by omega
      have hkn' : (n:ℝ) = (k:ℝ)+1 := by exact_mod_cast hkn.symm
      rw [hSm, hkn']
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
  -- the thresholds
  let t : ℕ → ℝ := fun k => Nat.casesOn k (-R-1) (fun k => if k+1 < n then c' k else max R (c' k))
  have ht0 : t 0 = -R-1 := rfl
  have htsucc : ∀ k, t (k+1) = if k+1 < n then c' k else max R (c' k) := fun k => rfl
  have htmono : Monotone t := by
    apply monotone_nat_of_le_succ
    intro k
    cases k with
    | zero =>
      rw [ht0, htsucc]
      split_ifs
      · exact hc'low 0
      · exact (hc'low 0).trans (le_max_right _ _)
    | succ k =>
      rw [htsucc, htsucc]
      split_ifs with h1 h2 h2
      · exact hc'mono (Nat.le_succ k)
      · exact (hc'mono (Nat.le_succ k)).trans (le_max_right _ _)
      · omega
      · exact max_le_max le_rfl (hc'mono (Nat.le_succ k))
  refine ⟨fun j => disjointed A j, t, htmono, fun j => MeasurableSet.disjointed hAm j, ?_, ?_, ?_, ?_⟩
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
    show μ.real (disjointed A k) = m
    cases k with
    | zero =>
      rw [disjointed_zero, hAmass 0 hk]
      push_cast
      ring
    | succ k =>
      have hs := hmono.disjointed_succ (i := k) (not_isMax k)
      rw [Order.succ_eq_add_one] at hs
      have hd : μ.real (A (k+1) \ A k) = μ.real (A (k+1))-μ.real (A k) :=
        measureReal_sdiff (hmono (show k ≤ k+1 by omega)) (hAm k) (measure_ne_top μ _)
      rw [hs]
      refine hd.trans ?_
      rw [hAmass (k+1) hk, hAmass k (by omega)]
      push_cast
      ring
  · intro j x hx
    obtain ⟨k, hk⟩ := j
    change x ∈ disjointed A k at hx
    have hxS : x ∈ S := (disjointed_subset A k).trans (hAS k) hx
    have hfx := hfR x
    simp only [mem_preimage, mem_Ioc]
    cases k with
    | zero =>
      rw [disjointed_zero] at hx
      refine ⟨by rw [ht0]; linarith, ?_⟩
      show f x ≤ t (0+1)
      rw [htsucc]
      split_ifs with h
      · simp only [hAdef, if_pos h] at hx
        exact hx.1
      · exact hfx.2.trans (le_max_left _ _)
    | succ k =>
      have hs := hmono.disjointed_succ (i := k) (not_isMax k)
      rw [Order.succ_eq_add_one] at hs
      rw [hs] at hx
      have hk1 : k+1 < n := hk
      constructor
      · rw [htsucc, if_pos hk1]
        by_contra hle
        apply hx.2
        simp only [hAdef, if_pos hk1]
        exact ⟨le_of_not_gt hle, hxS⟩
      · show f x ≤ t (k+1+1)
        rw [htsucc]
        split_ifs with h
        · have hx1 := hx.1
          simp only [hAdef, if_pos h] at hx1
          exact hx1.1
        · exact hfx.2.trans (le_max_left _ _)

/-- Carry-over slicing over coarse sets: at most `M` cells straddle two coarse sets. -/
theorem exists_exact_mass_carry_slices {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] {P : Set X} (hP : MeasurableSet P) {M : ℕ} (Q : Fin M → Set X)
    (hQm : ∀ k, MeasurableSet (Q k)) (hQd : Pairwise (fun i j => Disjoint (Q i) (Q j)))
    (hPQ : P ⊆ ⋃ k, Q k) {g : X → ℝ} (hg : Measurable g) (hg1 : ∀ x, |g x| ≤ 1)
    (hgnull : ∀ c, μ (g ⁻¹' {c} ∩ P) = 0) {n : ℕ} (hn : 0 < n) :
    ∃ C : Fin n → Set X, (∀ j, MeasurableSet (C j)) ∧
      Pairwise (fun i j => Disjoint (C i) (C j)) ∧ (⋃ j, C j) = P ∧
      (∀ j, μ.real (C j) = μ.real P/n) ∧
      ∃ T : Finset (Fin n), T.card ≤ M ∧
        ∀ j ∉ T, ∀ x ∈ C j, ∀ y ∈ C j, ∃ k, x ∈ Q k ∧ y ∈ Q k := by
  classical
  -- the sweep function
  set Φ : X → ℝ := fun x => (∑ k : Fin M, (Q k).indicator (fun _ => 3*(k:ℝ)) x)+g x with hΦdef
  have hΦm : Measurable Φ := by
    apply Measurable.add _ hg
    apply Finset.measurable_sum
    intro k _
    exact measurable_const.indicator (hQm k)
  have hΦval : ∀ k : Fin M, ∀ x ∈ Q k, Φ x = 3*(k:ℝ)+g x := by
    intro k x hx
    simp only [hΦdef]
    congr 1
    rw [Finset.sum_eq_single k]
    · rw [indicator_of_mem hx]
    · intro b _ hbk
      rw [indicator_of_notMem]
      exact fun hb => (hQd hbk).le_bot ⟨hb, hx⟩
    · intro h
      exact absurd (Finset.mem_univ k) h
  have hsum_le : ∀ x, |∑ k : Fin M, (Q k).indicator (fun _ => 3*(k:ℝ)) x| ≤ 3*M := by
    intro x
    by_cases hx : ∃ k, x ∈ Q k
    · obtain ⟨k, hk⟩ := hx
      have h := hΦval k x hk
      simp only [hΦdef] at h
      have heq : (∑ k : Fin M, (Q k).indicator (fun _ => 3*(k:ℝ)) x) = 3*(k:ℝ) := by linarith
      rw [heq, abs_of_nonneg (by positivity)]
      have : (k:ℝ) ≤ M := by exact_mod_cast k.2.le
      linarith
    · simp only [not_exists] at hx
      have h0 : (∑ k : Fin M, (Q k).indicator (fun _ => 3*(k:ℝ)) x) = 0 := by
        apply Finset.sum_eq_zero
        intro k _
        exact indicator_of_notMem (hx k) _
      rw [h0, abs_zero]
      positivity
  have hΦR : ∀ x, |Φ x| ≤ 3*M+1 := by
    intro x
    simp only [hΦdef]
    calc |(∑ k : Fin M, (Q k).indicator (fun _ => 3*(k:ℝ)) x)+g x|
        ≤ |∑ k : Fin M, (Q k).indicator (fun _ => 3*(k:ℝ)) x|+|g x| := abs_add_le _ _
      _ ≤ 3*M+1 := add_le_add (hsum_le x) (hg1 x)
  have hΦnull : ∀ c, μ (Φ ⁻¹' {c} ∩ P) = 0 := by
    intro c
    have hsub : Φ ⁻¹' {c} ∩ P ⊆ ⋃ k : Fin M, g ⁻¹' {c-3*(k:ℝ)} ∩ P := by
      intro x ⟨hx, hxP⟩
      obtain ⟨k, hk⟩ := mem_iUnion.mp (hPQ hxP)
      refine mem_iUnion.mpr ⟨k, ?_, hxP⟩
      simp only [mem_preimage, mem_singleton_iff] at hx ⊢
      rw [hΦval k x hk] at hx
      linarith
    exact measure_mono_null hsub (measure_iUnion_null fun k => hgnull _)
  obtain ⟨C, t, htm, hCm, hCd, hCu, hCmass, hCt⟩ :=
    exists_exact_mass_slices_Ioc μ hP hΦm hΦR hΦnull hn
  refine ⟨C, hCm, hCd, hCu, hCmass, ?_⟩
  -- the straddling cells
  set T : Finset (Fin n) := Finset.univ.filter
    (fun j : Fin n => ∃ k : Fin M, t j < 3*(k:ℝ)+3/2 ∧ 3*(k:ℝ)+3/2 ≤ t (j+1)) with hTdef
  refine ⟨T, ?_, ?_⟩
  · -- each straddling cell contains its own separator
    have hsep : ∀ j ∈ T, ∃ k : Fin M, t j < 3*(k:ℝ)+3/2 ∧ 3*(k:ℝ)+3/2 ≤ t (j+1) := by
      intro j hj
      exact (Finset.mem_filter.mp hj).2
    rcases Nat.eq_zero_or_pos M with hM | hM
    · have hT0 : T = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro j hj
        obtain ⟨k, _⟩ := hsep j hj
        exact absurd k.2 (by omega)
      rw [hT0, Finset.card_empty]
      exact Nat.zero_le _
    have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
    choose! κ hκ using hsep
    have hinj : Set.InjOn κ T := by
      intro i hi j hj hij
      by_contra hne
      have h1 := hκ i hi
      have h2 := hκ j hj
      rw [hij] at h1
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have hle : ((i:ℕ)+1) ≤ (j:ℕ) := hlt
        have := htm hle
        linarith [h1.2, h2.1]
      · have hle : ((j:ℕ)+1) ≤ (i:ℕ) := hlt
        have := htm hle
        linarith [h1.1, h2.2]
    calc T.card ≤ (Finset.univ : Finset (Fin M)).card :=
          Finset.card_le_card_of_injOn κ (fun j _ => Finset.mem_univ _) hinj
      _ = M := by simp
  · intro j hj x hx y hy
    obtain ⟨kx, hkx⟩ := mem_iUnion.mp (hPQ (hCu ▸ mem_iUnion.mpr ⟨j, hx⟩))
    obtain ⟨ky, hky⟩ := mem_iUnion.mp (hPQ (hCu ▸ mem_iUnion.mpr ⟨j, hy⟩))
    by_cases hk : kx = ky
    · exact ⟨kx, hkx, hk ▸ hky⟩
    · exfalso
      apply hj
      have hx' := hCt j hx
      have hy' := hCt j hy
      simp only [mem_preimage, mem_Ioc] at hx' hy'
      rw [hΦval kx x hkx] at hx'
      rw [hΦval ky y hky] at hy'
      have hgx := abs_le.mp (hg1 x)
      have hgy := abs_le.mp (hg1 y)
      rw [hTdef, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hk) with hlt | hlt
      · refine ⟨kx, by linarith, ?_⟩
        have : (kx:ℝ)+1 ≤ (ky:ℝ) := by exact_mod_cast hlt
        linarith
      · refine ⟨ky, by linarith, ?_⟩
        have : (ky:ℝ)+1 ≤ (kx:ℝ) := by exact_mod_cast hlt
        linarith

#print axioms exists_exact_mass_slices_Ioc
#print axioms exists_exact_mass_carry_slices

end SphericalRiesz
