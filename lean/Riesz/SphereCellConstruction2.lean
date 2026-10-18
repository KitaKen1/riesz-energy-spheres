import Riesz.CarryOverSlices
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Sort
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-! Exact-mass geometric cells in compact connected metric carriers.
Finite nets, measurable nearest-centre cells, an ordered graph parent map and the tree split
are proved here. Applying these theorems to S² patch residuals still requires their local measure
lower bound and connectedness; no sphere residual existence is asserted by this module. -/

section

/-! A geometric replacement for the coarse diameter-two carry-over estimate.
If every coarse part has mass greater than one final cell, an exact-mass interval slice
cannot meet two coarse parts with an intervening part. An adjacent coarse ordering therefore
controls the diameter of every carry-over cell. Constructing that ordering and the required
mass lower bounds for the actual S² residual region is a separate task. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz

/-- A covering family of slices inside consecutive intervals fills each such interval. -/
theorem intervalSlice_full {X : Type*} {n : ℕ} {S : Set X} {f : X → ℝ}
    {C : Fin n → Set X} {t : ℕ → ℝ} (ht : Monotone t)
    (hcover : ∀ x ∈ S, ∃ k, x ∈ C k)
    (hinterval : ∀ k, C k ⊆ f ⁻¹' Ioc (t k) (t (k+1)))
    (j : Fin n) {x : X} (hx : x ∈ S)
    (hfx : f x ∈ Ioc (t j) (t (j+1))) : x ∈ C j := by
  obtain ⟨k, hk⟩ := hcover x hx
  have hfk := hinterval k hk
  rcases lt_trichotomy k.val j.val with h | h | h
  · have hkj : k.val+1 ≤ j.val := by omega
    have htkj := ht hkj
    exact False.elim (by linarith [hfk.2, hfx.1])
  · exact (Fin.ext h) ▸ hk
  · have hjk : j.val+1 ≤ k.val := by omega
    have htjk := ht hjk
    exact False.elim (by linarith [hfk.1, hfx.2])

/-- A cell of mass `m` cannot span a coarse part of mass greater than `m`. -/
theorem carrySlice_no_far_pair {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {M : ℕ} (Q : Fin M → Set X)
    {S C : Set X} {f : X → ℝ} {a b m : ℝ}
    (hQsub : ∀ i, Q i ⊆ S)
    (hQmass : ∀ i, m < μ.real (Q i)) (hCmass : μ.real C = m)
    (hbound : ∀ i, ∀ x ∈ Q i,
      3*(i.val:ℝ)-1 ≤ f x ∧ f x ≤ 3*(i.val:ℝ)+1)
    (hinterval : C ⊆ f ⁻¹' Ioc a b)
    (hfull : ∀ x ∈ S, f x ∈ Ioc a b → x ∈ C)
    {i j : Fin M} {x y : X} (hxC : x ∈ C) (hxQ : x ∈ Q i)
    (hyC : y ∈ C) (hyQ : y ∈ Q j) : ¬ i.val+1 < j.val := by
  intro hij
  let k : Fin M := ⟨i.val+1, by omega⟩
  have hleft := (hbound i x hxQ).2
  have hright := (hbound j y hyQ).1
  have hxI := hinterval hxC
  have hyI := hinterval hyC
  have hidx : (i.val:ℝ)+2 ≤ j.val := by exact_mod_cast (by omega : i.val+2 ≤ j.val)
  have hsub : Q k ⊆ C := by
    intro z hz
    have hzB := hbound k z hz
    have hk : (k.val:ℝ) = (i.val:ℝ)+1 := by simp [k]
    rw [hk] at hzB
    exact hfull z (hQsub k hz) ⟨by linarith [hxI.1], by linarith [hyI.2]⟩
  have hle : μ.real (Q k) ≤ μ.real C := measureReal_mono (μ := μ) hsub
  rw [hCmass] at hle
  exact (not_lt_of_ge hle) (hQmass k)

/-- Adjacent coarse parts give a uniform diameter bound for an exact-mass carry-over cell. -/
theorem carrySlice_diameter_le {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {M : ℕ} (Q : Fin M → Set X)
    {S C : Set X} {f : X → ℝ} {a b m H : ℝ}
    (hQsub : ∀ i, Q i ⊆ S) (hcover : ∀ x ∈ S, ∃ i, x ∈ Q i)
    (hQmass : ∀ i, m < μ.real (Q i)) (hCmass : μ.real C = m)
    (hbound : ∀ i, ∀ x ∈ Q i,
      3*(i.val:ℝ)-1 ≤ f x ∧ f x ≤ 3*(i.val:ℝ)+1)
    (hCsub : C ⊆ S) (hinterval : C ⊆ f ⁻¹' Ioc a b)
    (hfull : ∀ x ∈ S, f x ∈ Ioc a b → x ∈ C)
    (hgeom : ∀ i j, i.val ≤ j.val+1 → j.val ≤ i.val+1 →
      ∀ x ∈ Q i, ∀ y ∈ Q j, dist x y ≤ H) :
    ∀ x ∈ C, ∀ y ∈ C, dist x y ≤ H := by
  intro x hx y hy
  obtain ⟨i, hi⟩ := hcover x (hCsub hx)
  obtain ⟨j, hj⟩ := hcover y (hCsub hy)
  have hij := carrySlice_no_far_pair μ Q hQsub hQmass hCmass hbound hinterval hfull hx hi hy hj
  have hji := carrySlice_no_far_pair μ Q hQsub hQmass hCmass hbound hinterval hfull hy hj hx hi
  exact hgeom i j (by omega) (by omega) x hi y hj

end SphericalRiesz
end
end

section

/-! One exact-mass step of a geometric tree partition.
The unallocated remainder is kept in the original parent cell `Q`, even when `S` also contains
remainders received from adjacent children. This prevents the geometric radius from growing
with the depth of the tree. No tree or sphere partition is assumed to exist here. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz

theorem exists_tree_cell_split {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {Q S : Set X}
    (hQ : MeasurableSet Q) (hS : MeasurableSet S) (hQS : Q ⊆ S)
    {m : ℝ} (hm : 0 < m) (hQmass : m < μ.real Q)
    {f : X → ℝ} (hf : Measurable f) {R : ℝ}
    (hR : ∀ x, |f x| ≤ R) (hnull : ∀ c, μ (f ⁻¹' {c}) = 0) :
    ∃ n : ℕ, ∃ W : Set X, ∃ C : Fin n → Set X,
      0 < n ∧ n = ⌊μ.real S/m⌋₊ ∧
      MeasurableSet W ∧ W ⊆ Q ∧ 0 ≤ μ.real W ∧ μ.real W < m ∧
      μ.real W = μ.real S-(n:ℝ)*m ∧
      (μ.real S = (n:ℝ)*m → W = ∅) ∧
      (∀ j, MeasurableSet (C j)) ∧
      Pairwise (fun i j => Disjoint (C i) (C j)) ∧
      (⋃ j, C j) = S \ W ∧
      (∀ j, μ.real (C j) = m) ∧
      (∀ j, C j ⊆ S \ W) := by
  classical
  let n : ℕ := ⌊μ.real S/m⌋₊
  have hSm : m < μ.real S := hQmass.trans_le (measureReal_mono hQS)
  have hratio0 : 0 ≤ μ.real S/m := div_nonneg measureReal_nonneg hm.le
  have hratio1 : 1 ≤ μ.real S/m := (le_div_iff₀ hm).mpr (by linarith)
  have hn : 0 < n := Nat.floor_pos.mpr hratio1
  have hfloor : (n:ℝ) ≤ μ.real S/m := Nat.floor_le hratio0
  have hceil : μ.real S/m < (n:ℝ)+1 := Nat.lt_floor_add_one _
  have hnlo : (n:ℝ)*m ≤ μ.real S := (le_div_iff₀ hm).mp hfloor
  have hnhi : μ.real S < ((n:ℝ)+1)*m := (div_lt_iff₀ hm).mp hceil
  let δ : ℝ := μ.real S-(n:ℝ)*m
  have hδ0 : 0 ≤ δ := sub_nonneg.mpr hnlo
  have hδm : δ < m := by dsimp [δ]; linarith
  have hδQ : δ ≤ μ.real Q := hδm.le.trans hQmass.le
  have hnullQ : ∀ c, μ (f ⁻¹' {c} ∩ Q) = 0 :=
    fun c => measure_mono_null inter_subset_left (hnull c)
  obtain ⟨W, hWm, hWQ, hWδ, hWempty⟩ :
      ∃ W : Set X, MeasurableSet W ∧ W ⊆ Q ∧ μ.real W = δ ∧
        (δ = 0 → W = ∅) := by
    by_cases hδ : δ = 0
    · exact ⟨∅, MeasurableSet.empty, empty_subset _, by simp [hδ], fun _ => rfl⟩
    · obtain ⟨c, hc⟩ := exists_cut_measure_eq_restrict μ Q hf hR hnullQ hδ0 hδQ
      exact ⟨f ⁻¹' Iic c ∩ Q, (hf measurableSet_Iic).inter hQ,
        inter_subset_right, hc, fun h => False.elim (hδ h)⟩
  have hWS : W ⊆ S := hWQ.trans hQS
  have hT : μ.real (S \ W) = (n:ℝ)*m := by
    rw [measureReal_sdiff hWS hWm (measure_ne_top μ _), hWδ]
    dsimp [δ]
    ring
  have hnullT : ∀ c, μ (f ⁻¹' {c} ∩ (S \ W)) = 0 :=
    fun c => measure_mono_null inter_subset_left (hnull c)
  obtain ⟨C, t, ht, hCm, hCd, hCu, hCmass, hCI⟩ :=
    exists_exact_mass_slices_Ioc μ (hS.diff hWm) hf hR hnullT hn
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨n, W, C, hn, rfl, hWm, hWQ, measureReal_nonneg,
    hWδ.le.trans_lt hδm, hWδ, ?_, hCm, hCd, hCu, ?_, ?_⟩
  · intro hmass
    apply hWempty
    dsimp [δ]
    rw [hmass, sub_self]
  · intro j
    rw [hCmass j, hT]
    field_simp
  · intro j
    rw [← hCu]
    exact subset_iUnion C j

end SphericalRiesz
end
end

section

/-! Join disjoint exact-mass partitions without changing any cell or its diameter. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz

theorem exists_exact_cell_union {X : Type*} [MeasurableSpace X] [PseudoMetricSpace X]
    (μ : Measure X) {n r : ℕ} (C : Fin n → Set X) (D : Fin r → Set X)
    {A B : Set X} {m H : ℝ}
    (hCm : ∀ i, MeasurableSet (C i)) (hDm : ∀ j, MeasurableSet (D j))
    (hCd : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hDd : Pairwise (fun i j => Disjoint (D i) (D j)))
    (hCu : (⋃ i, C i) = A) (hDu : (⋃ j, D j) = B) (hAB : Disjoint A B)
    (hCmass : ∀ i, μ.real (C i) = m) (hDmass : ∀ j, μ.real (D j) = m)
    (hCdiam : ∀ i, ∀ x ∈ C i, ∀ y ∈ C i, dist x y ≤ H)
    (hDdiam : ∀ j, ∀ x ∈ D j, ∀ y ∈ D j, dist x y ≤ H) :
    ∃ E : Fin (n+r) → Set X,
      (∀ i, MeasurableSet (E i)) ∧
      Pairwise (fun i j => Disjoint (E i) (E j)) ∧
      (⋃ i, E i) = A ∪ B ∧ (∀ i, μ.real (E i) = m) ∧
      ∀ i, ∀ x ∈ E i, ∀ y ∈ E i, dist x y ≤ H := by
  classical
  let e : Fin (n+r) ≃ Fin n ⊕ Fin r :=
    (Fintype.equivFinOfCardEq (show Fintype.card (Fin n ⊕ Fin r) = n+r by simp)).symm
  let E : Fin (n+r) → Set X := fun i => Sum.elim C D (e i)
  have hCA : ∀ i, C i ⊆ A := fun i => by rw [← hCu]; exact subset_iUnion C i
  have hDB : ∀ j, D j ⊆ B := fun j => by rw [← hDu]; exact subset_iUnion D j
  refine ⟨E, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    cases hi : e i with
    | inl a => simpa only [E, hi, Sum.elim_inl] using hCm a
    | inr b => simpa only [E, hi, Sum.elim_inr] using hDm b
  · intro i j hij
    cases hi : e i with
    | inl a =>
      cases hj : e j with
      | inl b =>
        have hab : a ≠ b := fun h => hij (e.injective (by rw [hi, hj, h]))
        simpa only [E, hi, hj, Sum.elim_inl] using hCd hab
      | inr b =>
        simpa only [E, hi, hj, Sum.elim_inl, Sum.elim_inr] using hAB.mono (hCA a) (hDB b)
    | inr a =>
      cases hj : e j with
      | inl b =>
        simpa only [E, hi, hj, Sum.elim_inl, Sum.elim_inr] using hAB.symm.mono (hDB a) (hCA b)
      | inr b =>
        have hab : a ≠ b := fun h => hij (e.injective (by rw [hi, hj, h]))
        simpa only [E, hi, hj, Sum.elim_inr] using hDd hab
  · ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      cases hei : e i with
      | inl a => exact Or.inl (hCA a (by simpa only [E, hei, Sum.elim_inl] using hi))
      | inr b => exact Or.inr (hDB b (by simpa only [E, hei, Sum.elim_inr] using hi))
    · intro hx
      rcases hx with hx | hx
      · rw [← hCu] at hx
        obtain ⟨a, ha⟩ := mem_iUnion.mp hx
        refine mem_iUnion.mpr ⟨e.symm (.inl a), ?_⟩
        simpa only [E, e.apply_symm_apply, Sum.elim_inl] using ha
      · rw [← hDu] at hx
        obtain ⟨b, hb⟩ := mem_iUnion.mp hx
        refine mem_iUnion.mpr ⟨e.symm (.inr b), ?_⟩
        simpa only [E, e.apply_symm_apply, Sum.elim_inr] using hb
  · intro i
    cases hi : e i with
    | inl a => simpa only [E, hi, Sum.elim_inl] using hCmass a
    | inr b => simpa only [E, hi, Sum.elim_inr] using hDmass b
  · intro i
    cases hi : e i with
    | inl a => simpa only [E, hi, Sum.elim_inl] using hCdiam a
    | inr b => simpa only [E, hi, Sum.elim_inr] using hDdiam b

end SphericalRiesz
end
end

section

/-! Exact-mass partitions along an ordered finite tree.
Original coarse cells contain more than one final cell of mass. A child remainder is kept in
its original coarse cell before being passed to its parent, so only one edge is crossed.
The geometric inputs in this general theorem must still be constructed for the S² residual. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz

theorem pair_distance_le_of_radius {X : Type*} [PseudoMetricSpace X]
    {S : Set X} {c : X} {r : ℝ}
    (hS : ∀ x ∈ S, dist x c ≤ r) :
    ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 2*r := by
  intro x hx y hy
  calc dist x y ≤ dist x c+dist c y := dist_triangle _ _ _
    _ = dist x c+dist y c := by rw [dist_comm c y]
    _ ≤ r+r := add_le_add (hS x hx) (hS y hy)
    _ = 2*r := by ring

theorem exists_exact_tree_metric_partition {X : Type*} [MeasurableSpace X]
    [PseudoMetricSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Measurable f) {T : ℝ} (hT : ∀ x, |f x| ≤ T)
    (hnull : ∀ a, μ (f ⁻¹' {a}) = 0)
    {m R : ℝ} (hm : 0 < m) (_hR : 0 ≤ R) {M N : ℕ} (hM : 0 < M)
    (p : Fin M → Fin M)
    (hp0 : ∀ i, i.val = 0 → (p i).val = 0)
    (hp : ∀ i, 0 < i.val → (p i).val < i.val)
    (Q S : Fin M → Set X) (c : Fin M → X)
    (hQm : ∀ i, MeasurableSet (Q i)) (hSm : ∀ i, MeasurableSet (S i))
    (hSd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hQS : ∀ i, Q i ⊆ S i) (hQmass : ∀ i, m < μ.real (Q i))
    (hQrad : ∀ i, ∀ x ∈ Q i, dist x (c i) ≤ R)
    (hSrad : ∀ i, ∀ x ∈ S i, dist x (c i) ≤ 3*R)
    (hedge : ∀ i, dist (c i) (c (p i)) ≤ 2*R)
    (htotal : (∑ i, μ.real (S i)) = (N:ℝ)*m) :
    ∃ C : Fin N → Set X,
      (∀ j, MeasurableSet (C j)) ∧
      Pairwise (fun i j => Disjoint (C i) (C j)) ∧
      (⋃ j, C j) = ⋃ i, S i ∧ (∀ j, μ.real (C j) = m) ∧
      ∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y ≤ 6*R := by
  classical
  induction M generalizing N with
  | zero => omega
  | succ M ih =>
    by_cases hM0 : M = 0
    · subst M
      have hmass : μ.real (S 0) = (N:ℝ)*m := by simpa using htotal
      have hpositive : m < μ.real (S 0) :=
        (hQmass 0).trans_le (measureReal_mono (μ := μ) (hQS 0))
      have hN : 0 < N := by
        by_contra hn
        have hzero : N = 0 := by omega
        rw [hzero] at hmass
        norm_num at hmass
        linarith
      have hnullS : ∀ a, μ (f ⁻¹' {a} ∩ S 0) = 0 :=
        fun a => measure_mono_null inter_subset_left (hnull a)
      obtain ⟨C, t, ht, hCm, hCd, hCu, hCmass, hCI⟩ :=
        exists_exact_mass_slices_Ioc μ (hSm 0) hf hT hnullS hN
      have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      refine ⟨C, hCm, hCd, ?_, ?_, ?_⟩
      · have hsing : (⋃ i : Fin 1, S i) = S 0 := by
          ext x
          simp only [mem_iUnion]
          constructor
          · rintro ⟨i, hi⟩
            have hi0 : i = 0 := Fin.ext (by omega)
            simpa only [hi0] using hi
          · intro hx
            exact ⟨0, hx⟩
        exact hCu.trans hsing.symm
      · intro j
        rw [hCmass j, hmass]
        field_simp
      · intro j
        have hsub : C j ⊆ S 0 := by rw [← hCu]; exact subset_iUnion C j
        have hb := pair_distance_le_of_radius (hSrad 0)
        intro x hx y hy
        simpa only [show 2*(3*R) = 6*R by ring] using hb x (hsub hx) y (hsub hy)
    · have hMp : 0 < M := Nat.pos_of_ne_zero hM0
      let leaf : Fin (M+1) := Fin.last M
      let parent : Fin M := ⟨(p leaf).val, hp leaf (by simpa [leaf] using hMp)⟩
      have hparent : parent.castSucc = p leaf := Fin.ext rfl
      obtain ⟨n, W, L, hn, hnfloor, hWm, hWQ, hW0, hWlt, hWmass, hWempty,
          hLm, hLd, hLu, hLmass, hLsub⟩ :=
        exists_tree_cell_split μ (hQm leaf) (hSm leaf) (hQS leaf)
          hm (hQmass leaf) hf hT hnull
      have hWS : W ⊆ S leaf := hWQ.trans (hQS leaf)
      have hnotleaf : ∀ i : Fin M, i.castSucc ≠ leaf := by
        intro i
        apply Fin.ne_of_val_ne
        simpa only [Fin.val_castSucc, leaf, Fin.val_last] using (ne_of_lt i.isLt)
      have hSW : ∀ i : Fin M, Disjoint (S i.castSucc) W :=
        fun i => (hSd (hnotleaf i)).mono_right hWS
      have hprefix0 : 0 < ∑ i : Fin M, μ.real (S i.castSucc) := by
        let z : Fin M := ⟨0, hMp⟩
        have hz : 0 < μ.real (S z.castSucc) :=
          hm.trans ((hQmass z.castSucc).trans_le (measureReal_mono (μ := μ) (hQS z.castSucc)))
        exact hz.trans_le (Finset.single_le_sum (fun i _ => (measureReal_nonneg (μ := μ) (s := S i.castSucc)))
          (Finset.mem_univ z))
      have hsumold : (∑ i : Fin M, μ.real (S i.castSucc))+μ.real (S leaf) = (N:ℝ)*m := by
        simpa only [Fin.sum_univ_castSucc, leaf] using htotal
      have hnlt : n < N := by
        have hreal : (n:ℝ)*m < (N:ℝ)*m := by linarith
        have hnn : (n:ℝ) < N := by nlinarith
        exact_mod_cast hnn
      have hremaining : 0 < N-n := Nat.sub_pos_of_lt hnlt
      let S' : Fin M → Set X := fun i => if i = parent then S i.castSucc ∪ W else S i.castSucc
      let q : Fin M → Fin M := fun i =>
        if hi : i.val = 0 then ⟨0, hMp⟩ else
          ⟨(p i.castSucc).val, (hp i.castSucc (by simpa using Nat.pos_of_ne_zero hi)).trans i.isLt⟩
      have hqcast : ∀ i, (q i).castSucc = p i.castSucc := by
        intro i
        by_cases hi : i.val = 0
        · apply Fin.ext
          simpa only [q, dite_eq_left hi, Fin.val_castSucc, Fin.val_mk] using (hp0 i.castSucc hi).symm
        · apply Fin.ext
          simp only [q, dite_eq_right hi, Fin.val_castSucc]
      have hq0 : ∀ i, i.val = 0 → (q i).val = 0 := by
        intro i hi
        simp only [q, dite_eq_left hi, Fin.val_mk]
      have hqlt : ∀ i, 0 < i.val → (q i).val < i.val := by
        intro i hi
        have hiz : i.val ≠ 0 := hi.ne'
        simpa only [q, dite_eq_right hiz, Fin.val_mk, Fin.val_castSucc] using hp i.castSucc hi
      have hS'm : ∀ i, MeasurableSet (S' i) := by
        intro i
        dsimp only [S']
        split_ifs
        · exact (hSm _).union hWm
        · exact hSm _
      have hS'd : Pairwise (fun i j => Disjoint (S' i) (S' j)) := by
        intro i j hij
        have hij' : i.castSucc ≠ j.castSucc := fun h => hij ((by simpa only [Fin.castSucc_inj] using h))
        by_cases hi : i = parent <;> by_cases hj : j = parent
        · exact False.elim (hij (hi.trans hj.symm))
        · simpa only [S', ite_eq_left hi, ite_eq_right hj] using (hSd hij').union_left (hSW j).symm
        · simpa only [S', ite_eq_right hi, ite_eq_left hj] using (hSd hij').union_right (hSW i)
        · simpa only [S', ite_eq_right hi, ite_eq_right hj] using hSd hij'
      have hQ'S : ∀ i, Q i.castSucc ⊆ S' i := by
        intro i x hx
        dsimp only [S']
        split_ifs
        · exact Or.inl (hQS _ hx)
        · exact hQS _ hx
      have hS'rad : ∀ i, ∀ x ∈ S' i, dist x (c i.castSucc) ≤ 3*R := by
        intro i x hx
        by_cases hi : i = parent
        · simp only [S', ite_eq_left hi, mem_union] at hx
          rcases hx with hx | hx
          · exact hSrad _ x hx
          · have he : i.castSucc = p leaf := hi ▸ hparent
            rw [he]
            calc dist x (c (p leaf)) ≤ dist x (c leaf)+dist (c leaf) (c (p leaf)) := dist_triangle _ _ _
              _ ≤ R+2*R := add_le_add (hQrad leaf x (hWQ hx)) (hedge leaf)
              _ = 3*R := by ring
        · exact hSrad _ x (by simpa only [S', ite_eq_right hi] using hx)
      have hS'real : ∀ i, μ.real (S' i) = μ.real (S i.castSucc)+(if i = parent then μ.real W else 0) := by
        intro i
        by_cases hi : i = parent
        · simp only [S', ite_eq_left hi]
          exact measureReal_union (hSW i) hWm
        · simp only [S', ite_eq_right hi, add_zero]
      have hsumnew : (∑ i, μ.real (S' i)) = ((N-n:ℕ):ℝ)*m := by
        rw [Finset.sum_congr rfl (fun i _ => hS'real i), Finset.sum_add_distrib]
        simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [Nat.cast_sub hnlt.le]
        linarith
      obtain ⟨D, hDm, hDd, hDu, hDmass, hDdiam⟩ := ih hMp q hq0 hqlt
        (fun i => Q i.castSucc) S' (fun i => c i.castSucc)
        (fun i => hQm _) hS'm hS'd hQ'S (fun i => hQmass _)
        (fun i => hQrad _) hS'rad
        (fun i => by simpa only [hqcast i] using hedge i.castSucc) hsumnew
      have hnewUnion : (⋃ i, S' i) = (⋃ i : Fin M, S i.castSucc) ∪ W := by
        ext x
        constructor
        · intro hx
          obtain ⟨i, hx⟩ := mem_iUnion.mp hx
          by_cases hi : i = parent
          · simp only [S', ite_eq_left hi, mem_union] at hx
            exact hx.imp (fun h => mem_iUnion.mpr ⟨i, h⟩) id
          · exact Or.inl (mem_iUnion.mpr ⟨i, by simpa only [S', ite_eq_right hi] using hx⟩)
        · intro hx
          rcases hx with hx | hx
          · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
            refine mem_iUnion.mpr ⟨i, ?_⟩
            dsimp only [S']
            split_ifs
            · exact Or.inl hi
            · exact hi
          · exact mem_iUnion.mpr ⟨parent, by simp only [S', ite_eq_left rfl]; exact Or.inr hx⟩
      have hsplitDisjoint : Disjoint (S leaf \ W) (⋃ i, S' i) := by
        rw [hnewUnion, Set.disjoint_left]
        intro x hx hy
        rcases hy with hy | hy
        · obtain ⟨i, hi⟩ := mem_iUnion.mp hy
          exact Set.disjoint_left.mp (hSd (hnotleaf i)) hi hx.1
        · exact hx.2 hy
      have hLdiam : ∀ j, ∀ x ∈ L j, ∀ y ∈ L j, dist x y ≤ 6*R := by
        intro j x hx y hy
        have hb := pair_distance_le_of_radius (hSrad leaf)
        simpa only [show 2*(3*R) = 6*R by ring] using hb x (hLsub j hx).1 y (hLsub j hy).1
      obtain ⟨E, hEm, hEd, hEu, hEmass, hEdiam⟩ :=
        exists_exact_cell_union μ L D hLm hDm hLd hDd hLu hDu hsplitDisjoint hLmass hDmass hLdiam hDdiam
      have hcard : n+(N-n) = N := Nat.add_sub_of_le hnlt.le
      have holdUnion : (⋃ i : Fin (M+1), S i) = (⋃ i : Fin M, S i.castSucc) ∪ S leaf := by
        ext x
        constructor
        · intro hx
          obtain ⟨i, hi⟩ := mem_iUnion.mp hx
          by_cases hiv : i.val < M
          · exact Or.inl (mem_iUnion.mpr ⟨⟨i.val, hiv⟩, by simpa using hi⟩)
          · have hei : i = leaf := Fin.ext (by dsimp [leaf]; omega)
            exact Or.inr (hei ▸ hi)
        · intro hx
          rcases hx with hx | hx
          · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
            exact mem_iUnion.mpr ⟨i.castSucc, hi⟩
          · exact mem_iUnion.mpr ⟨leaf, hx⟩
      have hfinal : (S leaf \ W) ∪ (⋃ i, S' i) = ⋃ i, S i := by
        rw [hnewUnion, holdUnion]
        ext x
        simp only [mem_union, mem_sdiff]
        have hWx : x ∈ W → x ∈ S leaf := fun hx => hWS hx
        tauto
      rw [hfinal] at hEu
      have hE : ∃ C : Fin (n+(N-n)) → Set X,
          (∀ j, MeasurableSet (C j)) ∧ Pairwise (fun i j => Disjoint (C i) (C j)) ∧
          (⋃ j, C j) = ⋃ i, S i ∧ (∀ j, μ.real (C j) = m) ∧
          ∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y ≤ 6*R :=
        ⟨E, hEm, hEd, hEu, hEmass, hEdiam⟩
      rw [hcard] at hE
      exact hE

end SphericalRiesz
end
end

section

/-! Measurable nearest-centre cells with ties assigned to the least index.
This supplies coarse cells for the geometric tree partition; it does not assert the existence
of suitable centres or any lower measure estimate for a sphere residual. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
namespace SphericalRiesz

def nearestCentreCell2 {X : Type*} [PseudoMetricSpace X] {M : ℕ}
    (A : Set X) (c : Fin M → X) (i : Fin M) : Set X :=
  {x | x ∈ A ∧ ∀ j, dist x (c i) ≤ dist x (c j) ∧
    (dist x (c i) = dist x (c j) → i ≤ j)}

theorem nearestCentreCell2_measurable {X : Type*} [MeasurableSpace X]
    [PseudoMetricSpace X] [BorelSpace X] {M : ℕ}
    {A : Set X} (hA : MeasurableSet A) (c : Fin M → X) (i : Fin M) :
    MeasurableSet (nearestCentreCell2 A c i) := by
  have heq : nearestCentreCell2 A c i = A ∩ ⋂ j,
      {x | dist x (c i) ≤ dist x (c j)} ∩
      ({x | dist x (c i) ≠ dist x (c j)} ∪ {x | i ≤ j}) := by
    ext x
    simp only [nearestCentreCell2, mem_ofPred_eq, mem_inter_iff, mem_iInter,
      mem_union, imp_iff_not_or]
  rw [heq]
  refine hA.inter (MeasurableSet.iInter fun j => ?_)
  exact (measurableSet_le (by fun_prop) (by fun_prop)).inter
    ((measurableSet_eq_fun (by fun_prop) (by fun_prop)).compl.union (by simp))

theorem nearestCentreCell2_disjoint {X : Type*} [PseudoMetricSpace X] {M : ℕ}
    (A : Set X) (c : Fin M → X) :
    Pairwise (fun i j => Disjoint (nearestCentreCell2 A c i) (nearestCentreCell2 A c j)) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hx hy
  have he : dist x (c i) = dist x (c j) := le_antisymm (hx.2 j).1 (hy.2 i).1
  exact hij (le_antisymm ((hx.2 j).2 he) ((hy.2 i).2 he.symm))

theorem nearestCentreCell2_cover {X : Type*} [PseudoMetricSpace X] {M : ℕ}
    (hM : 0 < M) (A : Set X) (c : Fin M → X) :
    (⋃ i, nearestCentreCell2 A c i) = A := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact hi.1
  · intro hx
    let z : Fin M := ⟨0, hM⟩
    obtain ⟨i, _, hi⟩ := (Finset.univ : Finset (Fin M)).exists_min_image
      (fun j => dist x (c j)) ⟨z, Finset.mem_univ z⟩
    let F : Finset (Fin M) := Finset.univ.filter (fun j => dist x (c j) = dist x (c i))
    have hF : F.Nonempty := ⟨i, by simp [F]⟩
    let k : Fin M := F.min' hF
    have hkF : k ∈ F := Finset.min'_mem _ _
    have hk : dist x (c k) = dist x (c i) := (Finset.mem_filter.mp hkF).2
    refine mem_iUnion.mpr ⟨k, hx, fun j => ⟨?_, ?_⟩⟩
    · rw [hk]
      exact hi j (Finset.mem_univ j)
    · intro hj
      apply Finset.min'_le
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hj.symm.trans hk

theorem nearestCentreCell2_contains_ball {X : Type*} [PseudoMetricSpace X] {M : ℕ}
    (A : Set X) (c : Fin M → X) {H : ℝ}
    (hsep : ∀ i j, i ≠ j → 2*H ≤ dist (c i) (c j)) (i : Fin M) :
    A ∩ ball (c i) H ⊆ nearestCentreCell2 A c i := by
  intro x hx
  have hxi : dist x (c i) < H := hx.2
  refine ⟨hx.1, fun j => ?_⟩
  by_cases hij : i = j
  · subst j
    exact ⟨le_rfl, fun _ => le_rfl⟩
  · have ht := dist_triangle (c i) x (c j)
    rw [dist_comm (c i) x] at ht
    have hj : dist x (c i) < dist x (c j) := by linarith [hsep i j hij]
    exact ⟨hj.le, fun he => False.elim (hj.ne he)⟩

theorem nearestCentreCell2_radius {X : Type*} [PseudoMetricSpace X] {M : ℕ}
    (A : Set X) (c : Fin M → X) {H : ℝ}
    (hcover : ∀ x ∈ A, ∃ j, dist x (c j) ≤ H) :
    ∀ i, ∀ x ∈ nearestCentreCell2 A c i, dist x (c i) ≤ H := by
  intro i x hx
  obtain ⟨j, hj⟩ := hcover x hx.1
  exact ((hx.2 j).1).trans hj

end SphericalRiesz
end
end

section

/-! Order the vertices of a finite connected graph by distance from a root.
The parent of every nonroot vertex has an earlier index. -/
set_option autoImplicit false
noncomputable section
open Set
namespace SphericalRiesz

theorem connected_graph_nearer_neighbour2 {V : Type*} (G : SimpleGraph V)
    (hG : G.Connected) (r v : V) (hvr : v ≠ r) :
    ∃ u, G.Adj v u ∧ G.dist r u < G.dist r v := by
  obtain ⟨w, hw⟩ := hG.exists_walk_length_eq_dist v r
  cases w with
  | nil => exact False.elim (hvr rfl)
  | @cons u v r hadj tail =>
    refine ⟨v, hadj, ?_⟩
    have ht := G.dist_le tail
    rw [SimpleGraph.dist_comm] at ht hw
    simp only [SimpleGraph.Walk.length_cons] at hw
    omega

theorem exists_ordered_graph_parent2 {M : ℕ} (hM : 0 < M)
    (G : SimpleGraph (Fin M)) (hG : G.Connected) :
    ∃ e : Fin M ≃ Fin M, ∃ p : Fin M → Fin M,
      (∀ i, i.val = 0 → (p i).val = 0) ∧
      (∀ i, 0 < i.val → (p i).val < i.val) ∧
      (∀ i, 0 < i.val → G.Adj (e i) (e (p i))) := by
  classical
  let r : Fin M := ⟨0, hM⟩
  let key : Fin M → ℕ := fun i => G.dist r i*M+i.val
  have hkey : Function.Injective key := by
    intro i j hij
    apply Fin.ext
    have hmod := congrArg (fun n => n%M) hij
    simpa only [key, Nat.add_mod, Nat.mul_mod, Nat.mod_self, mul_zero,
      Nat.zero_mod, zero_add, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hmod
  let F : Finset ℕ := Finset.univ.image key
  have hcard : F.card = M := by
    rw [Finset.card_image_of_injective _ hkey]
    exact Finset.card_fin M
  let k : Fin M ≃ {n // n ∈ F} := Equiv.ofBijective
    (fun i => ⟨key i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
    ⟨fun i j h => hkey (congrArg Subtype.val h), fun n => by
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp n.2
      exact ⟨i, Subtype.ext hi⟩⟩
  let ord : Fin M ≃o {n // n ∈ F} := F.orderIsoOfFin hcard
  let e : Fin M ≃ Fin M := ord.toEquiv.trans k.symm
  have hke : ∀ i, key (e i) = (ord i).val := by
    intro i
    have h := congrArg Subtype.val (k.apply_symm_apply (ord i))
    exact h
  have hkey_lt : ∀ i j, key (e i) < key (e j) → i < j := by
    intro i j hij
    rw [hke, hke] at hij
    exact ord.lt_iff_lt.mp hij
  have hkey_root : ∀ i, key r ≤ key i := by
    intro i
    simp only [key, SimpleGraph.dist_self, zero_mul, zero_add, r]
    omega
  have hroot : e ⟨0,hM⟩ = r := by
    have hle : e.symm r ≤ (⟨0,hM⟩ : Fin M) := by
      apply ord.le_iff_le.mp
      change (ord (e.symm r)).val ≤ (ord ⟨0,hM⟩).val
      rw [← hke, ← hke, e.apply_symm_apply]
      exact hkey_root _
    have hzero : e.symm r = (⟨0,hM⟩ : Fin M) := Fin.ext (by exact Nat.eq_zero_of_le_zero hle)
    have heq := congrArg e hzero
    simpa only [e.apply_symm_apply] using heq.symm
  have hnear : ∀ i : Fin M, 0 < i.val →
      ∃ j : Fin M, G.Adj (e i) (e j) ∧ j.val < i.val := by
    intro i hi
    have hir : e i ≠ r := by
      intro h
      have hi0 := e.injective (h.trans hroot.symm)
      have hiz : i.val = 0 := congrArg Fin.val hi0
      exact hi.ne' hiz
    obtain ⟨u, hu, hud⟩ := connected_graph_nearer_neighbour2 G hG r (e i) hir
    refine ⟨e.symm u, by simpa only [e.apply_symm_apply] using hu, ?_⟩
    apply hkey_lt
    rw [e.apply_symm_apply]
    dsimp only [key]
    have hv : u.val < M := u.isLt
    have hv' : 0 ≤ (e i).val := Nat.zero_le _
    have hd : G.dist r u+1 ≤ G.dist r (e i) := hud
    have hmul := Nat.mul_le_mul_right M hd
    rw [Nat.add_mul, one_mul] at hmul
    omega
  let p : Fin M → Fin M := fun i =>
    if hi : i.val = 0 then ⟨0,hM⟩ else (hnear i (Nat.pos_of_ne_zero hi)).choose
  refine ⟨e, p, ?_, ?_, ?_⟩
  · intro i hi
    simp only [p, dite_eq_left hi, Fin.val_mk]
  · intro i hi
    simpa only [p, dite_eq_right hi.ne'] using (hnear i hi).choose_spec.2
  · intro i hi
    simpa only [p, dite_eq_right hi.ne'] using (hnear i hi).choose_spec.1

end SphericalRiesz
end
end

section

/-! The overlap graph of a finite ball cover of a connected set is connected. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped NNReal
namespace SphericalRiesz

def ballCoverGraph2 {X : Type*} [PseudoMetricSpace X] {M : ℕ}
    (A : Set X) (c : Fin M → X) (H : ℝ) : SimpleGraph (Fin M) where
  Adj i j := i ≠ j ∧ ∃ x ∈ A, dist x (c i) < H ∧ dist x (c j) < H
  symm := ⟨by
    rintro i j ⟨hij, x, hx, hi, hj⟩
    exact ⟨hij.symm, x, hx, hj, hi⟩⟩
  loopless := ⟨fun i hi => hi.1 rfl⟩

theorem ballCoverGraph2_edge_dist {X : Type*} [PseudoMetricSpace X] {M : ℕ}
    (A : Set X) (c : Fin M → X) (H : ℝ) {i j : Fin M}
    (hij : (ballCoverGraph2 A c H).Adj i j) : dist (c i) (c j) < 2*H := by
  obtain ⟨_, x, _, hi, hj⟩ := hij
  have ht := dist_triangle (c i) x (c j)
  rw [dist_comm (c i) x] at ht
  linarith

theorem ballCoverGraph2_connected {X : Type*} [PseudoMetricSpace X] {M : ℕ}
    (hM : 0 < M) {A : Set X} (hA : IsPreconnected A) (c : Fin M → X)
    (hc : ∀ i, c i ∈ A) {H : ℝ} (hH : 0 < H)
    (hcover : ∀ x ∈ A, ∃ i, dist x (c i) < H) :
    (ballCoverGraph2 A c H).Connected := by
  classical
  have : Nonempty (Fin M) := ⟨⟨0,hM⟩⟩
  let G := ballCoverGraph2 A c H
  let r : Fin M := ⟨0,hM⟩
  have hreach : ∀ j, G.Reachable r j := by
    intro j
    let U : Set X := ⋃ i : {i : Fin M // G.Reachable r i}, ball (c i.val) H
    let V : Set X := ⋃ i : {i : Fin M // ¬G.Reachable r i}, ball (c i.val) H
    have hU : IsOpen U := isOpen_iUnion fun _ => isOpen_ball
    have hV : IsOpen V := isOpen_iUnion fun _ => isOpen_ball
    have hcov : A ⊆ U ∪ V := by
      intro x hx
      obtain ⟨i, hi⟩ := hcover x hx
      by_cases hri : G.Reachable r i
      · exact Or.inl (mem_iUnion.mpr ⟨⟨i,hri⟩, hi⟩)
      · exact Or.inr (mem_iUnion.mpr ⟨⟨i,hri⟩, hi⟩)
    have hrU : c r ∈ U := mem_iUnion.mpr ⟨⟨r,SimpleGraph.Reachable.refl r⟩, by simpa using hH⟩
    by_contra hj
    have hjV : c j ∈ V := mem_iUnion.mpr ⟨⟨j,hj⟩, by simpa using hH⟩
    obtain ⟨x, hxA, hxU, hxV⟩ := hA U V hU hV hcov ⟨c r,hc r,hrU⟩ ⟨c j,hc j,hjV⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxU
    obtain ⟨k, hk⟩ := mem_iUnion.mp hxV
    have hik : i.val ≠ k.val := fun h => k.prop (h ▸ i.prop)
    have hadj : G.Adj i.val k.val := ⟨hik,x,hxA,hi,hk⟩
    exact k.prop (i.prop.trans hadj.reachable)
  exact SimpleGraph.Connected.mk (fun i j => (hreach i).symm.trans (hreach j))

theorem exists_finite_separated_cover2 {X : Type*} [PseudoMetricSpace X]
    {A : Set X} (hA : IsCompact A) {H : ℝ≥0} (hH : H ≠ 0) :
    ∃ F : Set X, F ⊆ A ∧ F.Finite ∧ Metric.IsSeparated (2*H) F ∧
      Metric.IsCover (2*H) A F := by
  obtain ⟨C, _, hCf, hCcov⟩ := Metric.exists_finite_isCover_of_isCompact hH hA
  have hpack : Metric.packingNumber (2*H) A ≠ ⊤ := by
    have hle := (Metric.packingNumber_two_mul_le_externalCoveringNumber H A).trans
      hCcov.externalCoveringNumber_le_encard
    exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hCf) hle
  obtain ⟨F,hFA,hFf,hFsep,hFcard⟩ := Metric.exists_set_encard_eq_packingNumber hpack
  have hcover := Metric.isCover_maximalSeparatedSet hpack
  refine ⟨Metric.maximalSeparatedSet (2*H) A, Metric.maximalSeparatedSet_subset, ?_,
    Metric.isSeparated_maximalSeparatedSet, hcover⟩
  apply Set.encard_ne_top_iff.mp
  rwa [Metric.encard_maximalSeparatedSet hpack]

end SphericalRiesz
end
end

section

/-! Removing finitely many separated open holes with connected frontiers preserves
connectedness of a closed region. The sphere patch frontiers still have to be verified. -/
set_option autoImplicit false
open Set
namespace SphericalRiesz

theorem isPreconnected_sdiff_open_of_frontier2 {X : Type*} [TopologicalSpace X]
    {A U : Set X} (hAc : IsClosed A) (hA : IsPreconnected A) (hU : IsOpen U)
    (hUA : closure U ⊆ A) (hfront : IsPreconnected (frontier U)) :
    IsPreconnected (A \ U) := by
  apply isPreconnected_closed_iff.mpr
  intro a b ha hb hcover hna hnb
  by_contra hno
  have hFC : frontier U ⊆ A \ U := by
    rw [hU.frontier_eq]
    exact fun x hx => ⟨hUA hx.1,hx.2⟩
  have hFcover : frontier U ⊆ a ∪ b := hFC.trans hcover
  have hkill : ∀ a b : Set X, IsClosed a → IsClosed b →
      A \ U ⊆ a ∪ b → ((A \ U) ∩ a).Nonempty → ((A \ U) ∩ b).Nonempty →
      ¬((A \ U) ∩ (a ∩ b)).Nonempty → frontier U ⊆ a → False := by
    intro a b ha hb hcover hna hnb hno hFa
    let F : Set X := (A \ U) ∩ b
    let G : Set X := A ∩ (closure U ∪ a)
    have hFc : IsClosed F := (hAc.inter hU.isClosed_compl).inter hb
    have hGc : IsClosed G := hAc.inter (isClosed_closure.union ha)
    have hcoverA : A ⊆ F ∪ G := by
      intro x hx
      by_cases hxU : x ∈ U
      · exact Or.inr ⟨hx,Or.inl (subset_closure hxU)⟩
      · rcases hcover ⟨hx,hxU⟩ with hxa | hxb
        · exact Or.inr ⟨hx,Or.inr hxa⟩
        · exact Or.inl ⟨⟨hx,hxU⟩,hxb⟩
    have hFne : (A ∩ F).Nonempty := by
      obtain ⟨x,hx,hxb⟩ := hnb
      exact ⟨x,hx.1,hx,hxb⟩
    have hGne : (A ∩ G).Nonempty := by
      obtain ⟨x,hx,hxa⟩ := hna
      exact ⟨x,hx.1,hx.1,Or.inr hxa⟩
    obtain ⟨x,_,hxF,hxG⟩ := (isPreconnected_closed_iff.mp hA)
      F G hFc hGc hcoverA hFne hGne
    have hxa : x ∈ a := by
      rcases hxG.2 with hxcl | hxa
      · apply hFa
        rw [hU.frontier_eq]
        exact ⟨hxcl,hxF.1.2⟩
      · exact hxa
    exact hno ⟨x,hxF.1,hxa,hxF.2⟩
  by_cases hfa : (frontier U ∩ a).Nonempty
  · have hfb : ¬(frontier U ∩ b).Nonempty := by
      intro hfb
      obtain ⟨x,hxF,hxa,hxb⟩ := (isPreconnected_closed_iff.mp hfront)
        a b ha hb hFcover hfa hfb
      exact hno ⟨x,hFC hxF,hxa,hxb⟩
    have hFa : frontier U ⊆ a := by
      intro x hx
      rcases hFcover hx with hxa | hxb
      · exact hxa
      · exact False.elim (hfb ⟨x,hx,hxb⟩)
    exact hkill a b ha hb hcover hna hnb hno hFa
  · have hFb : frontier U ⊆ b := by
      intro x hx
      rcases hFcover hx with hxa | hxb
      · exact False.elim (hfa ⟨x,hx,hxa⟩)
      · exact hxb
    apply hkill b a hb ha (by simpa only [union_comm] using hcover) hnb hna
      (by simpa only [inter_comm a b] using hno) hFb

theorem isPreconnected_sdiff_finite_open_holes2 {X ι : Type*} [TopologicalSpace X]
    (A : Set X) (hAc : IsClosed A) (hA : IsPreconnected A)
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hUA : ∀ i, closure (U i) ⊆ A) (hfront : ∀ i, IsPreconnected (frontier (U i)))
    (hdisj : Pairwise (fun i j => Disjoint (closure (U i)) (closure (U j))))
    (F : Finset ι) : IsPreconnected (A \ ⋃ i ∈ F, U i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using hA
  | @insert i F hi ih =>
    have hclosed : IsClosed (A \ ⋃ j ∈ F, U j) :=
      hAc.inter (isOpen_biUnion fun j _ => hU j).isClosed_compl
    have hsub : closure (U i) ⊆ A \ ⋃ j ∈ F, U j := by
      intro x hx
      refine ⟨hUA i hx,?_⟩
      intro hxu
      obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp hxu
      have hij : i ≠ j := fun h => hi (h ▸ hj)
      exact Set.disjoint_left.mp (hdisj hij) hx (subset_closure hxj)
    have hconn := isPreconnected_sdiff_open_of_frontier2 hclosed ih (hU i) hsub (hfront i)
    convert hconn using 1
    ext x
    simp only [Finset.mem_insert, mem_iUnion, exists_prop, mem_sdiff, or_and_right, exists_or, exists_eq_left, not_or]
    tauto

end SphericalRiesz
end

section

/-! Exact-mass cells from local measure lower bounds on a compact connected carrier.
The lower bounds are explicit hypotheses, still to be proved for the actual S² residual. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped NNReal
namespace SphericalRiesz

theorem exists_exact_compact_metric_cells2 {X : Type*} [MeasurableSpace X]
    [PseudoMetricSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Measurable f) {T : ℝ} (hT : ∀ x, |f x| ≤ T)
    (hnull : ∀ a, μ (f ⁻¹' {a}) = 0)
    {A R : Set X} (hAc : IsCompact A) (hAconn : IsPreconnected A) (hAn : A.Nonempty)
    (hRm : MeasurableSet R) (hRA : R ⊆ A) {H : ℝ≥0} (hH : 0 < H)
    {m : ℝ} (hm : 0 < m) (hlower : ∀ x ∈ A, m < μ.real (R ∩ ball x H))
    {N : ℕ} (htotal : μ.real R = (N:ℝ)*m) :
    ∃ C : Fin N → Set X,
      (∀ j, MeasurableSet (C j)) ∧ Pairwise (fun i j => Disjoint (C i) (C j)) ∧
      (⋃ j, C j) = R ∧ (∀ j, μ.real (C j) = m) ∧
      ∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y ≤ 18*(H:ℝ) := by
  classical
  obtain ⟨F,hFA,hFf,hFsep,hFcover⟩ := exists_finite_separated_cover2 hAc hH.ne'
  have hFn : F.Nonempty := hFcover.nonempty hAn
  let : Fintype F := hFf.fintype
  have : Nonempty F := hFn.to_subtype
  let M := Fintype.card F
  have hM : 0 < M := Fintype.card_pos
  let e : Fin M ≃ F := (Fintype.equivFin F).symm
  let c : Fin M → X := fun i => (e i).val
  have hcA : ∀ i, c i ∈ A := fun i => hFA (e i).prop
  have hcover : ∀ x ∈ A, ∃ i, dist x (c i) ≤ 2*(H:ℝ) := by
    intro x hx
    obtain ⟨y,hy,hd⟩ := hFcover hx
    refine ⟨e.symm ⟨y,hy⟩,?_⟩
    have hh : nndist x y ≤ 2*H := edist_le_coe.mp hd
    simpa only [c,e.apply_symm_apply,NNReal.coe_mul,NNReal.coe_ofNat] using
      (show dist x y ≤ ((2*H:ℝ≥0):ℝ) from hh)
  have hsep : ∀ i j, i ≠ j → 2*(H:ℝ) ≤ dist (c i) (c j) := by
    intro i j hij
    have hne : (e i).val ≠ (e j).val := fun h => hij (e.injective (Subtype.ext h))
    have hd := hFsep (e i).prop (e j).prop hne
    have hh : 2*H < nndist (c i) (c j) := by
      apply ENNReal.coe_lt_coe.mp
      simpa only [c,edist_nndist,ENNReal.coe_mul,ENNReal.coe_ofNat] using hd
    exact_mod_cast hh.le
  let Q := nearestCentreCell2 R c
  have hQm : ∀ i, MeasurableSet (Q i) := nearestCentreCell2_measurable hRm c
  have hQd := nearestCentreCell2_disjoint R c
  have hQu := nearestCentreCell2_cover hM R c
  have hQmass : ∀ i, m < μ.real (Q i) := fun i =>
    (hlower (c i) (hcA i)).trans_le (measureReal_mono (μ := μ)
      (nearestCentreCell2_contains_ball R c hsep i))
  have hQr : ∀ i, ∀ x ∈ Q i, dist x (c i) ≤ 2*(H:ℝ) :=
    nearestCentreCell2_radius R c (fun x hx => hcover x (hRA hx))
  have hGc := ballCoverGraph2_connected hM hAconn c hcA
    (show 0 < 3*(H:ℝ) by exact mul_pos (by norm_num) hH)
    (fun x hx => by
      obtain ⟨i,hi⟩ := hcover x hx
      exact ⟨i,hi.trans_lt (by nlinarith [hH])⟩)
  obtain ⟨a,p,hp0,hp,hpadj⟩ := exists_ordered_graph_parent2 hM _ hGc
  have hsum : (∑ i, μ.real (Q (a i))) = (N:ℝ)*m := by
    rw [Equiv.sum_comp a (fun i => μ.real (Q i)), ← measureReal_iUnion_fintype (μ := μ) hQd hQm, hQu]
    exact htotal
  have hQR : ∀ i, ∀ x ∈ Q (a i), dist x (c (a i)) ≤ 3*(H:ℝ) := by
    intro i x hx
    exact (hQr _ x hx).trans (by nlinarith [hH])
  have hSR : ∀ i, ∀ x ∈ Q (a i), dist x (c (a i)) ≤ 3*(3*(H:ℝ)) := by
    intro i x hx
    exact (hQr _ x hx).trans (by nlinarith [hH])
  have hedge : ∀ i, dist (c (a i)) (c (a (p i))) ≤ 2*(3*(H:ℝ)) := by
    intro i
    by_cases hi : i.val = 0
    · have hpi : p i = i := Fin.ext ((hp0 i hi).trans hi.symm)
      rw [hpi,dist_self]
      positivity
    · exact (ballCoverGraph2_edge_dist _ _ _ (hpadj i (Nat.pos_of_ne_zero hi))).le
  obtain ⟨C,hCm,hCd,hCu,hCmass,hCdiam⟩ := exists_exact_tree_metric_partition μ hf hT hnull
    hm (show 0 ≤ 3*(H:ℝ) by positivity) hM p hp0 hp
    (fun i => Q (a i)) (fun i => Q (a i)) (fun i => c (a i))
    (fun i => hQm _) (fun i => hQm _)
    (fun i j hij => hQd (a.injective.ne hij)) (fun _ => subset_rfl)
    (fun i => hQmass _) hQR hSR hedge hsum
  refine ⟨C,hCm,hCd,?_,hCmass,?_⟩
  · rw [hCu]
    calc (⋃ i, Q (a i)) = ⋃ i, Q i := by
          ext x
          constructor
          · intro hx
            obtain ⟨i,hi⟩ := mem_iUnion.mp hx
            exact mem_iUnion.mpr ⟨a i,hi⟩
          · intro hx
            obtain ⟨i,hi⟩ := mem_iUnion.mp hx
            exact mem_iUnion.mpr ⟨a.symm i,by simpa only [a.apply_symm_apply] using hi⟩
      _ = R := hQu
  · intro j x hx y hy
    simpa only [show 6*(3*(H:ℝ)) = 18*(H:ℝ) by ring] using hCdiam j x hx y hy

end SphericalRiesz
end
end
