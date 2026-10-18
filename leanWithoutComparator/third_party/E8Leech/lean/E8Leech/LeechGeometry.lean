import E8Leech.LeechCoordinates
import E8Leech.E8Geometry

/-!
# Leech minimum distance from Golay weights and integer parity

No list of 196560 minimal vectors is used. The even branch uses minimum code
weight eight, or the mod-eight coordinate-sum condition for the zero codeword.
In the odd branch, a vector with only signs as coordinates violates that condition
because Golay weights are divisible by four. Thus the squared integer norm is at least 32.
-/

noncomputable section

namespace E8Leech

open Set Finset

private theorem int_square_ge_one {k : ℤ} (hk : k ≠ 0) : 1 ≤ k ^ 2 := by
  have h : k ≤ -1 ∨ 1 ≤ k := by omega
  rcases h with h | h <;> nlinarith [sq_nonneg (k + 1), sq_nonneg (k - 1)]

private theorem int_square_ge_dvd {k m : ℤ} (h : m ∣ k) (hk : k ≠ 0) : m ^ 2 ≤ k ^ 2 := by
  obtain ⟨a, rfl⟩ := h
  have ha : a ≠ 0 := by intro ha; simp [ha] at hk
  have hs := int_square_ge_one ha
  nlinarith [sq_nonneg m, sq_nonneg a]

theorem leechNumerators_square_sum_ge {z : Fin 24 → ℤ}
    (hz : z ∈ leechNumerators) (hne : z ≠ 0) : 32 ≤ ∑ i, z i ^ 2 := by
  obtain ⟨m, hm, hpar, hsum, hcode⟩ := leechNumerators_canonical hz
  rcases hm with rfl | rfl
  · simp only [sub_zero, mul_zero] at hpar hsum
    by_cases hc : leechResidue z 0 = 0
    · have hfour : ∀ i, (4 : ℤ) ∣ z i := by
        intro i
        have hi := hpar i
        have hq : (2 : ℤ) ∣ z i / 2 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd (z i / 2) 2).mp
            (by simpa [leechResidue] using congrFun hc i)
        omega
      obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
        by_contra h
        apply hne
        ext i
        simpa using not_exists.mp h i
      by_cases hother : ∃ j, j ≠ i ∧ z j ≠ 0
      · obtain ⟨j, hji, hj⟩ := hother
        have hi16 : 16 ≤ z i ^ 2 := by simpa using int_square_ge_dvd (hfour i) hi
        have hj16 : 16 ≤ z j ^ 2 := by simpa using int_square_ge_dvd (hfour j) hj
        have hs : ∑ k ∈ ({i, j} : Finset (Fin 24)), z k ^ 2 ≤ ∑ k : Fin 24, z k ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun k _ _ => sq_nonneg (z k))
        simp only [Finset.sum_pair hji.symm] at hs
        omega
      · have hs : ∑ k, z k = z i := by
          apply Finset.sum_eq_single i
          · intro j _ hji
            by_contra hj
            exact hother ⟨j, hji, hj⟩
          · simp
        have height : (8 : ℤ) ∣ z i := hs ▸ hsum
        have hi64 : 64 ≤ z i ^ 2 := by simpa using int_square_ge_dvd height hi
        have hs' : z i ^ 2 ≤ ∑ k : Fin 24, z k ^ 2 :=
          Finset.single_le_sum (fun k _ => sq_nonneg (z k)) (Finset.mem_univ i)
        omega
    · let S := Finset.univ.filter (fun i => leechResidue z 0 i ≠ 0)
      have hcard : (8 : ℤ) ≤ S.card := by
        exact_mod_cast golay_minimum_weight hcode hc
      have hs : (S.card : ℤ) * 4 ≤ ∑ i, z i ^ 2 := by
        calc
          _ = ∑ i ∈ S, (4 : ℤ) := by simp
          _ ≤ ∑ i ∈ S, z i ^ 2 := by
            apply Finset.sum_le_sum
            intro i hi
            have hres := (Finset.mem_filter.mp hi).2
            have hzi : z i ≠ 0 := by
              intro hzi
              apply hres
              simp [leechResidue, hzi]
            simpa using int_square_ge_dvd (hpar i) hzi
          _ ≤ ∑ i, z i ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ _) (fun i _ _ => sq_nonneg (z i))
      omega
  · have hnonzero : ∀ i, z i ≠ 0 := by
      intro i
      have hi := hpar i
      omega
    have hone : ∀ i, 1 ≤ z i ^ 2 := fun i => int_square_ge_one (hnonzero i)
    by_cases hlarge : ∃ i, 9 ≤ z i ^ 2
    · obtain ⟨i, hi⟩ := hlarge
      have hs : z i ^ 2 - 1 ≤ ∑ j : Fin 24, (z j ^ 2 - 1) :=
        Finset.single_le_sum (f := fun j : Fin 24 => z j ^ 2 - 1)
          (fun j _ => by have := hone j; omega) (Finset.mem_univ i)
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul] at hs
      omega
    · have hsign : ∀ i, z i = -1 ∨ z i = 1 := by
        intro i
        have hp := hpar i
        have hs : z i ^ 2 < 9 := not_le.mp (fun h => hlarge ⟨i, h⟩)
        have hb : -3 < z i ∧ z i < 3 := by constructor <;> nlinarith [sq_nonneg (z i)]
        omega
      let S := Finset.univ.filter (fun i => z i = -1)
      have hres : leechResidue z 1 = fun i => if z i = -1 then 1 else 0 := by
        ext i
        rcases hsign i with hi | hi <;> (norm_num [leechResidue, hi]; all_goals decide)
      have hw : hammingNorm (leechResidue z 1) = S.card := by
        simp [hammingNorm, hres, S]
      have hfour : (4 : ℤ) ∣ (S.card : ℤ) := by
        have hd : 4 ∣ S.card := by rw [← hw]; exact golay_weight_dvd_four hcode
        exact_mod_cast hd
      have hcount : (∑ i : Fin 24, if z i = -1 then (1 : ℤ) else 0) = S.card := by
        rw [Finset.sum_ite]
        simp [S]
      have hcoords : ∀ i, z i = 1 - 2 * (if z i = -1 then (1 : ℤ) else 0) := by
        intro i
        rcases hsign i with hi | hi <;> norm_num [hi]
      have htotal : (∑ i, z i) = 24 - 2 * (S.card : ℤ) := by
        calc
          _ = ∑ i : Fin 24, (1 - 2 * (if z i = -1 then (1 : ℤ) else 0)) :=
            Finset.sum_congr rfl (fun i _ => hcoords i)
          _ = _ := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hcount]
            norm_num
      rw [htotal] at hsum
      omega

theorem leechCoordinates_norm_sq (z : Fin 24 → ℤ) :
    ‖leechCoordinates z‖ ^ 2 = (∑ i, (z i : ℝ) ^ 2) / 8 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [leechCoordinates, PiLp.toLp_apply, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
  rw [Finset.sum_div]

theorem leechSet_norm_sq_lower {x : Ambient 24} (hx : x ∈ leechSet) (hne : x ≠ 0) :
    4 ≤ ‖x‖ ^ 2 := by
  obtain ⟨z, hz, rfl⟩ := hx
  have hzne : z ≠ 0 := by
    intro h
    subst z
    apply hne
    ext i
    simp [leechCoordinates]
  have hs : (32 : ℝ) ≤ ∑ i, (z i : ℝ) ^ 2 := by
    exact_mod_cast leechNumerators_square_sum_ge hz hzne
  rw [leechCoordinates_norm_sq]
  linarith

theorem leechSet_separated {x y : Ambient 24}
    (hx : x ∈ leechSet) (hy : y ∈ leechSet) (hne : x ≠ y) : 2 ≤ dist x y := by
  have hl := leechSet_norm_sq_lower (leechSet_sub hx hy) (sub_ne_zero.mpr hne)
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (x - y)]

theorem leechSet_inter_compact_finite {K : Set (Ambient 24)} (hK : IsCompact K) :
    (leechSet ∩ K).Finite :=
  separated_inter_compact_finite (by norm_num : (0 : ℝ) < 2)
    (fun _ hx _ hy hne => leechSet_separated hx hy hne) hK

def leechConfiguration : Configuration (Ambient 24) where
  support := leechSet
  finite_on_compacts _ hK := leechSet_inter_compact_finite hK

def leechMinimalNumerator : Fin 24 → ℤ := fun i => if i = 0 then 4 else if i = 1 then -4 else 0

theorem leechMinimalNumerator_mem : leechMinimalNumerator ∈ leechNumerators := by
  refine ⟨0, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [leechMinimalNumerator]
  · decide +kernel
  · have he : leechResidue leechMinimalNumerator 0 = 0 := by
      ext i
      fin_cases i <;> norm_num [leechResidue, leechMinimalNumerator] <;> decide
    rw [he]
    exact golayCode.zero_mem

theorem leechSet_minimum_attained : ∃ x ∈ leechSet, x ≠ 0 ∧ ‖x‖ = 2 := by
  have hs : ‖leechCoordinates leechMinimalNumerator‖ ^ 2 = 4 := by
    rw [leechCoordinates_norm_sq]
    have hint : ∑ i, leechMinimalNumerator i ^ 2 = 32 := by decide +kernel
    have hr : ∑ i, (leechMinimalNumerator i : ℝ) ^ 2 = 32 := by exact_mod_cast hint
    rw [hr]
    norm_num
  refine ⟨leechCoordinates leechMinimalNumerator, ⟨_, leechMinimalNumerator_mem, rfl⟩, ?_, ?_⟩
  · intro h
    rw [h] at hs
    norm_num at hs
  · nlinarith [norm_nonneg (leechCoordinates leechMinimalNumerator)]

end E8Leech
