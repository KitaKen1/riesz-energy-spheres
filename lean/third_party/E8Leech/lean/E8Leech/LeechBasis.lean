/-
Copyright (c) 2025 Bhavik Mehta, Gareth Ma. All rights reserved.
Released under Apache 2.0 license as described in licenses/Sphere-Packing-Apache-2.0.txt.
Authors: Bhavik Mehta, Gareth Ma; adapted for this project by Codex

The determinant-to-basis and volume-transfer proof pattern is adapted through
E8Leech/E8Lattice.lean from Sphere-Packing-Lean, commit
cbe754e5b699945fd391e6398e6293e9fafa16ec, SpherePacking/Basic/E8.lean.
The Leech integer reconstruction and odd-row replacement proofs are local.
-/
import E8Leech.LeechBasisCandidate
import E8Leech.LeechLattice
import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# A certified basis and covolume for the Golay-congruence Leech model

The even matrix is upper triangular. Replacing row one by the known odd vector
halves its determinant, as witnessed by the coefficient-one integer identity.
No external determinant calculation is used as a proof input.
-/

noncomputable section

namespace E8Leech

open Set Matrix Module MeasureTheory
open scoped ENNReal

theorem leechEvenCandidate_upper :
    leechEvenCandidateNumerators.BlockTriangular id := by
  decide +kernel

theorem leechEvenCandidate_det : leechEvenCandidateNumerators.det = 2 ^ 37 := by
  rw [Matrix.det_of_isUpperTriangular leechEvenCandidate_upper]
  norm_num [leechEvenCandidateNumerators, Fin.prod_univ_succ]

theorem leechCandidate_det : leechCandidateNumerators.det = 2 ^ 36 := by
  have h := Matrix.det_updateRow_sum leechEvenCandidateNumerators 1
    leechTwiceOddCoefficients
  rw [leechTwiceOdd_expansion, Matrix.det_updateRow_smul] at h
  change 2 * leechCandidateNumerators.det =
    leechTwiceOddCoefficients 1 * leechEvenCandidateNumerators.det at h
  norm_num [leechTwiceOddCoefficients, leechEvenCandidate_det] at h ⊢
  omega

private theorem even_rows_mem (i : Fin 24) :
    leechEvenCandidateNumerators i ∈ leechNumerators := by
  refine ⟨0, ?_, ?_, ?_⟩
  · fin_cases i <;> decide +kernel
  · fin_cases i <;> decide +kernel
  · rw [golay_mem_iff]
    refine ⟨fun j => leechResidue (leechEvenCandidateNumerators i) 0
      (j.castAdd 12), ?_⟩
    fin_cases i <;> decide +kernel

private theorem even_first_entries : ∀ i j : Fin 12,
    leechEvenCandidateNumerators (i.castAdd 12) (j.castAdd 12) =
      if i = j then 2 else 0 := by
  decide +kernel

private def leechFirstPart (z : Fin 24 → ℤ) : Fin 24 → ℤ :=
  ∑ i : Fin 12, (z (i.castAdd 12) / 2) • leechEvenCandidateNumerators (i.castAdd 12)

private theorem firstPart_mem (z : Fin 24 → ℤ) : leechFirstPart z ∈ leechNumerators := by
  change leechFirstPart z ∈ leechNumeratorSubgroup.toIntSubmodule
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (even_rows_mem _)

private theorem firstPart_apply (z : Fin 24 → ℤ) (j : Fin 12) :
    leechFirstPart z (j.castAdd 12) = 2 * (z (j.castAdd 12) / 2) := by
  simp [leechFirstPart, Finset.sum_apply, even_first_entries, mul_comm]

private theorem numerator_even_conditions {z : Fin 24 → ℤ}
    (hz : z ∈ leechNumerators) (hpar : ∀ i, (2 : ℤ) ∣ z i) :
    (8 : ℤ) ∣ ∑ i, z i ∧ leechResidue z 0 ∈ golayCode := by
  obtain ⟨m, hm, hp, hs, hc⟩ := leechNumerators_canonical hz
  rcases hm with rfl | rfl
  · simpa using And.intro hs hc
  · have h0 := hpar 0
    have h1 := hp 0
    omega

private theorem numerator_zero_first {y : Fin 24 → ℤ}
    (hy : y ∈ leechNumerators) (hp : ∀ i, (2 : ℤ) ∣ y i)
    (hfirst : ∀ i : Fin 12, y (i.castAdd 12) = 0) :
    (∀ i, (4 : ℤ) ∣ y i) ∧ (8 : ℤ) ∣ ∑ i, y i := by
  obtain ⟨hs, hc⟩ := numerator_even_conditions hy hp
  obtain ⟨a, ha⟩ := golay_mem_iff.mp hc
  have haz : a = 0 := by
    ext i
    have hi := congrFun ha (i.castAdd 12)
    simpa [golayEncode, leechResidue, hfirst] using hi
  have hz : leechResidue y 0 = 0 := by
    rw [← ha, haz]
    change golayEncoderLinear 0 = 0
    exact map_zero _
  refine ⟨fun i => ?_, hs⟩
  have hi := hp i
  have hq : (2 : ℤ) ∣ y i / 2 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (y i / 2) 2).mp
      (by simpa [leechResidue] using congrFun hz i)
  omega

def leechTailCoefficients (y : Fin 24 → ℤ) : Fin 24 → ℤ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    y 12 / 4, y 13 / 4, y 14 / 4, y 15 / 4, y 16 / 4, y 17 / 4,
    y 18 / 4, y 19 / 4, y 20 / 4, y 21 / 4, y 22 / 4, (∑ i, y i) / 8]

theorem leechTailCoefficients_reconstruct {y : Fin 24 → ℤ}
    (hfirst : ∀ i : Fin 12, y (i.castAdd 12) = 0)
    (hfour : ∀ i, (4 : ℤ) ∣ y i) (hsum : (8 : ℤ) ∣ ∑ i, y i) :
    ∑ i, leechTailCoefficients y i • leechEvenCandidateNumerators i = y := by
  have hz0 : y 0 = 0 := hfirst 0
  have hz1 : y 1 = 0 := hfirst 1
  have hz2 : y 2 = 0 := hfirst 2
  have hz3 : y 3 = 0 := hfirst 3
  have hz4 : y 4 = 0 := hfirst 4
  have hz5 : y 5 = 0 := hfirst 5
  have hz6 : y 6 = 0 := hfirst 6
  have hz7 : y 7 = 0 := hfirst 7
  have hz8 : y 8 = 0 := hfirst 8
  have hz9 : y 9 = 0 := hfirst 9
  have hz10 : y 10 = 0 := hfirst 10
  have hz11 : y 11 = 0 := hfirst 11
  have hd12 := hfour 12
  have hd13 := hfour 13
  have hd14 := hfour 14
  have hd15 := hfour 15
  have hd16 := hfour 16
  have hd17 := hfour 17
  have hd18 := hfour 18
  have hd19 := hfour 19
  have hd20 := hfour 20
  have hd21 := hfour 21
  have hd22 := hfour 22
  have hsumEq := Int.mul_ediv_cancel' hsum
  norm_num [Fin.sum_univ_succ] at hsumEq
  change 8 * ((y 0 + (y 1 + (y 2 + (y 3 + (y 4 + (y 5 + (y 6 + (y 7 + (y 8 + (y 9 + (y 10 + (y 11 + (y 12 + (y 13 + (y 14 + (y 15 + (y 16 + (y 17 + (y 18 + (y 19 + (y 20 + (y 21 + (y 22 + (y 23)))))))))))))))))))))))) / 8) = y 0 + (y 1 + (y 2 + (y 3 + (y 4 + (y 5 + (y 6 + (y 7 + (y 8 + (y 9 + (y 10 + (y 11 + (y 12 + (y 13 + (y 14 + (y 15 + (y 16 + (y 17 + (y 18 + (y 19 + (y 20 + (y 21 + (y 22 + (y 23))))))))))))))))))))))) at hsumEq
  ext j
  fin_cases j <;>
    simp [leechTailCoefficients, leechEvenCandidateNumerators, Fin.sum_univ_succ] <;> omega

private theorem even_rows_parity : ∀ i j : Fin 24,
    (2 : ℤ) ∣ leechEvenCandidateNumerators i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem firstPart_parity (z : Fin 24 → ℤ) (j : Fin 24) :
    (2 : ℤ) ∣ leechFirstPart z j := by
  unfold leechFirstPart
  rw [Finset.sum_apply]
  apply Finset.dvd_sum
  intro i _
  exact dvd_mul_of_dvd_right (even_rows_parity _ _) _

def leechNumeratorSpan : Submodule ℤ (Fin 24 → ℤ) :=
  Submodule.span ℤ (Set.range leechCandidateNumerators.row)

private theorem odd_mem_span : leechOddCandidateNumerator ∈ leechNumeratorSpan := by
  have h : leechCandidateNumerators 1 = leechOddCandidateNumerator := by
    simp [leechCandidateNumerators]
  rw [← h]
  exact Submodule.subset_span ⟨1, rfl⟩

private theorem even_row_mem_span (i : Fin 24) :
    leechEvenCandidateNumerators i ∈ leechNumeratorSpan := by
  by_cases hi : i = 1
  · subst i
    rw [leechOmittedRow_reconstruct]
    apply Submodule.sub_mem
    · exact Submodule.smul_mem _ _ odd_mem_span
    · apply Submodule.sum_mem
      intro j hj
      apply Submodule.smul_mem
      have hj1 : j ≠ 1 := (Finset.mem_erase.mp hj).1
      have he : leechCandidateNumerators j = leechEvenCandidateNumerators j := by
        simp only [leechCandidateNumerators, Function.update_of_ne hj1]
        rfl
      rw [← he]
      exact Submodule.subset_span ⟨j, rfl⟩
  · have he : leechCandidateNumerators i = leechEvenCandidateNumerators i := by
      simp only [leechCandidateNumerators, Function.update_of_ne hi]
      rfl
    rw [← he]
    exact Submodule.subset_span ⟨i, rfl⟩

theorem leechEvenNumerator_mem_span {z : Fin 24 → ℤ}
    (hz : z ∈ leechNumerators) (hp : ∀ i, (2 : ℤ) ∣ z i) : z ∈ leechNumeratorSpan := by
  let y := z - leechFirstPart z
  have hy : y ∈ leechNumerators := leechNumerators_sub hz (firstPart_mem z)
  have hpy : ∀ i, (2 : ℤ) ∣ y i := by
    intro i
    exact dvd_sub (hp i) (firstPart_parity z i)
  have hfirst : ∀ i : Fin 12, y (i.castAdd 12) = 0 := by
    intro i
    change z (i.castAdd 12) - leechFirstPart z (i.castAdd 12) = 0
    rw [firstPart_apply]
    have hi := hp (i.castAdd 12)
    omega
  obtain ⟨hfour, hsum⟩ := numerator_zero_first hy hpy hfirst
  have hfm : leechFirstPart z ∈ leechNumeratorSpan := by
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (even_row_mem_span _)
  have hym : y ∈ leechNumeratorSpan := by
    rw [← leechTailCoefficients_reconstruct hfirst hfour hsum]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (even_row_mem_span _)
  have he : z = leechFirstPart z + y := by dsimp [y]; abel
  rw [he]
  exact Submodule.add_mem _ hfm hym

private theorem odd_parity : ∀ i : Fin 24,
    (2 : ℤ) ∣ leechOddCandidateNumerator i - 1 := by
  decide +kernel

theorem leechNumerator_mem_span {z : Fin 24 → ℤ} (hz : z ∈ leechNumerators) :
    z ∈ leechNumeratorSpan := by
  obtain ⟨m, hm, hp, _, _⟩ := leechNumerators_canonical hz
  rcases hm with rfl | rfl
  · apply leechEvenNumerator_mem_span hz
    simpa using hp
  · have hv : leechOddCandidateNumerator ∈ leechNumerators := by
      simpa [leechCandidateNumerators] using leechCandidate_rows_mem 1
    have hy := leechNumerators_sub hz hv
    have hpy : ∀ i, (2 : ℤ) ∣ (z - leechOddCandidateNumerator) i := by
      intro i
      have he : z i - leechOddCandidateNumerator i =
          (z i - 1) - (leechOddCandidateNumerator i - 1) := by ring
      change (2 : ℤ) ∣ z i - leechOddCandidateNumerator i
      rw [he]
      exact dvd_sub (hp i) (odd_parity i)
    have hym := leechEvenNumerator_mem_span hy hpy
    have he : z = (z - leechOddCandidateNumerator) + leechOddCandidateNumerator := by abel
    rw [he]
    exact Submodule.add_mem _ hym odd_mem_span

theorem leechNumeratorSpan_eq : leechNumeratorSpan = leechNumeratorSubgroup.toIntSubmodule := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact leechCandidate_rows_mem i
  · intro z hz
    exact leechNumerator_mem_span hz

def leechBasisMatrix : Matrix (Fin 24) (Fin 24) ℝ :=
  fun i j => (leechCandidateNumerators i j : ℝ) / Real.sqrt 8

theorem leechBasisMatrix_det : leechBasisMatrix.det = 1 := by
  have hm : leechBasisMatrix = (Real.sqrt 8)⁻¹ •
      leechCandidateNumerators.map (fun x => (x : ℝ)) := by
    ext i j
    simp [leechBasisMatrix, div_eq_mul_inv, mul_comm]
  have hs : (Real.sqrt 8) ^ 24 = (2 : ℝ) ^ 36 := by
    rw [show 24 = 2 * 12 by decide, pow_mul, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [hm, Matrix.det_smul, ← Int.cast_det, leechCandidate_det]
  simp only [Fintype.card_fin, inv_pow, hs]
  norm_num

theorem leechBasisMatrix_is_basis :
    LinearIndependent ℝ leechBasisMatrix.row ∧
      Submodule.span ℝ (Set.range leechBasisMatrix.row) = ⊤ := by
  rw [Module.Basis.is_basis_iff_det (Pi.basisFun _ _), Pi.basisFun_det_apply]
  change IsUnit leechBasisMatrix.det
  rw [leechBasisMatrix_det]
  exact isUnit_one

def leechCoordinateBasis : Basis (Fin 24) ℝ (Fin 24 → ℝ) :=
  Basis.mk leechBasisMatrix_is_basis.1 leechBasisMatrix_is_basis.2.ge

theorem leechCoordinateBasis_apply (i : Fin 24) :
    leechCoordinateBasis i = leechBasisMatrix.row i := by
  rw [leechCoordinateBasis, Basis.coe_mk]

def leechEuclideanBasis : Basis (Fin 24) ℝ (Ambient 24) :=
  leechCoordinateBasis.map (WithLp.linearEquiv 2 ℝ (Fin 24 → ℝ)).symm

theorem leechEuclideanBasis_apply (i : Fin 24) :
    leechEuclideanBasis i = leechCoordinates (leechCandidateNumerators i) := by
  ext j
  simp [leechEuclideanBasis, leechCoordinateBasis_apply, leechCoordinates, leechBasisMatrix]

theorem leechLattice_eq_span :
    leechLattice = Submodule.span ℤ (Set.range leechEuclideanBasis) := by
  rw [leechLattice, ← leechNumeratorSpan_eq, leechNumeratorSpan, Submodule.map_span]
  have hr : leechCoordinatesLinear '' Set.range leechCandidateNumerators.row =
      Set.range leechEuclideanBasis := by
    rw [← Set.range_comp]
    congr 1
    funext i
    exact (leechEuclideanBasis_apply i).symm
  rw [hr]

theorem volume_leechCoordinateFundamentalDomain :
    volume (ZSpan.fundamentalDomain leechCoordinateBasis) = 1 := by
  rw [ZSpan.volume_fundamentalDomain]
  have hm : Matrix.of leechCoordinateBasis = leechBasisMatrix := by
    ext i j
    simp [leechCoordinateBasis_apply, Matrix.row]
  rw [hm, leechBasisMatrix_det]
  norm_num

theorem volume_leechFundamentalDomain :
    volume (ZSpan.fundamentalDomain leechEuclideanBasis) = 1 := by
  have heq : (@WithLp.ofLp 2 (Fin 24 → ℝ)) ⁻¹'
      ZSpan.fundamentalDomain leechCoordinateBasis =
        ZSpan.fundamentalDomain leechEuclideanBasis := by
    ext x
    simp [ZSpan.fundamentalDomain, leechEuclideanBasis, Basis.map_repr]
  rw [← heq,
    (PiLp.volume_preserving_ofLp (ι := Fin 24)).measure_preimage
      (ZSpan.fundamentalDomain_measurableSet _).nullMeasurableSet,
    volume_leechCoordinateFundamentalDomain]

theorem leechLattice_covolume : ZLattice.covolume leechLattice = 1 := by
  rw [leechLattice_eq_span,
    ZLattice.covolume_eq_measure_fundamentalDomain _ volume
      (ZSpan.isAddFundamentalDomain leechEuclideanBasis volume)]
  simp [measureReal_def, volume_leechFundamentalDomain]

end E8Leech
