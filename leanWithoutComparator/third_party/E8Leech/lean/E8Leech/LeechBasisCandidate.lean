import E8Leech.LeechCoordinates
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Small certificates for a proposed Leech basis

The explicit even matrix and a single odd-row replacement are candidate generators.
Row membership and the coefficient-one relation are checked by the Lean kernel.
Full span reconstruction and determinant/covolume are proved in LeechBasis.lean.
The determinant values in research/leech-basis-candidate.json are external candidate
calculations, not imported proof inputs.
-/

namespace E8Leech

open Matrix

def leechEvenCandidateNumerators : Matrix (Fin 24) (Fin 24) ℤ :=
  !![2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2;
     0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 2, 2, 2, 0, 0, 0, 2, 0;
     0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 2, 2, 0, 0, 0, 2, 0, 2;
     0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 0, 0, 0, 2, 0, 2, 2;
     0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 0, 0, 0, 2, 0, 2, 2, 0;
     0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 2, 0, 2, 2, 0, 2;
     0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 2, 0, 2, 2, 0, 2, 2;
     0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 2, 0, 2, 2, 2;
     0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 2, 2, 0, 2, 2, 2, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 2, 0, 2, 2, 0, 2, 2, 2, 0, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 2, 2, 0, 2, 2, 2, 0, 0, 0, 2;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, -4;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, -4;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, -4;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, -4;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, -4;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, -4;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, -4;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, -4;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, -4;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, -4;
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8]

def leechOddCandidateNumerator : Fin 24 → ℤ :=
  ![-3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

def leechCandidateNumerators : Matrix (Fin 24) (Fin 24) ℤ :=
  Function.update leechEvenCandidateNumerators.row 1 leechOddCandidateNumerator

def leechTwiceOddCoefficients : Fin 24 → ℤ :=
  ![-3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -5, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -8]

theorem leechCandidate_rows_mem (i : Fin 24) :
    leechCandidateNumerators i ∈ leechNumerators := by
  refine ⟨if i = 1 then 1 else 0, ?_, ?_, ?_⟩
  · fin_cases i <;> decide +kernel
  · fin_cases i <;> decide +kernel
  · rw [golay_mem_iff]
    refine ⟨fun j => leechResidue (leechCandidateNumerators i)
      (if i = 1 then 1 else 0) (j.castAdd 12), ?_⟩
    fin_cases i <;> decide +kernel

theorem leechTwiceOdd_expansion :
    ∑ i, leechTwiceOddCoefficients i • leechEvenCandidateNumerators i =
      (2 : ℤ) • leechOddCandidateNumerator := by
  decide +kernel

theorem leechOmittedRow_reconstruct :
    leechEvenCandidateNumerators 1 =
      (2 : ℤ) • leechOddCandidateNumerator -
        ∑ i ∈ Finset.univ.erase 1,
          leechTwiceOddCoefficients i • leechEvenCandidateNumerators i := by
  decide +kernel

end E8Leech
