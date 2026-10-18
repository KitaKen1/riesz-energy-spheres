import E8Leech.LeechBasis
import E8Leech.LeechGeometry
import E8Leech.E8GaussianCertificate
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The Leech lattice is even and contains its dual lattice

The Gram matrix of the basis `leechEuclideanBasis` (rows of `leechCandidateNumerators / √8`) is an
integer matrix with even diagonal, and its inverse is an integer matrix. Both facts are finite
kernel computations. So inner products on the lattice are integers, squared norms are even, and
the dual basis lies in the lattice. With the Lemma 6.2 interface this gives the Leech
certificate statement.
-/

noncomputable section

namespace E8Leech

open Finset Matrix
open scoped RealInnerProductSpace FourierTransform Real

/-- The Gram matrix of `leechEuclideanBasis`. -/
def leechGram : Matrix (Fin 24) (Fin 24) ℤ :=
  !![6, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2;
     2, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
     3, 2, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, -1, 0, 0, 0, -1, -1, -1, 0, -1, 2;
     3, 2, 2, 4, 2, 2, 2, 2, 2, 2, 2, 2, 0, -1, 0, 0, 0, -1, -1, -1, 0, -1, 0, 2;
     3, 2, 2, 2, 4, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0;
     3, 2, 2, 2, 2, 4, 2, 2, 2, 2, 2, 2, 0, 0, 0, -1, -1, -1, 0, -1, 0, 0, -1, 2;
     3, 2, 2, 2, 2, 2, 4, 2, 2, 2, 2, 2, 0, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0, 2;
     3, 2, 2, 2, 2, 2, 2, 4, 2, 2, 2, 2, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0, 0, 2;
     3, 2, 2, 2, 2, 2, 2, 2, 4, 2, 2, 2, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0;
     3, 2, 2, 2, 2, 2, 2, 2, 2, 4, 2, 2, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0;
     3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 2, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0;
     3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 0, -1, 0, 0, -1, 0, 0, 0, -1, -1, -1, 2;
     -1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, -4;
     0, 0, 0, -1, 1, 0, 0, -1, 0, 0, 1, -1, 2, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, -4;
     0, 0, -1, 0, 1, 0, -1, -1, 0, 1, 0, 0, 2, 2, 4, 2, 2, 2, 2, 2, 2, 2, 2, -4;
     0, 0, 0, 0, 1, -1, -1, -1, 1, 0, 1, 0, 2, 2, 2, 4, 2, 2, 2, 2, 2, 2, 2, -4;
     0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 1, -1, 2, 2, 2, 2, 4, 2, 2, 2, 2, 2, 2, -4;
     0, 0, 0, -1, 0, -1, 0, -1, 1, 1, 0, 0, 2, 2, 2, 2, 2, 4, 2, 2, 2, 2, 2, -4;
     0, 0, -1, -1, 0, 0, -1, 0, 1, 0, 1, 0, 2, 2, 2, 2, 2, 2, 4, 2, 2, 2, 2, -4;
     0, 0, -1, -1, 1, -1, 0, 0, 0, 1, 1, 0, 2, 2, 2, 2, 2, 2, 2, 4, 2, 2, 2, -4;
     0, 0, -1, 0, 0, 0, 0, -1, 1, 1, 1, -1, 2, 2, 2, 2, 2, 2, 2, 2, 4, 2, 2, -4;
     0, 0, 0, -1, 1, 0, -1, 0, 1, 1, 0, -1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, 2, -4;
     0, 0, -1, 0, 1, -1, 0, 0, 1, 0, 0, -1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, -4;
     2, 1, 2, 2, 0, 2, 2, 2, 0, 0, 0, 2, -4, -4, -4, -4, -4, -4, -4, -4, -4, -4, -4, 8]

/-- The inverse of `leechGram` (an integer matrix). -/
def leechGramInv : Matrix (Fin 24) (Fin 24) ℤ :=
  !![20, 12, -6, -6, -6, -6, -6, -6, -6, -6, -6, -6, 27, 2, 2, 5, 2, 2, 2, 5, 5, 5, 2, 32;
     12, 8, -4, -4, -4, -4, -4, -4, -4, -4, -4, -4, 18, 2, 2, 4, 2, 2, 2, 4, 4, 4, 2, 25;
     -6, -4, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2, -10, -2, -1, -3, -2, -2, -1, -2, -2, -3, -1, -16;
     -6, -4, 2, 4, 2, 2, 2, 2, 2, 2, 2, 2, -10, -1, -2, -3, -2, -1, -1, -2, -3, -2, -2, -16;
     -6, -4, 2, 2, 4, 2, 2, 2, 2, 2, 2, 2, -10, -2, -2, -3, -1, -1, -1, -3, -2, -3, -2, -16;
     -6, -4, 2, 2, 2, 4, 2, 2, 2, 2, 2, 2, -10, -2, -2, -2, -1, -1, -2, -2, -3, -3, -1, -16;
     -6, -4, 2, 2, 2, 2, 4, 2, 2, 2, 2, 2, -10, -2, -1, -2, -1, -2, -1, -3, -3, -2, -2, -16;
     -6, -4, 2, 2, 2, 2, 2, 4, 2, 2, 2, 2, -10, -1, -1, -2, -2, -1, -2, -3, -2, -3, -2, -16;
     -6, -4, 2, 2, 2, 2, 2, 2, 4, 2, 2, 2, -10, -1, -1, -3, -1, -2, -2, -2, -3, -3, -2, -16;
     -6, -4, 2, 2, 2, 2, 2, 2, 2, 4, 2, 2, -10, -1, -2, -2, -2, -2, -1, -3, -3, -3, -1, -16;
     -6, -4, 2, 2, 2, 2, 2, 2, 2, 2, 4, 2, -10, -2, -1, -3, -2, -1, -2, -3, -3, -2, -1, -16;
     -6, -4, 2, 2, 2, 2, 2, 2, 2, 2, 2, 4, -10, -1, -2, -3, -1, -2, -2, -3, -2, -2, -1, -16;
     27, 18, -10, -10, -10, -10, -10, -10, -10, -10, -10, -10, 46, 7, 7, 12, 7, 7, 7, 12, 12, 12, 7, 74;
     2, 2, -2, -1, -2, -2, -2, -1, -1, -1, -2, -1, 7, 4, 2, 3, 2, 2, 2, 3, 3, 3, 2, 18;
     2, 2, -1, -2, -2, -2, -1, -1, -1, -2, -1, -2, 7, 2, 4, 3, 2, 2, 2, 3, 3, 3, 2, 18;
     5, 4, -3, -3, -3, -2, -2, -2, -3, -2, -3, -3, 12, 3, 3, 6, 3, 3, 3, 4, 4, 4, 3, 26;
     2, 2, -2, -2, -1, -1, -1, -2, -1, -2, -2, -1, 7, 2, 2, 3, 4, 2, 2, 3, 3, 3, 2, 18;
     2, 2, -2, -1, -1, -1, -2, -1, -2, -2, -1, -2, 7, 2, 2, 3, 2, 4, 2, 3, 3, 3, 2, 18;
     2, 2, -1, -1, -1, -2, -1, -2, -2, -1, -2, -2, 7, 2, 2, 3, 2, 2, 4, 3, 3, 3, 2, 18;
     5, 4, -2, -2, -3, -2, -3, -3, -2, -3, -3, -3, 12, 3, 3, 4, 3, 3, 3, 6, 4, 4, 3, 26;
     5, 4, -2, -3, -2, -3, -3, -2, -3, -3, -3, -2, 12, 3, 3, 4, 3, 3, 3, 4, 6, 4, 3, 26;
     5, 4, -3, -2, -3, -3, -2, -3, -3, -3, -2, -2, 12, 3, 3, 4, 3, 3, 3, 4, 4, 6, 3, 26;
     2, 2, -1, -2, -2, -1, -2, -2, -2, -1, -1, -1, 7, 2, 2, 3, 2, 2, 2, 3, 3, 3, 4, 18;
     32, 25, -16, -16, -16, -16, -16, -16, -16, -16, -16, -16, 74, 18, 18, 26, 18, 18, 18, 26, 26, 26, 18, 156]

theorem leechCandidate_gram :
    leechCandidateNumerators * leechCandidateNumeratorsᵀ = (8 : ℤ) • leechGram := by
  decide +kernel

theorem leechGramInv_mul : leechGramInv * leechGram = 1 := by
  decide +kernel

theorem leechGram_diag_even : ∀ i, leechGram i i % 2 = 0 := by
  decide +kernel

theorem inner_leechCoordinates (z w : Fin 24 → ℤ) :
    ⟪leechCoordinates z, leechCoordinates w⟫ = (∑ k, (z k : ℝ) * w k) / 8 := by
  simp only [leechCoordinates, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
  ring

theorem inner_leechEuclideanBasis (i j : Fin 24) :
    ⟪leechEuclideanBasis i, leechEuclideanBasis j⟫ = (leechGram i j : ℝ) := by
  rw [leechEuclideanBasis_apply, leechEuclideanBasis_apply, inner_leechCoordinates]
  have h := congrFun (congrFun leechCandidate_gram i) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul] at h
  have h' : (∑ k, (leechCandidateNumerators i k : ℝ) * leechCandidateNumerators j k) =
      8 * leechGram i j := by
    exact_mod_cast h
  rw [h']
  ring

theorem leechEuclideanBasis_mem (i : Fin 24) : leechEuclideanBasis i ∈ leechLattice := by
  rw [leechLattice_eq_span]
  exact Submodule.subset_span ⟨i, rfl⟩

theorem inner_zsmul_right_real (x y : Ambient 24) (c : ℤ) :
    ⟪x, c • y⟫ = (c : ℝ) * ⟪x, y⟫ := by
  rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right]

theorem inner_zsmul_left_real (x y : Ambient 24) (c : ℤ) :
    ⟪c • x, y⟫ = (c : ℝ) * ⟪x, y⟫ := by
  rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left]

/-- Inner products on the Leech lattice are integers. -/
theorem leechLattice_inner_int {v w : Ambient 24} (hv : v ∈ leechLattice)
    (hw : w ∈ leechLattice) : ∃ k : ℤ, (k : ℝ) = ⟪v, w⟫ := by
  rw [leechLattice_eq_span] at hv hw
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact ⟨leechGram i j, (inner_leechEuclideanBasis i j).symm⟩
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, ha⟩ := hy
      obtain ⟨b, hb⟩ := hz
      exact ⟨a + b, by rw [inner_add_right, ← ha, ← hb]; push_cast; ring⟩
    | smul c y _ hy =>
      obtain ⟨a, ha⟩ := hy
      exact ⟨c * a, by rw [inner_zsmul_right_real, ← ha]; push_cast; ring⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [inner_add_left, ← ha, ← hb]; push_cast; ring⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by rw [inner_zsmul_left_real, ← ha]; push_cast; ring⟩

/-- **The Leech lattice is even.** -/
theorem leechLattice_norm_sq_even {v : Ambient 24} (hv : v ∈ leechLattice) :
    ∃ n : ℤ, ‖v‖ ^ 2 = 2 * n := by
  have hv' := hv
  rw [leechLattice_eq_span] at hv'
  induction hv' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    refine ⟨leechGram i i / 2, ?_⟩
    have h2 : leechGram i i = 2 * (leechGram i i / 2) := by
      have := leechGram_diag_even i
      omega
    rw [← real_inner_self_eq_norm_sq, inner_leechEuclideanBasis]
    exact_mod_cast h2
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy ihx ihy =>
    have hxL : x ∈ leechLattice := by rw [leechLattice_eq_span]; exact hx
    have hyL : y ∈ leechLattice := by rw [leechLattice_eq_span]; exact hy
    obtain ⟨a, ha⟩ := ihx hxL
    obtain ⟨b, hb⟩ := ihy hyL
    obtain ⟨k, hk⟩ := leechLattice_inner_int hxL hyL
    refine ⟨a + b + k, ?_⟩
    rw [norm_add_sq_real, ha, hb, ← hk]
    push_cast
    ring
  | smul c x hx ihx =>
    have hxL : x ∈ leechLattice := by rw [leechLattice_eq_span]; exact hx
    obtain ⟨a, ha⟩ := ihx hxL
    refine ⟨c ^ 2 * a, ?_⟩
    rw [← Int.cast_smul_eq_zsmul ℝ, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ha]
    push_cast
    ring

/-- **The Leech lattice contains its dual lattice.** -/
theorem mem_leechLattice_of_mem_dualLattice {m : Ambient 24}
    (hm : m ∈ SchwartzMap.dualLattice leechLattice) : m ∈ leechLattice := by
  have hk : ∀ i, ∃ k : ℤ, (k : ℝ) = ⟪m, leechEuclideanBasis i⟫ := by
    intro i
    obtain ⟨k, hk⟩ := Submodule.mem_one.mp
      ((LinearMap.BilinForm.mem_dualSubmodule
        (B := (innerₗ (Ambient 24) : LinearMap.BilinForm ℝ (Ambient 24)))).mp hm _
        (leechEuclideanBasis_mem i))
    exact ⟨k, by simpa using hk⟩
  choose k hk using hk
  let c : Fin 24 → ℤ := fun j => ∑ i, k i * leechGramInv i j
  have hint : ∀ l, ∑ j, c j * leechGram j l = k l := by
    intro l
    have h1 : ∀ i, ∑ j, leechGramInv i j * leechGram j l = if i = l then 1 else 0 := by
      intro i
      rw [← Matrix.mul_apply, leechGramInv_mul, Matrix.one_apply]
    calc ∑ j, c j * leechGram j l = ∑ i, k i * ∑ j, leechGramInv i j * leechGram j l := by
          simp only [c, Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
      _ = k l := by
          simp only [h1, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
            if_true]
  have hm_eq : m = ∑ j, (c j : ℝ) • leechEuclideanBasis j := by
    refine InnerProductSpace.ext_inner_right_basis leechEuclideanBasis fun l => ?_
    rw [← hk l, sum_inner]
    simp only [real_inner_smul_left, inner_leechEuclideanBasis]
    exact_mod_cast (hint l).symm
  rw [hm_eq]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [Int.cast_smul_eq_zsmul]
  exact Submodule.smul_mem _ _ (leechEuclideanBasis_mem j)

/-- **Lemma 6.2 interface for the Leech lattice.** -/
theorem leech_gaussianSchwartzCertificate_of_sin_sq (f : SchwartzMap (Ambient 24) ℂ) {α : ℝ}
    (hα : 0 < α) (J Jhat : Ambient 24 → ℝ)
    (hf : ∀ v : Ambient 24, v ≠ 0 →
      f v = ((gaussianKernel α v + 4 * Real.sin (π * ‖v‖ ^ 2 / 2) ^ 2 * J v : ℝ) : ℂ))
    (hJ : ∀ v : Ambient 24, v ≠ 0 → J v ≤ 0)
    (hfhat : ∀ ξ : Ambient 24, ξ ≠ 0 →
      𝓕 (⇑f) ξ = ((4 * Real.sin (π * ‖ξ‖ ^ 2 / 2) ^ 2 * Jhat ξ : ℝ) : ℂ))
    (hJhat : ∀ ξ : Ambient 24, ξ ≠ 0 → 0 ≤ Jhat ξ) :
    GaussianSchwartzCertificate leechSet α f := by
  have hfin := leech_gaussian_lattice_energy_ne_top hα
  rw [← coe_leechLattice] at hfin ⊢
  exact gaussianSchwartzCertificate_of_sin_sq (by norm_num) leechLattice leechLattice_covolume
    (fun v hv => leechLattice_norm_sq_even hv)
    (fun m hm => leechLattice_norm_sq_even (mem_leechLattice_of_mem_dualLattice hm))
    f hfin J Jhat hf hJ hfhat hJhat

end E8Leech
