import Riesz.SphereGaussianMellinBackground8

/-! The actual ordered finite inverse-fourth energy as a Gaussian Mellin integral.
Diagonal terms are removed before integration; both terms in the background
subtraction are separately integrable. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz

def sphereGaussianOffDiagonal8 {N : ℕ} (t : ℝ) (X : Configuration N) : ℝ :=
  ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, sphereGaussianKernel8 t (X i) (X j)

theorem sphereGaussianOffDiagonal8_continuous {N : ℕ} (X : Configuration N) :
    Continuous (fun t : ℝ => sphereGaussianOffDiagonal8 t X) := by
  unfold sphereGaussianOffDiagonal8 sphereGaussianKernel8
  fun_prop

theorem sphereGaussianOffDiagonal8_nonneg {N : ℕ} (t : ℝ) (X : Configuration N) :
    0 ≤ sphereGaussianOffDiagonal8 t X := by
  unfold sphereGaussianOffDiagonal8
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    sphereGaussianKernel8_nonneg t (X i) (X j)

theorem sphereGaussianSum8_diagonal {N : ℕ} (t : ℝ) (X : Configuration N) :
    (∑ i : Fin N, ∑ j : Fin N, sphereGaussianKernel8 t (X i) (X j)) =
      sphereGaussianOffDiagonal8 t X+(N:ℝ) := by
  calc
    _ = ∑ i : Fin N, ((∑ j ∈ Finset.univ.erase i,
        sphereGaussianKernel8 t (X i) (X j))+1) := by
      apply Finset.sum_congr rfl
      intro i _
      have h := Finset.sum_erase_add (s := Finset.univ) (a := i)
        (fun j : Fin N => sphereGaussianKernel8 t (X i) (X j)) (Finset.mem_univ i)
      simpa only [sphereGaussianKernel8_self] using h.symm
    _ = _ := by simp [sphereGaussianOffDiagonal8, Finset.sum_add_distrib]

theorem sphereGaussianOffDiagonal8_eq_full_sub {N : ℕ} (t : ℝ) (X : Configuration N) :
    sphereGaussianOffDiagonal8 t X =
      (∑ i : Fin N, ∑ j : Fin N, sphereGaussianKernel8 t (X i) (X j))-(N:ℝ) := by
  linarith [sphereGaussianSum8_diagonal t X]

theorem sphereGaussianPair8_weighted_integrable {N : ℕ} (X : Configuration N)
    {i j : Fin N} (hij : i ≠ j) :
    IntegrableOn (fun t : ℝ => t*sphereGaussianKernel8 t (X i) (X j)) (Ioi 0) := by
  have hi := linearGaussianMoment_integrable
    (sq_pos_of_pos (offDiagonal_dist_pos X hij))
  simpa only [sphereGaussianKernel8,mul_comm] using hi

theorem sphereGaussianPair8_mellin_four {N : ℕ} (X : Configuration N)
    {i j : Fin N} (hij : i ≠ j) :
    (∫ t : ℝ in Ioi 0, t*sphereGaussianKernel8 t (X i) (X j)) =
      (dist (X i) (X j))⁻¹^4 := by
  simpa only [sphereGaussianKernel8,mul_comm] using
    inverse_fourth_gaussian_integral (offDiagonal_dist_pos X hij)

theorem sphereGaussianOffDiagonal8_weighted_integrable {N : ℕ} (X : Configuration N) :
    IntegrableOn (fun t : ℝ => t*sphereGaussianOffDiagonal8 t X) (Ioi 0) := by
  unfold sphereGaussianOffDiagonal8
  simp_rw [Finset.mul_sum]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j hj
  exact sphereGaussianPair8_weighted_integrable X (Finset.mem_erase.mp hj).1.symm

theorem sphereGaussianOffDiagonal8_mellin_four {N : ℕ} (X : Configuration N) :
    (∫ t : ℝ in Ioi 0, t*sphereGaussianOffDiagonal8 t X) = energy4 X := by
  have hi (i : Fin N) : IntegrableOn
      (fun t : ℝ => ∑ j ∈ Finset.univ.erase i, t*sphereGaussianKernel8 t (X i) (X j))
      (Ioi 0) :=
    integrable_finsetSum _ (fun j hj =>
      sphereGaussianPair8_weighted_integrable X (Finset.mem_erase.mp hj).1.symm)
  unfold sphereGaussianOffDiagonal8 energy4
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j hj =>
    sphereGaussianPair8_weighted_integrable X (Finset.mem_erase.mp hj).1.symm)]
  apply Finset.sum_congr rfl
  intro j hj
  exact sphereGaussianPair8_mellin_four X (Finset.mem_erase.mp hj).1.symm

def sphereGaussianRieszDefect8 {N : ℕ} (t : ℝ) (X : Configuration N) : ℝ :=
  sphereGaussianOffDiagonal8 t X-(N:ℝ)^2*sphereGaussianBackground8 t

theorem sphereGaussianRieszDefect8_eq_full {N : ℕ} (t : ℝ) (X : Configuration N) :
    sphereGaussianRieszDefect8 t X =
      (∑ i : Fin N, ∑ j : Fin N, sphereGaussianKernel8 t (X i) (X j))-(N:ℝ)-
        (N:ℝ)^2*sphereGaussianBackground8 t := by
  rw [sphereGaussianRieszDefect8,sphereGaussianOffDiagonal8_eq_full_sub]

theorem sphereGaussianRieszDefect8_weighted_integrable {N : ℕ} (X : Configuration N) :
    IntegrableOn (fun t : ℝ => t*sphereGaussianRieszDefect8 t X) (Ioi 0) := by
  have hi := (sphereGaussianOffDiagonal8_weighted_integrable X).sub
    (sphereGaussianBackground8_weighted_integrable.const_mul ((N:ℝ)^2))
  apply hi.congr_fun _ measurableSet_Ioi
  intro t _
  change t*sphereGaussianOffDiagonal8 t X-(N:ℝ)^2*(t*sphereGaussianBackground8 t) =
    t*(sphereGaussianOffDiagonal8 t X-(N:ℝ)^2*sphereGaussianBackground8 t)
  ring

theorem sphereGaussianRieszDefect8_mellin_four {N : ℕ} (X : Configuration N) :
    (∫ t : ℝ in Ioi 0, t*sphereGaussianRieszDefect8 t X) =
      energy4 X-(7/16:ℝ)*(N:ℝ)^2 := by
  have he : (fun t : ℝ => t*sphereGaussianRieszDefect8 t X) =
      (fun t : ℝ => t*sphereGaussianOffDiagonal8 t X-
        (N:ℝ)^2*(t*sphereGaussianBackground8 t)) := by
    ext t
    unfold sphereGaussianRieszDefect8
    ring
  rw [he,integral_sub (sphereGaussianOffDiagonal8_weighted_integrable X)
      (sphereGaussianBackground8_weighted_integrable.const_mul ((N:ℝ)^2)),
    integral_const_mul,sphereGaussianOffDiagonal8_mellin_four,
    sphereGaussianBackground8_mellin_four]
  ring

end SphericalRiesz
