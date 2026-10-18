import Riesz.GaussianPSD

/-!
# Finite Gaussian background subtraction

The background here is an actual finite weighted family, not a postulated
positive-definite kernel.  Diffuse sphere probability and its constant
potential are not yet connected to this file.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SphericalRiesz

variable {E ι κ : Type*} [Fintype ι] [Fintype κ]

def kernelPair (K : E → E → ℝ) (a : ι → ℝ) (x : ι → E)
    (b : κ → ℝ) (y : κ → E) : ℝ :=
  ∑ i, ∑ j, a i * b j * K (x i) (y j)

theorem kernelPair_symm (K : E → E → ℝ) (hK : ∀ x y, K x y = K y x)
    (a : ι → ℝ) (x : ι → E) (b : κ → ℝ) (y : κ → E) :
    kernelPair K a x b y = kernelPair K b y a x := by
  unfold kernelPair
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [hK]
  ring

theorem kernelPair_scale_left (K : E → E → ℝ) (r : ℝ)
    (a : ι → ℝ) (x : ι → E) (b : κ → ℝ) (y : κ → E) :
    kernelPair K (fun i => r*a i) x b y = r * kernelPair K a x b y := by
  simp only [kernelPair, mul_assoc, ← Finset.mul_sum]

theorem kernelPair_scale_right (K : E → E → ℝ) (r : ℝ)
    (a : ι → ℝ) (x : ι → E) (b : κ → ℝ) (y : κ → E) :
    kernelPair K a x (fun j => r*b j) y = r * kernelPair K a x b y := by
  unfold kernelPair
  have h (i : ι) (j : κ) : a i * (r*b j) * K (x i) (y j) =
      r * (a i*b j*K (x i) (y j)) := by ring
  simp_rw [h, ← Finset.mul_sum]

theorem kernelPair_sum_family (K : E → E → ℝ) (a : ι → ℝ) (x : ι → E)
    (b : κ → ℝ) (y : κ → E) :
    kernelPair K (Sum.elim a b) (Sum.elim x y) (Sum.elim a b) (Sum.elim x y) =
      kernelPair K a x a x + kernelPair K a x b y +
        kernelPair K b y a x + kernelPair K b y b y := by
  simp only [kernelPair, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_add_distrib]
  ring

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The charge of each foreground atom is 1, and the background charge is −M b_j. -/
def finiteGaussianDefect (t M : ℝ) (x : ι → E) (b : κ → ℝ) (y : κ → E) : ℝ :=
  kernelPair (gaussianKernel t) (fun _ => 1) x (fun _ => 1) x -
    2*M*kernelPair (gaussianKernel t) (fun _ => 1) x b y +
    M^2*kernelPair (gaussianKernel t) b y b y

/-- A concrete signed-family calculation proves the neutralized energy is nonnegative. -/
theorem finiteGaussianDefect_nonneg {t : ℝ} (ht : 0 ≤ t) (M : ℝ)
    (x : ι → E) (b : κ → ℝ) (y : κ → E) :
    0 ≤ finiteGaussianDefect t M x b y := by
  have h := gaussian_weighted_sum_nonneg ht
    (Sum.elim (fun _ : ι => (1 : ℝ)) (fun j : κ => (-M)*b j)) (Sum.elim x y)
  change 0 ≤ kernelPair (gaussianKernel t)
    (Sum.elim (fun _ : ι => 1) (fun j : κ => (-M)*b j)) (Sum.elim x y)
    (Sum.elim (fun _ : ι => 1) (fun j : κ => (-M)*b j)) (Sum.elim x y) at h
  rw [kernelPair_sum_family, kernelPair_scale_right, kernelPair_scale_left,
    kernelPair_scale_left, kernelPair_scale_right] at h
  rw [kernelPair_symm (gaussianKernel t) (gaussianKernel_symm t) b y (fun _ => 1) x] at h
  unfold finiteGaussianDefect
  nlinarith [h]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem gaussian_diagonal_lower (t : ℝ) (x : ι → E) :
    (Fintype.card ι : ℝ) ≤ kernelPair (gaussianKernel t) (fun _ => 1) x (fun _ => 1) x := by
  classical
  have h (i : ι) : 1 ≤ ∑ j, gaussianKernel t (x i) (x j) := by
    simpa using Finset.single_le_sum
      (fun j (_ : j ∈ Finset.univ) => gaussianKernel_nonneg t (x i) (x j))
      (Finset.mem_univ i)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)
  simpa [kernelPair] using hs

/-- The two estimates needed for the eventual Fatou domination combine by a maximum. -/
theorem background_subtracted_common_lower {G B C : ℝ}
    (hdefect : 0 ≤ G-B) (hdiagonal : 1 ≤ G) (hbackground : B ≤ C) :
    -min 1 C ≤ G-B-1 := by
  by_cases h : 1 ≤ C
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right (le_of_lt (not_le.mp h))]; linarith

#print axioms finiteGaussianDefect_nonneg
#print axioms gaussian_diagonal_lower
#print axioms background_subtracted_common_lower

end SphericalRiesz
