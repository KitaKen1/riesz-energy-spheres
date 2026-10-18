import E8Leech.E8Lattice
import E8Leech.E8Geometry
import Riesz.PoissonLattice

/-!
# E8 is even and contains its dual lattice

`|x|²` is even on `E8`, and a vector with integer inner products against `E8` lies in `E8`
(test vectors `eᵢ ± eⱼ` and `(1/2, …, 1/2)`). These are the lattice inputs of the
Poisson-summation calibration (`LatticeCalibration`): the CKMRV functions and their Fourier
transforms carry the factor `sin²(π|x|²/2)`, which vanishes on `E8 = E8^*`.
-/

noncomputable section

namespace E8Leech

open Finset
open scoped RealInnerProductSpace

private theorem int_sq_sub_one_eight_dvd {k : ℤ} (hk : ¬ (2 : ℤ) ∣ k) :
    (8 : ℤ) ∣ k ^ 2 - 1 := by
  rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, rfl⟩
  · exact absurd ⟨m, by omega⟩ hk
  · rcases Int.even_or_odd m with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨a * (m + 1), by rw [ha]; ring⟩
    · exact ⟨m * (a + 1), by rw [ha]; ring⟩

private theorem int_sq_sub_two_mul_eight_dvd {k : ℤ} (hk : (2 : ℤ) ∣ k) :
    (8 : ℤ) ∣ k ^ 2 - 2 * k := by
  obtain ⟨a, rfl⟩ := hk
  rcases Int.even_or_odd a with ⟨b, hb⟩ | ⟨b, hb⟩
  · exact ⟨b * (a - 1), by rw [hb]; ring⟩
  · exact ⟨a * b, by rw [hb]; ring⟩

theorem e8Numerators_square_sum_dvd {z : Fin 8 → ℤ} (hz : z ∈ e8Numerators) :
    (8 : ℤ) ∣ ∑ i, z i ^ 2 := by
  by_cases heven : (2 : ℤ) ∣ z 0
  · have hdiv : ∀ i, (2 : ℤ) ∣ z i := fun i => by simpa using dvd_add (hz.1 i) heven
    have h1 : (8 : ℤ) ∣ ∑ i, (z i ^ 2 - 2 * z i) :=
      Finset.dvd_sum fun i _ => int_sq_sub_two_mul_eight_dvd (hdiv i)
    have h2 : (8 : ℤ) ∣ 2 * ∑ i, z i := by
      obtain ⟨c, hc⟩ := hz.2
      exact ⟨c, by rw [hc]; ring⟩
    have heq : ∑ i, z i ^ 2 = ∑ i, (z i ^ 2 - 2 * z i) + 2 * ∑ i, z i := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
      ring
    rw [heq]
    exact dvd_add h1 h2
  · have hodd : ∀ i, ¬ (2 : ℤ) ∣ z i := by
      intro i hi
      apply heven
      simpa using dvd_sub hi (hz.1 i)
    have h1 : (8 : ℤ) ∣ ∑ i, (z i ^ 2 - 1) :=
      Finset.dvd_sum fun i _ => int_sq_sub_one_eight_dvd (hodd i)
    have heq : ∑ i, z i ^ 2 = ∑ i, (z i ^ 2 - 1) + 8 := by
      rw [Finset.sum_sub_distrib]
      simp
    rw [heq]
    exact dvd_add h1 (dvd_refl 8)

/-- **`E8` is even.** -/
theorem e8Set_norm_sq_even {x : Ambient 8} (hx : x ∈ e8Set) : ∃ n : ℤ, ‖x‖ ^ 2 = 2 * n := by
  obtain ⟨z, hz, rfl⟩ := hx
  obtain ⟨c, hc⟩ := e8Numerators_square_sum_dvd hz
  refine ⟨c, ?_⟩
  have hc' : (∑ i, (z i : ℝ) ^ 2) = 8 * c := by exact_mod_cast hc
  rw [halfCoordinates_norm_sq, hc']
  ring

theorem inner_halfCoordinates (x : Ambient 8) (z : Fin 8 → ℤ) :
    ⟪x, halfCoordinates z⟫ = (∑ i, x i * (z i : ℝ)) / 2 := by
  simp only [halfCoordinates, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The doubled coordinates of `eᵢ + s eⱼ`. -/
def pairNum (i j : Fin 8) (s : ℤ) : Fin 8 → ℤ :=
  fun k => (if k = i then 2 else 0) + (if k = j then 2 * s else 0)

private theorem pairNum_one_parity :
    ∀ i j k : Fin 8, (pairNum i j 1 k - pairNum i j 1 0) % 2 = 0 := by decide

private theorem pairNum_one_sum : ∀ i j : Fin 8, (∑ k, pairNum i j 1 k) % 4 = 0 := by decide

private theorem pairNum_neg_one_parity :
    ∀ i j k : Fin 8, (pairNum i j (-1) k - pairNum i j (-1) 0) % 2 = 0 := by decide

private theorem pairNum_neg_one_sum : ∀ i j : Fin 8, (∑ k, pairNum i j (-1) k) % 4 = 0 := by
  decide

theorem pairNum_mem (i j : Fin 8) {s : ℤ} (hs : s = 1 ∨ s = -1) : pairNum i j s ∈ e8Numerators := by
  rcases hs with rfl | rfl
  · exact ⟨fun k => Int.dvd_of_emod_eq_zero (pairNum_one_parity i j k),
      Int.dvd_of_emod_eq_zero (pairNum_one_sum i j)⟩
  · exact ⟨fun k => Int.dvd_of_emod_eq_zero (pairNum_neg_one_parity i j k),
      Int.dvd_of_emod_eq_zero (pairNum_neg_one_sum i j)⟩

theorem inner_halfCoordinates_pairNum (x : Ambient 8) (i j : Fin 8) (s : ℤ) :
    ⟪x, halfCoordinates (pairNum i j s)⟫ = x i + s * x j := by
  rw [inner_halfCoordinates]
  simp only [pairNum, Int.cast_add, Int.cast_ite, Int.cast_ofNat, Int.cast_zero, Int.cast_mul,
    mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  ring

theorem ones_mem_e8Numerators : (fun _ : Fin 8 => (1 : ℤ)) ∈ e8Numerators :=
  ⟨fun k => by simp, by decide⟩

theorem inner_halfCoordinates_ones (x : Ambient 8) :
    ⟪x, halfCoordinates (fun _ : Fin 8 => (1 : ℤ))⟫ = (∑ i, x i) / 2 := by
  rw [inner_halfCoordinates]
  simp only [Int.cast_one, mul_one]

/-- **`E8` contains its dual lattice.** -/
theorem mem_e8Set_of_mem_dualLattice {x : Ambient 8}
    (hx : x ∈ SchwartzMap.dualLattice e8Lattice) : x ∈ e8Set := by
  have hint : ∀ z ∈ e8Numerators, ∃ k : ℤ, (k : ℝ) = ⟪x, halfCoordinates z⟫ := by
    intro z hz
    have hy : halfCoordinates z ∈ e8Lattice := by
      rw [← SetLike.mem_coe, coe_e8Lattice]
      exact ⟨z, hz, rfl⟩
    obtain ⟨k, hk⟩ := Submodule.mem_one.mp
      ((LinearMap.BilinForm.mem_dualSubmodule
        (B := (innerₗ (Ambient 8) : LinearMap.BilinForm ℝ (Ambient 8)))).mp hx _ hy)
    exact ⟨k, by simpa using hk⟩
  have hpm : ∀ i j : Fin 8, ∀ s : ℤ, (s = 1 ∨ s = -1) → ∃ k : ℤ, (k : ℝ) = x i + s * x j := by
    intro i j s hs
    obtain ⟨k, hk⟩ := hint _ (pairNum_mem i j hs)
    exact ⟨k, by rw [hk, inner_halfCoordinates_pairNum]⟩
  have h2x : ∀ i : Fin 8, ∃ k : ℤ, (k : ℝ) = 2 * x i := by
    intro i
    obtain ⟨a, ha⟩ := hpm i i 1 (Or.inl rfl)
    exact ⟨a, by rw [ha]; push_cast; ring⟩
  choose w hw using h2x
  have hdiff : ∀ i : Fin 8, ∃ k : ℤ, (k : ℝ) = x i - x 0 := by
    intro i
    obtain ⟨a, ha⟩ := hpm i 0 (-1) (Or.inr rfl)
    exact ⟨a, by rw [ha]; push_cast; ring⟩
  obtain ⟨m, hm⟩ := hint _ ones_mem_e8Numerators
  rw [inner_halfCoordinates_ones] at hm
  refine ⟨w, ⟨fun i => ?_, ?_⟩, ?_⟩
  · obtain ⟨a, ha⟩ := hdiff i
    refine ⟨a, ?_⟩
    have h : ((w i - w 0 : ℤ) : ℝ) = ((2 * a : ℤ) : ℝ) := by
      push_cast
      rw [hw, hw, ha]
      ring
    exact_mod_cast h
  · refine ⟨m, ?_⟩
    have h : ((∑ i, w i : ℤ) : ℝ) = ((4 * m : ℤ) : ℝ) := by
      push_cast
      simp only [hw]
      rw [← Finset.mul_sum, hm]
      ring
    exact_mod_cast h
  · ext i
    simp only [halfCoordinates, PiLp.toLp_apply]
    rw [hw]
    ring

theorem dualLattice_e8Lattice_le : SchwartzMap.dualLattice e8Lattice ≤ e8Lattice := by
  intro x hx
  rw [← SetLike.mem_coe, coe_e8Lattice]
  exact mem_e8Set_of_mem_dualLattice hx

/-- Every vector of the dual lattice of `E8` has even squared norm. -/
theorem dualLattice_e8Lattice_norm_sq_even {m : Ambient 8}
    (hm : m ∈ SchwartzMap.dualLattice e8Lattice) : ∃ n : ℤ, ‖m‖ ^ 2 = 2 * n :=
  e8Set_norm_sq_even (mem_e8Set_of_mem_dualLattice hm)

end E8Leech
