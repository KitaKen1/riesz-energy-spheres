import Riesz.Definitions

/-!
Exact global row assembly for the actual spherical ordered-pair energy.
The analytic row estimates and constancy of the uniform sphere potential remain inputs.
This assembly does not require a separate quadrature error for each patch background.
-/

set_option autoImplicit false
noncomputable section
namespace SphericalRiesz

def sphericalRow4 {N : ℕ} (X : Configuration N) (i : Fin N) : ℝ :=
  (∑ j ∈ Finset.univ.erase i, (dist (X i) (X j))⁻¹ ^ 4) / (N : ℝ)

def scaledRowDeviation4 {N : ℕ} (X : Configuration N) (i : Fin N) : ℝ :=
  (sphericalRow4 X i - (7 / 16 : ℝ)) * Real.sqrt N

/-- The baseline is subtracted once from the complete global rows. -/
theorem energy4_row_mean {N : ℕ} (X : Configuration N) (hN : 0 < N) (I : ℝ) :
    energy4 X / (N : ℝ)^2 - I =
      (∑ i : Fin N, (sphericalRow4 X i - I)) / (N : ℝ) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hsum : (∑ i : Fin N, sphericalRow4 X i) = energy4 X / (N : ℝ) := by
    simp only [sphericalRow4, Finset.sum_div, energy4]
  rw [Finset.sum_sub_distrib, hsum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hn]

/-- The target normalization is the arithmetic mean of scaled global row errors. -/
theorem normalizedEnergy_row_mean {N : ℕ} (X : Configuration N) (hN : 0 < N) :
    normalizedEnergy X = (∑ i : Fin N, scaledRowDeviation4 X i) / (N : ℝ) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hp : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  have hsq := Real.sq_sqrt hp.le
  simp only [scaledRowDeviation4, ← Finset.sum_mul]
  calc
    normalizedEnergy X = (energy4 X / (N : ℝ)^2 - (7 / 16 : ℝ)) *
        Real.sqrt N := by
      unfold normalizedEnergy
      field_simp [hn, hs]
      rw [hsq]
      ring
    _ = ((∑ i : Fin N, (sphericalRow4 X i - (7 / 16 : ℝ))) / (N : ℝ)) *
        Real.sqrt N := by rw [energy4_row_mean X hN (7 / 16)]
    _ = _ := by ring

theorem normalizedEnergy_le_of_rows {N : ℕ} (X : Configuration N) (hN : 0 < N)
    (b : ℝ) (hb : ∀ i, scaledRowDeviation4 X i ≤ b) :
    normalizedEnergy X ≤ b := by
  have hp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [normalizedEnergy_row_mean X hN, div_le_iff₀ hp]
  simpa [mul_comm] using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hb i)

/-- Good rows give the sharp coefficient; exceptional rows cost only their fraction. -/
theorem normalizedEnergy_le_of_good_rows {N : ℕ} (X : Configuration N) (hN : 0 < N)
    (good : Finset (Fin N)) (a b : ℝ)
    (ha : ∀ i ∈ good, scaledRowDeviation4 X i ≤ a)
    (hb : ∀ i ∉ good, scaledRowDeviation4 X i ≤ b) :
    normalizedEnergy X ≤
      a + ((Finset.univ \ good).card : ℝ) / (N : ℝ) * (b - a) := by
  have hp : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : ((Finset.univ \ good).card : ℝ) + (good.card : ℝ) = N := by
    have hcard : (Finset.univ \ good).card + good.card = N := by
      simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ good)
    exact_mod_cast hcard
  have hsum : (∑ i : Fin N, scaledRowDeviation4 X i) ≤
      (good.card : ℝ) * a + ((Finset.univ \ good).card : ℝ) * b := by
    rw [← Finset.sum_sdiff (Finset.subset_univ good)]
    have hg := Finset.sum_le_sum (fun i hi => ha i hi)
    have hd := Finset.sum_le_sum (s := Finset.univ \ good)
      (fun i hi => hb i (Finset.mem_sdiff.1 hi).2)
    simpa [add_comm] using add_le_add hd hg
  rw [normalizedEnergy_row_mean X hN, div_le_iff₀ hp]
  calc
    _ ≤ (good.card : ℝ) * a + ((Finset.univ \ good).card : ℝ) * b := hsum
    _ = _ := by
      have hn : (N : ℝ) ≠ 0 := hp.ne'
      field_simp [hn]
      rw [← hc]
      ring

#print axioms energy4_row_mean
#print axioms normalizedEnergy_row_mean
#print axioms normalizedEnergy_le_of_rows
#print axioms normalizedEnergy_le_of_good_rows

end SphericalRiesz
