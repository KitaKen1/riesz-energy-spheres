import Riesz.SphereGaussianMellinScale8
import Riesz.GaussianMellinGeneral

/-! All positive Riesz exponents on the actual unit S⁸ (stage HP, Mellin layer).

For `0 < s < 8` the ordered Riesz `s`-energy of an actual configuration is a Gaussian Mellin
integral with weight `t^(s/2-1)`. The continuous constant `I_s` is defined by the same Mellin
integral of the actual sphere Gaussian background (finite exactly for `0 < s < 8`); for `s = 4`
it is the checked value `7/16`. The density-scale normalization gives
`(E_s - I_s N²)/N^(1+s/8) = π^(s/2) A₈^(-s/8)/Γ(s/2) * ∫ α^(s/2-1) F_N(α) dα`
with the same centered profile `F_N` as the `s = 4` route. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz

/-- The ordered Riesz `s`-energy (distinct points, both orders). -/
def energyRpow (s : ℝ) {N : ℕ} (X : Configuration N) : ℝ :=
  ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, (dist (X i) (X j))^(-s)

theorem energyRpow_four {N : ℕ} (X : Configuration N) : energyRpow 4 X = energy4 X := by
  unfold energyRpow energy4
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.rpow_neg dist_nonneg, show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast, inv_pow]

theorem gaussianPair_mellin_rpow_integrable {s d : ℝ} (hs : 0 < s) (hd : 0 < d) :
    IntegrableOn (fun t : ℝ => t^(s/2-1)*Real.exp (-(d^2*t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := s/2-1) (p := 1) (b := d^2)
    (by linarith) zero_lt_one (by positivity)
  apply h.congr_fun _ measurableSet_Ioi
  intro t _
  simp only [Real.rpow_one, neg_mul]

theorem gaussianPair_mellin_rpow {s d : ℝ} (hs : 0 < s) (hd : 0 < d) :
    (∫ t : ℝ in Ioi 0, t^(s/2-1)*Real.exp (-(d^2*t))) = Real.Gamma (s/2)*d^(-s) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := s/2) (r := d^2) (by positivity)
    (by positivity)
  rw [h, one_div, Real.inv_rpow (sq_nonneg d), ← Real.rpow_natCast,
    ← Real.rpow_mul hd.le, show ((2:ℕ):ℝ)*(s/2) = s by push_cast; ring,
    ← Real.rpow_neg hd.le, mul_comm]

theorem sphereGaussianPair8_weighted_integrable_rpow {s : ℝ} (hs : 0 < s) {N : ℕ}
    (X : Configuration N) {i j : Fin N} (hij : i ≠ j) :
    IntegrableOn (fun t : ℝ => t^(s/2-1)*sphereGaussianKernel8 t (X i) (X j)) (Ioi 0) := by
  have h := gaussianPair_mellin_rpow_integrable hs (offDiagonal_dist_pos X hij)
  apply h.congr_fun _ measurableSet_Ioi
  intro t _
  simp only [sphereGaussianKernel8, mul_comm t]

theorem sphereGaussianPair8_mellin_rpow {s : ℝ} (hs : 0 < s) {N : ℕ}
    (X : Configuration N) {i j : Fin N} (hij : i ≠ j) :
    (∫ t : ℝ in Ioi 0, t^(s/2-1)*sphereGaussianKernel8 t (X i) (X j)) =
      Real.Gamma (s/2)*(dist (X i) (X j))^(-s) := by
  rw [← gaussianPair_mellin_rpow hs (offDiagonal_dist_pos X hij)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [sphereGaussianKernel8, mul_comm t]

theorem sphereGaussianOffDiagonal8_weighted_integrable_rpow {s : ℝ} (hs : 0 < s) {N : ℕ}
    (X : Configuration N) :
    IntegrableOn (fun t : ℝ => t^(s/2-1)*sphereGaussianOffDiagonal8 t X) (Ioi 0) := by
  unfold sphereGaussianOffDiagonal8
  simp_rw [Finset.mul_sum]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j hj
  exact sphereGaussianPair8_weighted_integrable_rpow hs X (Finset.mem_erase.mp hj).1.symm

theorem sphereGaussianOffDiagonal8_mellin_rpow {s : ℝ} (hs : 0 < s) {N : ℕ}
    (X : Configuration N) :
    (∫ t : ℝ in Ioi 0, t^(s/2-1)*sphereGaussianOffDiagonal8 t X) =
      Real.Gamma (s/2)*energyRpow s X := by
  have hi (i : Fin N) : IntegrableOn
      (fun t : ℝ => ∑ j ∈ Finset.univ.erase i, t^(s/2-1)*sphereGaussianKernel8 t (X i) (X j))
      (Ioi 0) :=
    integrable_finsetSum _ (fun j hj =>
      sphereGaussianPair8_weighted_integrable_rpow hs X (Finset.mem_erase.mp hj).1.symm)
  unfold sphereGaussianOffDiagonal8 energyRpow
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j hj =>
    sphereGaussianPair8_weighted_integrable_rpow hs X (Finset.mem_erase.mp hj).1.symm)]
  apply Finset.sum_congr rfl
  intro j hj
  exact sphereGaussianPair8_mellin_rpow hs X (Finset.mem_erase.mp hj).1.symm

theorem sphereGaussianBackground8_continuousOn : ContinuousOn sphereGaussianBackground8 (Ici 0) := by
  have hc : Continuous (fun t : ℝ => (35/32:ℝ)*∫ v in Icc (0:ℝ) 2, polePolynomialGaussian8 t v) := by
    apply continuous_const.mul
    apply continuous_parametric_integral_of_continuous _ isCompact_Icc
    unfold polePolynomialGaussian8
    fun_prop
  apply hc.continuousOn.congr
  intro t ht
  dsimp only
  rw [sphereGaussianBackground8_polynomial_set ht, integral_Icc_eq_integral_Ioo]

theorem sphereGaussianBackground8_weighted_le_majorant {s t : ℝ} (ht : 0 < t) :
    |t^(s/2-1)*sphereGaussianBackground8 t| ≤ (105/32:ℝ)*sphereGaussianMajorant8 s t := by
  have hB0 := sphereGaussianBackground8_nonneg t
  have hB := sphereGaussianBackground8_min_bound ht
  have hp : 0 ≤ t^(s/2-1) := Real.rpow_nonneg ht.le _
  rw [abs_of_nonneg (mul_nonneg hp hB0), sphereGaussianMajorant8]
  have hmin : min 1 ((105/32:ℝ)/t^4) ≤ (105/32:ℝ)*min 1 ((t^4)⁻¹) := by
    rcases le_total 1 ((t^4)⁻¹) with h | h
    · rw [min_eq_left h]
      exact (min_le_left _ _).trans (by norm_num)
    · rw [min_eq_right h, div_eq_mul_inv]
      exact min_le_right _ _
  calc t^(s/2-1)*sphereGaussianBackground8 t ≤ t^(s/2-1)*((105/32:ℝ)*min 1 ((t^4)⁻¹)) :=
        mul_le_mul_of_nonneg_left (hB.trans hmin) hp
    _ = _ := by ring

theorem sphereGaussianBackground8_weighted_integrable_rpow {s : ℝ} (hs : 0 < s) (hs8 : s < 8) :
    IntegrableOn (fun t : ℝ => t^(s/2-1)*sphereGaussianBackground8 t) (Ioi 0) := by
  have hmaj := (sphereGaussianMajorant8_integrable hs hs8).const_mul (105/32:ℝ)
  refine hmaj.mono' ?_ ?_
  · have hm : ContinuousOn (fun t : ℝ => t^(s/2-1)*sphereGaussianBackground8 t) (Ioi 0) := by
      apply ContinuousOn.mul
      · exact continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))
      · exact sphereGaussianBackground8_continuousOn.mono Ioi_subset_Ici_self
    exact hm.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs]
    exact sphereGaussianBackground8_weighted_le_majorant ht

/-- The continuous Riesz `s`-energy constant of the actual uniform S⁸, defined by the Gaussian
Mellin integral of the actual sphere Gaussian background. -/
def sphereRieszConst8 (s : ℝ) : ℝ :=
  (Real.Gamma (s/2))⁻¹ * ∫ t : ℝ in Ioi 0, t^(s/2-1)*sphereGaussianBackground8 t

theorem sphereRieszConst8_four : sphereRieszConst8 4 = 7/16 := by
  unfold sphereRieszConst8
  have hΓ : Real.Gamma (4/2) = 1 := by norm_num
  rw [hΓ, inv_one, one_mul, ← sphereGaussianBackground8_mellin_four]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only
  rw [show (4:ℝ)/2-1 = 1 by norm_num, Real.rpow_one]

theorem sphereGaussianRieszDefect8_weighted_integrable_rpow {s : ℝ} (hs : 0 < s) (hs8 : s < 8)
    {N : ℕ} (X : Configuration N) :
    IntegrableOn (fun t : ℝ => t^(s/2-1)*sphereGaussianRieszDefect8 t X) (Ioi 0) := by
  have hi := (sphereGaussianOffDiagonal8_weighted_integrable_rpow hs X).sub
    ((sphereGaussianBackground8_weighted_integrable_rpow hs hs8).const_mul ((N:ℝ)^2))
  apply hi.congr_fun _ measurableSet_Ioi
  intro t _
  change t^(s/2-1)*sphereGaussianOffDiagonal8 t X-(N:ℝ)^2*(t^(s/2-1)*sphereGaussianBackground8 t) =
    t^(s/2-1)*(sphereGaussianOffDiagonal8 t X-(N:ℝ)^2*sphereGaussianBackground8 t)
  ring

theorem sphereGaussianRieszDefect8_mellin_rpow {s : ℝ} (hs : 0 < s) (hs8 : s < 8)
    {N : ℕ} (X : Configuration N) :
    (∫ t : ℝ in Ioi 0, t^(s/2-1)*sphereGaussianRieszDefect8 t X) =
      Real.Gamma (s/2)*(energyRpow s X-sphereRieszConst8 s*(N:ℝ)^2) := by
  have hΓ : Real.Gamma (s/2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have he : (fun t : ℝ => t^(s/2-1)*sphereGaussianRieszDefect8 t X) =
      (fun t : ℝ => t^(s/2-1)*sphereGaussianOffDiagonal8 t X-
        (N:ℝ)^2*(t^(s/2-1)*sphereGaussianBackground8 t)) := by
    ext t
    unfold sphereGaussianRieszDefect8
    ring
  rw [he, integral_sub (sphereGaussianOffDiagonal8_weighted_integrable_rpow hs X)
      ((sphereGaussianBackground8_weighted_integrable_rpow hs hs8).const_mul ((N:ℝ)^2)),
    integral_const_mul, sphereGaussianOffDiagonal8_mellin_rpow hs]
  unfold sphereRieszConst8
  field_simp

theorem sphereGaussianRieszDefect8_scaled_mellin_rpow {s : ℝ} (hs : 0 < s) (hs8 : s < 8)
    {N : ℕ} (X : Configuration N) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun α : ℝ => α^(s/2-1)*sphereGaussianRieszDefect8 (c*α) X) (Ioi 0) ∧
    c^(s/2)*(∫ α : ℝ in Ioi 0, α^(s/2-1)*sphereGaussianRieszDefect8 (c*α) X) =
      Real.Gamma (s/2)*(energyRpow s X-sphereRieszConst8 s*(N:ℝ)^2) := by
  set g : ℝ → ℝ := fun t => t^(s/2-1)*sphereGaussianRieszDefect8 t X with hg
  have hcomp : ∀ α : ℝ, 0 < α → g (c*α) =
      c^(s/2-1)*(α^(s/2-1)*sphereGaussianRieszDefect8 (c*α) X) := by
    intro α hα
    simp only [hg]
    rw [Real.mul_rpow hc.le hα.le]
    ring
  have hgi : IntegrableOn g (Ioi 0) := sphereGaussianRieszDefect8_weighted_integrable_rpow hs hs8 X
  have hgc : IntegrableOn (fun α : ℝ => g (c*α)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff g 0 hc).mpr
    simpa only [mul_zero] using hgi
  have hcp : 0 < c^(s/2-1) := Real.rpow_pos_of_pos hc _
  constructor
  · have hh : IntegrableOn (fun α : ℝ => (c^(s/2-1))⁻¹*g (c*α)) (Ioi 0) := hgc.const_mul _
    apply hh.congr_fun _ measurableSet_Ioi
    intro α hα
    dsimp only
    rw [hcomp α hα]
    field_simp
  · have h := integral_comp_mul_left_Ioi' g 0 hc
    simp only [mul_zero, smul_eq_mul] at h
    have he : (∫ α : ℝ in Ioi 0, g (c*α)) =
        c^(s/2-1)*∫ α : ℝ in Ioi 0, α^(s/2-1)*sphereGaussianRieszDefect8 (c*α) X := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro α hα
      exact hcomp α hα
    rw [he, ← mul_assoc, ← Real.rpow_one_add' hc.le (by linarith), show 1+(s/2-1) = s/2 by ring,
      sphereGaussianRieszDefect8_mellin_rpow hs hs8] at h
    exact h

/-- The normalized ordered Riesz `s`-energy `(E_s - I_s N²)/N^(1+s/8)`. -/
def normalizedEnergyRpow (s : ℝ) {N : ℕ} (X : Configuration N) : ℝ :=
  (energyRpow s X-sphereRieszConst8 s*(N:ℝ)^2)/(N:ℝ)^(1+s/8)

theorem normalizedEnergyRpow_four {N : ℕ} (X : Configuration N) :
    normalizedEnergyRpow 4 X = normalizedEnergy X := by
  unfold normalizedEnergyRpow normalizedEnergy
  rw [energyRpow_four, sphereRieszConst8_four, show (1:ℝ)+4/8 = 1+1/2 by norm_num,
    Real.rpow_add' (Nat.cast_nonneg N) (by norm_num), Real.rpow_one, Real.sqrt_eq_rpow]

theorem sphereGaussianCenteredScaled8_weighted_integrable_rpow {s : ℝ} (hs : 0 < s) (hs8 : s < 8)
    {N : ℕ} (hN : 0 < N) (X : Configuration N) :
    IntegrableOn (fun α : ℝ => α^(s/2-1)*sphereGaussianCenteredScaled8 α X) (Ioi 0) := by
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hi : IntegrableOn (fun α : ℝ => (N:ℝ)⁻¹*(α^(s/2-1)*
      sphereGaussianRieszDefect8 (sphereGaussianDensityFactor8 N*α) X)) (Ioi 0) :=
    ((sphereGaussianRieszDefect8_scaled_mellin_rpow hs hs8 X
      (sphereGaussianDensityFactor8_pos hN)).1).const_mul (N:ℝ)⁻¹
  apply hi.congr_fun _ measurableSet_Ioi
  intro α _
  change (N:ℝ)⁻¹*(α^(s/2-1)*sphereGaussianRieszDefect8 (sphereGaussianDensityFactor8 N*α) X) =
    α^(s/2-1)*sphereGaussianCenteredScaled8 α X
  rw [← sphereGaussianScale8_eq_factor, sphereGaussianCenteredScaled8_defect hN]
  field_simp

theorem sphereGaussianDensityFactor8_rpow {s : ℝ} {N : ℕ} (hN : 0 < N) :
    (sphereGaussianDensityFactor8 N)^(s/2) =
      Real.pi^(s/2)*((N:ℝ)/sphereArea8.real univ)^(s/8) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
  have hρ : 0 ≤ (N:ℝ)/sphereArea8.real univ := (div_pos hNR hA).le
  simp only [sphereGaussianDensityFactor8, sphereGaussianScale8, mul_one]
  rw [Real.mul_rpow Real.pi_pos.le (Real.rpow_nonneg hρ _), ← Real.rpow_mul hρ]
  congr 2
  ring

/-- Density-scale Mellin form of the normalized `s`-energy. -/
theorem normalizedEnergyRpow_gaussian_mellin {s : ℝ} (hs : 0 < s) (hs8 : s < 8)
    {N : ℕ} (hN : 0 < N) (X : Configuration N) :
    normalizedEnergyRpow s X =
      (Real.pi^(s/2)*(sphereArea8.real univ)^(-(s/8))/Real.Gamma (s/2))*
        (∫ α : ℝ in Ioi 0, α^(s/2-1)*sphereGaussianCenteredScaled8 α X) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
  have hΓ : 0 < Real.Gamma (s/2) := Real.Gamma_pos_of_pos (by positivity)
  have h := (sphereGaussianRieszDefect8_scaled_mellin_rpow hs hs8 X
    (sphereGaussianDensityFactor8_pos hN)).2
  have he : (fun α : ℝ => α^(s/2-1)*sphereGaussianRieszDefect8 (sphereGaussianDensityFactor8 N*α) X) =
      (fun α : ℝ => (N:ℝ)*(α^(s/2-1)*sphereGaussianCenteredScaled8 α X)) := by
    ext α
    rw [← sphereGaussianScale8_eq_factor, sphereGaussianCenteredScaled8_defect hN]
    ring
  rw [he, integral_const_mul, sphereGaussianDensityFactor8_rpow hN] at h
  set I := ∫ α : ℝ in Ioi 0, α^(s/2-1)*sphereGaussianCenteredScaled8 α X
  have hdiv : ((N:ℝ)/sphereArea8.real univ)^(s/8) =
      (N:ℝ)^(s/8)*(sphereArea8.real univ)^(-(s/8)) := by
    rw [Real.div_rpow hNR.le hA.le, Real.rpow_neg hA.le, div_eq_mul_inv]
  have hpow : (N:ℝ)^(1+s/8) = (N:ℝ)*(N:ℝ)^(s/8) := by
    rw [Real.rpow_add' hNR.le (by positivity), Real.rpow_one]
  have hNs : 0 < (N:ℝ)^(s/8) := Real.rpow_pos_of_pos hNR _
  rw [hdiv] at h
  have h2 : energyRpow s X-sphereRieszConst8 s*(N:ℝ)^2 =
      Real.pi^(s/2)*((N:ℝ)^(s/8)*(sphereArea8.real univ)^(-(s/8)))*((N:ℝ)*I)/Real.Gamma (s/2) := by
    rw [eq_div_iff hΓ.ne']
    linear_combination (-1:ℝ)*h
  have hN0 : (N:ℝ) ≠ 0 := hNR.ne'
  have hNs0 : (N:ℝ)^(s/8) ≠ 0 := hNs.ne'
  have hΓ0 : Real.Gamma (s/2) ≠ 0 := hΓ.ne'
  unfold normalizedEnergyRpow
  rw [hpow, h2]
  field_simp

#print axioms energyRpow_four
#print axioms gaussianPair_mellin_rpow_integrable
#print axioms gaussianPair_mellin_rpow
#print axioms sphereGaussianPair8_weighted_integrable_rpow
#print axioms sphereGaussianPair8_mellin_rpow
#print axioms sphereGaussianOffDiagonal8_weighted_integrable_rpow
#print axioms sphereGaussianOffDiagonal8_mellin_rpow
#print axioms sphereGaussianBackground8_continuousOn
#print axioms sphereGaussianBackground8_weighted_le_majorant
#print axioms sphereGaussianBackground8_weighted_integrable_rpow
#print axioms sphereRieszConst8_four
#print axioms sphereGaussianRieszDefect8_weighted_integrable_rpow
#print axioms sphereGaussianRieszDefect8_mellin_rpow
#print axioms sphereGaussianRieszDefect8_scaled_mellin_rpow
#print axioms normalizedEnergyRpow_four
#print axioms sphereGaussianCenteredScaled8_weighted_integrable_rpow
#print axioms sphereGaussianDensityFactor8_rpow
#print axioms normalizedEnergyRpow_gaussian_mellin

end SphericalRiesz
