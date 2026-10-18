import Riesz.GammaNegStrip
import Riesz.SphereRieszLowerRpow8
import Riesz.SphereGaussianMonotone8

/-! Negative exponents `-2 < s < 0` on the actual unit S⁸ (stage NEG, Mellin layer).

For `-2 < s < 0` the kernel is `d^(-s) = d^|s|` and
`d^(-s) = Γ(s/2)⁻¹ ∫₀^∞ t^(s/2-1) (e^(-t d²) - 1) dt` (with `Γ(s/2) < 0`), the diagonal
included. Summing over all ordered pairs and subtracting the same Mellin integral of the
actual Gaussian background `B` gives
`E_s - I_s N² = Γ(s/2)⁻¹ ∫ t^(s/2-1) (Σ_{i,j} e^(-t|x_i-x_j|²) - N² B(t)) dt`,
`I_s = Γ(s/2)⁻¹ ∫ t^(s/2-1) (B(t) - 1) dt`, and in density scale
`(E_s - I_s N²)/N^(1+s/8) = π^(s/2) A₈^(-s/8)/Γ(s/2) ∫ α^(s/2-1) (F_N(α) + 1) dα`
with the same centered profile `F_N` as for positive exponents and `F_N + 1 ≥ 0`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SphericalRiesz

theorem sphere8_dist_le_two (x y : Sphere8) : dist x y ≤ 2 := by
  have hx : ‖(x:Ambient9)‖ = 1 := norm_eq_of_mem_sphere x
  have hy : ‖(y:Ambient9)‖ = 1 := norm_eq_of_mem_sphere y
  rw [Subtype.dist_eq, dist_eq_norm]
  calc ‖(x:Ambient9)-(y:Ambient9)‖ ≤ ‖(x:Ambient9)‖+‖(y:Ambient9)‖ := norm_sub_le _ _
    _ = 2 := by rw [hx, hy]; norm_num

theorem real_Gamma_neg_strip {a : ℝ} (ha : -1 < a) (ha0 : a < 0) : Real.Gamma a < 0 := by
  have h := Real.Gamma_add_one ha0.ne
  have hp : 0 < Real.Gamma (a+1) := Real.Gamma_pos_of_pos (by linarith)
  rw [h] at hp
  by_contra hc
  have hc' : 0 ≤ Real.Gamma a := le_of_not_gt hc
  nlinarith

theorem sphereGaussianPair8_mellin_neg {s : ℝ} (hs : -2 < s) (hs0 : s < 0) (x y : Sphere8) :
    IntegrableOn (fun t : ℝ => t^(s/2-1)*(sphereGaussianKernel8 t x y-1)) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, t^(s/2-1)*(sphereGaussianKernel8 t x y-1)) =
      Real.Gamma (s/2)*(dist x y)^(-s) := by
  have h := gaussianPair_mellin_neg hs hs0 (dist_nonneg (x := x) (y := y))
  have he : (fun t : ℝ => t^(s/2-1)*(sphereGaussianKernel8 t x y-1)) =
      (fun t : ℝ => t^(s/2-1)*(Real.exp (-((dist x y)^2*t))-1)) := by
    funext t
    simp only [sphereGaussianKernel8, mul_comm t]
  rw [he]
  exact h

/-- For `s < 0` the diagonal terms vanish, so the ordered energy is the full double sum. -/
theorem energyRpow_eq_full_neg {s : ℝ} (hs0 : s < 0) {N : ℕ} (X : Configuration N) :
    energyRpow s X = ∑ i : Fin N, ∑ j : Fin N, (dist (X i) (X j))^(-s) := by
  unfold energyRpow
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), dist_self,
    Real.zero_rpow (by linarith), add_zero]

theorem sphereGaussianBackground8_ge_one_sub {t : ℝ} (ht : 0 ≤ t) :
    1-4*t ≤ sphereGaussianBackground8 t := by
  have hle : ∀ p : Sphere8 × Sphere8, (1-4*t:ℝ) ≤ sphereGaussianKernel8 t p.1 p.2 := by
    intro p
    have hd := sphere8_dist_le_two p.1 p.2
    have hd0 : 0 ≤ dist p.1 p.2 := dist_nonneg
    have h1 := Real.add_one_le_exp (-(t*(dist p.1 p.2)^2))
    have hd2 : (dist p.1 p.2)^2 ≤ 4 := by nlinarith
    have h2 : t*(dist p.1 p.2)^2 ≤ 4*t := by nlinarith [mul_le_mul_of_nonneg_left hd2 ht]
    simp only [sphereGaussianKernel8]
    linarith
  have h := integral_mono
    (integrable_const (1-4*t:ℝ) (μ := sphereProbability8.prod sphereProbability8))
    (sphereGaussianKernel8_pair_integrable ht) hle
  unfold sphereGaussianBackground8
  simpa using h

theorem sphereGaussianBackground8_neg_integrable {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    IntegrableOn (fun t : ℝ => t^(s/2-1)*(sphereGaussianBackground8 t-1)) (Ioi 0) := by
  apply integrableOn_Ioi_of_rpow_min_bound (C := 4) (a := s/2) (by linarith) (by linarith)
  · intro t ht
    have ht0 : (0:ℝ) < t := ht
    exact ((Real.continuousAt_rpow_const t (s/2-1) (Or.inl ht0.ne')).continuousWithinAt).mul
      (((sphereGaussianBackground8_continuousOn.mono Ioi_subset_Ici_self) t ht).sub
        continuousWithinAt_const)
  · intro t ht
    have h1 := sphereGaussianBackground8_le_one ht.le
    have h2 := sphereGaussianBackground8_ge_one_sub ht.le
    have hw : 0 ≤ t^(s/2-1) := Real.rpow_nonneg ht.le _
    have hb : 1-sphereGaussianBackground8 t ≤ 4*min t 1 := by
      rcases le_total t 1 with h | h
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right h]
        have h0 : 0 ≤ sphereGaussianBackground8 t :=
          integral_nonneg (fun p => sphereGaussianKernel8_nonneg t p.1 p.2)
        linarith
    rw [abs_mul, abs_of_nonneg hw, abs_of_nonpos (by linarith), neg_sub]
    calc t^(s/2-1)*(1-sphereGaussianBackground8 t) ≤ t^(s/2-1)*(4*min t 1) :=
          mul_le_mul_of_nonneg_left hb hw
      _ = 4*(t^(s/2-1)*min t 1) := by ring

/-- The continuous Riesz constant for `-2 < s < 0`, by the subtracted Gaussian Mellin integral
of the actual sphere background. -/
def sphereRieszConstNeg8 (s : ℝ) : ℝ :=
  (Real.Gamma (s/2))⁻¹ * ∫ t : ℝ in Ioi 0, t^(s/2-1)*(sphereGaussianBackground8 t-1)

/-- The neutralized full Gaussian sum `Σ_{i,j} e^(-t|x_i-x_j|²) - N² B(t)`. -/
def sphereGaussianFullDefect8 {N : ℕ} (t : ℝ) (X : Configuration N) : ℝ :=
  (∑ i : Fin N, ∑ j : Fin N, sphereGaussianKernel8 t (X i) (X j))-(N:ℝ)^2*sphereGaussianBackground8 t

theorem sphereGaussianFullDefect8_mellin_neg {s : ℝ} (hs : -2 < s) (hs0 : s < 0) {N : ℕ}
    (X : Configuration N) :
    IntegrableOn (fun t : ℝ => t^(s/2-1)*sphereGaussianFullDefect8 t X) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, t^(s/2-1)*sphereGaussianFullDefect8 t X) =
      Real.Gamma (s/2)*(energyRpow s X-sphereRieszConstNeg8 s*(N:ℝ)^2) := by
  have hΓ : Real.Gamma (s/2) ≠ 0 := (real_Gamma_neg_strip (by linarith) (by linarith)).ne
  have hpt : ∀ t : ℝ, t^(s/2-1)*sphereGaussianFullDefect8 t X =
      (∑ i : Fin N, ∑ j : Fin N, t^(s/2-1)*(sphereGaussianKernel8 t (X i) (X j)-1))-
        (N:ℝ)^2*(t^(s/2-1)*(sphereGaussianBackground8 t-1)) := by
    intro t
    unfold sphereGaussianFullDefect8
    simp only [mul_sub, Finset.sum_sub_distrib, mul_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have hrow (i : Fin N) : IntegrableOn
      (fun t : ℝ => ∑ j : Fin N, t^(s/2-1)*(sphereGaussianKernel8 t (X i) (X j)-1)) (Ioi 0) :=
    integrable_finsetSum _ (fun j _ => (sphereGaussianPair8_mellin_neg hs hs0 (X i) (X j)).1)
  have hsum : IntegrableOn
      (fun t : ℝ => ∑ i : Fin N, ∑ j : Fin N, t^(s/2-1)*(sphereGaussianKernel8 t (X i) (X j)-1))
      (Ioi 0) := integrable_finsetSum _ (fun i _ => hrow i)
  have hbg := (sphereGaussianBackground8_neg_integrable hs hs0).const_mul ((N:ℝ)^2)
  have hfun : (fun t : ℝ => t^(s/2-1)*sphereGaussianFullDefect8 t X) =
      fun t : ℝ => (∑ i : Fin N, ∑ j : Fin N, t^(s/2-1)*(sphereGaussianKernel8 t (X i) (X j)-1))-
        (N:ℝ)^2*(t^(s/2-1)*(sphereGaussianBackground8 t-1)) := funext hpt
  rw [hfun]
  refine ⟨hsum.sub hbg, ?_⟩
  rw [integral_sub hsum hbg, integral_finsetSum _ (fun i _ => hrow i), integral_const_mul]
  have hrows : ∀ i : Fin N, (∫ t : ℝ in Ioi 0,
      ∑ j : Fin N, t^(s/2-1)*(sphereGaussianKernel8 t (X i) (X j)-1)) =
      ∑ j : Fin N, Real.Gamma (s/2)*(dist (X i) (X j))^(-s) := by
    intro i
    rw [integral_finsetSum _ (fun j _ => (sphereGaussianPair8_mellin_neg hs hs0 (X i) (X j)).1)]
    exact Finset.sum_congr rfl (fun j _ => (sphereGaussianPair8_mellin_neg hs hs0 (X i) (X j)).2)
  rw [Finset.sum_congr rfl (fun i _ => hrows i), energyRpow_eq_full_neg hs0 X]
  simp only [← Finset.mul_sum]
  unfold sphereRieszConstNeg8
  field_simp

/-- Change of variables `t = c α` in a weighted Mellin integral. -/
theorem weighted_mellin_scale {s c : ℝ} (hc : 0 < c) {h : ℝ → ℝ}
    (hi : IntegrableOn (fun t : ℝ => t^(s/2-1)*h t) (Ioi 0)) :
    IntegrableOn (fun α : ℝ => α^(s/2-1)*h (c*α)) (Ioi 0) ∧
    c^(s/2)*(∫ α : ℝ in Ioi 0, α^(s/2-1)*h (c*α)) = ∫ t : ℝ in Ioi 0, t^(s/2-1)*h t := by
  set g : ℝ → ℝ := fun t => t^(s/2-1)*h t with hg
  have hcomp : ∀ α ∈ Ioi (0:ℝ), g (c*α) = c^(s/2-1)*(α^(s/2-1)*h (c*α)) := by
    intro α hα
    have hα0 : (0:ℝ) < α := hα
    simp only [hg]
    rw [Real.mul_rpow hc.le hα0.le]
    ring
  have hgc : IntegrableOn (fun α : ℝ => g (c*α)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff g 0 hc).mpr
    simpa only [mul_zero] using hi
  have hcp : 0 < c^(s/2-1) := Real.rpow_pos_of_pos hc _
  constructor
  · refine IntegrableOn.congr_fun (Integrable.const_mul hgc (c^(s/2-1))⁻¹) (fun α hα => ?_)
      measurableSet_Ioi
    rw [hcomp α hα]
    field_simp
  · have h1 := integral_comp_mul_left_Ioi g 0 hc
    simp only [mul_zero, smul_eq_mul] at h1
    have he : (∫ α : ℝ in Ioi 0, g (c*α)) =
        c^(s/2-1)*∫ α : ℝ in Ioi 0, α^(s/2-1)*h (c*α) := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi hcomp
    rw [he] at h1
    have hpow : c^(s/2) = c^(s/2-1)*c := by
      rw [Real.rpow_sub_one hc.ne']
      field_simp
    calc c^(s/2)*(∫ α : ℝ in Ioi 0, α^(s/2-1)*h (c*α))
        = c*(c^(s/2-1)*∫ α : ℝ in Ioi 0, α^(s/2-1)*h (c*α)) := by rw [hpow]; ring
      _ = c*(c⁻¹*∫ t : ℝ in Ioi 0, g t) := by rw [h1]
      _ = ∫ t : ℝ in Ioi 0, t^(s/2-1)*h t := by rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

theorem sphereGaussianFullDefect8_scaled {N : ℕ} (hN : 0 < N) (α : ℝ) (X : Configuration N) :
    sphereGaussianFullDefect8 (sphereGaussianDensityFactor8 N*α) X =
      (N:ℝ)*(sphereGaussianCenteredScaled8 α X+1) := by
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold sphereGaussianFullDefect8 sphereGaussianCenteredScaled8
  rw [← sphereGaussianScale8_eq_factor]
  field_simp
  ring

/-- The normalized negative-exponent energy `(E_s - I_s N²)/N^(1+s/8)`. -/
def normalizedEnergyNeg8 (s : ℝ) {N : ℕ} (X : Configuration N) : ℝ :=
  (energyRpow s X-sphereRieszConstNeg8 s*(N:ℝ)^2)/(N:ℝ)^(1+s/8)

theorem sphereGaussianCenteredScaled8_neg_integrable {s : ℝ} (hs : -2 < s) (hs0 : s < 0)
    {N : ℕ} (hN : 0 < N) (X : Configuration N) :
    IntegrableOn (fun α : ℝ => α^(s/2-1)*(sphereGaussianCenteredScaled8 α X+1)) (Ioi 0) := by
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h := (weighted_mellin_scale (s := s) (sphereGaussianDensityFactor8_pos hN)
    (sphereGaussianFullDefect8_mellin_neg hs hs0 X).1).1
  refine IntegrableOn.congr_fun (Integrable.const_mul h (N:ℝ)⁻¹) (fun α _ => ?_) measurableSet_Ioi
  rw [sphereGaussianFullDefect8_scaled hN]
  field_simp

/-- Density-scale Mellin form of the normalized negative-exponent energy. -/
theorem normalizedEnergyNeg8_gaussian_mellin {s : ℝ} (hs : -2 < s) (hs0 : s < 0)
    {N : ℕ} (hN : 0 < N) (X : Configuration N) :
    normalizedEnergyNeg8 s X =
      (Real.pi^(s/2)*(sphereArea8.real univ)^(-(s/8))/Real.Gamma (s/2))*
        (∫ α : ℝ in Ioi 0, α^(s/2-1)*(sphereGaussianCenteredScaled8 α X+1)) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hA : 0 < sphereArea8.real univ := by rw [sphereArea8_mass_real]; positivity
  have hΓ : Real.Gamma (s/2) ≠ 0 := (real_Gamma_neg_strip (by linarith) (by linarith)).ne
  have hm := sphereGaussianFullDefect8_mellin_neg hs hs0 X
  have h := (weighted_mellin_scale (s := s) (sphereGaussianDensityFactor8_pos hN) hm.1).2
  rw [hm.2] at h
  have he : (fun α : ℝ => α^(s/2-1)*sphereGaussianFullDefect8 (sphereGaussianDensityFactor8 N*α) X) =
      (fun α : ℝ => (N:ℝ)*(α^(s/2-1)*(sphereGaussianCenteredScaled8 α X+1))) := by
    ext α
    rw [sphereGaussianFullDefect8_scaled hN]
    ring
  rw [he, integral_const_mul, sphereGaussianDensityFactor8_rpow hN] at h
  set I := ∫ α : ℝ in Ioi 0, α^(s/2-1)*(sphereGaussianCenteredScaled8 α X+1)
  have hdiv : ((N:ℝ)/sphereArea8.real univ)^(s/8) =
      (N:ℝ)^(s/8)*(sphereArea8.real univ)^(-(s/8)) := by
    rw [Real.div_rpow hNR.le hA.le, Real.rpow_neg hA.le, div_eq_mul_inv]
  have hpow : (N:ℝ)^(1+s/8) = (N:ℝ)*(N:ℝ)^(s/8) := by
    rw [Real.rpow_add' hNR.le (by linarith), Real.rpow_one]
  have hNs : 0 < (N:ℝ)^(s/8) := Real.rpow_pos_of_pos hNR _
  rw [hdiv] at h
  have h2 : energyRpow s X-sphereRieszConstNeg8 s*(N:ℝ)^2 =
      Real.pi^(s/2)*((N:ℝ)^(s/8)*(sphereArea8.real univ)^(-(s/8)))*((N:ℝ)*I)/
        Real.Gamma (s/2) := by
    rw [eq_div_iff hΓ]
    linear_combination (-1:ℝ)*h
  have hN0 : (N:ℝ) ≠ 0 := hNR.ne'
  have hNs0 : (N:ℝ)^(s/8) ≠ 0 := hNs.ne'
  unfold normalizedEnergyNeg8
  rw [hpow, h2]
  field_simp

#print axioms sphere8_dist_le_two
#print axioms real_Gamma_neg_strip
#print axioms sphereGaussianPair8_mellin_neg
#print axioms energyRpow_eq_full_neg
#print axioms sphereGaussianBackground8_ge_one_sub
#print axioms sphereGaussianBackground8_neg_integrable
#print axioms sphereGaussianFullDefect8_mellin_neg
#print axioms weighted_mellin_scale
#print axioms sphereGaussianFullDefect8_scaled
#print axioms sphereGaussianCenteredScaled8_neg_integrable
#print axioms normalizedEnergyNeg8_gaussian_mellin

end SphericalRiesz
