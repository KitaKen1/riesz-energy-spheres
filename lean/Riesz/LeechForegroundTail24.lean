import Riesz.LeechForegroundDefect24

/-! Short-range cost of a twelfth-order foreground family of one common scale.

Inside one patch the cost is the computed rational-density budget.  Two nodes of different
patches are separated by a fixed positive distance `δ`, and the short-range kernel at
separation `δ` is at most `e^{-cδ²/2} Γ(p+1) (2/(cδ²))^(p+1)`.  Hence

`Σ_{fg,fg} T ≤ M B + M² e^{-cδ²/2} Γ(p+1) (2/(cδ²))^(p+1)`,  `M = K n²⁴`.

The residual points and the full configuration are not part of this statement. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
open Boundary

/-- Bound of the short-range kernel at separation at least `δ`. -/
def separatedShortRangeBound24 (c p δ : ℝ) : ℝ :=
  Real.exp (-(c*δ^2/2))*((1/(c*δ^2/2))^(p+1)*Real.Gamma (p+1))

theorem separatedShortRangeBound24_nonneg {c p δ : ℝ} (hc : 0 < c) (hp : -1 < p)
    (hδ : 0 < δ) : 0 ≤ separatedShortRangeBound24 c p δ := by
  have hg : 0 < Real.Gamma (p+1) := Real.Gamma_pos_of_pos (by linarith)
  unfold separatedShortRangeBound24
  positivity

/-- The short-range kernel of two points at distance at least `δ`. -/
theorem shortRangeKernel24_le_of_separated {c p δ : ℝ} (hc : 0 < c) (hp : -1 < p)
    (hδ : 0 < δ) {x y : SphereD 24} (hxy : δ ≤ dist x y) :
    shortRangeKernel24 c p x y ≤ separatedShortRangeBound24 c p δ := by
  have hne : x ≠ y := by
    intro h
    rw [h, dist_self] at hxy
    linarith
  have hi : IntegrableOn (fun α : ℝ => α^p*sphereGaussianKernel24 (c*α) x y) (Ioi 1) := by
    simpa only [show 2*(p+1)/2-1=p by ring] using
      sphereGaussianPair24_scaled_tail_integrable (s := 2*(p+1)) hc (by linarith) zero_le_one hne
  unfold shortRangeKernel24 separatedShortRangeBound24
  set r := c*δ^2/2 with hr
  have hr0 : 0 < r := by positivity
  have hGval : (∫ α in Ioi (0:ℝ), α^p*Real.exp (-(r*α))) =
      (1/r)^(p+1)*Real.Gamma (p+1) := by
    simpa only [show p+1-1=p by ring] using
      Real.integral_rpow_mul_exp_neg_mul_Ioi (a := p+1) (r := r) (by linarith) hr0
  have hG : IntegrableOn (fun α : ℝ => α^p*Real.exp (-(r*α))) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [hGval]
    exact (mul_pos (Real.rpow_pos_of_pos (by positivity) _)
      (Real.Gamma_pos_of_pos (by linarith))).ne'
  calc
    _ ≤ ∫ α in Ioi (1:ℝ), Real.exp (-r)*(α^p*Real.exp (-(r*α))) := by
      apply setIntegral_mono_on hi ((hG.mono_set (Ioi_subset_Ioi zero_le_one)).const_mul _)
        measurableSet_Ioi
      intro α hα
      have hα1 : (1:ℝ) < α := hα
      have hk : sphereGaussianKernel24 (c*α) x y ≤ Real.exp (-r)*Real.exp (-(r*α)) := by
        unfold sphereGaussianKernel24
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hd2 : δ^2 ≤ dist x y^2 := pow_le_pow_left₀ hδ.le hxy 2
        have h1 : c*α*δ^2 ≤ c*α*dist x y^2 := mul_le_mul_of_nonneg_left hd2 (by positivity)
        have h2 : c*α*δ^2 = 2*r*α := by rw [hr]; ring
        have h3 : r ≤ r*α := by nlinarith
        linarith
      calc α^p*sphereGaussianKernel24 (c*α) x y ≤ α^p*(Real.exp (-r)*Real.exp (-(r*α))) :=
            mul_le_mul_of_nonneg_left hk (Real.rpow_nonneg (by linarith) _)
        _ = _ := by ring
    _ ≤ ∫ α in Ioi (0:ℝ), Real.exp (-r)*(α^p*Real.exp (-(r*α))) := by
      apply setIntegral_mono_set (hG.const_mul _)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
        exact mul_nonneg (Real.exp_pos _).le
          (mul_nonneg (Real.rpow_nonneg (le_of_lt hα) _) (Real.exp_pos _).le)
      · exact (Ioi_subset_Ioi zero_le_one).eventuallyLE
    _ = _ := by rw [integral_const_mul, hGval]

/-- Short-range cost of a separated twelfth-order foreground family. -/
theorem leechPatchFamily_shortRange_le :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ {K : ℕ} (P : Fin K → SmallLeechCubePatch24),
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius24 ≤ ρ) →
      ∀ {δ : ℝ}, 0 < δ →
      (∀ i j, i ≠ j → ∀ x ∈ smallLeechSpherePatch24 (P i),
        ∀ y ∈ smallLeechSpherePatch24 (P j), δ ≤ dist x y) →
      ∀ (a d m : ℕ), 0 < a → 0 < d → 0 < m →
      (∀ i, (P i).ε*(d:ℝ) = leechUnitDensityRadius24*(a:ℝ)) →
      ∀ (hn : 74 ≤ a*m) (p : ℝ), -1 < p →
      (∑ q, ∑ q', shortRangeKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) p
          (leechFamilyNodes24 P (a*m) hn q) (leechFamilyNodes24 P (a*m) hn q')) ≤
        (K:ℝ)*((a*m:ℕ):ℝ)^24*
          leechGaussianTailBudget24
            (leechCorrectedDensityBudgetScale24 leechUnitDensityRadius24) p+
        ((K:ℝ)*((a*m:ℕ):ℝ)^24)^2*
          separatedShortRangeBound24 (sphereGaussianDensityFactor24 ((d*m)^24)) p δ := by
  classical
  obtain ⟨ρ,hρ,hρ1,hb⟩ := equalAreaLeechTwelfth24_rational_density_budget
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro K P hv hε δ hδ hsep a d m ha hd hm hratio hn p hp
  have hc0 : 0 < sphereGaussianDensityFactor24 ((d*m)^24) :=
    sphereGaussianDensityFactor24_pos (by positivity)
  set c := sphereGaussianDensityFactor24 ((d*m)^24) with hc
  set τ := separatedShortRangeBound24 c p δ with hτ
  have hτ0 : 0 ≤ τ := separatedShortRangeBound24_nonneg hc0 hp hδ
  set B := leechGaussianTailBudget24
    (leechCorrectedDensityBudgetScale24 leechUnitDensityRadius24) p with hB
  set n : ℝ := ((a*m:ℕ):ℝ) with hndef
  have hn0 : 0 < n := by rw [hndef]; exact_mod_cast Nat.mul_pos ha hm
  have hcardNodes : (Fintype.card (Fin 24 → TwelveNodeIndex (a*m)) : ℝ) = n^24 := by
    rw [twelveCubeNode_card 24 (a*m) hn]
    exact Nat.cast_pow _ _
  -- one patch
  have hpatch : ∀ i, (∑ u, ∑ w, shortRangeKernel24 c p
      (smallLeechPatchNodes24 (P i) (a*m) hn u) (smallLeechPatchNodes24 (P i) (a*m) hn w)) ≤
      n^24*B := by
    intro i
    have h := hb (P i).g (P i).v (P i).c (hv i) (P i).c_mem (P i).ε (P i).ε_pos (hε i)
      (P i).small leechUnitDensityRadius24 p leechUnitDensityRadius24_pos hp a d m ha hd hm
      (hratio i) hn
    have h' := (div_le_iff₀ (pow_pos hn0 24)).mp h
    calc _ ≤ B*n^24 := h'
      _ = _ := mul_comm _ _
  -- two patches
  have hcross : ∀ i j, i ≠ j → ∀ u w, shortRangeKernel24 c p
      (smallLeechPatchNodes24 (P i) (a*m) hn u) (smallLeechPatchNodes24 (P j) (a*m) hn w) ≤ τ :=
    fun i j hij u w => shortRangeKernel24_le_of_separated hc0 hp hδ
      (hsep i j hij _ (smallLeechPatchNodes24_mem (P i) _ hn u) _
        (smallLeechPatchNodes24_mem (P j) _ hn w))
  have hrow : ∀ i u, (∑ j, ∑ w, shortRangeKernel24 c p
      (smallLeechPatchNodes24 (P i) (a*m) hn u) (smallLeechPatchNodes24 (P j) (a*m) hn w)) ≤
      (∑ w, shortRangeKernel24 c p (smallLeechPatchNodes24 (P i) (a*m) hn u)
        (smallLeechPatchNodes24 (P i) (a*m) hn w))+(K:ℝ)*(n^24*τ) := by
    intro i u
    have hstep : ∀ j, (∑ w, shortRangeKernel24 c p
        (smallLeechPatchNodes24 (P i) (a*m) hn u) (smallLeechPatchNodes24 (P j) (a*m) hn w)) ≤
        (if j = i then ∑ w, shortRangeKernel24 c p (smallLeechPatchNodes24 (P i) (a*m) hn u)
          (smallLeechPatchNodes24 (P i) (a*m) hn w) else 0)+n^24*τ := by
      intro j
      by_cases hji : j = i
      · subst hji
        rw [if_pos rfl]
        exact le_add_of_nonneg_right (mul_nonneg (pow_pos hn0 24).le hτ0)
      · rw [if_neg hji, zero_add]
        calc _ ≤ ∑ _w : Fin 24 → TwelveNodeIndex (a*m), τ :=
              Finset.sum_le_sum fun w _ => hcross i j (Ne.symm hji) u w
          _ = n^24*τ := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardNodes]
    calc _ ≤ ∑ j, ((if j = i then ∑ w, shortRangeKernel24 c p
            (smallLeechPatchNodes24 (P i) (a*m) hn u)
            (smallLeechPatchNodes24 (P i) (a*m) hn w) else 0)+n^24*τ) :=
          Finset.sum_le_sum fun j _ => hstep j
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ i),
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- all pairs
  have hsplit : (∑ q, ∑ q', shortRangeKernel24 c p
      (leechFamilyNodes24 P (a*m) hn q) (leechFamilyNodes24 P (a*m) hn q')) =
      ∑ i, ∑ u, ∑ j, ∑ w, shortRangeKernel24 c p
        (smallLeechPatchNodes24 (P i) (a*m) hn u) (smallLeechPatchNodes24 (P j) (a*m) hn w) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun u _ => ?_
    exact Fintype.sum_prod_type _
  rw [hsplit]
  calc _ ≤ ∑ i, ∑ u, ((∑ w, shortRangeKernel24 c p (smallLeechPatchNodes24 (P i) (a*m) hn u)
          (smallLeechPatchNodes24 (P i) (a*m) hn w))+(K:ℝ)*(n^24*τ)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun u _ => hrow i u
    _ = (∑ i, ∑ u, ∑ w, shortRangeKernel24 c p (smallLeechPatchNodes24 (P i) (a*m) hn u)
          (smallLeechPatchNodes24 (P i) (a*m) hn w))+(K:ℝ)*(n^24*((K:ℝ)*(n^24*τ))) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, hcardNodes]
    _ ≤ (∑ _i : Fin K, n^24*B)+(K:ℝ)*(n^24*((K:ℝ)*(n^24*τ))) :=
      add_le_add (Finset.sum_le_sum fun i _ => hpatch i) le_rfl
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end SphericalRiesz
