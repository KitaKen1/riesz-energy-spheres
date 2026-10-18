import Riesz.SphereRieszNegMellin8
import Riesz.HexGaussianEnds2
import Riesz.SphereNegMacroKernel8
import Riesz.HexConstruction2
import Riesz.StratifiedJointSelection
import Riesz.GaussianBlockUnion8
import Riesz.HexConstruction2
import Riesz.HexConstruction2
import Riesz.HexLattice2
/-! Negative Riesz energy and Mellin transfer on the two-dimensional sphere.

The triangular Gaussian profile gives the sharp universal bound; the construction is developed in HexNegSharp2. All formulas use surface dimension 2 and ambient dimension 3. -/

section

/-! # Negative exponents `-2 < s < 0` on `S²`: Mellin form, macroscopic end and transfer (stage S2-5)

Dimension-2 port of `SphereRieszNeg24`, for the unit sphere `S² ⊂ ℝ³` and the triangular lattice
of covolume one.  For `-2 < s < 0` the energy is the sum of `|x_i-x_j|^|s|` and the conjectured
second-order coefficient is `C_s = A^(-s/2) Re ζ_Λ(s)`, with `A = 4π` the area of `S²` and
`ζ_Λ(s) = hexEpsteinZeta (s/2)` the continued Epstein zeta function of the lattice.  The range
`-2 < s < 0` is the same in every dimension; the normalization is `N^(1+s/d) = N^(1+s/2)`.  This
module contains everything that does not depend on a particular configuration:

* the Mellin form `(E_s - I_s N²)/N^(1+s/2) = K ∫ α^(s/2-1)(F_N(α)+1) dα` with
  `K = π^(s/2) A^(-s/2)/Γ(s/2) < 0` and a nonnegative integrand;
* the subtracted macroscopic kernel `K'(x,y) = ∫_{(0,w]} α^p (e^(-cα|x-y|²)-1) dα`, its
  variance bound `c|x-y|² w^(p+2)/(p+2)` and the exchange of integrals for neutralized energies;
* the splitting of the Gaussian defect of a combined configuration into the mixed foreground
  defect and the residual defect, and the resulting bound of the macroscopic end;
* the stratified joint choice of residual points for `K'` and one Gaussian window;
* the coefficient as the Epstein value: for `u < 0` the completed theta value is the Mellin
  integral of `Θ(t) - t⁻¹` (theta weight `d/2 = 1`: `Θ(1/t) = t Θ(t)`);
* the universal bound `≤ C_s + η` for all configurations, under Gaussian contact certificates of
  the triangular lattice at all scales (`∀ β, 0 < β → ∃ f, HexGaussianContactCertificate2 β f`;
  this hypothesis is discharged in `Riesz.HexGaussianBridge2`, which is not imported here);
* the transfer theorem for attaining sequences: Gaussian windows `≤ Θ(α)+ε` at every scale and
  a small macroscopic end give `≥ C_s - η`, with no contact certificate. -/

section

/-! Negative exponents `-2 < s < 0` on the unit sphere `S²` (stage S2-5, Mellin layer).

For `-2 < s < 0` the kernel is `d^(-s) = d^|s|` and
`d^(-s) = Γ(s/2)⁻¹ ∫₀^∞ t^(s/2-1) (e^(-t d²) - 1) dt` (with `Γ(s/2) < 0`), the diagonal
included. Summing over all ordered pairs and subtracting the same Mellin integral of the
actual Gaussian background `B` gives
`E_s - I_s N² = Γ(s/2)⁻¹ ∫ t^(s/2-1) (Σ_{i,j} e^(-t|x_i-x_j|²) - N² B(t)) dt`,
`I_s = Γ(s/2)⁻¹ ∫ t^(s/2-1) (B(t) - 1) dt`, and in density scale (`t = π α N/A`, `A = 4π` the
area of `S²`)
`(E_s - I_s N²)/N^(1+s/2) = π^(s/2) A^(-s/2)/Γ(s/2) ∫ α^(s/2-1) (F_N(α) + 1) dα`
with the same centered profile `F_N` as for positive exponents and `F_N + 1 ≥ 0`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SphericalRiesz

theorem sphere2_dist_le_two (x y : (SphereD 2)) : dist x y ≤ 2 := by
  have hx : ‖(x:(AmbientD 2))‖ = 1 := norm_eq_of_mem_sphere x
  have hy : ‖(y:(AmbientD 2))‖ = 1 := norm_eq_of_mem_sphere y
  rw [Subtype.dist_eq, dist_eq_norm]
  calc ‖(x:(AmbientD 2))-(y:(AmbientD 2))‖ ≤ ‖(x:(AmbientD 2))‖+‖(y:(AmbientD 2))‖ := norm_sub_le _ _
    _ = 2 := by rw [hx, hy]; norm_num

theorem sphereGaussianPair2_mellin_neg {s : ℝ} (hs : -2 < s) (hs0 : s < 0) (x y : (SphereD 2)) :
    IntegrableOn (fun t : ℝ => t^(s/2-1)*(sphereGaussianKernel2 t x y-1)) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, t^(s/2-1)*(sphereGaussianKernel2 t x y-1)) =
      Real.Gamma (s/2)*(dist x y)^(-s) := by
  have h := gaussianPair_mellin_neg hs hs0 (dist_nonneg (x := x) (y := y))
  have he : (fun t : ℝ => t^(s/2-1)*(sphereGaussianKernel2 t x y-1)) =
      (fun t : ℝ => t^(s/2-1)*(Real.exp (-((dist x y)^2*t))-1)) := by
    funext t
    simp only [sphereGaussianKernel2, mul_comm t]
  rw [he]
  exact h

/-- For `s < 0` the diagonal terms vanish, so the ordered energy is the full double sum. -/
theorem energyRpowD_eq_full_neg2 {s : ℝ} (hs0 : s < 0) {d N : ℕ} (X : ConfigurationD d N) :
    energyRpowD s X = ∑ i : Fin N, ∑ j : Fin N, (dist (X i) (X j))^(-s) := by
  unfold energyRpowD
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), dist_self,
    Real.zero_rpow (by linarith), add_zero]

theorem sphereGaussianBackground2_ge_one_sub {t : ℝ} (ht : 0 ≤ t) :
    1-4*t ≤ sphereGaussianBackground2 t := by
  have hle : ∀ p : (SphereD 2) × (SphereD 2), (1-4*t:ℝ) ≤ sphereGaussianKernel2 t p.1 p.2 := by
    intro p
    have hd := sphere2_dist_le_two p.1 p.2
    have hd0 : 0 ≤ dist p.1 p.2 := dist_nonneg
    have h1 := Real.add_one_le_exp (-(t*(dist p.1 p.2)^2))
    have hd2 : (dist p.1 p.2)^2 ≤ 4 := by nlinarith
    have h2 : t*(dist p.1 p.2)^2 ≤ 4*t := by nlinarith [mul_le_mul_of_nonneg_left hd2 ht]
    simp only [sphereGaussianKernel2]
    linarith
  have h := integral_mono
    (integrable_const (1-4*t:ℝ) (μ := (sphereProbabilityD 2).prod (sphereProbabilityD 2)))
    (sphereGaussianKernel2_pair_integrable ht) hle
  unfold sphereGaussianBackground2
  simpa using h

theorem sphereGaussianBackground2_neg_integrable {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    IntegrableOn (fun t : ℝ => t^(s/2-1)*(sphereGaussianBackground2 t-1)) (Ioi 0) := by
  apply integrableOn_Ioi_of_rpow_min_bound (C := 4) (a := s/2) (by linarith) (by linarith)
  · intro t ht
    have ht0 : (0:ℝ) < t := ht
    exact ((Real.continuousAt_rpow_const t (s/2-1) (Or.inl ht0.ne')).continuousWithinAt).mul
      (((sphereGaussianBackground2_continuousOn.mono Ioi_subset_Ici_self) t ht).sub
        continuousWithinAt_const)
  · intro t ht
    have h1 := sphereGaussianBackground2_le_one ht.le
    have h2 := sphereGaussianBackground2_ge_one_sub ht.le
    have hw : 0 ≤ t^(s/2-1) := Real.rpow_nonneg ht.le _
    have hb : 1-sphereGaussianBackground2 t ≤ 4*min t 1 := by
      rcases le_total t 1 with h | h
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right h]
        have h0 : 0 ≤ sphereGaussianBackground2 t :=
          integral_nonneg (fun p => sphereGaussianKernel2_nonneg t p.1 p.2)
        linarith
    rw [abs_mul, abs_of_nonneg hw, abs_of_nonpos (by linarith), neg_sub]
    calc t^(s/2-1)*(1-sphereGaussianBackground2 t) ≤ t^(s/2-1)*(4*min t 1) :=
          mul_le_mul_of_nonneg_left hb hw
      _ = 4*(t^(s/2-1)*min t 1) := by ring

/-- The continuous Riesz constant for `-2 < s < 0`, by the subtracted Gaussian Mellin integral
of the actual sphere background. -/
def sphereRieszConstNeg2 (s : ℝ) : ℝ :=
  (Real.Gamma (s/2))⁻¹ * ∫ t : ℝ in Ioi 0, t^(s/2-1)*(sphereGaussianBackground2 t-1)

/-- The neutralized full Gaussian sum `Σ_{i,j} e^(-t|x_i-x_j|²) - N² B(t)`. -/
def sphereGaussianFullDefect2 {N : ℕ} (t : ℝ) (X : ConfigurationD 2 N) : ℝ :=
  (∑ i : Fin N, ∑ j : Fin N, sphereGaussianKernel2 t (X i) (X j))-(N:ℝ)^2*sphereGaussianBackground2 t

theorem sphereGaussianFullDefect2_mellin_neg {s : ℝ} (hs : -2 < s) (hs0 : s < 0) {N : ℕ}
    (X : ConfigurationD 2 N) :
    IntegrableOn (fun t : ℝ => t^(s/2-1)*sphereGaussianFullDefect2 t X) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, t^(s/2-1)*sphereGaussianFullDefect2 t X) =
      Real.Gamma (s/2)*(energyRpowD s X-sphereRieszConstNeg2 s*(N:ℝ)^2) := by
  have hΓ : Real.Gamma (s/2) ≠ 0 := (real_Gamma_neg_strip (by linarith) (by linarith)).ne
  have hpt : ∀ t : ℝ, t^(s/2-1)*sphereGaussianFullDefect2 t X =
      (∑ i : Fin N, ∑ j : Fin N, t^(s/2-1)*(sphereGaussianKernel2 t (X i) (X j)-1))-
        (N:ℝ)^2*(t^(s/2-1)*(sphereGaussianBackground2 t-1)) := by
    intro t
    unfold sphereGaussianFullDefect2
    simp only [mul_sub, Finset.sum_sub_distrib, mul_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    ring
  have hrow (i : Fin N) : IntegrableOn
      (fun t : ℝ => ∑ j : Fin N, t^(s/2-1)*(sphereGaussianKernel2 t (X i) (X j)-1)) (Ioi 0) :=
    integrable_finsetSum _ (fun j _ => (sphereGaussianPair2_mellin_neg hs hs0 (X i) (X j)).1)
  have hsum : IntegrableOn
      (fun t : ℝ => ∑ i : Fin N, ∑ j : Fin N, t^(s/2-1)*(sphereGaussianKernel2 t (X i) (X j)-1))
      (Ioi 0) := integrable_finsetSum _ (fun i _ => hrow i)
  have hbg := (sphereGaussianBackground2_neg_integrable hs hs0).const_mul ((N:ℝ)^2)
  have hfun : (fun t : ℝ => t^(s/2-1)*sphereGaussianFullDefect2 t X) =
      fun t : ℝ => (∑ i : Fin N, ∑ j : Fin N, t^(s/2-1)*(sphereGaussianKernel2 t (X i) (X j)-1))-
        (N:ℝ)^2*(t^(s/2-1)*(sphereGaussianBackground2 t-1)) := funext hpt
  rw [hfun]
  refine ⟨hsum.sub hbg, ?_⟩
  rw [integral_sub hsum hbg, integral_finsetSum _ (fun i _ => hrow i), integral_const_mul]
  have hrows : ∀ i : Fin N, (∫ t : ℝ in Ioi 0,
      ∑ j : Fin N, t^(s/2-1)*(sphereGaussianKernel2 t (X i) (X j)-1)) =
      ∑ j : Fin N, Real.Gamma (s/2)*(dist (X i) (X j))^(-s) := by
    intro i
    rw [integral_finsetSum _ (fun j _ => (sphereGaussianPair2_mellin_neg hs hs0 (X i) (X j)).1)]
    exact Finset.sum_congr rfl (fun j _ => (sphereGaussianPair2_mellin_neg hs hs0 (X i) (X j)).2)
  rw [Finset.sum_congr rfl (fun i _ => hrows i), energyRpowD_eq_full_neg2 hs0 X]
  simp only [← Finset.mul_sum]
  unfold sphereRieszConstNeg2
  field_simp

theorem sphereGaussianFullDefect2_scaled {N : ℕ} (hN : 0 < N) (α : ℝ) (X : ConfigurationD 2 N) :
    sphereGaussianFullDefect2 (sphereGaussianDensityFactor2 N*α) X =
      (N:ℝ)*(sphereGaussianCenteredScaled2 α X+1) := by
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold sphereGaussianFullDefect2 sphereGaussianCenteredScaled2
  rw [← sphereGaussianScale2_eq_factor]
  field_simp
  ring

/-- The normalized negative-exponent energy `(E_s - I_s N²)/N^(1+s/2)`. -/
def normalizedEnergyNeg2 (s : ℝ) {N : ℕ} (X : ConfigurationD 2 N) : ℝ :=
  (energyRpowD s X-sphereRieszConstNeg2 s*(N:ℝ)^2)/(N:ℝ)^(1+s/2)

theorem sphereGaussianCenteredScaled2_neg_integrable {s : ℝ} (hs : -2 < s) (hs0 : s < 0)
    {N : ℕ} (hN : 0 < N) (X : ConfigurationD 2 N) :
    IntegrableOn (fun α : ℝ => α^(s/2-1)*(sphereGaussianCenteredScaled2 α X+1)) (Ioi 0) := by
  have hNR : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have h := (weighted_mellin_scale (s := s) (sphereGaussianDensityFactor2_pos hN)
    (sphereGaussianFullDefect2_mellin_neg hs hs0 X).1).1
  refine IntegrableOn.congr_fun (Integrable.const_mul h (N:ℝ)⁻¹) (fun α _ => ?_) measurableSet_Ioi
  rw [sphereGaussianFullDefect2_scaled hN]
  field_simp

/-- Density-scale Mellin form of the normalized negative-exponent energy. -/
theorem normalizedEnergyNeg2_gaussian_mellin {s : ℝ} (hs : -2 < s) (hs0 : s < 0)
    {N : ℕ} (hN : 0 < N) (X : ConfigurationD 2 N) :
    normalizedEnergyNeg2 s X =
      (Real.pi^(s/2)*((sphereAreaD 2).real univ)^(-(s/2))/Real.Gamma (s/2))*
        (∫ α : ℝ in Ioi 0, α^(s/2-1)*(sphereGaussianCenteredScaled2 α X+1)) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hA : 0 < (sphereAreaD 2).real univ := sphereAreaD_univ_pos 2
  have hΓ : Real.Gamma (s/2) ≠ 0 := (real_Gamma_neg_strip (by linarith) (by linarith)).ne
  have hm := sphereGaussianFullDefect2_mellin_neg hs hs0 X
  have h := (weighted_mellin_scale (s := s) (sphereGaussianDensityFactor2_pos hN) hm.1).2
  rw [hm.2] at h
  have he : (fun α : ℝ => α^(s/2-1)*sphereGaussianFullDefect2 (sphereGaussianDensityFactor2 N*α) X) =
      (fun α : ℝ => (N:ℝ)*(α^(s/2-1)*(sphereGaussianCenteredScaled2 α X+1))) := by
    ext α
    rw [sphereGaussianFullDefect2_scaled hN]
    ring
  rw [he, integral_const_mul, sphereGaussianDensityFactor2_rpow hN] at h
  set I := ∫ α : ℝ in Ioi 0, α^(s/2-1)*(sphereGaussianCenteredScaled2 α X+1)
  have hdiv : ((N:ℝ)/(sphereAreaD 2).real univ)^(s/2) =
      (N:ℝ)^(s/2)*((sphereAreaD 2).real univ)^(-(s/2)) := by
    rw [Real.div_rpow hNR.le hA.le, Real.rpow_neg hA.le, div_eq_mul_inv]
  have hpow : (N:ℝ)^(1+s/2) = (N:ℝ)*(N:ℝ)^(s/2) := by
    rw [Real.rpow_add' hNR.le (by linarith), Real.rpow_one]
  have hNs : 0 < (N:ℝ)^(s/2) := Real.rpow_pos_of_pos hNR _
  rw [hdiv] at h
  have h2 : energyRpowD s X-sphereRieszConstNeg2 s*(N:ℝ)^2 =
      Real.pi^(s/2)*((N:ℝ)^(s/2)*((sphereAreaD 2).real univ)^(-(s/2)))*((N:ℝ)*I)/
        Real.Gamma (s/2) := by
    rw [eq_div_iff hΓ]
    linear_combination (-1:ℝ)*h
  have hN0 : (N:ℝ) ≠ 0 := hNR.ne'
  have hNs0 : (N:ℝ)^(s/2) ≠ 0 := hNs.ne'
  unfold normalizedEnergyNeg2
  rw [hpow, h2]
  field_simp


end SphericalRiesz
end
end

section

/-! The subtracted macroscopic kernel for negative exponents on `S²` (stage S2-5).

For `-2 < p` the kernel `K'(x,y) = ∫_{(0,w]} α^p (e^(-cα|x-y|²) - 1) dα` is finite
(`0 ≤ 1 - e^(-cα d²) ≤ cα d² ≤ 4cα` on the sphere, and `α^(p+1)` is integrable at `0`),
symmetric, nonpositive, zero on the diagonal, and `0 - K'(x,y) ≤ c |x-y|² w^(p+2)/(p+2)`.
It is jointly measurable and commutes with integration against finite measures:

`∫∫ K' dμ₁ dμ₂ = ∫_{(0,w]} α^p (∫∫ e^(-cα|x-y|²) dμ₁ dμ₂ - μ₁(S) μ₂(S)) dα`.

For a probability measure `μ` and `n` points the constants cancel, so the neutralized energy of
`K'` is the `α^p`-integral of the neutralized Gaussian energies: this is the macroscopic end
`∫_{(0,w]} α^p D(cα) dα` of the negative-exponent Mellin integral, in the form used by the
stratified selection (a cell of diameter `d` costs at most `c d² w^(p+2)/(p+2)`). -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SphericalRiesz

/-- The subtracted macroscopic Gaussian kernel on `S²`. -/
def negMacroKernel2 (c p w : ℝ) (x y : SphereD 2) : ℝ :=
  ∫ α in Ioc (0:ℝ) w, α^p*(sphereGaussianKernel2 (c*α) x y-1)

theorem sphereGaussianKernel2_scale_eq (c α : ℝ) (x y : SphereD 2) :
    sphereGaussianKernel2 (c*α) x y = Real.exp (-(c*α*(dist x y)^2)) := by
  unfold sphereGaussianKernel2
  ring_nf

theorem negMacro2_dom_integrableOn {p w : ℝ} (hp : -2 < p) (hw : 0 ≤ w) (C : ℝ) :
    IntegrableOn (fun α : ℝ => C*α^(p+1)) (Ioc 0 w) :=
  ((intervalIntegrable_iff_integrableOn_Ioc_of_le hw).mp
    (intervalIntegral.intervalIntegrable_rpow' (by linarith))).const_mul _

theorem negMacro2_dom_integral {p w : ℝ} (hp : -2 < p) (hw : 0 ≤ w) (C : ℝ) :
    (∫ α in Ioc (0:ℝ) w, C*α^(p+1)) = C*(w^(p+2)/(p+2)) := by
  rw [integral_const_mul, ← intervalIntegral.integral_of_le hw,
    integral_rpow (Or.inl (by linarith : -1 < p+1))]
  have hp2 : p+1+1 = p+2 := by ring
  rw [hp2, Real.zero_rpow (by linarith)]
  ring

/-- Pointwise bounds of the integrand: `-(c d²) α^(p+1) ≤ α^p (e^(-cα d²) - 1) ≤ 0`. -/
theorem negMacroIntegrand2_bounds {c : ℝ} (hc : 0 ≤ c) (p : ℝ) {α : ℝ} (hα : 0 < α)
    (x y : SphereD 2) :
    -((c*(dist x y)^2)*α^(p+1)) ≤ α^p*(sphereGaussianKernel2 (c*α) x y-1) ∧
      α^p*(sphereGaussianKernel2 (c*α) x y-1) ≤ 0 := by
  obtain ⟨h1, h2⟩ := negMacro_integrand_bounds hc hα (dist_nonneg (x := x) (y := y)) p
  have hpa : α^p*α = α^(p+1) := by rw [Real.rpow_add_one (ne_of_gt hα)]
  rw [sphereGaussianKernel2_scale_eq]
  refine ⟨?_, h2⟩
  calc -((c*(dist x y)^2)*α^(p+1)) = -(α^p*(c*α*(dist x y)^2)) := by rw [← hpa]; ring
    _ ≤ _ := h1

theorem negMacroIntegrand2_abs_le {c : ℝ} (hc : 0 ≤ c) (p : ℝ) {α : ℝ} (hα : 0 < α)
    (x y : SphereD 2) :
    |α^p*(sphereGaussianKernel2 (c*α) x y-1)| ≤ (4*c)*α^(p+1) := by
  obtain ⟨h1, h2⟩ := negMacroIntegrand2_bounds hc p hα x y
  have hd := sphere2_dist_le_two x y
  have hd0 : 0 ≤ dist x y := dist_nonneg
  have hd2 : (dist x y)^2 ≤ 4 := by nlinarith
  have hw : 0 ≤ α^(p+1) := Real.rpow_nonneg hα.le _
  rw [abs_of_nonpos h2]
  calc -(α^p*(sphereGaussianKernel2 (c*α) x y-1)) ≤ (c*(dist x y)^2)*α^(p+1) := by linarith
    _ ≤ (c*4)*α^(p+1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd2 hc) hw
    _ = (4*c)*α^(p+1) := by ring

theorem negMacroIntegrand2_measurable (c p : ℝ) (x y : SphereD 2) :
    Measurable (fun α : ℝ => α^p*(sphereGaussianKernel2 (c*α) x y-1)) := by
  unfold sphereGaussianKernel2
  exact (measurable_id.pow_const p).mul (by fun_prop)

theorem negMacro_integrableOn2 {c p w : ℝ} (hc : 0 ≤ c) (hp : -2 < p) (hw : 0 ≤ w)
    (x y : SphereD 2) :
    IntegrableOn (fun α : ℝ => α^p*(sphereGaussianKernel2 (c*α) x y-1)) (Ioc 0 w) := by
  refine Integrable.mono' (negMacro2_dom_integrableOn hp hw (4*c))
    (negMacroIntegrand2_measurable c p x y).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
  rw [Real.norm_eq_abs]
  exact negMacroIntegrand2_abs_le hc p hα.1 x y

@[simp]
theorem negMacroKernel2_self (c p w : ℝ) (x : SphereD 2) : negMacroKernel2 c p w x x = 0 := by
  simp [negMacroKernel2, sphereGaussianKernel2_self]

theorem negMacroKernel2_symm (c p w : ℝ) (x y : SphereD 2) :
    negMacroKernel2 c p w x y = negMacroKernel2 c p w y x := by
  unfold negMacroKernel2 sphereGaussianKernel2
  rw [dist_comm]

theorem negMacroKernel2_nonpos {c : ℝ} (hc : 0 ≤ c) (p w : ℝ) (x y : SphereD 2) :
    negMacroKernel2 c p w x y ≤ 0 := by
  unfold negMacroKernel2
  apply setIntegral_nonpos measurableSet_Ioc
  intro α hα
  exact (negMacroIntegrand2_bounds hc p hα.1 x y).2

/-- The cell variance bound: `0 - K'(x,y) ≤ c |x-y|² w^(p+2)/(p+2)`. -/
theorem negMacroKernel2_variance {c p w : ℝ} (hc : 0 ≤ c) (hp : -2 < p) (hw : 0 ≤ w)
    (x y : SphereD 2) :
    0-negMacroKernel2 c p w x y ≤ c*(dist x y)^2*(w^(p+2)/(p+2)) := by
  have hint := negMacro_integrableOn2 hc hp hw x y
  have hmono : (∫ α in Ioc (0:ℝ) w, -(α^p*(sphereGaussianKernel2 (c*α) x y-1))) ≤
      ∫ α in Ioc (0:ℝ) w, (c*(dist x y)^2)*α^(p+1) := by
    apply setIntegral_mono_on hint.neg (negMacro2_dom_integrableOn hp hw _) measurableSet_Ioc
    intro α hα
    have := (negMacroIntegrand2_bounds hc p hα.1 x y).1
    show -(α^p*(sphereGaussianKernel2 (c*α) x y-1)) ≤ (c*(dist x y)^2)*α^(p+1)
    linarith
  rw [negMacro2_dom_integral hp hw, integral_neg] at hmono
  unfold negMacroKernel2
  linarith

/-- A uniform bound of the kernel. -/
theorem negMacroKernel2_abs_le {c p w : ℝ} (hc : 0 ≤ c) (hp : -2 < p) (hw : 0 ≤ w)
    (x y : SphereD 2) :
    |negMacroKernel2 c p w x y| ≤ 4*c*(w^(p+2)/(p+2)) := by
  have h1 := negMacroKernel2_variance hc hp hw x y
  have h2 := negMacroKernel2_nonpos hc p w x y
  have hd := sphere2_dist_le_two x y
  have hd0 : 0 ≤ dist x y := dist_nonneg
  have hd2 : (dist x y)^2 ≤ 4 := by nlinarith
  have hq : 0 ≤ w^(p+2)/(p+2) := div_nonneg (Real.rpow_nonneg hw _) (by linarith)
  rw [abs_of_nonpos h2]
  calc -negMacroKernel2 c p w x y ≤ c*(dist x y)^2*(w^(p+2)/(p+2)) := by linarith
    _ ≤ c*4*(w^(p+2)/(p+2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd2 hc) hq
    _ = 4*c*(w^(p+2)/(p+2)) := by ring

theorem negMacroJoint2_measurable (c p : ℝ) :
    Measurable (fun z : (SphereD 2 × SphereD 2) × ℝ =>
      z.2^p*(sphereGaussianKernel2 (c*z.2) z.1.1 z.1.2-1)) := by
  unfold sphereGaussianKernel2
  apply Measurable.mul (measurable_snd.pow_const p)
  apply Measurable.sub _ measurable_const
  apply Real.measurable_exp.comp
  apply Measurable.neg
  apply Measurable.mul (measurable_const.mul measurable_snd)
  exact ((continuous_dist.comp (continuous_fst.comp continuous_fst |>.prodMk
    (continuous_snd.comp continuous_fst))).measurable).pow_const 2

theorem negMacroKernel2_measurable (c p w : ℝ) :
    StronglyMeasurable (fun q : SphereD 2 × SphereD 2 => negMacroKernel2 c p w q.1 q.2) :=
  (negMacroJoint2_measurable c p).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0:ℝ) w))

theorem negMacroKernel2_row_measurable (c p w : ℝ) (x : SphereD 2) :
    StronglyMeasurable (fun y : SphereD 2 => negMacroKernel2 c p w x y) := by
  have hf : StronglyMeasurable (fun z : SphereD 2 × ℝ =>
      z.2^p*(sphereGaussianKernel2 (c*z.2) x z.1-1)) := by
    apply Measurable.stronglyMeasurable
    unfold sphereGaussianKernel2
    apply Measurable.mul (measurable_snd.pow_const p)
    apply Measurable.sub _ measurable_const
    apply Real.measurable_exp.comp
    apply Measurable.neg
    apply Measurable.mul (measurable_const.mul measurable_snd)
    exact ((continuous_dist.comp (continuous_const.prodMk continuous_fst)).measurable).pow_const 2
  exact hf.integral_prod_right' (ν := volume.restrict (Ioc (0:ℝ) w))

/-- The kernel is bounded, hence integrable against every finite measure on pairs. -/
theorem negMacroKernel2_integrable {c p w : ℝ} (hc : 0 ≤ c) (hp : -2 < p) (hw : 0 ≤ w)
    (ρ : Measure (SphereD 2 × SphereD 2)) [IsFiniteMeasure ρ] :
    Integrable (fun q : SphereD 2 × SphereD 2 => negMacroKernel2 c p w q.1 q.2) ρ := by
  refine Integrable.of_bound (negMacroKernel2_measurable c p w).aestronglyMeasurable
    (4*c*(w^(p+2)/(p+2))) ?_
  refine Eventually.of_forall fun q => ?_
  rw [Real.norm_eq_abs]
  exact negMacroKernel2_abs_le hc hp hw _ _

theorem negMacroKernel2_row_integrable {c p w : ℝ} (hc : 0 ≤ c) (hp : -2 < p) (hw : 0 ≤ w)
    (x : SphereD 2) (μ : Measure (SphereD 2)) [IsFiniteMeasure μ] :
    Integrable (fun y : SphereD 2 => negMacroKernel2 c p w x y) μ := by
  refine Integrable.of_bound (negMacroKernel2_row_measurable c p w x).aestronglyMeasurable
    (4*c*(w^(p+2)/(p+2))) ?_
  refine Eventually.of_forall fun y => ?_
  rw [Real.norm_eq_abs]
  exact negMacroKernel2_abs_le hc hp hw _ _

/-- Joint integrability of the subtracted weighted Gaussian in the pair and the scale. -/
theorem negMacroJoint2_integrable {c p w : ℝ} (hc : 0 ≤ c) (hp : -2 < p) (hw : 0 ≤ w)
    (ρ : Measure (SphereD 2 × SphereD 2)) [IsFiniteMeasure ρ] :
    Integrable (fun z : (SphereD 2 × SphereD 2) × ℝ =>
      z.2^p*(sphereGaussianKernel2 (c*z.2) z.1.1 z.1.2-1))
      (ρ.prod (volume.restrict (Ioc (0:ℝ) w))) := by
  refine Integrable.mono' (Integrable.comp_snd (negMacro2_dom_integrableOn hp hw (4*c)) ρ)
    (negMacroJoint2_measurable c p).aestronglyMeasurable ?_
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)]
    with z hz
  rw [Real.norm_eq_abs]
  exact negMacroIntegrand2_abs_le hc p hz.1 _ _

theorem negMacro2_pair_integral_eq {c : ℝ} (hc : 0 ≤ c) (p : ℝ) (μ₁ μ₂ : Measure (SphereD 2))
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] {α : ℝ} (hα : 0 ≤ α) :
    (∫ q : SphereD 2 × SphereD 2, α^p*(sphereGaussianKernel2 (c*α) q.1 q.2-1) ∂μ₁.prod μ₂) =
      α^p*((∫ x, ∫ y, sphereGaussianKernel2 (c*α) x y ∂μ₂ ∂μ₁)-μ₁.real univ*μ₂.real univ) := by
  have hG := sphereGaussianKernel2_integrable_finite (mul_nonneg hc hα) (μ₁.prod μ₂)
  have hsub : Integrable (fun q : SphereD 2 × SphereD 2 =>
      sphereGaussianKernel2 (c*α) q.1 q.2-1) (μ₁.prod μ₂) := hG.sub (integrable_const 1)
  have hL : Integrable (fun x => ∫ y, sphereGaussianKernel2 (c*α) x y ∂μ₂) μ₁ :=
    hG.integral_prod_left
  have hrow : ∀ x, (∫ y, (sphereGaussianKernel2 (c*α) x y-1) ∂μ₂) =
      (∫ y, sphereGaussianKernel2 (c*α) x y ∂μ₂)-μ₂.real univ := by
    intro x
    rw [integral_sub (sphereGaussianKernel2_row_integrable_finite (mul_nonneg hc hα) x μ₂)
      (integrable_const 1), integral_const, smul_eq_mul, mul_one]
  rw [integral_const_mul, integral_prod _ hsub]
  congr 1
  calc (∫ x, ∫ y, (sphereGaussianKernel2 (c*α) x y-1) ∂μ₂ ∂μ₁)
      = ∫ x, ((∫ y, sphereGaussianKernel2 (c*α) x y ∂μ₂)-μ₂.real univ) ∂μ₁ :=
        integral_congr_ae (Filter.Eventually.of_forall hrow)
    _ = _ := by
        rw [integral_sub hL (integrable_const _), integral_const, smul_eq_mul]

/-- The subtracted scale integral commutes with integration against two finite measures. -/
theorem negMacroKernel2_integral_swap {c p w : ℝ} (hc : 0 ≤ c) (hp : -2 < p) (hw : 0 ≤ w)
    (μ₁ μ₂ : Measure (SphereD 2)) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] :
    ∫ x, ∫ y, negMacroKernel2 c p w x y ∂μ₂ ∂μ₁ =
      ∫ α in Ioc (0:ℝ) w, α^p*((∫ x, ∫ y, sphereGaussianKernel2 (c*α) x y ∂μ₂ ∂μ₁)-
        μ₁.real univ*μ₂.real univ) := by
  have hκ := negMacroKernel2_integrable hc hp hw (μ₁.prod μ₂)
  rw [← integral_prod _ hκ]
  have hswap := integral_integral_swap
    (f := fun (q : SphereD 2 × SphereD 2) (α : ℝ) =>
      α^p*(sphereGaussianKernel2 (c*α) q.1 q.2-1))
    (negMacroJoint2_integrable hc hp hw (μ₁.prod μ₂))
  calc (∫ q : SphereD 2 × SphereD 2, negMacroKernel2 c p w q.1 q.2 ∂μ₁.prod μ₂)
      = ∫ α in Ioc (0:ℝ) w, ∫ q : SphereD 2 × SphereD 2,
          α^p*(sphereGaussianKernel2 (c*α) q.1 q.2-1) ∂μ₁.prod μ₂ := hswap
    _ = _ := setIntegral_congr_fun measurableSet_Ioc fun α hα =>
      negMacro2_pair_integral_eq hc p μ₁ μ₂ hα.1.le

/-- Integrability in the scale of the subtracted pair integral against two finite measures. -/
theorem negMacroScale2_integrableOn {c p w : ℝ} (hc : 0 ≤ c) (hp : -2 < p) (hw : 0 ≤ w)
    (μ₁ μ₂ : Measure (SphereD 2)) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] :
    IntegrableOn (fun α : ℝ => α^p*((∫ x, ∫ y, sphereGaussianKernel2 (c*α) x y ∂μ₂ ∂μ₁)-
      μ₁.real univ*μ₂.real univ)) (Ioc 0 w) := by
  have h := (negMacroJoint2_integrable hc hp hw (μ₁.prod μ₂)).integral_prod_right
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
  exact negMacro2_pair_integral_eq hc p μ₁ μ₂ hα.1.le

theorem negMacroKernel2_row_integral {c p w : ℝ} (hc : 0 ≤ c) (hp : -2 < p) (hw : 0 ≤ w)
    (x : SphereD 2) (μ : Measure (SphereD 2)) [IsProbabilityMeasure μ] :
    ∫ y, negMacroKernel2 c p w x y ∂μ =
      ∫ α in Ioc (0:ℝ) w, α^p*((∫ y, sphereGaussianKernel2 (c*α) x y ∂μ)-1) := by
  have h := negMacroKernel2_integral_swap hc hp hw (Measure.dirac x) μ
  simpa only [integral_dirac, probReal_univ, mul_one] using h

theorem negMacroScale2_row_integrableOn {c p w : ℝ} (hc : 0 ≤ c) (hp : -2 < p) (hw : 0 ≤ w)
    (x : SphereD 2) (μ : Measure (SphereD 2)) [IsProbabilityMeasure μ] :
    IntegrableOn (fun α : ℝ => α^p*((∫ y, sphereGaussianKernel2 (c*α) x y ∂μ)-1))
      (Ioc 0 w) := by
  have h := negMacroScale2_integrableOn hc hp hw (Measure.dirac x) μ
  simpa only [integral_dirac, probReal_univ, mul_one] using h

/-- For a probability measure and `n` points the neutralized energy of the subtracted
macroscopic kernel is the `α^p`-integral of the neutralized Gaussian energies. -/
theorem negMacro2_residualNeutralizedEnergy_eq {c p w : ℝ} (hc : 0 ≤ c) (hp : -2 < p)
    (hw : 0 ≤ w) (μ : Measure (SphereD 2)) [IsProbabilityMeasure μ] {n : ℕ}
    (z : Fin n → SphereD 2) :
    IntegrableOn (fun α : ℝ => α^p*residualNeutralizedEnergy μ
      (sphereGaussianKernel2 (c*α)) (fun _ => 0) z) (Ioc 0 w) ∧
    residualNeutralizedEnergy μ (negMacroKernel2 c p w) (fun _ => 0) z =
      ∫ α in Ioc (0:ℝ) w, α^p*residualNeutralizedEnergy μ
        (sphereGaussianKernel2 (c*α)) (fun _ => 0) z := by
  -- the three subtracted pieces
  have hpair : ∀ i j, IntegrableOn
      (fun α : ℝ => α^p*(sphereGaussianKernel2 (c*α) (z i) (z j)-1)) (Ioc 0 w) :=
    fun i j => negMacro_integrableOn2 hc hp hw (z i) (z j)
  have hrow : ∀ i, IntegrableOn
      (fun α : ℝ => α^p*((∫ y, sphereGaussianKernel2 (c*α) (z i) y ∂μ)-1)) (Ioc 0 w) :=
    fun i => negMacroScale2_row_integrableOn hc hp hw (z i) μ
  have hbg : IntegrableOn (fun α : ℝ =>
      α^p*((∫ x, ∫ y, sphereGaussianKernel2 (c*α) x y ∂μ ∂μ)-1)) (Ioc 0 w) := by
    have h := negMacroScale2_integrableOn hc hp hw μ μ
    simpa only [probReal_univ, mul_one] using h
  have hP : IntegrableOn (fun α : ℝ =>
      ∑ i, ∑ j, α^p*(sphereGaussianKernel2 (c*α) (z i) (z j)-1)) (Ioc 0 w) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hpair i j
  have hR : IntegrableOn (fun α : ℝ =>
      ∑ i, α^p*((∫ y, sphereGaussianKernel2 (c*α) (z i) y ∂μ)-1)) (Ioc 0 w) :=
    integrable_finsetSum _ fun i _ => hrow i
  -- pointwise: the constants cancel
  have hpt : ∀ α : ℝ, α^p*residualNeutralizedEnergy μ
      (sphereGaussianKernel2 (c*α)) (fun _ => 0) z =
      (∑ i, ∑ j, α^p*(sphereGaussianKernel2 (c*α) (z i) (z j)-1))-
        2*(n:ℝ)*(∑ i, α^p*((∫ y, sphereGaussianKernel2 (c*α) (z i) y ∂μ)-1))+
        (n:ℝ)^2*(α^p*((∫ x, ∫ y, sphereGaussianKernel2 (c*α) x y ∂μ ∂μ)-1)) := by
    intro α
    have e0 : ∀ i : Fin n, (∑ j, α^p*(sphereGaussianKernel2 (c*α) (z i) (z j)-1)) =
        α^p*(∑ j, sphereGaussianKernel2 (c*α) (z i) (z j))-(n:ℝ)*α^p := by
      intro i
      rw [Finset.sum_congr rfl (fun j _ => (by ring :
        α^p*(sphereGaussianKernel2 (c*α) (z i) (z j)-1) =
          α^p*sphereGaussianKernel2 (c*α) (z i) (z j)-α^p)),
        Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    have e1 : (∑ i, ∑ j, α^p*(sphereGaussianKernel2 (c*α) (z i) (z j)-1)) =
        α^p*(∑ i, ∑ j, sphereGaussianKernel2 (c*α) (z i) (z j))-(n:ℝ)*((n:ℝ)*α^p) := by
      rw [Finset.sum_congr rfl (fun i _ => e0 i), Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have e2 : (∑ i, α^p*((∫ y, sphereGaussianKernel2 (c*α) (z i) y ∂μ)-1)) =
        α^p*(∑ i, ∫ y, sphereGaussianKernel2 (c*α) (z i) y ∂μ)-(n:ℝ)*α^p := by
      rw [Finset.sum_congr rfl (fun i _ => (by ring :
        α^p*((∫ y, sphereGaussianKernel2 (c*α) (z i) y ∂μ)-1) =
          α^p*(∫ y, sphereGaussianKernel2 (c*α) (z i) y ∂μ)-α^p)),
        Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    rw [e1, e2]
    unfold residualNeutralizedEnergy residualPairEnergy residualBackground residualRowPotential
    simp only [Finset.sum_const_zero, integral_zero, mul_zero, add_zero, sub_zero]
    ring
  have hfun : (fun α : ℝ => α^p*residualNeutralizedEnergy μ
      (sphereGaussianKernel2 (c*α)) (fun _ => 0) z) = fun α : ℝ =>
      (∑ i, ∑ j, α^p*(sphereGaussianKernel2 (c*α) (z i) (z j)-1))-
        2*(n:ℝ)*(∑ i, α^p*((∫ y, sphereGaussianKernel2 (c*α) (z i) y ∂μ)-1))+
        (n:ℝ)^2*(α^p*((∫ x, ∫ y, sphereGaussianKernel2 (c*α) x y ∂μ ∂μ)-1)) := funext hpt
  have h1 : IntegrableOn (fun α : ℝ =>
      (∑ i, ∑ j, α^p*(sphereGaussianKernel2 (c*α) (z i) (z j)-1))-
        2*(n:ℝ)*(∑ i, α^p*((∫ y, sphereGaussianKernel2 (c*α) (z i) y ∂μ)-1))) (Ioc 0 w) :=
    hP.sub (hR.const_mul _)
  rw [hfun]
  refine ⟨h1.add (hbg.const_mul _), ?_⟩
  rw [integral_add h1 (hbg.const_mul _), integral_sub hP (hR.const_mul _), integral_const_mul,
    integral_const_mul, integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hpair i j),
    integral_finsetSum _ (fun i _ => hrow i)]
  have hsw := negMacroKernel2_integral_swap hc hp hw μ μ
  simp only [probReal_univ, mul_one] at hsw
  have hA : (∑ i, ∑ j, negMacroKernel2 c p w (z i) (z j)) =
      ∑ i, ∫ α in Ioc (0:ℝ) w, ∑ j, α^p*(sphereGaussianKernel2 (c*α) (z i) (z j)-1) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => hpair i j)]
    rfl
  have hB : (∑ i, ∫ y, negMacroKernel2 c p w (z i) y ∂μ) =
      ∑ i, ∫ α in Ioc (0:ℝ) w, α^p*((∫ y, sphereGaussianKernel2 (c*α) (z i) y ∂μ)-1) :=
    Finset.sum_congr rfl fun i _ => negMacroKernel2_row_integral hc hp hw (z i) μ
  unfold residualNeutralizedEnergy residualPairEnergy residualBackground residualRowPotential
  simp only [Finset.sum_const_zero, integral_zero, mul_zero, add_zero, sub_zero]
  rw [hsw, hA, hB]

end SphericalRiesz
end
end

section

/-! The macroscopic end of a combined configuration on `S²` (stage S2-5).

A configuration made of foreground points `x` (in a measurable region `P`) and residual points
`z` splits, in characteristic functions, as
`(μ_x + N σ|_{Pᶜ} - N σ) + (μ_z - N σ|_{Pᶜ})`, so by `|u+v|² ≤ 2|u|² + 2|v|²`

`D_Z(t) ≤ 2 D_mix(t) + 2 D_res(t)`,

where `D_mix` is the neutralized Gaussian defect of the mixed measure (foreground points plus
`N σ` on `Pᶜ`) and `D_res` the defect of the residual points against `N σ|_{Pᶜ}`.  With exact
residual mass `n = N σ(Pᶜ)` the residual defect is the neutralized energy of the Gaussian kernel
for the normalized restriction of `σ` to `Pᶜ`, and its `α^p`-integral over `(0,1]` is the
neutralized energy of the subtracted macroscopic kernel.  Hence, for `-2 < s < 0`, `p = s/2-1`
and every cutoff `0 < w ≤ 1`,

`∫_{(0,w]} α^p (F_Z(α)+1) dα ≤ 2 ∫_{(0,w]} α^p g(α) dα + (2/N) NE(K'_1; z)`

as soon as `D_mix(c_N α) ≤ N g(α)` on `(0,w]`.  The first term is small for small `w` (order
fourteen foreground), the second one is controlled by the stratified selection of `z`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ComplexConjugate ENNReal NNReal
namespace SphericalRiesz

/-- The ambient image of the sphere probability restricted to `S`. -/
def ambientRestricted2 (S : Set (SphereD 2)) : Measure (AmbientD 2) :=
  ((sphereProbabilityD 2).restrict S).map (fun x : SphereD 2 => (x : AmbientD 2))

instance ambientRestricted2_finite (S : Set (SphereD 2)) :
    IsFiniteMeasure (ambientRestricted2 S) := by
  unfold ambientRestricted2
  infer_instance

theorem ambientRestricted2_split {S : Set (SphereD 2)} (hS : MeasurableSet S) :
    ambientSphereProbability2 = ambientRestricted2 S+ambientRestricted2 Sᶜ := by
  unfold ambientSphereProbability2 ambientRestricted2
  rw [← Measure.map_add _ _ (by fun_prop), Measure.restrict_add_restrict_compl hS]

theorem ambientRestricted2_kernel_integral (t : ℝ) (S : Set (SphereD 2)) (x : SphereD 2) :
    (∫ y, gaussianKernel t (x : AmbientD 2) y ∂ambientRestricted2 S) =
      ∫ y in S, sphereGaussianKernel2 t x y ∂(sphereProbabilityD 2) := by
  rw [ambientRestricted2, integral_map (by fun_prop) (by unfold gaussianKernel; fun_prop)]
  simp only [sphereGaussianKernel2_eq_ambient]

theorem ambientRestricted2_kernel_pair {t : ℝ} (ht : 0 ≤ t) (S : Set (SphereD 2)) :
    gaussianMeasurePair t (ambientRestricted2 S) (ambientRestricted2 S) =
      ∫ x in S, ∫ y in S, sphereGaussianKernel2 t x y ∂(sphereProbabilityD 2)
        ∂(sphereProbabilityD 2) := by
  have h1 : (∫ w, (∫ y, gaussianKernel t w y ∂ambientRestricted2 S) ∂ambientRestricted2 S) =
      ∫ x in S, (∫ y, gaussianKernel t (x : AmbientD 2) y ∂ambientRestricted2 S)
        ∂(sphereProbabilityD 2) :=
    integral_map (μ := (sphereProbabilityD 2).restrict S)
      (φ := fun x : SphereD 2 => (x : AmbientD 2)) (by fun_prop)
      (gaussianKernel_potential_measurableS2 t (ambientRestricted2 S)).aestronglyMeasurable
  rw [gaussianMeasurePair_iterated ht, h1]
  simp only [ambientRestricted2_kernel_integral]

/-- Kernel form of the neutralized Gaussian defect of finitely many sphere points against
`M σ|_S`. -/
theorem restrictedDefect2_eq_kernel {κ : Type*} [Fintype κ] {t : ℝ} (ht : 0 ≤ t)
    (z : κ → SphereD 2) (S : Set (SphereD 2)) (M : ℝ) :
    gaussianMeasureDefect t M (finitePointMeasure (fun j => (z j : AmbientD 2)))
        (ambientRestricted2 S) =
      (∑ j, ∑ l, sphereGaussianKernel2 t (z j) (z l))-
        2*M*(∑ j, ∫ y in S, sphereGaussianKernel2 t (z j) y ∂(sphereProbabilityD 2))+
        M^2*(∫ x in S, ∫ y in S, sphereGaussianKernel2 t x y ∂(sphereProbabilityD 2)
          ∂(sphereProbabilityD 2)) := by
  rw [← diffuseGaussianDefect_eq_measureDefect ht]
  unfold diffuseGaussianDefect
  simp only [← sphereGaussianKernel2_eq_ambient, ambientRestricted2_kernel_integral,
    ambientRestricted2_kernel_pair ht]

/-- With exact residual mass the neutralized Gaussian energy for the normalized restriction is
the ambient defect against `N σ|_R`. -/
theorem residualGaussianEnergy2_eq_defect {n N : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (z : Fin n → SphereD 2) (R : Set (SphereD 2)) (hR : (sphereProbabilityD 2) R ≠ 0)
    (hmass : (n:ℝ) = (N:ℝ)*(sphereProbabilityD 2).real R) :
    residualNeutralizedEnergy (sphereRestrictedProbability2 R) (sphereGaussianKernel2 t)
        (fun _ => 0) z =
      gaussianMeasureDefect t (N:ℝ) (finitePointMeasure (fun j => (z j : AmbientD 2)))
        (ambientRestricted2 R) := by
  rw [restrictedDefect2_eq_kernel ht]
  have hr : (sphereProbabilityD 2).real R ≠ 0 :=
    (ENNReal.toReal_pos hR (measure_ne_top _ _)).ne'
  have hint : ∀ f : SphereD 2 → ℝ, (∫ y, f y ∂sphereRestrictedProbability2 R) =
      ((sphereProbabilityD 2).real R)⁻¹*∫ y in R, f y ∂(sphereProbabilityD 2) := by
    intro f
    simp only [sphereRestrictedProbability2]
    rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv]
    rfl
  unfold residualNeutralizedEnergy residualPairEnergy residualBackground residualRowPotential
  simp only [Finset.sum_const_zero, integral_zero, mul_zero, add_zero, sub_zero, hint]
  have e1 : (∑ j, ((sphereProbabilityD 2).real R)⁻¹*
      ∫ y in R, sphereGaussianKernel2 t (z j) y ∂(sphereProbabilityD 2)) =
      ((sphereProbabilityD 2).real R)⁻¹*
        ∑ j, ∫ y in R, sphereGaussianKernel2 t (z j) y ∂(sphereProbabilityD 2) :=
    (Finset.mul_sum _ _ _).symm
  have e2 : (∫ x in R, ((sphereProbabilityD 2).real R)⁻¹*
      ∫ y in R, sphereGaussianKernel2 t x y ∂(sphereProbabilityD 2) ∂(sphereProbabilityD 2)) =
      ((sphereProbabilityD 2).real R)⁻¹*
        ∫ x in R, ∫ y in R, sphereGaussianKernel2 t x y ∂(sphereProbabilityD 2)
          ∂(sphereProbabilityD 2) := integral_const_mul _ _
  rw [e1, e2, hmass]
  field_simp

theorem charFun_nnreal_smul2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] (c : ℝ≥0) (ν : Measure E) (w : E) :
    charFun (c • ν) w = ((c:ℝ):ℂ)*charFun ν w := by
  rw [charFun_apply, charFun_apply, integral_smul_nnreal_measure, NNReal.smul_def,
    Complex.real_smul]

/-- The mixed defect is the defect of the foreground points against `N σ|_P`. -/
theorem mixedForeground2_defect_eq_restricted {ι : Type*} [Fintype ι] (x : ι → SphereD 2)
    (N : ℕ) {P : Set (SphereD 2)} (hP : MeasurableSet P) {t : ℝ} (ht : 0 ≤ t) :
    gaussianMeasureDefect t (N:ℝ) (mixedForegroundMeasure2 x N Pᶜ) ambientSphereProbability2 =
      gaussianMeasureDefect t (N:ℝ) (finitePointMeasure (fun i => (x i : AmbientD 2)))
        (ambientRestricted2 P) := by
  rw [gaussianMeasureDefect_eq_normSq ht, gaussianMeasureDefect_eq_normSq ht]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  dsimp only
  have hmix : mixedForegroundMeasure2 x N Pᶜ =
      finitePointMeasure (fun i => (x i : AmbientD 2))+(N:ℝ≥0) • ambientRestricted2 Pᶜ := rfl
  have hsplit := ambientRestricted2_split hP
  have he : charFun (mixedForegroundMeasure2 x N Pᶜ) (Real.sqrt (2*t) • w)-
      ((N:ℝ):ℂ)*charFun ambientSphereProbability2 (Real.sqrt (2*t) • w) =
      charFun (finitePointMeasure (fun i => (x i : AmbientD 2))) (Real.sqrt (2*t) • w)-
        ((N:ℝ):ℂ)*charFun (ambientRestricted2 P) (Real.sqrt (2*t) • w) := by
    rw [hmix, hsplit, charFun_add_measure, charFun_add_measure, charFun_nnreal_smul2]
    push_cast
    ring
  rw [he]

/-- Cauchy–Schwarz for a foreground in `P` and a residual part: the defect of the union is at
most twice the mixed defect plus twice the residual defect. -/
theorem gaussianDefect2_union_le {ι κ : Type*} [Fintype ι] [Fintype κ] {t : ℝ} (ht : 0 ≤ t)
    (x : ι → SphereD 2) (z : κ → SphereD 2) {P : Set (SphereD 2)} (hP : MeasurableSet P)
    (N : ℕ) :
    gaussianMeasureDefect t (N:ℝ)
        (finitePointMeasure (fun a : ι ⊕ κ => ((Sum.elim x z a : SphereD 2) : AmbientD 2)))
        ambientSphereProbability2 ≤
      2*gaussianMeasureDefect t (N:ℝ) (mixedForegroundMeasure2 x N Pᶜ)
          ambientSphereProbability2+
        2*gaussianMeasureDefect t (N:ℝ) (finitePointMeasure (fun j => (z j : AmbientD 2)))
          (ambientRestricted2 Pᶜ) := by
  have hfun : (fun a : ι ⊕ κ => ((Sum.elim x z a : SphereD 2) : AmbientD 2)) =
      Sum.elim (fun i => (x i : AmbientD 2)) (fun j => (z j : AmbientD 2)) := by
    funext a
    cases a <;> rfl
  rw [hfun, finitePointMeasure_sum_elim, mixedForeground2_defect_eq_restricted x N hP ht,
    ambientRestricted2_split hP]
  exact gaussianMeasureDefect_add_le ht (N:ℝ) _ _ _ _

/-- The same inequality for a combined configuration. -/
theorem combinedConfiguration2_defect_le {ι : Type*} [Fintype ι] {n N : ℕ}
    (x : ι → SphereD 2) (z : Fin n → SphereD 2) (hcard : Fintype.card ι+n = N)
    (hx : Function.Injective x) (hz : Function.Injective z) (havoid : ∀ j, z j ∉ range x)
    {P : Set (SphereD 2)} (hP : MeasurableSet P) {t : ℝ} (ht : 0 ≤ t) :
    sphereGaussianDefect2 t (N:ℝ) (combinedConfiguration2 x z hcard hx hz havoid) ≤
      2*gaussianMeasureDefect t (N:ℝ) (mixedForegroundMeasure2 x N Pᶜ)
          ambientSphereProbability2+
        2*gaussianMeasureDefect t (N:ℝ) (finitePointMeasure (fun j => (z j : AmbientD 2)))
          (ambientRestricted2 Pᶜ) := by
  rw [sphereGaussianDefect2_eq_diffuse ht, diffuseGaussianDefect_eq_measureDefect ht]
  have hfpm : finitePointMeasure (fun i : Fin N =>
      ((combinedConfiguration2 x z hcard hx hz havoid i : SphereD 2) : AmbientD 2)) =
      finitePointMeasure (fun a : ι ⊕ Fin n => ((Sum.elim x z a : SphereD 2) : AmbientD 2)) := by
    unfold finitePointMeasure
    exact Equiv.sum_comp ((Fintype.equivFinOfCardEq
      (show Fintype.card (ι ⊕ Fin n) = N by
        rw [Fintype.card_sum, Fintype.card_fin, hcard])).symm)
      (fun a => Measure.dirac ((Sum.elim x z a : SphereD 2) : AmbientD 2))
  rw [hfpm]
  exact gaussianDefect2_union_le ht x z hP N

/-- The macroscopic end of a combined configuration: foreground bound plus the neutralized
energy of the subtracted macroscopic kernel of the residual points. -/
theorem combinedConfiguration2_macroEnd_le {s : ℝ} (hs : -2 < s) (hs0 : s < 0)
    {ι : Type*} [Fintype ι] {n N : ℕ} (hN : 0 < N)
    (x : ι → SphereD 2) (z : Fin n → SphereD 2) (hcard : Fintype.card ι+n = N)
    (hx : Function.Injective x) (hz : Function.Injective z) (havoid : ∀ j, z j ∉ range x)
    {P : Set (SphereD 2)} (hP : MeasurableSet P) (hR : (sphereProbabilityD 2) Pᶜ ≠ 0)
    (hmass : (n:ℝ) = (N:ℝ)*(sphereProbabilityD 2).real Pᶜ)
    {w : ℝ} (hw1 : w ≤ 1) (g : ℝ → ℝ)
    (hg : IntegrableOn (fun α : ℝ => α^(s/2-1)*g α) (Ioc 0 w))
    (hfg : ∀ α ∈ Ioc (0:ℝ) w,
      gaussianMeasureDefect (sphereGaussianScale2 N α) (N:ℝ) (mixedForegroundMeasure2 x N Pᶜ)
        ambientSphereProbability2 ≤ (N:ℝ)*g α) :
    (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled2 α
        (combinedConfiguration2 x z hcard hx hz havoid)+1)) ≤
      2*(∫ α in Ioc (0:ℝ) w, α^(s/2-1)*g α)+
        2/(N:ℝ)*residualNeutralizedEnergy (sphereRestrictedProbability2 Pᶜ)
          (negMacroKernel2 (sphereGaussianDensityFactor2 N) (s/2-1) 1) (fun _ => 0) z := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hc : 0 < sphereGaussianDensityFactor2 N := sphereGaussianDensityFactor2_pos hN
  have hp : -2 < s/2-1 := by linarith
  have : IsProbabilityMeasure (sphereRestrictedProbability2 Pᶜ) :=
    sphereRestrictedProbability2_probability _ hR
  obtain ⟨hNEint, hNEeq⟩ := negMacro2_residualNeutralizedEnergy_eq hc.le hp zero_le_one
    (sphereRestrictedProbability2 Pᶜ) z
  set E : ℝ → ℝ := fun α => residualNeutralizedEnergy (sphereRestrictedProbability2 Pᶜ)
    (sphereGaussianKernel2 (sphereGaussianDensityFactor2 N*α)) (fun _ => 0) z with hE
  have hE0 : ∀ α : ℝ, 0 < α → 0 ≤ E α := by
    intro α hα
    have ht : 0 ≤ sphereGaussianDensityFactor2 N*α := mul_nonneg hc.le hα.le
    simp only [hE]
    rw [residualGaussianEnergy2_eq_defect ht z Pᶜ hR hmass]
    exact gaussianMeasureDefect_nonneg ht _ _ _
  have hpt : ∀ α ∈ Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled2 α
      (combinedConfiguration2 x z hcard hx hz havoid)+1) ≤
      2*(α^(s/2-1)*g α)+2/(N:ℝ)*(α^(s/2-1)*E α) := by
    intro α hα
    have hα0 : 0 < α := hα.1
    have ht : 0 ≤ sphereGaussianDensityFactor2 N*α := mul_nonneg hc.le hα0.le
    have hwα : 0 ≤ α^(s/2-1) := Real.rpow_nonneg hα0.le _
    have hF := sphereGaussianCenteredScaled2_add_one hN hα0.le
      (combinedConfiguration2 x z hcard hx hz havoid)
    have hD := combinedConfiguration2_defect_le x z hcard hx hz havoid hP ht
    have hres := residualGaussianEnergy2_eq_defect ht z Pᶜ hR hmass
    have hmix := hfg α hα
    rw [sphereGaussianScale2_eq_factor] at hF hmix
    rw [← hres] at hD
    have hbound : sphereGaussianCenteredScaled2 α
        (combinedConfiguration2 x z hcard hx hz havoid)+1 ≤ 2*g α+2/(N:ℝ)*E α := by
      rw [hF, div_le_iff₀ hNR]
      have he : (2*g α+2/(N:ℝ)*E α)*(N:ℝ) = 2*((N:ℝ)*g α)+2*E α := by
        calc (2*g α+2/(N:ℝ)*E α)*(N:ℝ) = 2*((N:ℝ)*g α)+2*E α*((N:ℝ)/(N:ℝ)) := by ring
          _ = _ := by rw [div_self hNR.ne', mul_one]
      rw [he]
      simp only [hE]
      linarith
    calc α^(s/2-1)*(sphereGaussianCenteredScaled2 α
          (combinedConfiguration2 x z hcard hx hz havoid)+1)
        ≤ α^(s/2-1)*(2*g α+2/(N:ℝ)*E α) := mul_le_mul_of_nonneg_left hbound hwα
      _ = _ := by ring
  have hFint : IntegrableOn (fun α : ℝ => α^(s/2-1)*(sphereGaussianCenteredScaled2 α
      (combinedConfiguration2 x z hcard hx hz havoid)+1)) (Ioc 0 w) :=
    (sphereGaussianCenteredScaled2_neg_integrable hs hs0 hN _).mono_set Ioc_subset_Ioi_self
  have hEint1 : IntegrableOn (fun α : ℝ => α^(s/2-1)*E α) (Ioc 0 1) := hNEint
  have hEint : IntegrableOn (fun α : ℝ => α^(s/2-1)*E α) (Ioc 0 w) :=
    hEint1.mono_set (Ioc_subset_Ioc_right hw1)
  have hmono : (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*E α) ≤ ∫ α in Ioc (0:ℝ) 1, α^(s/2-1)*E α := by
    apply setIntegral_mono_set hEint1
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with α hα
      exact mul_nonneg (Real.rpow_nonneg hα.1.le _) (hE0 α hα.1)
    · exact (Ioc_subset_Ioc_right hw1).eventuallyLE
  calc (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled2 α
        (combinedConfiguration2 x z hcard hx hz havoid)+1))
      ≤ ∫ α in Ioc (0:ℝ) w, (2*(α^(s/2-1)*g α)+2/(N:ℝ)*(α^(s/2-1)*E α)) :=
        setIntegral_mono_on hFint ((hg.const_mul 2).add (hEint.const_mul _)) measurableSet_Ioc hpt
    _ = 2*(∫ α in Ioc (0:ℝ) w, α^(s/2-1)*g α)+
          2/(N:ℝ)*(∫ α in Ioc (0:ℝ) w, α^(s/2-1)*E α) := by
        rw [integral_add (hg.const_mul 2) (hEint.const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ 2*(∫ α in Ioc (0:ℝ) w, α^(s/2-1)*g α)+
          2/(N:ℝ)*(∫ α in Ioc (0:ℝ) 1, α^(s/2-1)*E α) := by
        have h2N : 0 ≤ 2/(N:ℝ) := by positivity
        linarith [mul_le_mul_of_nonneg_left hmono h2N]
    _ = _ := by
        simp only [hE]
        rw [hNEeq]

end SphericalRiesz
end
end

section

/-! Stratified joint residual selection for negative exponents on `S²` (stage S2-5).

On a residual region cut into `n` cells of probability exactly `1/N` and diameters `d_j`, one
point per cell can be chosen so that the neutralized energy of the subtracted macroscopic kernel
`K'` (cutoff `1`, any density factor `c ≥ 0`) plus `w₃` times the centered residual Gaussian
window is at most `n w₃ + c/(p+2) Σ_j d_j²`: the Gaussian window has diagonal `1`, and `K'` has
zero diagonal and cell variance at most `c d_j²/(p+2)`.  The neutralized energy of `K'` is
nonnegative (it is the `α^p`-integral of Gaussian defects with exact mass), so both parts are
controlled by one choice.  The density factor is free because the same selection is used for a
residual region at the density of the configuration (`c = c_N`, cells of mass `1/N`) and for
points added on the whole sphere at their own scale (`c = c_N`, cells of mass `1/r`).  No
foreground estimate and no configuration is asserted here. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SphericalRiesz

/-- With exact residual mass the neutralized energy of the subtracted macroscopic kernel is
nonnegative. -/
theorem negMacro2_residualNeutralizedEnergy_nonneg {n N : ℕ} {c p w : ℝ} (hc : 0 ≤ c)
    (hp : -2 < p) (hw : 0 ≤ w) (z : Fin n → SphereD 2) (R : Set (SphereD 2))
    (hR : (sphereProbabilityD 2) R ≠ 0)
    (hmass : (n:ℝ) = (N:ℝ)*(sphereProbabilityD 2).real R) :
    0 ≤ residualNeutralizedEnergy (sphereRestrictedProbability2 R)
      (negMacroKernel2 c p w) (fun _ => 0) z := by
  have : IsProbabilityMeasure (sphereRestrictedProbability2 R) :=
    sphereRestrictedProbability2_probability _ hR
  rw [(negMacro2_residualNeutralizedEnergy_eq hc hp hw (sphereRestrictedProbability2 R) z).2]
  apply setIntegral_nonneg measurableSet_Ioc
  intro α hα
  have ht : 0 ≤ c*α := mul_nonneg hc hα.1.le
  rw [residualGaussianEnergy2_eq_defect ht z R hR hmass]
  exact mul_nonneg (Real.rpow_nonneg hα.1.le _) (gaussianMeasureDefect_nonneg ht _ _ _)

/-- One joint residual choice for the subtracted macroscopic kernel (with any density factor
`c ≥ 0`) and one Gaussian window. -/
theorem exists_hex_neg_joint_residual2 {N n : ℕ} (hN : 0 < N) (hn : 0 < n)
    {c p t₀ w₃ : ℝ} (hc : 0 ≤ c) (hp : -2 < p) (ht₀ : 0 ≤ t₀) (hw₃ : 0 ≤ w₃)
    {ι : Type*} [Fintype ι] (X : ι → SphereD 2)
    (C : Fin n → Set (SphereD 2)) (hCm : ∀ i, MeasurableSet (C i))
    (hCd : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hCmass : ∀ i, (sphereProbabilityD 2) (C i) = (N : ℝ≥0∞)⁻¹)
    (dm : Fin n → ℝ) (hdm : ∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y ≤ dm j) :
    ∃ z : Fin n → SphereD 2, Function.Injective z ∧ (∀ j, z j ∈ C j) ∧
      (∀ j, z j ∉ range X) ∧
      0 ≤ residualNeutralizedEnergy (sphereRestrictedProbability2 (⋃ j, C j))
        (negMacroKernel2 c p 1) (fun _ => 0) z ∧
      residualNeutralizedEnergy (sphereRestrictedProbability2 (⋃ j, C j))
          (negMacroKernel2 c p 1) (fun _ => 0) z+
        w₃*(cellPairSum (sphereGaussianKernel2 t₀) z-
          (n:ℝ)*((N:ℝ)*sphereGaussianBackground2 t₀)) ≤
      (n:ℝ)*w₃+c/(p+2)*∑ j, (dm j)^2 := by
  classical
  have hRm : MeasurableSet (⋃ j, C j) := MeasurableSet.iUnion hCm
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hN0 : (N:ℝ≥0∞) ≠ 0 := by exact_mod_cast hN.ne'
  have hNt : (N:ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
  have hn0 : (n:ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
  have hnt : (n:ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hnne : (n:ℝ) ≠ 0 := hnR.ne'
  have hNne : (N:ℝ) ≠ 0 := hNR.ne'
  have hσR : (sphereProbabilityD 2) (⋃ j, C j) = (n:ℝ≥0∞)*(N:ℝ≥0∞)⁻¹ := by
    rw [measure_iUnion (fun i j hij => hCd hij) hCm, tsum_fintype]
    simp [hCmass]
  have hR0 : (sphereProbabilityD 2) (⋃ j, C j) ≠ 0 := by
    rw [hσR]
    exact mul_ne_zero hn0 (ENNReal.inv_ne_zero.mpr hNt)
  have hinv : ((sphereProbabilityD 2) (⋃ j, C j))⁻¹ = (N:ℝ≥0∞)*(n:ℝ≥0∞)⁻¹ := by
    rw [hσR, ENNReal.mul_inv (Or.inl hn0) (Or.inl hnt), inv_inv, mul_comm]
  have htoReal : (((sphereProbabilityD 2) (⋃ j, C j))⁻¹).toReal = (N:ℝ)/(n:ℝ) := by
    rw [hinv, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_natCast, div_eq_mul_inv]
  -- the residual probability measure, as a variable with its defining equation
  obtain ⟨μ, hμdef⟩ : ∃ μ : Measure (SphereD 2), μ = sphereRestrictedProbability2 (⋃ j, C j) :=
    ⟨_, rfl⟩
  have hμP : IsProbabilityMeasure μ := by
    rw [hμdef]
    exact sphereRestrictedProbability2_probability _ hR0
  have hμA : NullSingletonClass μ := by
    rw [hμdef]
    infer_instance
  have hμC : ∀ j, μ (C j) = (n:ℝ≥0∞)⁻¹ := by
    intro j
    have hsub : C j ∩ ⋃ i, C i = C j := inter_eq_left.mpr (subset_iUnion C j)
    rw [hμdef]
    simp only [sphereRestrictedProbability2, Measure.smul_apply, smul_eq_mul]
    rw [Measure.restrict_apply (hCm j), hsub, hCmass j, hinv, mul_comm (N:ℝ≥0∞) _, mul_assoc,
      ENNReal.mul_inv_cancel hN0 hNt, mul_one]
  have hcover : μ (⋃ j, C j)ᶜ = 0 := by
    rw [hμdef]
    exact sphereRestrictedProbability2_compl _ hRm
  have hB : μ (range X) = 0 := (finite_range X).measure_zero μ
  have hint_eq : ∀ f : SphereD 2 → ℝ,
      (∫ y, f y ∂μ) = (N:ℝ)/(n:ℝ)*∫ y in ⋃ j, C j, f y ∂(sphereProbabilityD 2) := by
    intro f
    rw [hμdef]
    simp only [sphereRestrictedProbability2]
    rw [integral_smul_measure, smul_eq_mul, htoReal]
  have hp2 : 0 < p+2 := by linarith
  have hmassR : (n:ℝ) = (N:ℝ)*(sphereProbabilityD 2).real (⋃ j, C j) := by
    rw [Measure.real, hσR, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ENNReal.toReal_natCast]
    field_simp
  -- integrability of the two kernels
  have hKprod : Integrable (Function.uncurry
      (negMacroKernel2 c p 1)) (μ.prod μ) :=
    negMacroKernel2_integrable hc hp zero_le_one (μ.prod μ)
  have hKk : ∀ x, Integrable (negMacroKernel2 c p 1 x) μ :=
    fun x => negMacroKernel2_row_integrable hc hp zero_le_one x μ
  have hKV : Integrable (residualRowPotential μ
      (negMacroKernel2 c p 1)) μ := hKprod.integral_prod_left
  have hGprod : Integrable (Function.uncurry (sphereGaussianKernel2 t₀)) (μ.prod μ) :=
    sphereGaussianKernel2_integrable_finite ht₀ (μ.prod μ)
  have hGk : ∀ x, Integrable (sphereGaussianKernel2 t₀ x) μ :=
    fun x => sphereGaussianKernel2_row_integrable_finite ht₀ x μ
  have hGV : Integrable (residualRowPotential μ (sphereGaussianKernel2 t₀)) μ :=
    hGprod.integral_prod_left
  have hL₃ : Integrable (residualCrossLinear μ (sphereGaussianKernel2 t₀)
      (Fin.elim0 : Fin 0 → SphereD 2) n) μ :=
    residualCrossLinear_integrable (sphereGaussianKernel2 t₀) (sphereGaussianKernel2_comm t₀)
      (Fin.elim0 : Fin 0 → SphereD 2) hGk hGV n
  -- the joint choice
  obtain ⟨z, hinj, hzC, hzB, hne⟩ := exists_stratified_residualNeutralizedEnergy_le_diag μ
    (fun x y => negMacroKernel2 c p 1 x y+
      w₃*sphereGaussianKernel2 t₀ x y)
    (fun x => (0:ℝ)+w₃*residualCrossLinear μ (sphereGaussianKernel2 t₀)
      (Fin.elim0 : Fin 0 → SphereD 2) n x)
    (fun x y => show negMacroKernel2 c p 1 x y+
        w₃*sphereGaussianKernel2 t₀ x y =
        negMacroKernel2 c p 1 y x+
          w₃*sphereGaussianKernel2 t₀ y x by
      rw [negMacroKernel2_symm _ p 1 x y, sphereGaussianKernel2_comm t₀ x y])
    (0+w₃*1)
    (fun x => show negMacroKernel2 c p 1 x x+
        w₃*sphereGaussianKernel2 t₀ x x = 0+w₃*1 by
      rw [negMacroKernel2_self, sphereGaussianKernel2_self])
    hn C hCm hCd hcover hμC
    (fun j => w₃+c/(p+2)*(dm j)^2)
    (fun j x hx y hy => show 0+w₃*1-(negMacroKernel2 c p 1 x y+
        w₃*sphereGaussianKernel2 t₀ x y) ≤
        w₃+c/(p+2)*(dm j)^2 by
      have hvar := negMacroKernel2_variance hc hp zero_le_one x y
      rw [Real.one_rpow] at hvar
      have hd := hdm j x hx y hy
      have hd0 : 0 ≤ dist x y := dist_nonneg
      have hd2 : (dist x y)^2 ≤ (dm j)^2 := pow_le_pow_left₀ hd0 hd 2
      have hG := sphereGaussianKernel2_nonneg t₀ x y
      have hcp : 0 ≤ c/(p+2) := div_nonneg hc hp2.le
      have h1 : c*(dist x y)^2*(1/(p+2)) ≤
          c/(p+2)*(dm j)^2 := by
        calc c*(dist x y)^2*(1/(p+2))
            = c/(p+2)*(dist x y)^2 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hd2 hcp
      have h2 : 0 ≤ w₃*sphereGaussianKernel2 t₀ x y := mul_nonneg hw₃ hG
      linarith)
    (fun x => (hKk x).add ((hGk x).const_mul w₃))
    (residualRowPotential_add_smul_integrable _ _ w₃ hKk hGk hKV hGV)
    (hKprod.add (hGprod.const_mul w₃))
    ((integrable_zero _ _ _).add (hL₃.const_mul w₃)) (range X) hB
  have hKnonneg := negMacro2_residualNeutralizedEnergy_nonneg hc hp zero_le_one z (⋃ j, C j) hR0
    hmassR
  rw [← hμdef] at hKnonneg
  refine ⟨z, hinj, hzC, hzB, ?_, ?_⟩
  · rw [← hμdef]
    exact hKnonneg
  have hsplit : residualNeutralizedEnergy μ
      (fun x y => negMacroKernel2 c p 1 x y+
        w₃*sphereGaussianKernel2 t₀ x y)
      (fun x => (0:ℝ)+w₃*residualCrossLinear μ (sphereGaussianKernel2 t₀)
        (Fin.elim0 : Fin 0 → SphereD 2) n x) z =
      residualNeutralizedEnergy μ (negMacroKernel2 c p 1)
        (fun _ => 0) z+
      w₃*residualNeutralizedEnergy μ (sphereGaussianKernel2 t₀)
        (residualCrossLinear μ (sphereGaussianKernel2 t₀)
          (Fin.elim0 : Fin 0 → SphereD 2) n) z :=
    residualNeutralizedEnergy_add_smul _ _ (fun _ => (0:ℝ)) _ w₃ hKk hGk hKV hGV
      (integrable_zero _ _ _) hL₃ z
  have hcross := residualNeutralizedEnergy_crossLinear (sphereGaussianKernel2 t₀)
    (sphereGaussianKernel2_comm t₀) (Fin.elim0 : Fin 0 → SphereD 2) hGk hGV z
  rw [hsplit, hcross] at hne
  -- the Gaussian window: bounded smooth mean
  have hGU : ∀ x, residualRowPotential μ (sphereGaussianKernel2 t₀) x ≤
      (N:ℝ)/(n:ℝ)*sphereGaussianBackground2 t₀ := by
    intro x
    unfold residualRowPotential
    rw [hint_eq]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc (∫ y in ⋃ j, C j, sphereGaussianKernel2 t₀ x y ∂(sphereProbabilityD 2))
        ≤ ∫ y, sphereGaussianKernel2 t₀ x y ∂(sphereProbabilityD 2) :=
          setIntegral_le_integral (sphereGaussianKernel2_integrable ht₀ x)
            (Filter.Eventually.of_forall fun y => sphereGaussianKernel2_nonneg _ _ _)
      _ = sphereGaussianBackground2 t₀ := (sphereGaussianBackground2_eq_potential ht₀ x).symm
  have hGbg : residualBackground μ (sphereGaussianKernel2 t₀) ≤
      (N:ℝ)/(n:ℝ)*sphereGaussianBackground2 t₀ := by
    unfold residualBackground
    calc _ ≤ ∫ _x, (N:ℝ)/(n:ℝ)*sphereGaussianBackground2 t₀ ∂μ :=
          integral_mono hGV (integrable_const _) hGU
      _ = _ := by simp
  have hc₃ : cellPairSum (sphereGaussianKernel2 t₀) z-
      (n:ℝ)*((N:ℝ)*sphereGaussianBackground2 t₀) ≤
      residualCentered μ (sphereGaussianKernel2 t₀) (Fin.elim0 : Fin 0 → SphereD 2) z := by
    have hbgn : (n:ℝ)^2*residualBackground μ (sphereGaussianKernel2 t₀) ≤
        (n:ℝ)*((N:ℝ)*sphereGaussianBackground2 t₀) := by
      calc _ ≤ (n:ℝ)^2*((N:ℝ)/(n:ℝ)*sphereGaussianBackground2 t₀) :=
            mul_le_mul_of_nonneg_left hGbg (by positivity)
        _ = _ := by field_simp
    unfold residualCentered residualPairEnergy cellPairSum
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_const_zero, mul_zero, sub_zero,
      add_zero]
    linarith
  have hm₃ := mul_le_mul_of_nonneg_left hc₃ hw₃
  have hsum : (∑ j, (w₃+c/(p+2)*(dm j)^2)) =
      (n:ℝ)*w₃+c/(p+2)*∑ j, (dm j)^2 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum]
  rw [hsum] at hne
  rw [← hμdef]
  linarith

end SphericalRiesz
end
end

section

/-! The negative-exponent coefficient on `S²` as the continued Epstein value of the triangular
lattice (stage S2-5).

For real `u < 0` the completed theta value `Λ(u)` of the triangular lattice (the `WeakFEPair` Λ of
`hexThetaFEPair`, weight `k = d/2 = 1`) is the Mellin integral of `Θ(t) - t⁻¹` (no subtraction of
`1` is needed since `u < 0`): the modified function of the strong FE pair is Mellin convergent
everywhere and differs from `Θ - t⁻¹` by `t^(u-1) - t^(u-2)` on `(1,∞)`, whose integral
`-1/u - 1/(1-u)` is exactly the pole correction of `Λ`.  Hence for `s < 0` the profile
`α^(s/2-1)(Θ(α) - α⁻¹)` is integrable on `(0,∞)` and

`C_s = π^(s/2) A^(-s/2)/Γ(s/2) ∫ α^(s/2-1) (Θ(α) - α⁻¹) dα = A^(-s/2) Re ζ_Λ(s)`,

`A = 4π` the area of `S²`: the same continued Epstein value as for positive exponents
(`sphereRieszCoefficient2_eq_epstein`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace SphericalRiesz

/-- The weighted negative-exponent Gaussian profile `α^(s/2-1)(Θ(α) - α⁻¹)` of the triangular
lattice. -/
def hexGaussianRieszProfileNeg2 (s α : ℝ) : ℝ :=
  α^(s/2-1)*(hexGaussianThetaReal2 α-α⁻¹)

theorem hexGaussianRieszProfileNeg2_eq_re (s : ℝ) {α : ℝ} (hα : 0 < α) :
    hexGaussianRieszProfileNeg2 s α =
      ((α:ℂ)^(((s/2:ℝ):ℂ)-1) • (hexThetaImag α-((α:ℂ))⁻¹)).re := by
  have hc : (α:ℂ)^(((s/2:ℝ):ℂ)-1) = ((α^(s/2-1):ℝ):ℂ) := by
    rw [Complex.ofReal_cpow hα.le]
    push_cast
    ring_nf
  rw [hc, smul_eq_mul, Complex.re_ofReal_mul]
  have hre : (hexThetaImag α-((α:ℂ))⁻¹).re = hexGaussianThetaReal2 α-α⁻¹ := by
    rw [hexThetaImag_eq_real hα]
    simp only [Complex.sub_re, ← Complex.ofReal_inv, Complex.ofReal_re]
  rw [hre]
  rfl

theorem hexThetaFEPair_modified_weighted_ae_neg (u : ℝ) :
    (fun t : ℝ => ((t:ℂ)^((u:ℂ)-1)) • (hexThetaImag t-((t:ℂ))⁻¹)) =ᵐ[volume.restrict (Ioi 0)]
      (fun t : ℝ => ((t:ℂ)^((u:ℂ)-1)) • hexThetaFEPair.f_modif t +
        (Ioi 1).indicator (fun t : ℝ => ((t^(u-1)-t^(u-2) : ℝ) : ℂ)) t) := by
  have hne : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), t ≠ 1 := by
    apply Filter.Eventually.mono (compl_mem_ae_iff.mpr (measure_singleton (1 : ℝ)) :
      ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), t ∈ ({1} : Set ℝ)ᶜ)
    intro t ht
    simpa using ht
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hne] with t ht ht1
  have ht0 : 0 < t := ht
  have hc : (t:ℂ)^((u:ℂ)-1) = ((t^(u-1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow ht0.le]
    push_cast
    ring_nf
  have hc2 : ((t^(u-2) : ℝ) : ℂ) = ((t^(u-1) : ℝ) : ℂ) * ((t:ℂ))⁻¹ := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
    congr 1
    rw [show u-2 = (u-1)-(1:ℝ) by ring, Real.rpow_sub ht0, Real.rpow_one, div_eq_mul_inv]
  have h1 : ((t^(-(1:ℝ)) : ℝ) : ℂ) = ((t:ℂ))⁻¹ := by
    rw [Real.rpow_neg ht0.le, Real.rpow_one, Complex.ofReal_inv]
  simp only [WeakFEPair.f_modif, hexThetaFEPair, Pi.add_apply, hc, smul_eq_mul]
  rcases lt_or_gt_of_ne ht1 with hsmall | hlarge
  · have hA : t ∉ Ioi (1:ℝ) := by simpa using hsmall.le
    have hB : t ∈ Ioo (0:ℝ) 1 := ⟨ht0, hsmall⟩
    simp only [indicator_of_notMem hA, indicator_of_mem hB, h1]
    ring
  · have hA : t ∈ Ioi (1:ℝ) := hlarge
    have hB : t ∉ Ioo (0:ℝ) 1 := notMem_Ioo_of_ge hlarge.le
    simp only [indicator_of_notMem hB, indicator_of_mem hA, Complex.ofReal_sub, hc2]
    ring

/-- For real `u < 0` the completed theta value is the Mellin integral of `Θ(t) - t⁻¹`. -/
theorem hexThetaCompleted_eq_integral_neg {u : ℝ} (hu : u < 0) :
    IntegrableOn (fun t : ℝ => ((t:ℂ)^((u:ℂ)-1)) • (hexThetaImag t-((t:ℂ))⁻¹)) (Ioi 0) ∧
    hexThetaCompleted (u:ℂ) =
      ∫ t : ℝ in Ioi 0, ((t:ℂ)^((u:ℂ)-1)) • (hexThetaImag t-((t:ℂ))⁻¹) := by
  have hmod : IntegrableOn (fun t : ℝ => ((t:ℂ)^((u:ℂ)-1)) • hexThetaFEPair.f_modif t) (Ioi 0) :=
    (hexThetaFEPair.isStrongFEPair_toStrongFEPair.hasMellin (u:ℂ)).1
  have h1 : IntegrableOn (fun t : ℝ => ((t^(u-1) : ℝ) : ℂ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).ofReal
  have h5 : IntegrableOn (fun t : ℝ => ((t^(u-2) : ℝ) : ℂ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).ofReal
  have hind : IntegrableOn (fun t : ℝ => ((t^(u-1)-t^(u-2) : ℝ) : ℂ)) (Ioi 1) := by
    refine (h1.sub h5).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, Complex.ofReal_sub]
  have hl := (hind.integrable_indicator measurableSet_Ioi).integrableOn (s := Ioi 0)
  have hint : IntegrableOn
      (fun t : ℝ => ((t:ℂ)^((u:ℂ)-1)) • (hexThetaImag t-((t:ℂ))⁻¹)) (Ioi 0) :=
    (hmod.add hl).congr_fun_ae (hexThetaFEPair_modified_weighted_ae_neg u).symm
  refine ⟨hint, ?_⟩
  have Iind : (∫ t : ℝ in Ioi 0, (Ioi 1).indicator
      (fun t : ℝ => ((t^(u-1)-t^(u-2) : ℝ) : ℂ)) t) = -1/(u:ℂ)-1/(1-(u:ℂ)) := by
    rw [setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1)),
      integral_complex_ofReal]
    have hr : (∫ t : ℝ in Ioi 1, (t^(u-1)-t^(u-2))) = -1/u-1/(1-u) := by
      rw [integral_sub (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one)
          (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one),
        integral_Ioi_rpow_of_lt (by linarith) zero_lt_one,
        integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
      have hd1 : u-1 ≠ 0 := by linarith
      have hd2 : 1-u ≠ 0 := by linarith
      have hval : -1/(u-1) = 1/(1-u) := by
        rw [div_eq_div_iff hd1 hd2]
        ring
      simp only [Real.one_rpow, show u-1+1 = u by ring, show u-2+1 = u-1 by ring]
      linear_combination (-1:ℝ)*hval
    rw [hr]
    push_cast
    ring
  have hm : (∫ t : ℝ in Ioi 0, ((t:ℂ)^((u:ℂ)-1)) • (hexThetaImag t-((t:ℂ))⁻¹)) =
      mellin hexThetaFEPair.f_modif (u:ℂ)+(-1/(u:ℂ)-1/(1-(u:ℂ))) := by
    rw [integral_congr_ae (hexThetaFEPair_modified_weighted_ae_neg u),
      integral_add hmod hl, Iind]
    rfl
  rw [hm]
  change mellin hexThetaFEPair.f_modif (u:ℂ)-(1/(u:ℂ))*1-(1/(1-(u:ℂ)))*1 = _
  ring

theorem hexGaussianRieszProfileNeg2_integrable {s : ℝ} (hs0 : s < 0) :
    IntegrableOn (hexGaussianRieszProfileNeg2 s) (Ioi 0) := by
  have h := (hexThetaCompleted_eq_integral_neg (u := s/2) (by linarith)).1
  have hre := h.re
  apply hre.congr_fun _ measurableSet_Ioi
  intro α hα
  exact (hexGaussianRieszProfileNeg2_eq_re s hα).symm

theorem hexGaussianRieszProfileNeg2_integral_eq {s : ℝ} (hs0 : s < 0) :
    (∫ α : ℝ in Ioi 0, hexGaussianRieszProfileNeg2 s α) =
      (hexThetaCompleted ((s/2:ℝ):ℂ)).re := by
  obtain ⟨hint, heq⟩ := hexThetaCompleted_eq_integral_neg (u := s/2) (by linarith)
  rw [heq]
  have h := integral_re hint
  change (∫ t : ℝ in Ioi 0, (((t:ℂ)^(((s/2:ℝ):ℂ)-1)) • (hexThetaImag t-((t:ℂ))⁻¹)).re) =
    (∫ t : ℝ in Ioi 0, ((t:ℂ)^(((s/2:ℝ):ℂ)-1)) • (hexThetaImag t-((t:ℂ))⁻¹)).re at h
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro α hα
  exact hexGaussianRieszProfileNeg2_eq_re s hα

/-- The second-order coefficient on `S²` for `-2 < s < 0`, as a Gaussian profile integral. -/
def sphereRieszCoefficientNeg2 (s : ℝ) : ℝ :=
  (Real.pi^(s/2)*((sphereAreaD 2).real univ)^(-(s/2))/Real.Gamma (s/2))*
    ∫ α : ℝ in Ioi 0, hexGaussianRieszProfileNeg2 s α

/-- For `s < 0` the coefficient is the continued Epstein zeta value of the triangular lattice,
`C_s = A^(-s/2) Re ζ_Λ(s)` with `A = 4π` the area of `S²`, as for positive exponents. -/
theorem sphereRieszCoefficientNeg2_eq_epstein {s : ℝ} (hs0 : s < 0) :
    sphereRieszCoefficientNeg2 s =
      ((sphereAreaD 2).real univ)^(-(s/2))*(hexEpsteinZeta ((s/2:ℝ):ℂ)).re := by
  have hG : Complex.Gamma ((s/2:ℝ):ℂ) = ((Real.Gamma (s/2) : ℝ) : ℂ) :=
    Complex.Gamma_ofReal (s/2)
  have hP : (Real.pi : ℂ)^((s/2:ℝ):ℂ) = ((Real.pi^(s/2) : ℝ) : ℂ) :=
    (Complex.ofReal_cpow Real.pi_pos.le (s/2)).symm
  have hre : (((Real.pi^(s/2) : ℝ) : ℂ)*hexThetaCompleted ((s/2:ℝ):ℂ)/
      ((Real.Gamma (s/2) : ℝ) : ℂ)).re =
      Real.pi^(s/2)/Real.Gamma (s/2)*(hexThetaCompleted ((s/2:ℝ):ℂ)).re := by
    rw [mul_div_right_comm, ← Complex.ofReal_div, Complex.re_ofReal_mul]
  unfold sphereRieszCoefficientNeg2 hexEpsteinZeta
  rw [hexGaussianRieszProfileNeg2_integral_eq hs0, hG, hP, hre]
  ring

end SphericalRiesz
end
end

section

/-! The universal sharp bound for negative exponents `-2 < s < 0` on `S²` (stage S2-5).

For `-2 < s < 0` every configuration satisfies, for all large `N`,
`(E_s(X) - I_s N²)/N^(1+s/2) ≤ C_s + η`, `C_s = A^(-s/2) Re ζ_Λ(s)`, where
`E_s(X) = Σ_{i≠j} |x_i-x_j|^|s|` and `I_s` is the double integral of `|x-y|^|s|`: the integrand
`α^(s/2-1)(F_N(α)+1)` is nonnegative, so Fatou needs no majorant, and the negative prefactor
turns the Fatou lower bound of the Mellin integral into an upper bound of the energy.  The input
is the sharp Gaussian profile of the sphere, which follows from Gaussian contact certificates of
the triangular lattice at all scales (`sphereGaussianSharpProfileLower2_of_contact`; the
certificates are a hypothesis here and are supplied by `Riesz.HexGaussianBridge2`). -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SphericalRiesz

theorem sphereGaussianCenteredScaled2_neg_profile_eventually (s : ℝ)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, ConfigurationD 2 (N k))
    {α : ℝ} (hα : 0 < α)
    (hp : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      hexGaussianThetaReal2 α-ε ≤ sphereGaussianFullScaled2 α (X k)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      hexGaussianRieszProfileNeg2 s α-ε ≤
        α^(s/2-1)*(sphereGaussianCenteredScaled2 α (X k)+1) := by
  intro ε hε
  have hw : 0 < α^(s/2-1) := Real.rpow_pos_of_pos hα _
  filter_upwards [hp (ε/α^(s/2-1)) (div_pos hε hw)] with k hk
  have hb : sphereGaussianFullScaled2 α (X k)-α⁻¹-1 ≤
      sphereGaussianCenteredScaled2 α (X k) := by
    simpa only [sphereGaussianFullScaled2, sphereGaussianCenteredScaled2] using
      sphereGaussianCentered2_flat_baseline_lower (hN k) hα (X k)
  have he : α^(s/2-1)*(ε/α^(s/2-1)) = ε := mul_div_cancel₀ _ hw.ne'
  unfold hexGaussianRieszProfileNeg2
  nlinarith [mul_le_mul_of_nonneg_left hk hw.le, mul_le_mul_of_nonneg_left hb hw.le]

theorem sphereGaussianSequence_integral_lower_neg2 {s : ℝ} (hs : -2 < s) (hs0 : s < 0)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, ConfigurationD 2 (N k))
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      hexGaussianThetaReal2 α-ε ≤ sphereGaussianFullScaled2 α (X k))
    {C : ℝ}
    (hC : ∀ k, (∫ α : ℝ in Ioi 0, α^(s/2-1)*(sphereGaussianCenteredScaled2 α (X k)+1)) ≤ C) :
    (∫ α : ℝ in Ioi 0, hexGaussianRieszProfileNeg2 s α) ≤ C :=
  integral_le_of_eventual_lower_profile
    (μ := volume.restrict (Ioi (0:ℝ)))
    (g := hexGaussianRieszProfileNeg2 s) (M := fun _ => 0)
    (f := fun k α => α^(s/2-1)*(sphereGaussianCenteredScaled2 α (X k)+1))
    (hexGaussianRieszProfileNeg2_integrable hs0)
    (fun k => sphereGaussianCenteredScaled2_neg_integrable hs hs0 (hN k) (X k))
    (integrable_zero _ _ _)
    (Eventually.of_forall (fun _ => le_refl 0))
    (by
      intro k
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      have hα0 : (0:ℝ) < α := hα
      rw [neg_zero]
      exact mul_nonneg (Real.rpow_nonneg hα0.le _)
        (sphereGaussianCenteredScaled2_add_one_nonneg (hN k) hα0.le (X k)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact sphereGaussianCenteredScaled2_neg_profile_eventually s hN X hα (hp α hα))
    hC

theorem sphereRieszNegPrefactor2_neg {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    Real.pi^(s/2)*((sphereAreaD 2).real univ)^(-(s/2))/Real.Gamma (s/2) < 0 := by
  have hA : 0 < (sphereAreaD 2).real univ := sphereAreaD_univ_pos 2
  have h1 : 0 < Real.pi^(s/2) := Real.rpow_pos_of_pos Real.pi_pos _
  have h2 : 0 < ((sphereAreaD 2).real univ)^(-(s/2)) := Real.rpow_pos_of_pos hA _
  exact div_neg_of_pos_of_neg (mul_pos h1 h2) (real_Gamma_neg_strip (by linarith) (by linarith))

theorem sphereGaussianSequence_energy_upper_neg2 {s : ℝ} (hs : -2 < s) (hs0 : s < 0)
    {N : ℕ → ℕ} (hN : ∀ k, 0 < N k) (X : ∀ k, ConfigurationD 2 (N k))
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      hexGaussianThetaReal2 α-ε ≤ sphereGaussianFullScaled2 α (X k))
    {C : ℝ} (hC : ∀ k, C ≤ normalizedEnergyNeg2 s (X k)) :
    C ≤ sphereRieszCoefficientNeg2 s := by
  have hK := sphereRieszNegPrefactor2_neg hs hs0
  set K := Real.pi^(s/2)*((sphereAreaD 2).real univ)^(-(s/2))/Real.Gamma (s/2) with hKdef
  have hi : ∀ k, (∫ α : ℝ in Ioi 0, α^(s/2-1)*(sphereGaussianCenteredScaled2 α (X k)+1)) ≤
      C/K := by
    intro k
    rw [le_div_iff_of_neg hK, mul_comm]
    rw [← normalizedEnergyNeg2_gaussian_mellin hs hs0 (hN k) (X k)]
    exact hC k
  have h := sphereGaussianSequence_integral_lower_neg2 hs hs0 hN X hp hi
  rw [le_div_iff_of_neg hK] at h
  unfold sphereRieszCoefficientNeg2
  rw [← hKdef]
  linarith

/-- Universal sharp bound for every `-2 < s < 0` from the pointwise sharp sphere Gaussian
profile. -/
theorem sphere2_riesz_neg_upper_of_gaussian_profile (hp : SphereGaussianSharpProfileLower2)
    {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ X : ConfigurationD 2 N, normalizedEnergyNeg2 s X ≤ sphereRieszCoefficientNeg2 s+η := by
  classical
  intro η hη
  by_contra h
  have hbad : ∀ k : ℕ, ∃ N : ℕ, k+1 ≤ N ∧
      ∃ X : ConfigurationD 2 N, sphereRieszCoefficientNeg2 s+η < normalizedEnergyNeg2 s X := by
    intro k
    by_contra hk
    apply h
    refine ⟨k+1, fun N hN X => ?_⟩
    by_contra hX
    exact hk ⟨N, hN, X, lt_of_not_ge hX⟩
  choose N hN X hX using hbad
  have hN0 : ∀ k, 0 < N k := by intro k; have := hN k; omega
  have ht : Tendsto N atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    filter_upwards [eventually_ge_atTop M] with k hk
    have := hN k
    omega
  have hc := sphereGaussianSequence_energy_upper_neg2 hs hs0 hN0 X
    (hp N ht hN0 X) (fun k => (hX k).le)
  linarith

/-- The universal bound under Gaussian contact certificates of the triangular lattice at all scales. -/
theorem sphere2_riesz_neg_upper_of_contact
    (hG2 : ∀ β : ℝ, 0 < β → ∃ f, HexGaussianContactCertificate2 β f)
    {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ X : ConfigurationD 2 N, normalizedEnergyNeg2 s X ≤ sphereRieszCoefficientNeg2 s+η :=
  sphere2_riesz_neg_upper_of_gaussian_profile (sphereGaussianSharpProfileLower2_of_contact hG2)
    hs hs0

end SphericalRiesz
end
end

section

/-! Transfer for negative exponents on `S²` from Gaussian windows and a small macroscopic end
(stage S2-5).

For `-2 < s < 0`, `(E_s - I_s N²)/N^(1+s/2) = K ∫ α^(s/2-1)(F_N(α)+1) dα` with `K < 0` and a
nonnegative integrand.  If along a sequence the full Gaussian sums are eventually at most
`Θ(α)+ε` at every scale, and the macroscopic end `∫_{(0,w]} α^(s/2-1)(F+1) dα` is eventually
small for a suitable cutoff `w`, then the normalized energy is eventually at least
`C_s - η`, `C_s = K ∫ α^(s/2-1)(Θ(α) - α⁻¹) dα`.  On `(w,∞)` the integrand is dominated by
`α^(s/2-1)(Θ(w)+1)` (the full Gaussian sum decreases with the scale), so reverse Fatou applies;
no Gaussian lower bound and no contact certificate enters.  This is the unconditional
direction: configurations whose sum of `|x-y|^|s|` is at least the conjectured value. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace SphericalRiesz

/-- `Θ(α) ≥ α⁻¹` for the theta function of the triangular lattice (theta transformation of weight
one, `Θ(1/α) = α Θ(α)`, and `Θ ≥ 1`). -/
theorem hexGaussianThetaReal2_ge_inv_pow {α : ℝ} (hα : 0 < α) :
    α⁻¹ ≤ hexGaussianThetaReal2 α := by
  have h := hexThetaImag_transform hα
  rw [hexThetaImag_eq_real hα, hexThetaImag_eq_real (inv_pos.mpr hα)] at h
  have hr : hexGaussianThetaReal2 α⁻¹ = α*hexGaussianThetaReal2 α := by
    exact_mod_cast h
  have h1 := hexGaussianThetaReal2_ge_one' (inv_pos.mpr hα)
  rw [inv_eq_one_div, div_le_iff₀ hα]
  linarith

theorem hexGaussianRieszProfileNeg2_nonneg (s : ℝ) {α : ℝ} (hα : 0 < α) :
    0 ≤ hexGaussianRieszProfileNeg2 s α :=
  mul_nonneg (Real.rpow_nonneg hα.le _) (sub_nonneg.mpr (hexGaussianThetaReal2_ge_inv_pow hα))

/-- The full Gaussian sum decreases with the scale. -/
theorem sphereGaussianFullScaled2_anti {N : ℕ} (hN : 0 < N) (X : ConfigurationD 2 N)
    {α β : ℝ} (h : α ≤ β) :
    sphereGaussianFullScaled2 β X ≤ sphereGaussianFullScaled2 α X := by
  have hc : 0 < sphereGaussianDensityFactor2 N := sphereGaussianDensityFactor2_pos hN
  unfold sphereGaussianFullScaled2
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  unfold sphereGaussianKernel2
  apply Real.exp_le_exp.mpr
  rw [sphereGaussianScale2_eq_factor, sphereGaussianScale2_eq_factor]
  have hd : 0 ≤ (dist (X i) (X j))^2 := sq_nonneg _
  have h1 := mul_le_mul_of_nonneg_left h hc.le
  have h2 := mul_le_mul_of_nonneg_right h1 hd
  linarith

/-- `F + 1` is at most the full Gaussian sum. -/
theorem sphereGaussianCenteredScaled2_add_one_le_full {N : ℕ} (α : ℝ)
    (X : ConfigurationD 2 N) :
    sphereGaussianCenteredScaled2 α X+1 ≤ sphereGaussianFullScaled2 α X := by
  have hB := sphereGaussianBackground2_nonneg (sphereGaussianScale2 N α)
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  unfold sphereGaussianCenteredScaled2 sphereGaussianFullScaled2
  nlinarith [mul_nonneg hN0 hB]

/-- Negative-exponent transfer: Gaussian windows at every scale and a small macroscopic end give
the conjectured value from below. -/
theorem sphere2_riesz_neg_lower_of_full_profile {s : ℝ} (hs : -2 < s) (hs0 : s < 0)
    {N : ℕ → ℕ} (hNt : Tendsto N atTop atTop) (hN : ∀ k, 0 < N k)
    (X : ∀ k, ConfigurationD 2 (N k))
    (hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      sphereGaussianFullScaled2 α (X k) ≤ hexGaussianThetaReal2 α+ε)
    (hmacro : ∀ η : ℝ, 0 < η → ∃ w : ℝ, 0 < w ∧ ∀ᶠ k in atTop,
      (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled2 α (X k)+1)) ≤ η) :
    ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
      sphereRieszCoefficientNeg2 s-η ≤ normalizedEnergyNeg2 s (X k) := by
  intro η hη
  have hA : 0 < (sphereAreaD 2).real univ := sphereAreaD_univ_pos 2
  have hΓ : Real.Gamma (s/2) < 0 := real_Gamma_neg_strip (by linarith) (by linarith)
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ,
      K = Real.pi^(s/2)*((sphereAreaD 2).real univ)^(-(s/2))/Real.Gamma (s/2) := ⟨_, rfl⟩
  have hK0 : K < 0 := by
    rw [hKdef]
    exact div_neg_of_pos_of_neg
      (mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.rpow_pos_of_pos hA _)) hΓ
  have hgint : IntegrableOn (hexGaussianRieszProfileNeg2 s) (Ioi 0) :=
    hexGaussianRieszProfileNeg2_integrable hs0
  have hfint : ∀ k, IntegrableOn (fun α : ℝ =>
      α^(s/2-1)*(sphereGaussianCenteredScaled2 α (X k)+1)) (Ioi 0) :=
    fun k => sphereGaussianCenteredScaled2_neg_integrable hs hs0 (hN k) (X k)
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = η/(-K) := ⟨_, rfl⟩
  have hδ : 0 < δ := by
    rw [hδdef]
    exact div_pos hη (by linarith)
  have hδK : δ*(-K) = η := by
    rw [hδdef]
    exact div_mul_cancel₀ η (neg_ne_zero.mpr hK0.ne)
  obtain ⟨w, hw, hmac⟩ := hmacro (δ/2) (half_pos hδ)
  -- reverse Fatou on `(w,∞)`
  have htail : ∀ᶠ k in atTop,
      (∫ α in Ioi w, α^(s/2-1)*(sphereGaussianCenteredScaled2 α (X k)+1)) ≤
        (∫ α in Ioi w, hexGaussianRieszProfileNeg2 s α)+δ/2 := by
    by_contra hcon
    rw [not_eventually] at hcon
    obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hcon
    have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hφt.eventually (hp w hw 1 one_pos))
    have hψt : Tendsto (fun n => φ (n+n₀)) atTop atTop :=
      hφt.comp (tendsto_add_atTop_nat n₀)
    have hNψ : Tendsto (fun n => N (φ (n+n₀))) atTop atTop := hNt.comp hψt
    have hG : IntegrableOn (fun α : ℝ => α^(s/2-1)*(hexGaussianThetaReal2 w+1)) (Ioi w) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith : s/2-1 < -1) hw).mul_const _
    have hΘ1 : 0 ≤ hexGaussianThetaReal2 w+1 := by
      linarith [hexGaussianThetaReal2_ge_one' hw]
    have h := integral_ge_of_eventual_upper_profile2
      (μ := volume.restrict (Ioi w)) (g := hexGaussianRieszProfileNeg2 s)
      (G := fun α : ℝ => α^(s/2-1)*(hexGaussianThetaReal2 w+1))
      (f := fun n α => α^(s/2-1)*(sphereGaussianCenteredScaled2 α (X (φ (n+n₀)))+1))
      (C := (∫ α in Ioi w, hexGaussianRieszProfileNeg2 s α)+δ/2)
      (hgint.mono_set (Ioi_subset_Ioi hw.le))
      (fun n => (hfint (φ (n+n₀))).mono_set (Ioi_subset_Ioi hw.le)) hG
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
        exact mul_nonneg (Real.rpow_nonneg (hw.le.trans (le_of_lt hα)) _) hΘ1)
      (fun n => by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
        have hα0 : 0 < α := hw.trans hα
        have h1 := sphereGaussianCenteredScaled2_add_one_le_full α (X (φ (n+n₀)))
        have h2 := sphereGaussianFullScaled2_anti (hN (φ (n+n₀))) (X (φ (n+n₀))) (le_of_lt hα)
        have h3 := hn₀ (n+n₀) (Nat.le_add_left n₀ n)
        exact mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hα0.le _))
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
        have hα0 : 0 < α := hw.trans hα
        intro ε hε
        have hev := sphereGaussianCenteredScaled2_weighted_profile_upper_eventually s hNψ
          (fun n => hN (φ (n+n₀))) (fun n => X (φ (n+n₀))) hα0
          (fun ε' hε' => hψt.eventually (hp α hα0 ε' hε')) ε hε
        filter_upwards [hev] with n hn
        have he : hexGaussianRieszProfileNeg2 s α =
            hexGaussianRieszProfileRpow2 s α+α^(s/2-1) := by
          unfold hexGaussianRieszProfileNeg2 hexGaussianRieszProfileRpow2
          ring
        rw [he]
        linarith [mul_add (α^(s/2-1)) (sphereGaussianCenteredScaled2 α (X (φ (n+n₀)))) 1,
          mul_one (α^(s/2-1))])
      (fun n => (lt_of_not_ge (hbad (n+n₀))).le)
    linarith
  filter_upwards [hmac, htail] with k hk1 hk2
  have hsplit : (∫ α in Ioi (0:ℝ), α^(s/2-1)*(sphereGaussianCenteredScaled2 α (X k)+1)) =
      (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled2 α (X k)+1))+
        ∫ α in Ioi w, α^(s/2-1)*(sphereGaussianCenteredScaled2 α (X k)+1) := by
    rw [← Ioc_union_Ioi_eq_Ioi hw.le]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      ((hfint k).mono_set Ioc_subset_Ioi_self) ((hfint k).mono_set (Ioi_subset_Ioi hw.le))
  have hgle : (∫ α in Ioi w, hexGaussianRieszProfileNeg2 s α) ≤
      ∫ α in Ioi (0:ℝ), hexGaussianRieszProfileNeg2 s α := by
    apply setIntegral_mono_set hgint
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
      exact hexGaussianRieszProfileNeg2_nonneg s hα
    · exact (Ioi_subset_Ioi hw.le).eventuallyLE
  have hI : (∫ α in Ioi (0:ℝ), α^(s/2-1)*(sphereGaussianCenteredScaled2 α (X k)+1)) ≤
      (∫ α in Ioi (0:ℝ), hexGaussianRieszProfileNeg2 s α)+δ := by
    rw [hsplit]
    linarith
  rw [normalizedEnergyNeg2_gaussian_mellin hs hs0 (hN k) (X k), sphereRieszCoefficientNeg2,
    ← hKdef]
  have hmul := mul_le_mul_of_nonpos_left hI hK0.le
  linarith [hmul, hδK]

end SphericalRiesz
end
end
end
