import Riesz.LeechFourteenth24
import Riesz.SphereRieszNeg24
import Riesz.LeechSharpUpper24

/-! # Block configurations and a sharp sequence for negative exponents on `S²⁴`

Two parts.

* The macroscopic profile of the fourteenth-order foreground: for the mixed measure of a Leech
  patch family (foreground nodes plus `N σ` on the complement of the patches) and every scaled
  Gaussian parameter `α ∈ (0,4]`, `defect(α) ≤ N (A α² + B (N/n²⁶) α)` with constants independent
  of the family; against the weight `α^p`, `-2 < p`, it integrates over `(0,w]` to
  `A w^(p+3)/(p+3) + B (N/n²⁶) w^(p+2)/(p+2)`.
* The block: for a tolerance index `L ≥ 2`, a near-full rational family of residual fraction
  below `L⁻¹⁴`, the fourteenth-order nodes of a refinement and one residual point per cell of an
  exact-mass stratification of the complement, chosen jointly for the subtracted macroscopic
  kernel and one Gaussian window, form an actual configuration of `N = (d m)²⁴` points with a
  Gaussian window at every scale `α ≥ 1/L` and a small macroscopic end at every cutoff
  `0 < w ≤ 1`.  Along `L → ∞` the transfer theorem gives configurations whose normalized
  negative-exponent energy is eventually at least `C_s - η`.

The stratification of the residual regions is a hypothesis of this module
(`LeechResidualStratifiable24`); no contact certificate is used. -/

section

/-! Macroscopic profile of the fourteenth-order foreground defect on S²⁴ (stage NEG).

For the mixed measure of a fourteenth-order Leech patch family (foreground nodes plus `N σ` on
the complement of the patches) and every `α ∈ (0,4]`,

`defect(α) ≤ N (A α² + B (N/n²⁶) α)`,

with constants `A`, `B` independent of the family: for `2π n² α > 1` the general bound and
`n⁻¹⁴ ≤ (2πα)⁷`, `N B₂₄ ≤ 8¹²/α¹²` give `N A α²`; for `2π n² α ≤ 1` the macroscopic bound and
`B₂₄ ≤ 1` give `N B (N/n²⁶) α`.  Since `N/n²⁶ = (d/a)²⁴/n²`, the second term vanishes under
refinement.  Against the weight `α^p`, `-2 < p`, the profile integrates over `(0,w]` to
`A w^(p+3)/(p+3) + B (N/n²⁶) w^(p+2)/(p+2)`. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace SphericalRiesz
open Boundary

/-- Family-independent constant of the mesoscopic foreground defect `N A α²`. -/
def leechMacroConstA24 : ℝ :=
  4*(8:ℝ)^((25:ℝ)/2)*(8:ℝ)^12*
    (bumpErrorConstFourteen24 patchChartUpper24 patchChartLower24)^2*(2*Real.pi)^14

/-- Constant of the macroscopic foreground defect `N B (N/n²⁶) α`. -/
def leechMacroConstB24 : ℝ :=
  (8:ℝ)^((25:ℝ)/2)*
    (bumpErrorConstFourteenSmall24 patchChartUpper24 patchChartLower24)^2*(2*Real.pi)

theorem leechMacroConstA24_nonneg : 0 ≤ leechMacroConstA24 := by
  unfold leechMacroConstA24
  positivity

theorem leechMacroConstB24_nonneg : 0 ≤ leechMacroConstB24 := by
  unfold leechMacroConstB24
  positivity

/-- The weighted integral of a profile `A α² + B α` over `(0,w]`. -/
theorem negMacro_poly_integral {p w : ℝ} (hp : -2 < p) (hw : 0 ≤ w) (A B : ℝ) :
    IntegrableOn (fun α : ℝ => α^p*(A*α^2+B*α)) (Ioc 0 w) ∧
    (∫ α in Ioc (0:ℝ) w, α^p*(A*α^2+B*α)) = A*(w^(p+3)/(p+3))+B*(w^(p+2)/(p+2)) := by
  have h2 : IntegrableOn (fun α : ℝ => A*α^(p+2)) (Ioc 0 w) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hw).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))).const_mul _
  have h1 : IntegrableOn (fun α : ℝ => B*α^(p+1)) (Ioc 0 w) := negMacro_dom_integrableOn hp hw B
  have heq : ∀ α ∈ Ioc (0:ℝ) w, α^p*(A*α^2+B*α) = A*α^(p+2)+B*α^(p+1) := by
    intro α hα
    have h0 : 0 < α := hα.1
    rw [Real.rpow_add h0 p 2, Real.rpow_two, Real.rpow_add_one h0.ne' p]
    ring
  have h3 : p+2+1 = p+3 := by ring
  constructor
  · exact (h2.add h1).congr_fun (fun α hα => (heq α hα).symm) measurableSet_Ioc
  · rw [setIntegral_congr_fun measurableSet_Ioc heq, integral_add h2 h1,
      negMacro_dom_integral hp hw B, integral_const_mul,
      ← intervalIntegral.integral_of_le hw, integral_rpow (Or.inl (by linarith : -1 < p+2)),
      h3, Real.zero_rpow (by linarith : p+3 ≠ 0), sub_zero]

/-- The foreground defect of a fourteenth-order family: `N (A α² + B (N/n²⁶) α)` on `(0,4]`. -/
theorem leechPatchFamily_mixed_defect_macroF :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ {K : ℕ} (P : Fin K → SmallLeechCubePatch24),
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius24 ≤ ρ) →
      Pairwise (fun i j => Disjoint (smallLeechSpherePatch24 (P i))
        (smallLeechSpherePatch24 (P j))) →
      ∀ (a d m : ℕ), 0 < d → 0 < m →
      (∀ i, (P i).ε*(d:ℝ) = leechUnitDensityRadius24*(a:ℝ)) →
      ∀ (hn : 48 ≤ a*m), ∀ α ∈ Ioc (0:ℝ) 4,
      gaussianMeasureDefect (sphereGaussianScale24 ((d*m)^24) α) (((d*m)^24:ℕ):ℝ)
        (mixedForegroundMeasure24 (leechFamilyNodesF24 P (a*m) hn) ((d*m)^24)
          (leechFamilyUnion24 P)ᶜ) ambientSphereProbability24 ≤
      (((d*m)^24:ℕ):ℝ)*(leechMacroConstA24*α^2+
        leechMacroConstB24*((((d*m)^24:ℕ):ℝ)/((a*m:ℕ):ℝ)^26)*α) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := leechPatchFamily_mixed_defect_leF
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro K P hv hε hdisj a d m hd hm hratio hn α hα
  obtain ⟨hA, hB⟩ := hb P hv hε hdisj a d m hd hm hratio hn α hα
  have hα0 : 0 < α := hα.1
  have hNpos : 0 < (d*m)^24 := by positivity
  have hscale : sphereGaussianScale24 ((d*m)^24) α/8 = sphereGaussianScale24 ((d*m)^24) (α/8) := by
    unfold sphereGaussianScale24
    ring
  have hcap0 := sphereGaussianBackground24_scaled_cap hNpos (α := α/8) (by positivity)
  rw [← hscale] at hcap0
  have hB1' : sphereGaussianBackground24 (sphereGaussianScale24 ((d*m)^24) α/8) ≤ 1 :=
    sphereGaussianBackground24_le_one
      (by rw [hscale]; exact (sphereGaussianScale24_pos hNpos (by positivity)).le)
  have hB0' := sphereGaussianBackground24_nonneg (sphereGaussianScale24 ((d*m)^24) α/8)
  -- abbreviations as opaque reals with their equations
  obtain ⟨NR, hNR⟩ : ∃ NR : ℝ, NR = (((d*m)^24:ℕ):ℝ) := ⟨_, rfl⟩
  obtain ⟨n, hndef⟩ : ∃ n : ℝ, n = ((a*m:ℕ):ℝ) := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ,
      B = sphereGaussianBackground24 (sphereGaussianScale24 ((d*m)^24) α/8) := ⟨_, rfl⟩
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ,
      K₀ = bumpErrorConstFourteen24 patchChartUpper24 patchChartLower24 := ⟨_, rfl⟩
  obtain ⟨Ks, hKs⟩ : ∃ Ks : ℝ,
      Ks = bumpErrorConstFourteenSmall24 patchChartUpper24 patchChartLower24 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = gaussianMeasureDefect (sphereGaussianScale24 ((d*m)^24) α)
      (((d*m)^24:ℕ):ℝ) (mixedForegroundMeasure24 (leechFamilyNodesF24 P (a*m) hn) ((d*m)^24)
        (leechFamilyUnion24 P)ᶜ) ambientSphereProbability24 := ⟨_, rfl⟩
  have hAc : leechMacroConstA24 = 4*(8:ℝ)^((25:ℝ)/2)*(8:ℝ)^12*K₀^2*(2*Real.pi)^14 := by
    rw [hK₀]
    rfl
  have hBc : leechMacroConstB24 = (8:ℝ)^((25:ℝ)/2)*Ks^2*(2*Real.pi) := by
    rw [hKs]
    rfl
  rw [← hD, ← hNR, ← hndef, hAc, hBc]
  rw [← hD, ← hNR, ← hndef, ← hBdef, ← hK₀] at hA
  rw [← hD, ← hNR, ← hndef, ← hBdef, ← hKs] at hB
  rw [← hNR, ← hBdef] at hcap0
  rw [← hBdef] at hB1' hB0'
  have hNR0 : 0 < NR := by rw [hNR]; exact_mod_cast hNpos
  have hn0 : 0 < n := by rw [hndef]; exact_mod_cast (by omega : 0 < a*m)
  have hT : 0 < (8:ℝ)^((25:ℝ)/2) := Real.rpow_pos_of_pos (by norm_num) _
  have hcap : NR*B ≤ (8:ℝ)^12/α^12 := by
    calc NR*B ≤ ((α/8)^12)⁻¹ := hcap0
      _ = _ := by rw [div_pow, inv_div]
  have hAterm : 0 ≤ 4*(8:ℝ)^((25:ℝ)/2)*(8:ℝ)^12*K₀^2*(2*Real.pi)^14*α^2 := by positivity
  have hBterm : 0 ≤ (8:ℝ)^((25:ℝ)/2)*Ks^2*(2*Real.pi)*(NR/n^26)*α := by positivity
  by_cases hsmall : 2*Real.pi*n^2*α ≤ 1
  · have h := hB hsmall
    have hsq : (Ks*(Real.sqrt (2*Real.pi*α)/n^13))^2 = Ks^2*(2*Real.pi*α)/n^26 := by
      rw [mul_pow, div_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 2*Real.pi*α)]
      ring
    rw [hsq] at h
    have h1 : (8:ℝ)^((25:ℝ)/2)*(Ks^2*(2*Real.pi*α)/n^26)*NR^2*B ≤
        (8:ℝ)^((25:ℝ)/2)*(Ks^2*(2*Real.pi*α)/n^26)*NR^2*1 :=
      mul_le_mul_of_nonneg_left hB1' (by positivity)
    have h2 : (8:ℝ)^((25:ℝ)/2)*(Ks^2*(2*Real.pi*α)/n^26)*NR^2*1 =
        NR*((8:ℝ)^((25:ℝ)/2)*Ks^2*(2*Real.pi)*(NR/n^26)*α) := by
      ring
    calc D ≤ (8:ℝ)^((25:ℝ)/2)*(Ks^2*(2*Real.pi*α)/n^26)*NR^2*B := h
      _ ≤ NR*((8:ℝ)^((25:ℝ)/2)*Ks^2*(2*Real.pi)*(NR/n^26)*α) := h1.trans_eq h2
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hNR0.le
  · have hlarge : 1 < 2*Real.pi*n^2*α := lt_of_not_ge hsmall
    have h2 : 1/n^2 ≤ 2*Real.pi*α := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have h1 : 1/n^14 ≤ (2*Real.pi*α)^7 := by
      calc 1/n^14 = (1/n^2)^7 := by ring
        _ ≤ (2*Real.pi*α)^7 := pow_le_pow_left₀ (by positivity) h2 7
    have h7 : 0 ≤ (2*Real.pi*α)^7 := by positivity
    have hn14 : 0 ≤ 1/n^14 := by positivity
    have h3 : (1/n^14+(2*Real.pi*α)^7)^2 ≤ (2*(2*Real.pi*α)^7)^2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hsq : (K₀*(1/n^14+(2*Real.pi*α)^7))^2 ≤ K₀^2*(4*(2*Real.pi)^14*α^14) := by
      calc (K₀*(1/n^14+(2*Real.pi*α)^7))^2 = K₀^2*(1/n^14+(2*Real.pi*α)^7)^2 := by ring
        _ ≤ K₀^2*(2*(2*Real.pi*α)^7)^2 := mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
        _ = _ := by ring
    have hstep : (8:ℝ)^((25:ℝ)/2)*(K₀*(1/n^14+(2*Real.pi*α)^7))^2*NR*(NR*B) ≤
        (8:ℝ)^((25:ℝ)/2)*(K₀^2*(4*(2*Real.pi)^14*α^14))*NR*((8:ℝ)^12/α^12) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hT.le) hNR0.le) hcap
        (mul_nonneg hNR0.le hB0') (by positivity)
    have heq : (8:ℝ)^((25:ℝ)/2)*(K₀^2*(4*(2*Real.pi)^14*α^14))*NR*((8:ℝ)^12/α^12) =
        NR*(4*(8:ℝ)^((25:ℝ)/2)*(8:ℝ)^12*K₀^2*(2*Real.pi)^14*α^2) := by
      have hα12 : α^12 ≠ 0 := by positivity
      calc (8:ℝ)^((25:ℝ)/2)*(K₀^2*(4*(2*Real.pi)^14*α^14))*NR*((8:ℝ)^12/α^12)
          = NR*(4*(8:ℝ)^((25:ℝ)/2)*(8:ℝ)^12*K₀^2*(2*Real.pi)^14*(α^12*α^2/α^12)) := by ring
        _ = _ := by rw [mul_div_cancel_left₀ _ hα12]
    calc D ≤ (8:ℝ)^((25:ℝ)/2)*(K₀*(1/n^14+(2*Real.pi*α)^7))^2*NR^2*B := hA
      _ = (8:ℝ)^((25:ℝ)/2)*(K₀*(1/n^14+(2*Real.pi*α)^7))^2*NR*(NR*B) := by ring
      _ ≤ NR*(4*(8:ℝ)^((25:ℝ)/2)*(8:ℝ)^12*K₀^2*(2*Real.pi)^14*α^2) := hstep.trans_eq heq
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hNR0.le

end SphericalRiesz
end
end

section

/-! Block configurations and a sharp sequence for negative exponents on S²⁴ (stage NEG).

For a tolerance index `L ≥ 2` take a near-full rational Leech patch family of residual fraction
below `L⁻¹⁴`, the fourteenth-order nodes of a refinement `m`, and one residual point per cell of
an exact-mass stratification of the complement with `Σ_j c_N d_j² ≤ B n + N/L²`, chosen jointly
for the subtracted macroscopic kernel and one Gaussian window.  The resulting configuration of
`N = (d m)²⁴` points satisfies

* the window `Full_α ≤ (1+1/L)(Θ(α(1-1/L)²)+2/L)+(1+L) C/L²` for every `α ≥ 1/L`,
* the macroscopic end `∫_{(0,w]} α^(s/2-1)(F+1) ≤ 2(A w^(s/2+2)/(s/2+2)+w^(s/2+1)/(L(s/2+1)))+2C/L²`
  for every cutoff `0 < w ≤ 1`,

with `A` and `C` independent of `L` and of the refinement.  Along `L → ∞` the transfer theorem
gives a sequence of configurations whose normalized negative-exponent energy is eventually at
least `C_s - η`.  The stratification of the residual regions is a hypothesis of this file
(`LeechResidualStratifiable24`); it is discharged separately. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace SphericalRiesz
open Boundary

/-- Exact-mass stratifications of the complements of Leech patch families with cells at the
density scale up to `o(N)`: `Σ_j c_N d_j² ≤ B r + ε N`. -/
def LeechResidualStratifiable24 (Bst : ℝ) : Prop :=
  ∀ {K : ℕ} (P : Fin K → SmallLeechCubePatch24) (ε : ℝ), 0 < ε → ∃ N₀ : ℕ, ∀ N r : ℕ,
    N₀ ≤ N → 0 < r →
    (r:ℝ) = (N:ℝ)*(sphereProbabilityD 24).real (leechFamilyUnion24 P)ᶜ →
    ∃ C : Fin r → Set (SphereD 24), ∃ dm : Fin r → ℝ,
      (∀ j, MeasurableSet (C j)) ∧ Pairwise (fun i j => Disjoint (C i) (C j)) ∧
      (⋃ j, C j) = (leechFamilyUnion24 P)ᶜ ∧
      (∀ j, sphereProbabilityD 24 (C j) =
        sphereProbabilityD 24 (leechFamilyUnion24 P)ᶜ/(r:ℝ≥0∞)) ∧
      (∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y ≤ dm j) ∧
      ∑ j, sphereGaussianDensityFactor24 N*(dm j)^2 ≤ Bst*r+ε*N

/-- Common residual constant of the negative-exponent blocks. -/
def leechNegBlockConst24 (s Bst : ℝ) : ℝ := 2+(Bst+1)/(s/2+1)

/-- The number of residual points of a refinement of a fourteenth-order family. -/
theorem leechFamilyF_residual_count {K : ℕ} (P : Fin K → SmallLeechCubePatch24) (a d : ℕ)
    (hd : 0 < d)
    (hmassP : (sphereProbabilityD 24).real (leechFamilyUnion24 P) = (K:ℝ)*((a:ℝ)/d)^24)
    (hbudget : K*a^24 < d^24) (m : ℕ) (hm : 0 < m) (hn : 48 ≤ a*m) :
    ∃ n : ℕ, 0 < n ∧
      Fintype.card (Fin K × (Fin 24 → FourteenNodeIndex (a*m)))+n = (d*m)^24 ∧
      (n:ℝ)/(((d*m)^24:ℕ):ℝ) = 1-(K:ℝ)*((a:ℝ)/d)^24 ∧
      (n:ℝ) = (((d*m)^24:ℕ):ℝ)*(sphereProbabilityD 24).real (leechFamilyUnion24 P)ᶜ := by
  have hcardM : Fintype.card (Fin K × (Fin 24 → FourteenNodeIndex (a*m))) = K*(a*m)^24 := by
    rw [Fintype.card_prod, Fintype.card_fin, fourteenCubeNode_card 24 (a*m) hn]
  have hlt : K*(a*m)^24 < (d*m)^24 := by
    have h1 : K*(a*m)^24 = K*a^24*m^24 := by rw [mul_pow, mul_assoc]
    have h2 : (d*m)^24 = d^24*m^24 := mul_pow d m 24
    rw [h1, h2]
    exact mul_lt_mul_of_pos_right hbudget (pow_pos hm 24)
  have hNpos : 0 < (d*m)^24 := by positivity
  have hNR : (0:ℝ) < (((d*m)^24:ℕ):ℝ) := by exact_mod_cast hNpos
  have hdR : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hfrac : (((d*m)^24-K*(a*m)^24 : ℕ) : ℝ)/(((d*m)^24:ℕ):ℝ) =
      1-(K:ℝ)*((a:ℝ)/d)^24 := by
    rw [Nat.cast_sub hlt.le]
    push_cast
    field_simp
  have hres : (sphereProbabilityD 24).real (leechFamilyUnion24 P)ᶜ =
      (((d*m)^24-K*(a*m)^24 : ℕ) : ℝ)/(((d*m)^24:ℕ):ℝ) := by
    rw [probReal_compl_eq_one_sub (leechFamilyUnion24_measurable P), hmassP, hfrac]
  refine ⟨(d*m)^24-K*(a*m)^24, Nat.sub_pos_of_lt hlt, ?_, hfrac, ?_⟩
  · rw [hcardM]
    exact Nat.add_sub_of_le hlt.le
  · rw [hres, mul_div_cancel₀ _ hNR.ne']

/-- One block for negative exponents: explicit conditions on the family, the refinement and the
residual cells give an actual configuration with a Gaussian window and a small macroscopic
end. -/
theorem exists_leech_neg_block_configuration24 {s : ℝ} (hs : -2 < s) (hs0 : s < 0) {L : ℕ}
    (hL : 2 ≤ L) {Bst : ℝ} (hBst : 0 ≤ Bst) :
    ∃ ρ > 0, ∀ {K : ℕ} (P : Fin K → SmallLeechCubePatch24) (a d : ℕ) {δ : ℝ},
      0 < a → 0 < d → 0 < δ →
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius24 ≤ ρ) →
      (∀ i, (P i).ε*(d:ℝ) = leechUnitDensityRadius24*(a:ℝ)) →
      Pairwise (fun i j => Disjoint (smallLeechSpherePatch24 (P i))
        (smallLeechSpherePatch24 (P j))) →
      (∀ i j, i ≠ j → ∀ x ∈ smallLeechSpherePatch24 (P i),
        ∀ y ∈ smallLeechSpherePatch24 (P j), δ ≤ dist x y) →
      ∀ m : ℕ, 0 < m → 48 ≤ a*m →
      2*(1-(1-48/((a*m:ℕ):ℝ))^24)*
        leechGaussianThetaReal24 (1/(L:ℝ)*leechConservativeRowFactor24) ≤ 1/(L:ℝ) →
      (((d*m)^24:ℕ):ℝ)*Real.exp (-(sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ))*δ^2)) ≤
        1/(L:ℝ) →
      leechMacroConstB24*((((d*m)^24:ℕ):ℝ)/((a*m:ℕ):ℝ)^26) ≤ 1/(L:ℝ) →
      ∀ {n : ℕ}, 0 < n →
      Fintype.card (Fin K × (Fin 24 → FourteenNodeIndex (a*m)))+n = (d*m)^24 →
      (n:ℝ) ≤ 1/(L:ℝ)^14*(((d*m)^24:ℕ):ℝ) →
      ∀ (C : Fin n → Set (SphereD 24)) (dm : Fin n → ℝ), (∀ i, MeasurableSet (C i)) →
      Pairwise (fun i j => Disjoint (C i) (C j)) →
      (∀ i, (sphereProbabilityD 24) (C i) = (((d*m)^24:ℕ):ℝ≥0∞)⁻¹) →
      (⋃ j, C j) = (leechFamilyUnion24 P)ᶜ →
      (∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y ≤ dm j) →
      (∑ j, sphereGaussianDensityFactor24 ((d*m)^24)*(dm j)^2) ≤
        Bst*(n:ℝ)+1/(L:ℝ)^2*(((d*m)^24:ℕ):ℝ) →
      ∃ X : ConfigurationD 24 ((d*m)^24),
        (∀ α : ℝ, 1/(L:ℝ) ≤ α → sphereGaussianFullScaled24 α X ≤
          (1+1/(L:ℝ))*(leechGaussianThetaReal24 (α*(1-1/(L:ℝ))^2)+2/(L:ℝ))+
            (1+(L:ℝ))*(leechNegBlockConst24 s Bst/(L:ℝ)^2)) ∧
        (∀ w : ℝ, 0 < w → w ≤ 1 →
          (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled24 α X+1)) ≤
            2*(leechMacroConstA24*(w^(s/2+2)/(s/2+2))+1/(L:ℝ)*(w^(s/2+1)/(s/2+1)))+
              2*(leechNegBlockConst24 s Bst/(L:ℝ)^2)) := by
  have hp : -2 < s/2-1 := by linarith
  have hp2 : 0 < s/2+1 := by linarith
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0:ℝ) < L := by linarith
  have hL1 : (1:ℝ) ≤ L := by linarith
  have hη : 0 < 1/(L:ℝ) := one_div_pos.mpr hL0
  have hη1 : 1/(L:ℝ) < 1 := by
    rw [div_lt_one hL0]
    linarith
  have hη0 : 0 < 1-1/(L:ℝ) := by linarith
  have hκ := leechConservativeRowFactor24_pos
  obtain ⟨ρ₁,hρ₁,_,hmacro⟩ := leechPatchFamily_mixed_defect_macroF
  obtain ⟨ρ₃,hρ₃,_,hwindow⟩ := leechPatchFamily_gaussianWindow_leF hη hη1
  refine ⟨min ρ₁ ρ₃, lt_min hρ₁ hρ₃, ?_⟩
  intro K P a d δ ha hd hδ hv hε hratio hdisj hsep m hm hn he4 he5 he6 n hnpos hcard hnfrac
    C dm hCm hCd hCmass hCu hdiam hstrat
  have hv₁ : ∀ i, ‖(P i).v‖ ≤ ρ₁ := fun i => (hv i).trans (min_le_left _ _)
  have hv₃ : ∀ i, ‖(P i).v‖ ≤ ρ₃ := fun i => (hv i).trans (min_le_right _ _)
  have hε₁ : ∀ i, (P i).ε*equalAreaScaleRadius24 ≤ ρ₁ := fun i => (hε i).trans (min_le_left _ _)
  have hε₃ : ∀ i, (P i).ε*equalAreaScaleRadius24 ≤ ρ₃ := fun i => (hε i).trans (min_le_right _ _)
  have hNpos : 0 < (d*m)^24 := by positivity
  have hNR : (0:ℝ) < (((d*m)^24:ℕ):ℝ) := by exact_mod_cast hNpos
  have hc0 : 0 < sphereGaussianDensityFactor24 ((d*m)^24) := sphereGaussianDensityFactor24_pos hNpos
  have ht₀ : 0 ≤ sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ)) :=
    (sphereGaussianScale24_pos hNpos hη).le
  -- one joint residual choice
  obtain ⟨z, hz, _, havoid, _, hjoint⟩ := exists_leech_neg_joint_residual24 hNpos hnpos hc0.le
    hp ht₀ (zero_le_one : (0:ℝ) ≤ 1) (leechFamilyNodesF24 P (a*m) hn) C hCm hCd hCmass dm hdiam
  rw [show s/2-1+2 = s/2+1 by ring] at hjoint
  -- cardinalities as real numbers
  have hM0 : (0:ℝ) ≤ ((Fintype.card (Fin K × (Fin 24 → FourteenNodeIndex (a*m))) : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hMn : ((Fintype.card (Fin K × (Fin 24 → FourteenNodeIndex (a*m))) : ℕ) : ℝ)+(n:ℝ) =
      (((d*m)^24:ℕ):ℝ) := by exact_mod_cast hcard
  have hn0R : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hMN : ((Fintype.card (Fin K × (Fin 24 → FourteenNodeIndex (a*m))) : ℕ) : ℝ) ≤
      (((d*m)^24:ℕ):ℝ) := by linarith
  have hMK : ((Fintype.card (Fin K × (Fin 24 → FourteenNodeIndex (a*m))) : ℕ) : ℝ) =
      (K:ℝ)*((a*m:ℕ):ℝ)^24 := by
    rw [Fintype.card_prod, Fintype.card_fin, fourteenCubeNode_card 24 (a*m) hn, Nat.cast_mul,
      Nat.cast_pow]
  -- the residual quantities are at most `N C/L²`
  have hBcap : (((d*m)^24:ℕ):ℝ)*
      sphereGaussianBackground24 (sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ))) ≤ (L:ℝ)^12 := by
    have h := sphereGaussianBackground24_scaled_cap hNpos hη
    have e : ((1/(L:ℝ))^12)⁻¹ = (L:ℝ)^12 := by rw [one_div, inv_pow, inv_inv]
    rw [e] at h
    exact h
  have hNB0 : 0 ≤ (((d*m)^24:ℕ):ℝ)*
      sphereGaussianBackground24 (sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ))) :=
    mul_nonneg hNR.le (sphereGaussianBackground24_nonneg _)
  have hsumdm : sphereGaussianDensityFactor24 ((d*m)^24)/(s/2+1)*∑ j, (dm j)^2 ≤
      (Bst*(n:ℝ)+1/(L:ℝ)^2*(((d*m)^24:ℕ):ℝ))/(s/2+1) := by
    rw [div_mul_eq_mul_div, Finset.mul_sum]
    exact div_le_div_of_nonneg_right hstrat hp2.le
  have hLpow : 1/(L:ℝ)^14 ≤ 1/(L:ℝ)^2 :=
    one_div_le_one_div_of_le (pow_pos hL0 2) (pow_le_pow_right₀ hL1 (by norm_num))
  have hn2 : (n:ℝ) ≤ 1/(L:ℝ)^2*(((d*m)^24:ℕ):ℝ) :=
    hnfrac.trans (mul_le_mul_of_nonneg_right hLpow hNR.le)
  have hL14 : (L:ℝ)^14 = (L:ℝ)^2*(L:ℝ)^12 := by ring
  have hL12 : (0:ℝ) < (L:ℝ)^12 := pow_pos hL0 12
  have hc12 : 1/(L:ℝ)^14*(L:ℝ)^12 = 1/(L:ℝ)^2 := by
    rw [hL14, one_div, one_div, mul_inv, mul_assoc, inv_mul_cancel₀ hL12.ne', mul_one]
  have hnB : (n:ℝ)*((((d*m)^24:ℕ):ℝ)*
      sphereGaussianBackground24 (sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ)))) ≤
      1/(L:ℝ)^2*(((d*m)^24:ℕ):ℝ) := by
    calc (n:ℝ)*((((d*m)^24:ℕ):ℝ)*
          sphereGaussianBackground24 (sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ))))
        ≤ (1/(L:ℝ)^14*(((d*m)^24:ℕ):ℝ))*(L:ℝ)^12 :=
          mul_le_mul hnfrac hBcap hNB0
            (mul_nonneg (one_div_nonneg.mpr (pow_pos hL0 14).le) hNR.le)
      _ = (1/(L:ℝ)^14*(L:ℝ)^12)*(((d*m)^24:ℕ):ℝ) := by ring
      _ = 1/(L:ℝ)^2*(((d*m)^24:ℕ):ℝ) := by rw [hc12]
  have hRbound : (n:ℝ)+(Bst*(n:ℝ)+1/(L:ℝ)^2*(((d*m)^24:ℕ):ℝ))/(s/2+1)+
      (n:ℝ)*((((d*m)^24:ℕ):ℝ)*
        sphereGaussianBackground24 (sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ)))) ≤
      (((d*m)^24:ℕ):ℝ)*(leechNegBlockConst24 s Bst/(L:ℝ)^2) := by
    have h1 : (Bst*(n:ℝ)+1/(L:ℝ)^2*(((d*m)^24:ℕ):ℝ))/(s/2+1) ≤
        ((Bst+1)*(1/(L:ℝ)^2*(((d*m)^24:ℕ):ℝ)))/(s/2+1) := by
      refine div_le_div_of_nonneg_right ?_ hp2.le
      have h := mul_le_mul_of_nonneg_left hn2 hBst
      linarith
    have e : (((d*m)^24:ℕ):ℝ)*(leechNegBlockConst24 s Bst/(L:ℝ)^2) =
        1/(L:ℝ)^2*(((d*m)^24:ℕ):ℝ)+((Bst+1)*(1/(L:ℝ)^2*(((d*m)^24:ℕ):ℝ)))/(s/2+1)+
          1/(L:ℝ)^2*(((d*m)^24:ℕ):ℝ) := by
      unfold leechNegBlockConst24
      ring
    rw [e]
    linarith
  have hcell0 : 0 ≤ cellPairSum (sphereGaussianKernel24
      (sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ)))) z :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sphereGaussianKernel24_nonneg _ _ _
  have hcellN : cellPairSum (sphereGaussianKernel24
      (sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ)))) z ≤
      (((d*m)^24:ℕ):ℝ)*(leechNegBlockConst24 s Bst/(L:ℝ)^2) := by linarith
  have hNE : residualNeutralizedEnergy (sphereRestrictedProbability24 (⋃ j, C j))
      (negMacroKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) (s/2-1) 1) (fun _ => 0) z ≤
      (((d*m)^24:ℕ):ℝ)*(leechNegBlockConst24 s Bst/(L:ℝ)^2) := by linarith
  refine ⟨combinedConfiguration24 (leechFamilyNodesF24 P (a*m) hn) z hcard
    (leechFamilyNodesF24_injective P hdisj (a*m) hn) hz havoid, ?_, ?_⟩
  · -- the window
    intro α hα
    have hαpos : 0 < α := hη.trans_le hα
    have hfull := combinedConfiguration24_fullScaled_le hNpos (leechFamilyNodesF24 P (a*m) hn) z
      hcard (leechFamilyNodesF24_injective P hdisj (a*m) hn) hz havoid hη.le hα hη
    rw [one_div_one_div] at hfull
    have hw := hwindow P hv₃ hε₃ hδ hsep a d m ha hd hm hratio hn α hαpos
    rw [← hMK] at hw
    have hθ : leechGaussianThetaReal24 (α*leechConservativeRowFactor24) ≤
        leechGaussianThetaReal24 (1/(L:ℝ)*leechConservativeRowFactor24) :=
      leechGaussianThetaReal24_anti (mul_pos hη hκ) (mul_le_mul_of_nonneg_right hα hκ.le)
    have hθ0 : 0 ≤ leechGaussianThetaReal24 (α*leechConservativeRowFactor24) :=
      zero_le_one.trans (leechGaussianThetaReal24_ge_one (mul_pos hαpos hκ))
    have hA0 : 0 ≤ leechGaussianThetaReal24 (α*(1-1/(L:ℝ))^2) :=
      zero_le_one.trans (leechGaussianThetaReal24_ge_one (mul_pos hαpos (pow_pos hη0 2)))
    have h48 : (48:ℝ) ≤ ((a*m:ℕ):ℝ) := by exact_mod_cast hn
    have hn₀ : (0:ℝ) < ((a*m:ℕ):ℝ) := by linarith
    have hfr0 : 0 ≤ 1-(1-48/((a*m:ℕ):ℝ))^24 := by
      have h1 : 48/((a*m:ℕ):ℝ) ≤ 1 := (div_le_one hn₀).mpr h48
      have h2 : 0 ≤ 48/((a*m:ℕ):ℝ) := div_nonneg (by norm_num) hn₀.le
      have h3 : (1-48/((a*m:ℕ):ℝ))^24 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      linarith
    have hR0 : 0 ≤ 2*(1-(1-48/((a*m:ℕ):ℝ))^24)*
        leechGaussianThetaReal24 (α*leechConservativeRowFactor24) :=
      mul_nonneg (mul_nonneg (by norm_num) hfr0) hθ0
    have hR : 2*(1-(1-48/((a*m:ℕ):ℝ))^24)*
        leechGaussianThetaReal24 (α*leechConservativeRowFactor24) ≤ 1/(L:ℝ) :=
      (mul_le_mul_of_nonneg_left hθ (mul_nonneg (by norm_num) hfr0)).trans he4
    have hscale : sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ)) ≤
        sphereGaussianScale24 ((d*m)^24) α := by
      rw [sphereGaussianScale24_eq_factor, sphereGaussianScale24_eq_factor]
      exact mul_le_mul_of_nonneg_left hα hc0.le
    have hE : Real.exp (-(sphereGaussianScale24 ((d*m)^24) α*δ^2)) ≤
        Real.exp (-(sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ))*δ^2)) :=
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hscale (sq_nonneg δ)))
    have hfg := leechBlock_window_arith hNR hM0 hMN hA0 hR0 hR (Real.exp_pos _).le hE he5 hw
    have hres : cellPairSum (sphereGaussianKernel24
        (sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ)))) z/(((d*m)^24:ℕ):ℝ) ≤
        leechNegBlockConst24 s Bst/(L:ℝ)^2 := by
      rw [div_le_iff₀ hNR]
      linarith
    have h2L : leechGaussianThetaReal24 (α*(1-1/(L:ℝ))^2)+2*(1/(L:ℝ)) =
        leechGaussianThetaReal24 (α*(1-1/(L:ℝ))^2)+2/(L:ℝ) := by rw [mul_one_div]
    rw [h2L] at hfg
    exact hfull.trans (add_le_add
      (mul_le_mul_of_nonneg_left hfg (by positivity))
      (mul_le_mul_of_nonneg_left hres (by positivity)))
  · -- the macroscopic end
    intro w hw hw1
    have hPm := leechFamilyUnion24_measurable P
    have hσR : (sphereProbabilityD 24) (⋃ j, C j) =
        (n:ℝ≥0∞)*(((d*m)^24:ℕ):ℝ≥0∞)⁻¹ := by
      rw [measure_iUnion (fun i j hij => hCd hij) hCm, tsum_fintype]
      simp [hCmass]
    have hRne : (sphereProbabilityD 24) (leechFamilyUnion24 P)ᶜ ≠ 0 := by
      rw [← hCu, hσR]
      exact mul_ne_zero (by exact_mod_cast hnpos.ne')
        (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _))
    have hmassR : (n:ℝ) =
        (((d*m)^24:ℕ):ℝ)*(sphereProbabilityD 24).real (leechFamilyUnion24 P)ᶜ := by
      rw [← hCu, Measure.real, hσR, ENNReal.toReal_mul, ENNReal.toReal_inv,
        ENNReal.toReal_natCast, ENNReal.toReal_natCast, mul_comm (n:ℝ), ← mul_assoc,
        mul_inv_cancel₀ hNR.ne', one_mul]
    obtain ⟨hgint, hgval⟩ := negMacro_poly_integral hp hw.le leechMacroConstA24
      (leechMacroConstB24*((((d*m)^24:ℕ):ℝ)/((a*m:ℕ):ℝ)^26))
    have hmain : (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled24 α
        (combinedConfiguration24 (leechFamilyNodesF24 P (a*m) hn) z hcard
          (leechFamilyNodesF24_injective P hdisj (a*m) hn) hz havoid)+1)) ≤
        2*(∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(leechMacroConstA24*α^2+
          leechMacroConstB24*((((d*m)^24:ℕ):ℝ)/((a*m:ℕ):ℝ)^26)*α))+
        2/(((d*m)^24:ℕ):ℝ)*residualNeutralizedEnergy
          (sphereRestrictedProbability24 (leechFamilyUnion24 P)ᶜ)
          (negMacroKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) (s/2-1) 1)
          (fun _ => 0) z :=
      combinedConfiguration24_macroEnd_le hs hs0 hNpos
        (leechFamilyNodesF24 P (a*m) hn) z hcard (leechFamilyNodesF24_injective P hdisj (a*m) hn)
        hz havoid hPm hRne hmassR hw1
        (fun α => leechMacroConstA24*α^2+
          leechMacroConstB24*((((d*m)^24:ℕ):ℝ)/((a*m:ℕ):ℝ)^26)*α) hgint
        (fun α hα => hmacro P hv₁ hε₁ hdisj a d m hd hm hratio hn α
          ⟨hα.1, hα.2.trans (hw1.trans (by norm_num))⟩)
    rw [hgval, show s/2-1+3 = s/2+2 by ring, show s/2-1+2 = s/2+1 by ring, ← hCu] at hmain
    have hwq : 0 ≤ w^(s/2+1)/(s/2+1) := div_nonneg (Real.rpow_nonneg hw.le _) hp2.le
    have hB' : leechMacroConstB24*((((d*m)^24:ℕ):ℝ)/((a*m:ℕ):ℝ)^26)*(w^(s/2+1)/(s/2+1)) ≤
        1/(L:ℝ)*(w^(s/2+1)/(s/2+1)) := mul_le_mul_of_nonneg_right he6 hwq
    have h2N : 2/(((d*m)^24:ℕ):ℝ)*residualNeutralizedEnergy
        (sphereRestrictedProbability24 (⋃ j, C j))
        (negMacroKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) (s/2-1) 1) (fun _ => 0) z ≤
        2*(leechNegBlockConst24 s Bst/(L:ℝ)^2) := by
      have h := mul_le_mul_of_nonneg_left hNE (by positivity : (0:ℝ) ≤ 2/(((d*m)^24:ℕ):ℝ))
      have e : 2/(((d*m)^24:ℕ):ℝ)*((((d*m)^24:ℕ):ℝ)*(leechNegBlockConst24 s Bst/(L:ℝ)^2)) =
          2*(leechNegBlockConst24 s Bst/(L:ℝ)^2) := by
        rw [← mul_assoc, div_mul_cancel₀ _ hNR.ne']
      rw [e] at h
      exact h
    linarith

/-- The explicit conditions of a negative-exponent block hold for every sufficiently large
refinement. -/
theorem leechNegBlock_conditions_eventually {L : ℕ} (hL : 2 ≤ L) (a d : ℕ)
    (ha : 0 < a) (hd : 0 < d) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, 0 < m ∧ 48 ≤ a*m ∧
      2*(1-(1-48/((a*m:ℕ):ℝ))^24)*
        leechGaussianThetaReal24 (1/(L:ℝ)*leechConservativeRowFactor24) ≤ 1/(L:ℝ) ∧
      (((d*m)^24:ℕ):ℝ)*Real.exp (-(sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ))*δ^2)) ≤
        1/(L:ℝ) ∧
      leechMacroConstB24*((((d*m)^24:ℕ):ℝ)/((a*m:ℕ):ℝ)^26) ≤ 1/(L:ℝ) := by
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0:ℝ) < L := by linarith
  have hη : 0 < 1/(L:ℝ) := one_div_pos.mpr hL0
  have ham : Tendsto (fun m : ℕ => a*m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m ha) tendsto_id
  have hNt : Tendsto (fun m : ℕ => (d*(m+1))^24) atTop atTop :=
    tendsto_atTop_mono (fun m => (Nat.le_succ m).trans
      ((Nat.le_mul_of_pos_left (m+1) hd).trans (Nat.le_self_pow (by norm_num) _))) tendsto_id
  have hNp : ∀ m : ℕ, 0 < (d*(m+1))^24 := fun m => by positivity
  -- the corrected fraction
  have h4 : Tendsto (fun m : ℕ => 2*(1-(1-48/((a*m:ℕ):ℝ))^24)*
      leechGaussianThetaReal24 (1/(L:ℝ)*leechConservativeRowFactor24)) atTop (𝓝 0) := by
    have hcast : Tendsto (fun m : ℕ => ((a*m:ℕ):ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp ham
    have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h48 : Tendsto (fun _ : ℕ => (48:ℝ)) atTop (𝓝 48) := tendsto_const_nhds
    have hx : Tendsto (fun m : ℕ => (48:ℝ)/((a*m:ℕ):ℝ)) atTop (𝓝 0) := h48.div_atTop hcast
    have h := (((hone.sub ((hone.sub hx).pow 24)).const_mul 2).mul_const
      (leechGaussianThetaReal24 (1/(L:ℝ)*leechConservativeRowFactor24)))
    have h0 : 2*((1:ℝ)-(1-0)^24)*
        leechGaussianThetaReal24 (1/(L:ℝ)*leechConservativeRowFactor24) = 0 := by norm_num
    rw [h0] at h
    exact h
  have e4 := (tendsto_order.mp h4).2 (1/(L:ℝ)) hη
  -- the cross-patch window
  have h5 : Tendsto (fun m : ℕ => (((d*m)^24:ℕ):ℝ)*
      Real.exp (-(sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ))*δ^2))) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mp (sphereGaussianScale24_separated_tendsto hNt hNp hη hδ)
  have e5 := (tendsto_order.mp h5).2 (1/(L:ℝ)) hη
  -- the macroscopic gain
  have h6 : Tendsto (fun m : ℕ => (leechMacroConstB24*(d:ℝ)^24/(a:ℝ)^26)/(m:ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have e6 := (tendsto_order.mp h6).2 (1/(L:ℝ)) hη
  filter_upwards [eventually_ge_atTop 48, e4, e5, e6] with m hm1 hm4 hm5 hm6
  refine ⟨by omega, hm1.trans (Nat.le_mul_of_pos_left m ha), hm4.le, hm5.le, ?_⟩
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hm0 : (0:ℝ) < m := by linarith
  have hm0' : (m:ℝ) ≠ 0 := hm0.ne'
  have ha0 : (a:ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hBn := leechMacroConstB24_nonneg
  have hEq : leechMacroConstB24*((((d*m)^24:ℕ):ℝ)/((a*m:ℕ):ℝ)^26) =
      (leechMacroConstB24*(d:ℝ)^24/(a:ℝ)^26)/(m:ℝ)*(1/(m:ℝ)) := by
    have h24 : (((d*m)^24:ℕ):ℝ) = (d:ℝ)^24*(m:ℝ)^24 := by
      push_cast
      ring
    have h26 : ((a*m:ℕ):ℝ)^26 = (a:ℝ)^26*((m:ℝ)*(m:ℝ))*(m:ℝ)^24 := by
      push_cast
      ring
    rw [h24, h26, mul_div_mul_right _ _ (pow_ne_zero 24 hm0')]
    ring
  have hc0 : 0 ≤ (leechMacroConstB24*(d:ℝ)^24/(a:ℝ)^26)/(m:ℝ) :=
    div_nonneg (div_nonneg (mul_nonneg hBn (pow_nonneg (Nat.cast_nonneg d) 24))
      (pow_nonneg (Nat.cast_nonneg a) 26)) hm0.le
  have h1m : 1/(m:ℝ) ≤ 1 := by
    rw [div_le_one hm0]
    exact hmR
  rw [hEq]
  calc (leechMacroConstB24*(d:ℝ)^24/(a:ℝ)^26)/(m:ℝ)*(1/(m:ℝ))
      ≤ (leechMacroConstB24*(d:ℝ)^24/(a:ℝ)^26)/(m:ℝ)*1 := mul_le_mul_of_nonneg_left h1m hc0
    _ = (leechMacroConstB24*(d:ℝ)^24/(a:ℝ)^26)/(m:ℝ) := mul_one _
    _ ≤ 1/(L:ℝ) := hm6.le

/-- For every tolerance index there is a denominator `d` such that every sufficiently large
refinement carries a negative-exponent block configuration. -/
theorem exists_leech_neg_block24 {s : ℝ} (hs : -2 < s) (hs0 : s < 0) {Bst : ℝ} (hBst : 0 ≤ Bst)
    (hstrat : LeechResidualStratifiable24 Bst) {L : ℕ} (hL : 2 ≤ L) :
    ∃ d : ℕ, 0 < d ∧ ∀ᶠ m : ℕ in atTop, ∃ X : ConfigurationD 24 ((d*m)^24),
      (∀ α : ℝ, 1/(L:ℝ) ≤ α → sphereGaussianFullScaled24 α X ≤
        (1+1/(L:ℝ))*(leechGaussianThetaReal24 (α*(1-1/(L:ℝ))^2)+2/(L:ℝ))+
          (1+(L:ℝ))*(leechNegBlockConst24 s Bst/(L:ℝ)^2)) ∧
      (∀ w : ℝ, 0 < w → w ≤ 1 →
        (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled24 α X+1)) ≤
          2*(leechMacroConstA24*(w^(s/2+2)/(s/2+2))+1/(L:ℝ)*(w^(s/2+1)/(s/2+1)))+
            2*(leechNegBlockConst24 s Bst/(L:ℝ)^2)) := by
  obtain ⟨ρ, hρ, hblock⟩ := exists_leech_neg_block_configuration24 hs hs0 hL hBst
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0:ℝ) < L := by linarith
  obtain ⟨K, P, a, d, δ, ha, hd, hδ, hv, hε, hratio, hdisj, hsep, hmassP, hcov, hKad⟩ :=
    exists_leech_patch_family24 ρ (1/(L:ℝ)^14) hρ (one_div_pos.mpr (pow_pos hL0 14))
  obtain ⟨N₀, hN₀⟩ := hstrat P (1/(L:ℝ)^2) (one_div_pos.mpr (pow_pos hL0 2))
  refine ⟨d, hd, ?_⟩
  have hNt : Tendsto (fun m : ℕ => (d*m)^24) atTop atTop :=
    tendsto_atTop_mono (fun m => (Nat.le_mul_of_pos_left m hd).trans
      (Nat.le_self_pow (by norm_num) _)) tendsto_id
  filter_upwards [leechNegBlock_conditions_eventually hL a d ha hd hδ,
    hNt.eventually (eventually_ge_atTop N₀)] with m hm hmN
  obtain ⟨hm0, hn, he4, he5, he6⟩ := hm
  obtain ⟨n, hnpos, hcard, hfrac, hmass⟩ :=
    leechFamilyF_residual_count P a d hd hmassP hKad m hm0 hn
  obtain ⟨C, dm, hCm, hCd, hCu, hCmassA, hdiam, hsum⟩ := hN₀ ((d*m)^24) n hmN hnpos hmass
  have hNpos : 0 < (d*m)^24 := by positivity
  have hNR : (0:ℝ) < (((d*m)^24:ℕ):ℝ) := by exact_mod_cast hNpos
  have hn0 : (n:ℝ≥0∞) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hnt : (n:ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hσA : (sphereProbabilityD 24) (leechFamilyUnion24 P)ᶜ =
      (n:ℝ≥0∞)*(((d*m)^24:ℕ):ℝ≥0∞)⁻¹ := by
    have hreal : (sphereProbabilityD 24).real (leechFamilyUnion24 P)ᶜ =
        (n:ℝ)/(((d*m)^24:ℕ):ℝ) := by
      rw [eq_div_iff hNR.ne']
      linarith
    rw [← ofReal_measureReal (measure_ne_top (sphereProbabilityD 24) (leechFamilyUnion24 P)ᶜ),
      hreal, ENNReal.ofReal_div_of_pos hNR, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
      div_eq_mul_inv]
  have hCmass : ∀ i, (sphereProbabilityD 24) (C i) = (((d*m)^24:ℕ):ℝ≥0∞)⁻¹ := by
    intro i
    rw [hCmassA i, hσA, ENNReal.div_eq_inv_mul, ← mul_assoc, ENNReal.inv_mul_cancel hn0 hnt,
      one_mul]
  have hnfrac : (n:ℝ) ≤ 1/(L:ℝ)^14*(((d*m)^24:ℕ):ℝ) := by
    have h1 : (n:ℝ)/(((d*m)^24:ℕ):ℝ) < 1/(L:ℝ)^14 := by
      rw [hfrac]
      linarith
    exact ((div_lt_iff₀ hNR).mp h1).le
  exact hblock P a d ha hd hδ hv hε hratio hdisj hsep m hm0 hn he4 he5 he6 hnpos hcard hnfrac
    C dm hCm hCd hCmass hCu hdiam hsum

/-- A sharp sequence for negative exponents, given the stratification of residual regions:
configurations of sizes tending to infinity whose normalized energy is eventually at least
`C_s - η`. -/
theorem sphere24_riesz_neg_sharp_sequence_of_stratifiable {s : ℝ} (hs : -2 < s) (hs0 : s < 0)
    {Bst : ℝ} (hBst : 0 ≤ Bst) (hstrat : LeechResidualStratifiable24 Bst) :
    ∃ (N : ℕ → ℕ) (X : ∀ k, ConfigurationD 24 (N k)), Tendsto N atTop atTop ∧
      ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
        sphereRieszCoefficientNeg24 s-η ≤ normalizedEnergyNeg24 s (X k) := by
  have hp2 : 0 < s/2+1 := by linarith
  have hp3 : 0 < s/2+2 := by linarith
  have hblocks : ∀ j : ℕ, ∃ d : ℕ, 0 < d ∧ ∀ᶠ m : ℕ in atTop,
      ∃ X : ConfigurationD 24 ((d*m)^24),
        (∀ α : ℝ, 1/((j+2:ℕ):ℝ) ≤ α → sphereGaussianFullScaled24 α X ≤
          (1+1/((j+2:ℕ):ℝ))*(leechGaussianThetaReal24 (α*(1-1/((j+2:ℕ):ℝ))^2)+2/((j+2:ℕ):ℝ))+
            (1+((j+2:ℕ):ℝ))*(leechNegBlockConst24 s Bst/((j+2:ℕ):ℝ)^2)) ∧
        (∀ w : ℝ, 0 < w → w ≤ 1 →
          (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled24 α X+1)) ≤
            2*(leechMacroConstA24*(w^(s/2+2)/(s/2+2))+1/((j+2:ℕ):ℝ)*(w^(s/2+1)/(s/2+1)))+
              2*(leechNegBlockConst24 s Bst/((j+2:ℕ):ℝ)^2)) :=
    fun j => exists_leech_neg_block24 hs hs0 hBst hstrat (L := j+2) (by omega)
  choose d hd hev using hblocks
  have hpick : ∀ j : ℕ, ∃ m : ℕ, j+1 ≤ m ∧ ∃ X : ConfigurationD 24 ((d j*m)^24),
      (∀ α : ℝ, 1/((j+2:ℕ):ℝ) ≤ α → sphereGaussianFullScaled24 α X ≤
        (1+1/((j+2:ℕ):ℝ))*(leechGaussianThetaReal24 (α*(1-1/((j+2:ℕ):ℝ))^2)+2/((j+2:ℕ):ℝ))+
          (1+((j+2:ℕ):ℝ))*(leechNegBlockConst24 s Bst/((j+2:ℕ):ℝ)^2)) ∧
      (∀ w : ℝ, 0 < w → w ≤ 1 →
        (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled24 α X+1)) ≤
          2*(leechMacroConstA24*(w^(s/2+2)/(s/2+2))+1/((j+2:ℕ):ℝ)*(w^(s/2+1)/(s/2+1)))+
            2*(leechNegBlockConst24 s Bst/((j+2:ℕ):ℝ)^2)) :=
    fun j => ((eventually_ge_atTop (j+1)).and (hev j)).exists
  choose m hmj X hW hM using hpick
  have hmpos : ∀ j, 0 < m j := fun j => lt_of_lt_of_le (Nat.succ_pos j) (hmj j)
  have hNpos : ∀ j, 0 < (d j*m j)^24 := fun j => pow_pos (Nat.mul_pos (hd j) (hmpos j)) 24
  have hNt : Tendsto (fun j : ℕ => (d j*m j)^24) atTop atTop :=
    tendsto_atTop_mono (fun j => (Nat.le_succ j).trans ((hmj j).trans
      ((Nat.le_mul_of_pos_left (m j) (hd j)).trans (Nat.le_self_pow (by norm_num) _))))
      tendsto_id
  refine ⟨fun j => (d j*m j)^24, X, hNt, ?_⟩
  have hLt : Tendsto (fun j : ℕ => j+2) atTop atTop :=
    tendsto_atTop_mono (fun j => Nat.le_add_right j 2) tendsto_id
  have hLR : Tendsto (fun j : ℕ => ((j+2:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hLt
  have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hu : Tendsto (fun j : ℕ => 1/((j+2:ℕ):ℝ)) atTop (𝓝 0) := hone.div_atTop hLR
  -- the pointwise window
  have hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
      sphereGaussianFullScaled24 α (X j) ≤ leechGaussianThetaReal24 α+ε := by
    intro α hα ε hε
    have hΦ := leechBlockWindowBound_tendsto (B := leechNegBlockConst24 s Bst) hα hLt
    have e1 := (tendsto_order.mp hΦ).2 (leechGaussianThetaReal24 α+ε) (by linarith)
    have e2 := (tendsto_order.mp hu).2 α hα
    filter_upwards [e1, e2] with j hj1 hj2
    exact (hW j α hj2.le).trans hj1.le
  -- the macroscopic end
  have hmacro : ∀ η : ℝ, 0 < η → ∃ w : ℝ, 0 < w ∧ ∀ᶠ j in atTop,
      (∫ α in Ioc (0:ℝ) w, α^(s/2-1)*(sphereGaussianCenteredScaled24 α (X j)+1)) ≤ η := by
    intro η hη
    have hA := leechMacroConstA24_nonneg
    have hden : 0 < 4*(leechMacroConstA24+1) := by linarith
    have hw0 : 0 < η*(s/2+2)/(4*(leechMacroConstA24+1)) := div_pos (mul_pos hη hp3) hden
    refine ⟨min 1 (η*(s/2+2)/(4*(leechMacroConstA24+1))), lt_min one_pos hw0, ?_⟩
    obtain ⟨w, hwdef⟩ : ∃ w : ℝ, w = min 1 (η*(s/2+2)/(4*(leechMacroConstA24+1))) := ⟨_, rfl⟩
    rw [← hwdef]
    have hw : 0 < w := by rw [hwdef]; exact lt_min one_pos hw0
    have hw1 : w ≤ 1 := by rw [hwdef]; exact min_le_left _ _
    have hw2 : w ≤ η*(s/2+2)/(4*(leechMacroConstA24+1)) := by rw [hwdef]; exact min_le_right _ _
    have hpow3 : w^(s/2+2) ≤ w := by
      have h := Real.rpow_le_rpow_of_exponent_ge hw hw1 (by linarith : (1:ℝ) ≤ s/2+2)
      rwa [Real.rpow_one] at h
    have hpow2 : w^(s/2+1) ≤ 1 := Real.rpow_le_one hw.le hw1 hp2.le
    have hfirst : 2*(leechMacroConstA24*(w^(s/2+2)/(s/2+2))) ≤ η/2 := by
      have h1 : w^(s/2+2)/(s/2+2) ≤ η/(4*(leechMacroConstA24+1)) := by
        rw [div_le_iff₀ hp3]
        calc w^(s/2+2) ≤ w := hpow3
          _ ≤ η*(s/2+2)/(4*(leechMacroConstA24+1)) := hw2
          _ = η/(4*(leechMacroConstA24+1))*(s/2+2) := by ring
      have h2 : leechMacroConstA24*(w^(s/2+2)/(s/2+2)) ≤
          leechMacroConstA24*(η/(4*(leechMacroConstA24+1))) := mul_le_mul_of_nonneg_left h1 hA
      have h3 : leechMacroConstA24*(η/(4*(leechMacroConstA24+1))) ≤ η/4 := by
        rw [mul_div_assoc', div_le_div_iff₀ hden (by norm_num : (0:ℝ) < 4)]
        linarith
      linarith
    have hCc : Tendsto (fun _ : ℕ => leechNegBlockConst24 s Bst) atTop
        (𝓝 (leechNegBlockConst24 s Bst)) := tendsto_const_nhds
    have hsq : Tendsto (fun j : ℕ => leechNegBlockConst24 s Bst/((j+2:ℕ):ℝ)^2) atTop (𝓝 0) :=
      hCc.div_atTop ((tendsto_pow_atTop two_ne_zero).comp hLR)
    have hφ : Tendsto (fun j : ℕ => 2*(1/((j+2:ℕ):ℝ)*(1/(s/2+1)))+
        2*(leechNegBlockConst24 s Bst/((j+2:ℕ):ℝ)^2)) atTop (𝓝 (2*(0*(1/(s/2+1)))+2*0)) :=
      ((hu.mul_const _).const_mul 2).add (hsq.const_mul 2)
    have hφ0 : (2*(0*(1/(s/2+1)))+2*0 : ℝ) = 0 := by ring
    rw [hφ0] at hφ
    have e := (tendsto_order.mp hφ).2 (η/2) (half_pos hη)
    filter_upwards [e] with j hj
    have hMj := hM j w hw hw1
    have hsec : 1/((j+2:ℕ):ℝ)*(w^(s/2+1)/(s/2+1)) ≤ 1/((j+2:ℕ):ℝ)*(1/(s/2+1)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpow2 hp2.le)
        (one_div_nonneg.mpr (Nat.cast_nonneg _))
    linarith
  exact sphere24_riesz_neg_lower_of_full_profile hs hs0 hNt hNpos X hp hmacro

end SphericalRiesz
end
end
