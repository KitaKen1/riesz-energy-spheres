import Riesz.SphereRationalFamily24
import Riesz.LeechForegroundDefect24
import Riesz.SphereResidualCells24
import Riesz.LeechWindowReduction24
import Riesz.LeechForegroundWindow24
import Riesz.RationalSizeCeiling24
import Riesz.LeechEpstein24
import Riesz.SphereRieszUpperFourLtAllN8

/-! Sharp upper bound for the Riesz energy on S²⁴ at every large `N`, for all `0 < s < 24`.

The module has three parts.

* `LeechPatchFamily`: near-full separated rational Leech patch families as families of small
  cube patches, and the residual cells of a refinement (`n = (d m)²⁴ - K (a m)²⁴` cells of
  probability `1/N` whose union is the complement of the family).
* `LeechBlock`: for a tolerance index `L ≥ 2` and every sufficiently large refinement, an actual
  configuration of `(d m)²⁴` points with a common small-alpha budget, a common short-range cost
  and a Gaussian window bound which tends to the Leech theta profile as `L → ∞`.
* `LeechSharpUpper`: a diagonal choice over `L` gives one configuration of size `M(N) ≥ N`,
  `M(N)/N → 1`, for every large `N`; the Gaussian-only bridge bounds its normalized Riesz energy
  by the regularized-theta coefficient, and a subconfiguration of `N` points keeps the normalized
  energy up to the factor `(N/M)^(1-s/24) → 1`.

The upper bound uses no Gaussian certificate and no CKMRV input.  The two-sided statement at
the end assumes all-scale Leech contact certificates for its lower half.  The coefficient is
the regularized theta Mellin integral `sphereRieszCoefficient24`; its Epstein form is not
identified here. -/

set_option autoImplicit false
noncomputable section
namespace SphericalRiesz

section LeechPatchFamily
open Set MeasureTheory
open scoped ENNReal
open Boundary

/-! ### LeechPatchFamily

Near-full rational Leech patch families on S²⁴ and the residual cells of a refinement.

For every smallness radius `ρ` and every residual fraction `b` there is a finite family of small
Leech cube patches of one common rational scale `ε d = r₀ a` which is pairwise disjoint,
separated by a positive distance, of exact probability `K (a/d)²⁴ > 1-b`, with
`K a²⁴ < d²⁴`.

For every refinement `m` the complement of the family has probability exactly `n/N`,
`N = (d m)²⁴`, `n = N - K (a m)²⁴ > 0`, and it splits into `n` measurable pairwise disjoint
cells of probability `1/N`.  These are the premises of the common Gaussian budget.  No point
choice, budget or attaining sequence is asserted here. -/

/-- A near-full separated family of small Leech cube patches of one rational scale. -/
theorem exists_leech_patch_family24 (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b) :
    ∃ (K : ℕ) (P : Fin K → SmallLeechCubePatch24) (a d : ℕ) (δ : ℝ),
      0 < a ∧ 0 < d ∧ 0 < δ ∧
      (∀ i, ‖(P i).v‖ ≤ ρ) ∧ (∀ i, (P i).ε*equalAreaScaleRadius24 ≤ ρ) ∧
      (∀ i, (P i).ε*(d:ℝ) = leechUnitDensityRadius24*(a:ℝ)) ∧
      Pairwise (fun i j => Disjoint (smallLeechSpherePatch24 (P i))
        (smallLeechSpherePatch24 (P j))) ∧
      (∀ i j, i ≠ j → ∀ x ∈ smallLeechSpherePatch24 (P i),
        ∀ y ∈ smallLeechSpherePatch24 (P j), δ ≤ dist x y) ∧
      (sphereProbabilityD 24).real (leechFamilyUnion24 P) = (K:ℝ)*((a:ℝ)/d)^24 ∧
      1-b < (K:ℝ)*((a:ℝ)/d)^24 ∧ K*a^24 < d^24 := by
  obtain ⟨K,g,v,p,q,hp,hq,ℓ,hℓ,hℓdef,hscale,hcell,hd,⟨δ,hδ,hsep⟩,hlower,_,hmass,_,hbudget⟩ :=
    sphere24_near_full_rational_affine_cubes ρ b hρ hb
  have hqR : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hratio : ℓ*(q:ℝ) = leechUnitDensityRadius24*(p:ℝ) := by
    rw [hℓdef, equalAreaLeechNormalizedScale24, mul_assoc, div_mul_cancel₀ _ hqR]
  refine ⟨K, fun i => ⟨g i, v i, cubeMidpoint24, ℓ, hℓ, cubeMidpoint24_mem_unitCube,
    (hcell i).2.1⟩, p, q, δ, hp, hq, hδ, fun i => (hcell i).1, fun _ => hscale,
    fun _ => hratio, hd, ?_, hmass, ?_, hbudget⟩
  · intro i j hij x hx y hy
    exact (hsep i j hij x hx y hy).le
  · rw [← hmass]
    exact hlower

/-- Residual cells of a refinement: `n = (d m)²⁴ - K (a m)²⁴ > 0` cells of probability `1/N`
whose union is the complement of the family. -/
theorem exists_leech_refinement_cells24 {K : ℕ} (P : Fin K → SmallLeechCubePatch24) (a d : ℕ)
    (hd : 0 < d)
    (hmassP : (sphereProbabilityD 24).real (leechFamilyUnion24 P) = (K:ℝ)*((a:ℝ)/d)^24)
    (hbudget : K*a^24 < d^24) (m : ℕ) (hm : 0 < m) (hn : 74 ≤ a*m) :
    ∃ n : ℕ, 0 < n ∧
      Fintype.card (Fin K × (Fin 24 → TwelveNodeIndex (a*m)))+n = (d*m)^24 ∧
      (n:ℝ)/(((d*m)^24:ℕ):ℝ) = 1-(K:ℝ)*((a:ℝ)/d)^24 ∧
      ∃ C : Fin n → Set (SphereD 24), (∀ i, MeasurableSet (C i)) ∧
        Pairwise (fun i j => Disjoint (C i) (C j)) ∧
        (∀ i, (sphereProbabilityD 24) (C i) = (((d*m)^24:ℕ):ℝ≥0∞)⁻¹) ∧
        (⋃ j, C j) = (leechFamilyUnion24 P)ᶜ := by
  have hcardM : Fintype.card (Fin K × (Fin 24 → TwelveNodeIndex (a*m))) = K*(a*m)^24 := by
    rw [Fintype.card_prod, Fintype.card_fin, twelveCubeNode_card 24 (a*m) hn]
  have hlt : K*(a*m)^24 < (d*m)^24 := by
    have h1 : K*(a*m)^24 = K*a^24*m^24 := by rw [mul_pow, mul_assoc]
    have h2 : (d*m)^24 = d^24*m^24 := mul_pow d m 24
    rw [h1, h2]
    exact mul_lt_mul_of_pos_right hbudget (pow_pos hm 24)
  have hNpos : 0 < (d*m)^24 := by positivity
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
  obtain ⟨C, hCm, hCd, hCu, hCmass⟩ := exists_sphere24_equal_mass_cells hNpos
    (Nat.sub_pos_of_lt hlt) (leechFamilyUnion24_measurable P).compl hres
  refine ⟨(d*m)^24-K*(a*m)^24, Nat.sub_pos_of_lt hlt, ?_, hfrac, C, hCm, hCd, hCmass, hCu⟩
  rw [hcardM]
  exact Nat.add_sub_of_le hlt.le

end LeechPatchFamily

section LeechBlock
open Set MeasureTheory Filter
open scoped ENNReal Topology
open Boundary

/-! ### LeechBlock

One block of the S²⁴ upper construction: an actual configuration with three Gaussian
controls.

For a tolerance index `L ≥ 2` take `η = α₀ = ε = 1/L`, the window weight `L²` and a near-full
rational Leech family of residual fraction below `L⁻¹⁴`.  For every sufficiently large
refinement `m` the foreground nodes and one joint residual choice form an actual configuration
`X` of `N = (d m)²⁴` points with

* the small-alpha budget `H_{s/4}(X) ≤ B_s`,
* the short-range cost `Σ T_{s/4+5}(X)/N ≤ D_s`,
* the window `Full_α(X) ≤ (1+1/L)(Θ(α(1-1/L)²)+2/L)+(1+L) B_s/L²` for every `α ≥ 1/L`,

where `B_s` and `D_s` depend only on `s`.  No limit in `L`, no attaining sequence and no Riesz
energy bound is asserted here. -/

/-- The joint bound is at most `N` times a constant when the residual fraction is at most
`λ⁻¹⁴`, the window weight is `λ²` and the window background is at most `λ¹²`. -/
theorem leechJointBound24_le {N n : ℕ} {M Fg Fb q p t₀ lam : ℝ}
    (hM0 : 0 ≤ M) (hMn : M+(n:ℝ) = (N:ℝ)) (hFg : Fg ≤ Fb) (hq : 0 < q) (hp : p < 11)
    (hlam : 1 ≤ lam) (hn : (n:ℝ) ≤ 1/lam^14*(N:ℝ))
    (hB : (N:ℝ)*sphereGaussianBackground24 t₀ ≤ lam^12) :
    leechJointBound24 N n M Fg q p t₀ 1 (lam^2) ≤ (N:ℝ)*(Fb+4^q/q+3/(11-p)+2) := by
  have hlam0 : 0 < lam := lt_of_lt_of_le zero_lt_one hlam
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hnN : (n:ℝ) ≤ N := by linarith
  have hMN : M ≤ N := by linarith
  have h11 : 0 < 11-p := by linarith
  have h4q : 0 ≤ (4:ℝ)^q/q := div_nonneg (Real.rpow_nonneg (by norm_num) q) hq.le
  have hpow : lam^2*lam^12 = lam^14 := by ring
  have hc14 : 1/lam^14*lam^2*lam^12 = 1 := by
    rw [mul_assoc, hpow, one_div_mul_cancel (pow_ne_zero 14 hlam0.ne')]
  have hc2 : 1/lam^14*lam^2 ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one (pow_pos hlam0 14)]
    exact pow_le_pow_right₀ hlam (by norm_num)
  have h12 : 0 ≤ lam^12 := pow_nonneg hlam0.le 12
  have t1 : (N:ℝ)*Fg ≤ (N:ℝ)*Fb := mul_le_mul_of_nonneg_left hFg hN0
  have t2a : (n:ℝ)*((4:ℝ)^q/q) ≤ (N:ℝ)*((4:ℝ)^q/q) := mul_le_mul_of_nonneg_right hnN h4q
  have t2b : (n:ℝ)*lam^2 ≤ (N:ℝ) := by
    calc (n:ℝ)*lam^2 ≤ 1/lam^14*(N:ℝ)*lam^2 := mul_le_mul_of_nonneg_right hn (sq_nonneg lam)
      _ = (N:ℝ)*(1/lam^14*lam^2) := by ring
      _ ≤ (N:ℝ)*1 := mul_le_mul_of_nonneg_left hc2 hN0
      _ = N := mul_one _
  have t3 : (2*M+(n:ℝ))/(11-p) ≤ (N:ℝ)*(3/(11-p)) := by
    rw [div_le_iff₀ h11]
    calc 2*M+(n:ℝ) ≤ (N:ℝ)*3 := by linarith
      _ = (N:ℝ)*(3/(11-p))*(11-p) := by rw [mul_assoc, div_mul_cancel₀ _ h11.ne']
  have t4 : lam^2*((n:ℝ)*((N:ℝ)*sphereGaussianBackground24 t₀)) ≤ (N:ℝ) := by
    calc lam^2*((n:ℝ)*((N:ℝ)*sphereGaussianBackground24 t₀))
        ≤ lam^2*((n:ℝ)*lam^12) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB hn0) (sq_nonneg lam)
      _ ≤ lam^2*(1/lam^14*(N:ℝ)*lam^12) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hn h12) (sq_nonneg lam)
      _ = (N:ℝ)*(1/lam^14*lam^2*lam^12) := by ring
      _ = N := by rw [hc14, mul_one]
  unfold leechJointBound24
  have e2 : (n:ℝ)*((4:ℝ)^q/q+lam^2) = (n:ℝ)*((4:ℝ)^q/q)+(n:ℝ)*lam^2 := by ring
  have e3 : (N:ℝ)*(Fb+(4:ℝ)^q/q+3/(11-p)+2) =
      (N:ℝ)*Fb+(N:ℝ)*((4:ℝ)^q/q)+(N:ℝ)*(3/(11-p))+(N:ℝ)+(N:ℝ) := by ring
  rw [e2, e3, one_mul]
  linarith

/-- Arithmetic of the short-range cost of a block. -/
theorem leechBlock_tail_arith {N M TB sep S rCS JB Bs : ℝ} (hN : 0 < N) (hM0 : 0 ≤ M)
    (hMN : M ≤ N) (hTB : 0 ≤ TB) (hsep : 0 ≤ sep) (hNsep : N*sep ≤ 1)
    (hS : S ≤ M*TB+M^2*sep) (hr : 1*rCS ≤ JB) (hJB : JB ≤ N*Bs) : (S+rCS)/N ≤ TB+1+Bs := by
  rw [div_le_iff₀ hN]
  have h1 : M*TB ≤ N*TB := mul_le_mul_of_nonneg_right hMN hTB
  have h2 : M^2*sep ≤ N := by
    calc M^2*sep = M*(M*sep) := by ring
      _ ≤ N*(N*sep) := mul_le_mul hMN (mul_le_mul_of_nonneg_right hMN hsep)
          (mul_nonneg hM0 hsep) hN.le
      _ ≤ N*1 := mul_le_mul_of_nonneg_left hNsep hN.le
      _ = N := mul_one N
  have h3 : rCS ≤ N*Bs := by linarith
  linarith

/-- Arithmetic of the foreground window of a block. -/
theorem leechBlock_window_arith {N M A R E E₀ c S : ℝ} (hN : 0 < N) (hM0 : 0 ≤ M) (hMN : M ≤ N)
    (hA : 0 ≤ A) (hR0 : 0 ≤ R) (hR : R ≤ c) (hE0 : 0 ≤ E) (hE : E ≤ E₀) (hNE : N*E₀ ≤ c)
    (hS : S ≤ M*(A+R)+M^2*E) : S/N ≤ A+2*c := by
  rw [div_le_iff₀ hN]
  have h1 : M*(A+R) ≤ N*(A+c) := mul_le_mul hMN (by linarith) (by linarith) hN.le
  have h2 : M^2*E ≤ N*c := by
    calc M^2*E = M*(M*E) := by ring
      _ ≤ N*(N*E₀) := mul_le_mul hMN (mul_le_mul hMN hE hE0 hN.le) (mul_nonneg hM0 hE0) hN.le
      _ ≤ N*c := mul_le_mul_of_nonneg_left hNE hN.le
  linarith

/-- Common small-alpha constant of the blocks. -/
def leechBlockSmallConst24 (s : ℝ) : ℝ :=
  leechForegroundProfileConst24*(4^(s/4)/(s/4))+
    leechForegroundProfileGain24 (s/4)*(4^(s/4/2)/(s/4/2))+4^(s/4)/(s/4)+3/(11-(s/4+5))+2

/-- Common short-range constant of the blocks. -/
def leechBlockTailConst24 (s : ℝ) : ℝ :=
  leechGaussianTailBudget24 (leechCorrectedDensityBudgetScale24 leechUnitDensityRadius24)
    (s/4+5)+1+leechBlockSmallConst24 s

/-- One block: explicit conditions on the family and on the refinement give an actual
configuration with the three Gaussian controls. -/
theorem exists_leech_block_configuration24 {s : ℝ} (hs : 0 < s) (hs24 : s < 24) {L : ℕ}
    (hL : 2 ≤ L) :
    ∃ ρ > 0, ∀ {K : ℕ} (P : Fin K → SmallLeechCubePatch24) (a d : ℕ) {δ : ℝ},
      0 < a → 0 < d → 0 < δ →
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius24 ≤ ρ) →
      (∀ i, (P i).ε*(d:ℝ) = leechUnitDensityRadius24*(a:ℝ)) →
      Pairwise (fun i j => Disjoint (smallLeechSpherePatch24 (P i))
        (smallLeechSpherePatch24 (P j))) →
      (∀ i j, i ≠ j → ∀ x ∈ smallLeechSpherePatch24 (P i),
        ∀ y ∈ smallLeechSpherePatch24 (P j), δ ≤ dist x y) →
      (sphereProbabilityD 24).real (leechFamilyUnion24 P) = (K:ℝ)*((a:ℝ)/d)^24 →
      1-1/(L:ℝ)^14 < (K:ℝ)*((a:ℝ)/d)^24 → K*a^24 < d^24 →
      ∀ m : ℕ, 0 < m → 74 ≤ a*m →
      ((d:ℝ)/(a:ℝ))^24*((d*m:ℕ):ℝ)^(-(s/4)) ≤ 1 →
      (((d*m)^24:ℕ):ℝ)*separatedShortRangeBound24
        (sphereGaussianDensityFactor24 ((d*m)^24)) (s/4+5) δ ≤ 1 →
      2*(1-(1-74/((a*m:ℕ):ℝ))^24)*
        leechGaussianThetaReal24 (1/(L:ℝ)*leechConservativeRowFactor24) ≤ 1/(L:ℝ) →
      (((d*m)^24:ℕ):ℝ)*Real.exp (-(sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ))*δ^2)) ≤
        1/(L:ℝ) →
      ∃ X : ConfigurationD 24 ((d*m)^24),
        sphereGaussianSmallBudget24 (s/4) X ≤ leechBlockSmallConst24 s ∧
        cellPairSum (shortRangeKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) (s/4+5)) X/
          (((d*m)^24:ℕ):ℝ) ≤ leechBlockTailConst24 s ∧
        ∀ α : ℝ, 1/(L:ℝ) ≤ α → sphereGaussianFullScaled24 α X ≤
          (1+1/(L:ℝ))*(leechGaussianThetaReal24 (α*(1-1/(L:ℝ))^2)+2/(L:ℝ))+
            (1+(L:ℝ))*(leechBlockSmallConst24 s/(L:ℝ)^2) := by
  have hq : 0 < s/4 := by linarith
  have hq24 : s/4 ≤ 24 := by linarith
  have hp0 : -1 ≤ s/4+5 := by linarith
  have hp1 : -1 < s/4+5 := by linarith
  have hp : s/4+5 < 11 := by linarith
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0:ℝ) < L := by linarith
  have hL1 : (1:ℝ) ≤ L := by linarith
  have hη : 0 < 1/(L:ℝ) := one_div_pos.mpr hL0
  have hη1 : 1/(L:ℝ) < 1 := by
    rw [div_lt_one hL0]
    linarith
  have hη0 : 0 < 1-1/(L:ℝ) := by linarith
  have hκ := leechConservativeRowFactor24_pos
  obtain ⟨ρ₁,hρ₁,_,hbudget⟩ := exists_leech_common_budget24
  obtain ⟨ρ₂,hρ₂,_,htail⟩ := leechPatchFamily_shortRange_le
  obtain ⟨ρ₃,hρ₃,_,hwindow⟩ := leechPatchFamily_gaussianWindow_le hη hη1
  refine ⟨min ρ₁ (min ρ₂ ρ₃), lt_min hρ₁ (lt_min hρ₂ hρ₃), ?_⟩
  intro K P a d δ ha hd hδ hv hε hratio hdisj hsep hmassP hcov hKad m hm hn he2 he3 he4 he5
  have hv₁ : ∀ i, ‖(P i).v‖ ≤ ρ₁ := fun i => (hv i).trans (min_le_left _ _)
  have hv₂ : ∀ i, ‖(P i).v‖ ≤ ρ₂ := fun i =>
    (hv i).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hv₃ : ∀ i, ‖(P i).v‖ ≤ ρ₃ := fun i =>
    (hv i).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hε₁ : ∀ i, (P i).ε*equalAreaScaleRadius24 ≤ ρ₁ := fun i =>
    (hε i).trans (min_le_left _ _)
  have hε₂ : ∀ i, (P i).ε*equalAreaScaleRadius24 ≤ ρ₂ := fun i =>
    (hε i).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε₃ : ∀ i, (P i).ε*equalAreaScaleRadius24 ≤ ρ₃ := fun i =>
    (hε i).trans ((min_le_right _ _).trans (min_le_right _ _))
  -- the residual cells of the refinement
  obtain ⟨n, hnpos, hcard, hfrac, C, hCm, hCd, hCmass, hCu⟩ :=
    exists_leech_refinement_cells24 P a d hd hmassP hKad m hm hn
  have hNpos : 0 < (d*m)^24 := by positivity
  have hNR : (0:ℝ) < (((d*m)^24:ℕ):ℝ) := by exact_mod_cast hNpos
  have hc0 : 0 < sphereGaussianDensityFactor24 ((d*m)^24) := sphereGaussianDensityFactor24_pos hNpos
  have ht₀ : 0 ≤ sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ)) :=
    (sphereGaussianScale24_pos hNpos hη).le
  -- one joint residual choice
  obtain ⟨z, hz, havoid, _, hH, hT, hG⟩ := hbudget P hv₁ hε₁ hdisj a d m hd hm hratio hn hnpos
    hcard C hCm hCd hCmass hCu hq hq24 hp0 hp ht₀ (zero_le_one : (0:ℝ) ≤ 1) (sq_nonneg (L:ℝ))
  -- cardinalities as real numbers
  have hM0 : (0:ℝ) ≤ ((Fintype.card (Fin K × (Fin 24 → TwelveNodeIndex (a*m))) : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hMn : ((Fintype.card (Fin K × (Fin 24 → TwelveNodeIndex (a*m))) : ℕ) : ℝ)+(n:ℝ) =
      (((d*m)^24:ℕ):ℝ) := by exact_mod_cast hcard
  have hMN : ((Fintype.card (Fin K × (Fin 24 → TwelveNodeIndex (a*m))) : ℕ) : ℝ) ≤
      (((d*m)^24:ℕ):ℝ) := by
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hMK : ((Fintype.card (Fin K × (Fin 24 → TwelveNodeIndex (a*m))) : ℕ) : ℝ) =
      (K:ℝ)*((a*m:ℕ):ℝ)^24 := by
    rw [Fintype.card_prod, Fintype.card_fin, twelveCubeNode_card 24 (a*m) hn, Nat.cast_mul,
      Nat.cast_pow]
  -- the joint bound is at most N B_s
  have hFg : leechForegroundBudget24 a d m (s/4) ≤
      leechForegroundProfileConst24*(4^(s/4)/(s/4))+
        leechForegroundProfileGain24 (s/4)*(4^(s/4/2)/(s/4/2)) := by
    unfold leechForegroundBudget24
    have hG0 := leechForegroundProfileGain24_nonneg (s/4)
    have hZ0 : 0 ≤ (4:ℝ)^(s/4/2)/(s/4/2) :=
      div_nonneg (Real.rpow_nonneg (by norm_num) _) (by linarith)
    have h1 : leechForegroundProfileGain24 (s/4)*((d:ℝ)/(a:ℝ))^24*((d*m:ℕ):ℝ)^(-(s/4))*
        ((4:ℝ)^(s/4/2)/(s/4/2)) ≤ leechForegroundProfileGain24 (s/4)*((4:ℝ)^(s/4/2)/(s/4/2)) := by
      calc leechForegroundProfileGain24 (s/4)*((d:ℝ)/(a:ℝ))^24*((d*m:ℕ):ℝ)^(-(s/4))*
            ((4:ℝ)^(s/4/2)/(s/4/2))
          = leechForegroundProfileGain24 (s/4)*(((d:ℝ)/(a:ℝ))^24*((d*m:ℕ):ℝ)^(-(s/4)))*
            ((4:ℝ)^(s/4/2)/(s/4/2)) := by ring
        _ ≤ leechForegroundProfileGain24 (s/4)*1*((4:ℝ)^(s/4/2)/(s/4/2)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he2 hG0) hZ0
        _ = _ := by rw [mul_one]
    linarith
  have hnfrac : (n:ℝ) ≤ 1/(L:ℝ)^14*(((d*m)^24:ℕ):ℝ) := by
    have h1 : (n:ℝ)/(((d*m)^24:ℕ):ℝ) < 1/(L:ℝ)^14 := by
      rw [hfrac]
      linarith
    exact ((div_lt_iff₀ hNR).mp h1).le
  have hBcap : (((d*m)^24:ℕ):ℝ)*
      sphereGaussianBackground24 (sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ))) ≤ (L:ℝ)^12 := by
    have h := sphereGaussianBackground24_scaled_cap hNpos hη
    have e : ((1/(L:ℝ))^12)⁻¹ = (L:ℝ)^12 := by rw [one_div, inv_pow, inv_inv]
    rw [e] at h
    exact h
  have hJB : leechJointBound24 ((d*m)^24) n
      ((Fintype.card (Fin K × (Fin 24 → TwelveNodeIndex (a*m))) : ℕ) : ℝ)
      (leechForegroundBudget24 a d m (s/4)) (s/4) (s/4+5)
      (sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ))) 1 ((L:ℝ)^2) ≤
      (((d*m)^24:ℕ):ℝ)*leechBlockSmallConst24 s :=
    leechJointBound24_le hM0 hMn hFg hq hp hL1 hnfrac hBcap
  refine ⟨combinedConfiguration24 (leechFamilyNodes24 P (a*m) hn) z hcard
    (leechFamilyNodes24_injective P hdisj (a*m) hn) hz havoid, ?_, ?_, ?_⟩
  · -- the small-alpha budget
    exact le_of_mul_le_mul_left (hH.trans hJB) hNR
  · -- the short-range cost
    have hsumT := combinedConfiguration24_sum (leechFamilyNodes24 P (a*m) hn) z hcard
      (leechFamilyNodes24_injective P hdisj (a*m) hn) hz havoid
      (shortRangeKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) (s/4+5))
      (shortRangeKernel24_symm _ _)
    have htailP := htail P hv₂ hε₂ hδ hsep a d m ha hd hm hratio hn (s/4+5) hp1
    rw [← hMK] at htailP
    have hTB0 : 0 ≤ leechGaussianTailBudget24
        (leechCorrectedDensityBudgetScale24 leechUnitDensityRadius24) (s/4+5) :=
      leechGaussianTailBudget24_nonneg
        (leechCorrectedDensityBudgetScale24_pos leechUnitDensityRadius24_pos) hp1
    have hsep0 : 0 ≤ separatedShortRangeBound24
        (sphereGaussianDensityFactor24 ((d*m)^24)) (s/4+5) δ :=
      separatedShortRangeBound24_nonneg hc0 hp1 hδ
    unfold cellPairSum leechBlockTailConst24
    rw [hsumT]
    exact leechBlock_tail_arith hNR hM0 hMN hTB0 hsep0 he3 htailP hT hJB
  · -- the window
    intro α hα
    have hαpos : 0 < α := hη.trans_le hα
    have hfull := combinedConfiguration24_fullScaled_le hNpos (leechFamilyNodes24 P (a*m) hn) z
      hcard (leechFamilyNodes24_injective P hdisj (a*m) hn) hz havoid hη.le hα hη
    rw [one_div_one_div] at hfull
    have hw := hwindow P hv₃ hε₃ hδ hsep a d m ha hd hm hratio hn α hαpos
    rw [← hMK] at hw
    -- the three small quantities
    have hθ : leechGaussianThetaReal24 (α*leechConservativeRowFactor24) ≤
        leechGaussianThetaReal24 (1/(L:ℝ)*leechConservativeRowFactor24) :=
      leechGaussianThetaReal24_anti (mul_pos hη hκ) (mul_le_mul_of_nonneg_right hα hκ.le)
    have hθ0 : 0 ≤ leechGaussianThetaReal24 (α*leechConservativeRowFactor24) :=
      zero_le_one.trans (leechGaussianThetaReal24_ge_one (mul_pos hαpos hκ))
    have hA0 : 0 ≤ leechGaussianThetaReal24 (α*(1-1/(L:ℝ))^2) :=
      zero_le_one.trans (leechGaussianThetaReal24_ge_one (mul_pos hαpos (pow_pos hη0 2)))
    have h74 : (74:ℝ) ≤ ((a*m:ℕ):ℝ) := by exact_mod_cast hn
    have hn₀ : (0:ℝ) < ((a*m:ℕ):ℝ) := by linarith
    have hfr0 : 0 ≤ 1-(1-74/((a*m:ℕ):ℝ))^24 := by
      have h1 : 74/((a*m:ℕ):ℝ) ≤ 1 := (div_le_one hn₀).mpr h74
      have h2 : 0 ≤ 74/((a*m:ℕ):ℝ) := div_nonneg (by norm_num) hn₀.le
      have h3 : (1-74/((a*m:ℕ):ℝ))^24 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      linarith
    have hR0 : 0 ≤ 2*(1-(1-74/((a*m:ℕ):ℝ))^24)*
        leechGaussianThetaReal24 (α*leechConservativeRowFactor24) :=
      mul_nonneg (mul_nonneg (by norm_num) hfr0) hθ0
    have hR : 2*(1-(1-74/((a*m:ℕ):ℝ))^24)*
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
        leechBlockSmallConst24 s/(L:ℝ)^2 := by
      rw [div_le_div_iff₀ hNR (pow_pos hL0 2)]
      have h := hG.trans hJB
      linarith
    have h2L : leechGaussianThetaReal24 (α*(1-1/(L:ℝ))^2)+2*(1/(L:ℝ)) =
        leechGaussianThetaReal24 (α*(1-1/(L:ℝ))^2)+2/(L:ℝ) := by rw [mul_one_div]
    rw [h2L] at hfg
    exact hfull.trans (add_le_add
      (mul_le_mul_of_nonneg_left hfg (by positivity))
      (mul_le_mul_of_nonneg_left hres (by positivity)))

/-- The explicit conditions of a block hold for every sufficiently large refinement. -/
theorem leechBlock_conditions_eventually {s : ℝ} (hs : 0 < s) {L : ℕ} (hL : 2 ≤ L) (a d : ℕ)
    (ha : 0 < a) (hd : 0 < d) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, 0 < m ∧ 74 ≤ a*m ∧
      ((d:ℝ)/(a:ℝ))^24*((d*m:ℕ):ℝ)^(-(s/4)) ≤ 1 ∧
      (((d*m)^24:ℕ):ℝ)*separatedShortRangeBound24
        (sphereGaussianDensityFactor24 ((d*m)^24)) (s/4+5) δ ≤ 1 ∧
      2*(1-(1-74/((a*m:ℕ):ℝ))^24)*
        leechGaussianThetaReal24 (1/(L:ℝ)*leechConservativeRowFactor24) ≤ 1/(L:ℝ) ∧
      (((d*m)^24:ℕ):ℝ)*Real.exp (-(sphereGaussianScale24 ((d*m)^24) (1/(L:ℝ))*δ^2)) ≤
        1/(L:ℝ) := by
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0:ℝ) < L := by linarith
  have hη : 0 < 1/(L:ℝ) := one_div_pos.mpr hL0
  have hΓ : 0 < Real.Gamma (s/4+5+1) := Real.Gamma_pos_of_pos (by linarith)
  have hδ2 : 0 < δ^2 := pow_pos hδ 2
  -- sizes
  have hdm : Tendsto (fun m : ℕ => d*m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m hd) tendsto_id
  have ham : Tendsto (fun m : ℕ => a*m) atTop atTop :=
    tendsto_atTop_mono (fun m => Nat.le_mul_of_pos_left m ha) tendsto_id
  have hNt0 : Tendsto (fun m : ℕ => (d*m)^24) atTop atTop :=
    tendsto_atTop_mono (fun m => (Nat.le_mul_of_pos_left m hd).trans
      (Nat.le_self_pow (by norm_num) _)) tendsto_id
  have hNt : Tendsto (fun m : ℕ => (d*(m+1))^24) atTop atTop :=
    tendsto_atTop_mono (fun m => (Nat.le_succ m).trans
      ((Nat.le_mul_of_pos_left (m+1) hd).trans (Nat.le_self_pow (by norm_num) _))) tendsto_id
  have hNp : ∀ m : ℕ, 0 < (d*(m+1))^24 := fun m => by positivity
  -- the gain of the small-alpha profile
  have h2 : Tendsto (fun m : ℕ => ((d:ℝ)/(a:ℝ))^24*((d*m:ℕ):ℝ)^(-(s/4))) atTop (𝓝 0) := by
    have hcast : Tendsto (fun m : ℕ => ((d*m:ℕ):ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hdm
    have h := ((tendsto_rpow_neg_atTop (by linarith : (0:ℝ) < s/4)).comp hcast).const_mul
      (((d:ℝ)/(a:ℝ))^24)
    simpa only [mul_zero, Function.comp_apply] using h
  have e2 := (tendsto_order.mp h2).2 1 one_pos
  -- the separated short-range bound
  have h3 : Tendsto (fun m : ℕ => (((d*m)^24:ℕ):ℝ)*
      Real.exp (-(sphereGaussianScale24 ((d*m)^24) (1/2)*δ^2))) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mp
      (sphereGaussianScale24_separated_tendsto hNt hNp (by norm_num : (0:ℝ) < 1/2) hδ)
  have h3g : Tendsto (fun m : ℕ => (((d*m)^24:ℕ):ℝ)*
      Real.exp (-(sphereGaussianScale24 ((d*m)^24) (1/2)*δ^2))*Real.Gamma (s/4+5+1))
      atTop (𝓝 0) := by
    simpa only [zero_mul] using h3.mul_const (Real.Gamma (s/4+5+1))
  have e3a := (tendsto_order.mp h3g).2 1 one_pos
  have e3b := (tendsto_atTop.mp
    (sphereGaussianScale24_tendsto hNt0 (by norm_num : (0:ℝ) < 1/2))) (1/δ^2)
  -- the corrected fraction
  have h4 : Tendsto (fun m : ℕ => 2*(1-(1-74/((a*m:ℕ):ℝ))^24)*
      leechGaussianThetaReal24 (1/(L:ℝ)*leechConservativeRowFactor24)) atTop (𝓝 0) := by
    have hcast : Tendsto (fun m : ℕ => ((a*m:ℕ):ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp ham
    have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h74 : Tendsto (fun _ : ℕ => (74:ℝ)) atTop (𝓝 74) := tendsto_const_nhds
    have hx : Tendsto (fun m : ℕ => (74:ℝ)/((a*m:ℕ):ℝ)) atTop (𝓝 0) := h74.div_atTop hcast
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
  filter_upwards [eventually_ge_atTop 74, e2, e3a, e3b, e4, e5] with m hm1 hm2 hm3a hm3b hm4 hm5
  refine ⟨by omega, hm1.trans (Nat.le_mul_of_pos_left m ha), hm2.le, ?_, hm4.le, hm5.le⟩
  have hx : sphereGaussianScale24 ((d*m)^24) (1/2)*δ^2 =
      sphereGaussianDensityFactor24 ((d*m)^24)*δ^2/2 := by
    rw [sphereGaussianScale24_eq_factor]
    ring
  have hx1 : 1 ≤ sphereGaussianDensityFactor24 ((d*m)^24)*δ^2/2 := by
    rw [← hx]
    exact (div_le_iff₀ hδ2).mp hm3b
  have hx0 : 0 < sphereGaussianDensityFactor24 ((d*m)^24)*δ^2/2 := by linarith
  have hpow : (1/(sphereGaussianDensityFactor24 ((d*m)^24)*δ^2/2))^(s/4+5+1) ≤ 1 :=
    Real.rpow_le_one (one_div_nonneg.mpr hx0.le) ((div_le_one hx0).mpr hx1) (by linarith)
  rw [hx] at hm3a
  unfold separatedShortRangeBound24
  calc (((d*m)^24:ℕ):ℝ)*(Real.exp (-(sphereGaussianDensityFactor24 ((d*m)^24)*δ^2/2))*
        ((1/(sphereGaussianDensityFactor24 ((d*m)^24)*δ^2/2))^(s/4+5+1)*Real.Gamma (s/4+5+1)))
      ≤ (((d*m)^24:ℕ):ℝ)*(Real.exp (-(sphereGaussianDensityFactor24 ((d*m)^24)*δ^2/2))*
        (1*Real.Gamma (s/4+5+1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpow hΓ.le) (Real.exp_pos _).le) (Nat.cast_nonneg _)
    _ = (((d*m)^24:ℕ):ℝ)*Real.exp (-(sphereGaussianDensityFactor24 ((d*m)^24)*δ^2/2))*
        Real.Gamma (s/4+5+1) := by ring
    _ ≤ 1 := hm3a.le

/-- For every tolerance index there is a denominator `d` such that every sufficiently large
refinement carries a block configuration. -/
theorem exists_leech_block24 {s : ℝ} (hs : 0 < s) (hs24 : s < 24) {L : ℕ} (hL : 2 ≤ L) :
    ∃ d : ℕ, 0 < d ∧ ∀ᶠ m : ℕ in atTop, ∃ X : ConfigurationD 24 ((d*m)^24),
      sphereGaussianSmallBudget24 (s/4) X ≤ leechBlockSmallConst24 s ∧
      cellPairSum (shortRangeKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) (s/4+5)) X/
        (((d*m)^24:ℕ):ℝ) ≤ leechBlockTailConst24 s ∧
      ∀ α : ℝ, 1/(L:ℝ) ≤ α → sphereGaussianFullScaled24 α X ≤
        (1+1/(L:ℝ))*(leechGaussianThetaReal24 (α*(1-1/(L:ℝ))^2)+2/(L:ℝ))+
          (1+(L:ℝ))*(leechBlockSmallConst24 s/(L:ℝ)^2) := by
  obtain ⟨ρ, hρ, hblock⟩ := exists_leech_block_configuration24 hs hs24 hL
  have hLR : (2:ℝ) ≤ L := by exact_mod_cast hL
  have hL0 : (0:ℝ) < L := by linarith
  obtain ⟨K, P, a, d, δ, ha, hd, hδ, hv, hε, hratio, hdisj, hsep, hmassP, hcov, hKad⟩ :=
    exists_leech_patch_family24 ρ (1/(L:ℝ)^14) hρ (one_div_pos.mpr (pow_pos hL0 14))
  refine ⟨d, hd, ?_⟩
  filter_upwards [leechBlock_conditions_eventually hs hL a d ha hd hδ] with m hm
  obtain ⟨hm0, hn, he2, he3, he4, he5⟩ := hm
  exact hblock P a d ha hd hδ hv hε hratio hdisj hsep hmassP hcov hKad m hm0 hn he2 he3 he4 he5

end LeechBlock

section LeechSharpUpper
open Set MeasureTheory Filter
open scoped Topology

/-! ### LeechSharpUpper

Sharp upper bound for the Riesz energy on S²⁴ at every large `N`, for all `0 < s < 24`.

For every tolerance index the block construction gives actual configurations at all rational
sizes `(d m)²⁴` with common Gaussian budgets and a window bound which tends to the Leech theta
profile.  A diagonal choice over the tolerance index gives one configuration of size
`M(N) ≥ N`, `M(N)/N → 1`, for every large `N`; the Gaussian-only bridge bounds its normalized
Riesz energy by the regularized-theta coefficient.  A subconfiguration of `N` points keeps the
normalized energy up to the factor `(N/M)^(1-s/24) → 1`.

No Gaussian certificate, no lower bound and no CKMRV input is used: this is the upper half only.
The coefficient is the regularized theta Mellin integral `sphereRieszCoefficient24`; its Epstein
form is not identified here. -/

/-- The ordered off-diagonal Riesz energy as a full pair sum with zero diagonal. -/
theorem energyRpowD_eq_orderedPair (s : ℝ) {d N : ℕ} (X : ConfigurationD d N) :
    energyRpowD s X =
      finiteOrderedPair (fun i j : Fin N => if i = j then (0:ℝ) else (dist (X i) (X j))^(-s)) := by
  unfold energyRpowD finiteOrderedPair
  refine Finset.sum_congr rfl fun i _ => ?_
  show (∑ j ∈ Finset.univ.erase i, (dist (X i) (X j))^(-s)) =
    ∑ j : Fin N, (if i = j then (0:ℝ) else (dist (X i) (X j))^(-s))
  rw [← Finset.add_sum_erase Finset.univ
    (fun j : Fin N => if i = j then (0:ℝ) else (dist (X i) (X j))^(-s)) (Finset.mem_univ i),
    if_pos rfl, zero_add]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [if_neg (Finset.ne_of_mem_erase hj).symm]

theorem energyRpowD_nonneg (s : ℝ) {d N : ℕ} (X : ConfigurationD d N) : 0 ≤ energyRpowD s X := by
  unfold energyRpowD
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Real.rpow_nonneg dist_nonneg _

/-- A subconfiguration of `N` points whose Riesz energy is at most `(N/M)²` times the energy of
the whole configuration. -/
theorem energyRpowD_exists_subconfiguration (s : ℝ) {d : ℕ} (N M : ℕ) (hN : 2 ≤ N)
    (hNM : N ≤ M) (X : ConfigurationD d M) :
    ∃ e : Fin N ↪ Fin M, energyRpowD s (e.trans X) ≤ ((N:ℝ)/(M:ℝ))^2*energyRpowD s X := by
  obtain ⟨e, he⟩ := finiteOrderedPair_exists_subembedding N M hN hNM
    (fun i j : Fin M => if i = j then (0:ℝ) else (dist (X i) (X j))^(-s))
    (fun i j => by
      show (if i = j then (0:ℝ) else (dist (X i) (X j))^(-s)) =
        if j = i then (0:ℝ) else (dist (X j) (X i))^(-s)
      by_cases h : i = j
      · subst h
        rfl
      · rw [if_neg h, if_neg (Ne.symm h), dist_comm])
    (fun i => if_pos rfl)
  refine ⟨e, ?_⟩
  have hX := energyRpowD_eq_orderedPair s X
  have hY : energyRpowD s (e.trans X) = finiteOrderedPair (fun i j : Fin N =>
      if e i = e j then (0:ℝ) else (dist (X (e i)) (X (e j)))^(-s)) := by
    rw [energyRpowD_eq_orderedPair]
    unfold finiteOrderedPair
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    show (if i = j then (0:ℝ) else (dist ((e.trans X) i) ((e.trans X) j))^(-s)) =
      if e i = e j then (0:ℝ) else (dist (X (e i)) (X (e j)))^(-s)
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, if_pos rfl]
    · have h' : e i ≠ e j := fun he' => h (e.injective he')
      rw [if_neg h, if_neg h']
      rfl
  have he' : energyRpowD s (e.trans X)/((N:ℝ)*(N-1)) ≤ energyRpowD s X/((M:ℝ)*(M-1)) := by
    rw [hY, hX]
    exact he
  have hn : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hnm : (N:ℝ) ≤ M := by exact_mod_cast hNM
  have hm : (0:ℝ) < M := by linarith
  have h1 : 0 < (N:ℝ)*(N-1) := mul_pos (by linarith) (by linarith)
  have h2 : 0 < (M:ℝ)*(M-1) := mul_pos hm (by linarith)
  have hE0 := energyRpowD_nonneg s X
  have hh := (div_le_iff₀ h1).mp he'
  have hcoef : ((N:ℝ)*(N-1))/((M:ℝ)*(M-1)) ≤ ((N:ℝ)/(M:ℝ))^2 := by
    rw [div_pow]
    apply (div_le_div_iff₀ h2 (sq_pos_of_pos hm)).mpr
    have hprod := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ N) hm.le) (sub_nonneg.mpr hnm)
    nlinarith
  calc energyRpowD s (e.trans X) ≤ energyRpowD s X/((M:ℝ)*(M-1))*((N:ℝ)*(N-1)) := hh
    _ = ((N:ℝ)*(N-1))/((M:ℝ)*(M-1))*energyRpowD s X := by ring
    _ ≤ ((N:ℝ)/(M:ℝ))^2*energyRpowD s X := mul_le_mul_of_nonneg_right hcoef hE0

/-- A subconfiguration of `N` points keeps the normalized Riesz energy on S²⁴ up to the factor
`(N/M)^(1-s/24)`. -/
theorem normalizedEnergyRpow24_exists_subconfiguration (s : ℝ) (N M : ℕ) (hN : 2 ≤ N)
    (hNM : N ≤ M) (X : ConfigurationD 24 M) :
    ∃ Y : ConfigurationD 24 N, normalizedEnergyRpow24 s Y ≤
      ((N:ℝ)/(M:ℝ))^(1-s/24)*normalizedEnergyRpow24 s X := by
  obtain ⟨e, he⟩ := energyRpowD_exists_subconfiguration s N M hN hNM X
  refine ⟨e.trans X, ?_⟩
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hr : 0 < (N:ℝ)/(M:ℝ) := div_pos hn hm
  have hNp : 0 < (N:ℝ)^(1+s/24) := Real.rpow_pos_of_pos hn _
  have hMp : 0 < (M:ℝ)^(1+s/24) := Real.rpow_pos_of_pos hm _
  have hcancel : ((N:ℝ)/(M:ℝ))^2*(M:ℝ)^2 = (N:ℝ)^2 := by
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hm.ne')]
  have he' : energyRpowD s (e.trans X)-sphereRieszConst24 s*(N:ℝ)^2 ≤
      ((N:ℝ)/(M:ℝ))^2*(energyRpowD s X-sphereRieszConst24 s*(M:ℝ)^2) := by
    have hexp : ((N:ℝ)/(M:ℝ))^2*(energyRpowD s X-sphereRieszConst24 s*(M:ℝ)^2) =
        ((N:ℝ)/(M:ℝ))^2*energyRpowD s X-sphereRieszConst24 s*(((N:ℝ)/(M:ℝ))^2*(M:ℝ)^2) := by
      ring
    rw [hexp, hcancel]
    linarith
  have hNpow : (N:ℝ)^(1+s/24) = ((N:ℝ)/(M:ℝ))^(1+s/24)*(M:ℝ)^(1+s/24) := by
    rw [← Real.mul_rpow hr.le hm.le, div_mul_cancel₀ _ hm.ne']
  have hr2 : ((N:ℝ)/(M:ℝ))^(1-s/24)*((N:ℝ)/(M:ℝ))^(1+s/24) = ((N:ℝ)/(M:ℝ))^2 := by
    rw [← Real.rpow_add hr, show (1-s/24)+(1+s/24) = (2:ℝ) by ring]
    exact Real.rpow_two _
  have hpow : ((N:ℝ)/(M:ℝ))^2/(N:ℝ)^(1+s/24) =
      ((N:ℝ)/(M:ℝ))^(1-s/24)/(M:ℝ)^(1+s/24) := by
    rw [div_eq_div_iff hNp.ne' hMp.ne', hNpow, ← hr2]
    ring
  unfold normalizedEnergyRpow24
  calc (energyRpowD s (e.trans X)-sphereRieszConst24 s*(N:ℝ)^2)/(N:ℝ)^(1+s/24)
      ≤ (((N:ℝ)/(M:ℝ))^2*(energyRpowD s X-sphereRieszConst24 s*(M:ℝ)^2))/(N:ℝ)^(1+s/24) :=
        div_le_div_of_nonneg_right he' hNp.le
    _ = ((N:ℝ)/(M:ℝ))^2/(N:ℝ)^(1+s/24)*(energyRpowD s X-sphereRieszConst24 s*(M:ℝ)^2) := by
        ring
    _ = ((N:ℝ)/(M:ℝ))^(1-s/24)*
        ((energyRpowD s X-sphereRieszConst24 s*(M:ℝ)^2)/(M:ℝ)^(1+s/24)) := by
        rw [hpow]
        ring

/-- The window bound of the blocks tends to the Leech theta profile. -/
theorem leechBlockWindowBound_tendsto {α B : ℝ} (hα : 0 < α) {L : ℕ → ℕ}
    (hL : Tendsto L atTop atTop) :
    Tendsto (fun k => (1+1/(L k:ℝ))*(leechGaussianThetaReal24 (α*(1-1/(L k:ℝ))^2)+2/(L k:ℝ))+
      (1+(L k:ℝ))*(B/(L k:ℝ)^2)) atTop (𝓝 (leechGaussianThetaReal24 α)) := by
  have hLR : Tendsto (fun k => (L k:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hL
  have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have htwo : Tendsto (fun _ : ℕ => (2:ℝ)) atTop (𝓝 2) := tendsto_const_nhds
  have hBc : Tendsto (fun _ : ℕ => B) atTop (𝓝 B) := tendsto_const_nhds
  have hu : Tendsto (fun k => 1/(L k:ℝ)) atTop (𝓝 0) := hone.div_atTop hLR
  have h2u : Tendsto (fun k => 2/(L k:ℝ)) atTop (𝓝 0) := htwo.div_atTop hLR
  have hBL : Tendsto (fun k => B/(L k:ℝ)) atTop (𝓝 0) := hBc.div_atTop hLR
  have hBsq : Tendsto (fun k => B/(L k:ℝ)^2) atTop (𝓝 0) :=
    hBc.div_atTop ((tendsto_pow_atTop (two_ne_zero)).comp hLR)
  have harg : Tendsto (fun k => α*(1-1/(L k:ℝ))^2) atTop (𝓝 (α*(1-0)^2)) :=
    ((hone.sub hu).pow 2).const_mul α
  have hc : ContinuousAt leechGaussianThetaReal24 (α*(1-0)^2) :=
    leechGaussianThetaReal24_continuousOn.continuousAt
      (isOpen_Ioi.mem_nhds (by simpa using hα))
  have hθ : Tendsto (fun k => leechGaussianThetaReal24 (α*(1-1/(L k:ℝ))^2)) atTop
      (𝓝 (leechGaussianThetaReal24 (α*(1-0)^2))) := hc.tendsto.comp harg
  have hsum := ((hone.add hu).mul (hθ.add h2u)).add (hBsq.add hBL)
  have hlim : (1+0)*(leechGaussianThetaReal24 (α*(1-0)^2)+0)+((0:ℝ)+0) =
      leechGaussianThetaReal24 α := by norm_num
  rw [hlim] at hsum
  refine hsum.congr' ?_
  filter_upwards [hL.eventually (eventually_gt_atTop 0)] with k hk
  have hLne : (L k:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have h1 : (L k:ℝ)*(B/(L k:ℝ)^2) = B/(L k:ℝ) := by
    rw [← mul_div_assoc, sq, mul_div_mul_left _ _ hLne]
  have h2 : (1+(L k:ℝ))*(B/(L k:ℝ)^2) = B/(L k:ℝ)^2+B/(L k:ℝ) := by
    rw [add_mul, one_mul, h1]
  rw [h2]

/-- Sharp upper bound on S²⁴ at every large `N`: actual configurations whose normalized Riesz
energy is at most the regularized-theta coefficient plus `η`. -/
theorem sphere24_riesz_sharp_upper_allN {s : ℝ} (hs : 0 < s) (hs24 : s < 24) (η : ℝ)
    (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 24 N,
      normalizedEnergyRpow24 s Y ≤ sphereRieszCoefficient24 s+η := by
  -- blocks for every tolerance index
  have hblocks : ∀ j : ℕ, ∃ d : ℕ, 0 < d ∧ ∀ᶠ m : ℕ in atTop,
      ∃ X : ConfigurationD 24 ((d*m)^24),
        sphereGaussianSmallBudget24 (s/4) X ≤ leechBlockSmallConst24 s ∧
        cellPairSum (shortRangeKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) (s/4+5)) X/
          (((d*m)^24:ℕ):ℝ) ≤ leechBlockTailConst24 s ∧
        ∀ α : ℝ, 1/((j+2:ℕ):ℝ) ≤ α → sphereGaussianFullScaled24 α X ≤
          (1+1/((j+2:ℕ):ℝ))*(leechGaussianThetaReal24 (α*(1-1/((j+2:ℕ):ℝ))^2)+2/((j+2:ℕ):ℝ))+
            (1+((j+2:ℕ):ℝ))*(leechBlockSmallConst24 s/((j+2:ℕ):ℝ)^2) :=
    fun j => exists_leech_block24 hs hs24 (L := j+2) (by omega)
  choose d hd hev using hblocks
  -- every tolerance index reaches every large N
  have hP : ∀ j : ℕ, ∀ᶠ N : ℕ in atTop,
      (rationalSizeCeiling24 (d j) N:ℝ)/(N:ℝ) ≤ 1+1/((j:ℝ)+1) ∧
      ∃ X : ConfigurationD 24 (rationalSizeCeiling24 (d j) N),
        sphereGaussianSmallBudget24 (s/4) X ≤ leechBlockSmallConst24 s ∧
        cellPairSum (shortRangeKernel24
          (sphereGaussianDensityFactor24 (rationalSizeCeiling24 (d j) N)) (s/4+5)) X/
          ((rationalSizeCeiling24 (d j) N:ℕ):ℝ) ≤ leechBlockTailConst24 s ∧
        ∀ α : ℝ, 1/((j+2:ℕ):ℝ) ≤ α → sphereGaussianFullScaled24 α X ≤
          (1+1/((j+2:ℕ):ℝ))*(leechGaussianThetaReal24 (α*(1-1/((j+2:ℕ):ℝ))^2)+2/((j+2:ℕ):ℝ))+
            (1+((j+2:ℕ):ℝ))*(leechBlockSmallConst24 s/((j+2:ℕ):ℝ)^2) := by
    intro j
    have h1 := (rationalSizeIndex24_tendsto (d j) (hd j)).eventually (hev j)
    have hgap : (1:ℝ) < 1+1/((j:ℝ)+1) := by
      have : (0:ℝ) < 1/((j:ℝ)+1) := by positivity
      linarith
    have h2 := (tendsto_order.mp (rationalSizeCeiling24_ratio_tendsto (d j) (hd j))).2 _ hgap
    filter_upwards [h1, h2] with N hN1 hN2
    exact ⟨hN2.le, hN1⟩
  obtain ⟨J, hJt, hJ⟩ := exists_diagonal_eventually hP
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hJ
  obtain ⟨N₂, hN₂1, hN₂2⟩ : ∃ N₂ : ℕ, N₁ ≤ N₂ ∧ 2 ≤ N₂ :=
    ⟨max N₁ 2, le_max_left _ _, le_max_right _ _⟩
  -- one configuration for every index k, of size M k ≥ N₂ + k
  have hQ := fun k : ℕ => hN₁ (N₂+k) (hN₂1.trans (Nat.le_add_right N₂ k))
  choose hratio Z hZ1 hZ2 hZ3 using hQ
  have hge : ∀ k : ℕ, N₂+k ≤ rationalSizeCeiling24 (d (J (N₂+k))) (N₂+k) := fun k =>
    rationalSizeCeiling24_ge _ _ (hd _)
  have hMt : Tendsto (fun k : ℕ => rationalSizeCeiling24 (d (J (N₂+k))) (N₂+k)) atTop atTop :=
    tendsto_atTop_mono (fun k => (Nat.le_add_left k N₂).trans (hge k)) tendsto_id
  have hMpos : ∀ k : ℕ, 0 < rationalSizeCeiling24 (d (J (N₂+k))) (N₂+k) := fun k =>
    lt_of_lt_of_le (by omega) (hge k)
  have hidx : Tendsto (fun k : ℕ => N₂+k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_add_left k N₂) tendsto_id
  have hLt : Tendsto (fun k : ℕ => J (N₂+k)+2) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_add_right (J (N₂+k)) 2) (hJt.comp hidx)
  -- the pointwise window
  have hp : ∀ α : ℝ, 0 < α → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      sphereGaussianFullScaled24 α (Z k) ≤ leechGaussianThetaReal24 α+ε := by
    intro α hα ε hε
    have hΦ := leechBlockWindowBound_tendsto (B := leechBlockSmallConst24 s) hα hLt
    have e1 := (tendsto_order.mp hΦ).2 (leechGaussianThetaReal24 α+ε) (by linarith)
    have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hu : Tendsto (fun k : ℕ => 1/((J (N₂+k)+2:ℕ):ℝ)) atTop (𝓝 0) :=
      hone.div_atTop (tendsto_natCast_atTop_atTop.comp hLt)
    have e2 := (tendsto_order.mp hu).2 α hα
    filter_upwards [e1, e2] with k hk1 hk2
    exact (hZ3 k α hk2.le).trans hk1.le
  have hfin := sphere24_riesz_upper_of_gaussian_budgets hs hs24 hMt hMpos Z
    (leechBlockSmallConst24 s) (leechBlockTailConst24 s) hZ1 hZ2 hp (η/2) (half_pos hη)
  -- the size ratio tends to one
  have hNk : ∀ k : ℕ, (0:ℝ) < ((N₂+k:ℕ):ℝ) := fun k => by
    exact_mod_cast (show 0 < N₂+k by omega)
  have hratio_lower : ∀ k : ℕ, (1:ℝ) ≤
      (rationalSizeCeiling24 (d (J (N₂+k))) (N₂+k):ℝ)/((N₂+k:ℕ):ℝ) := fun k => by
    rw [le_div_iff₀ (hNk k), one_mul]
    exact_mod_cast hge k
  have hupper : Tendsto (fun k : ℕ => 1+1/((J (N₂+k):ℝ)+1)) atTop (𝓝 1) := by
    have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hJR : Tendsto (fun k : ℕ => (J (N₂+k):ℝ)+1) atTop atTop :=
      tendsto_atTop_mono
        (fun k => (le_add_of_nonneg_right zero_le_one : (J (N₂+k):ℝ) ≤ (J (N₂+k):ℝ)+1))
        (tendsto_natCast_atTop_atTop.comp (hJt.comp hidx))
    have h := hone.add (hone.div_atTop hJR)
    rw [add_zero] at h
    exact h
  have hratio_t : Tendsto (fun k : ℕ =>
      (rationalSizeCeiling24 (d (J (N₂+k))) (N₂+k):ℝ)/((N₂+k:ℕ):ℝ)) atTop (𝓝 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper hratio_lower hratio
  have hinv_t : Tendsto (fun k : ℕ =>
      ((N₂+k:ℕ):ℝ)/(rationalSizeCeiling24 (d (J (N₂+k))) (N₂+k):ℝ)) atTop (𝓝 1) := by
    simpa only [inv_div, inv_one] using hratio_t.inv₀ one_ne_zero
  have hpow_t : Tendsto (fun k : ℕ =>
      (((N₂+k:ℕ):ℝ)/(rationalSizeCeiling24 (d (J (N₂+k))) (N₂+k):ℝ))^(1-s/24)) atTop (𝓝 1) := by
    have h := hinv_t.rpow_const (p := 1-s/24) (Or.inl one_ne_zero)
    rw [Real.one_rpow] at h
    exact h
  have hprod_t : Tendsto (fun k : ℕ =>
      (((N₂+k:ℕ):ℝ)/(rationalSizeCeiling24 (d (J (N₂+k))) (N₂+k):ℝ))^(1-s/24)*
        (sphereRieszCoefficient24 s+η/2)) atTop (𝓝 (sphereRieszCoefficient24 s+η/2)) := by
    have h := hpow_t.mul_const (sphereRieszCoefficient24 s+η/2)
    rw [one_mul] at h
    exact h
  have e3 := (tendsto_order.mp hprod_t).2 (sphereRieszCoefficient24 s+η) (by linarith)
  -- subconfigurations of every large size
  have hall : ∀ᶠ k : ℕ in atTop, ∃ Y : ConfigurationD 24 (N₂+k),
      normalizedEnergyRpow24 s Y ≤ sphereRieszCoefficient24 s+η := by
    filter_upwards [hfin, e3] with k hk1 hk3
    obtain ⟨Y, hY⟩ := normalizedEnergyRpow24_exists_subconfiguration s (N₂+k)
      (rationalSizeCeiling24 (d (J (N₂+k))) (N₂+k)) (by omega) (hge k) (Z k)
    refine ⟨Y, hY.trans ?_⟩
    have hr0 : 0 ≤ (((N₂+k:ℕ):ℝ)/(rationalSizeCeiling24 (d (J (N₂+k))) (N₂+k):ℝ))^(1-s/24) :=
      Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _
    exact (mul_le_mul_of_nonneg_left hk1 hr0).trans hk3.le
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hall
  refine ⟨N₂+k₀, fun N hN => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, N = N₂+k := Nat.exists_eq_add_of_le (by omega)
  exact hk₀ k (by omega)

/-- The sharp upper bound at every large `N` in the original ordered-pair normalization, with
the actual uniform double integral.  No hypothesis is used. -/
theorem sphere24_riesz_sharp_upper_conjecture_form {s : ℝ} (hs : 0 < s) (hs24 : s < 24) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 24 N,
      (energyRpowD s Y-(∫ p : SphereD 24 × SphereD 24, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 24).prod (sphereProbabilityD 24)))*(N:ℝ)^2)/(N:ℝ)^(1+s/24) ≤
        sphereRieszCoefficient24 s+η := by
  intro η hη
  obtain ⟨N₀, h⟩ := sphere24_riesz_sharp_upper_allN hs hs24 η hη
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨Y, hY⟩ := h N hN
  refine ⟨Y, ?_⟩
  rwa [normalizedEnergyRpow24, sphereRieszConst24_eq_pair_integral hs hs24] at hY

/-- Two-sided sharp asymptotics on S²⁴ for every `0 < s < 24`, with the regularized-theta Mellin
coefficient and the actual uniform double integral.  The lower half assumes all-scale Leech
contact certificates (the CKMRV input); the upper half is unconditional. -/
theorem sphere24_riesz_sharp_asymptotic_all
    (hG24 : ∀ β : ℝ, 0 < β → ∃ f, LeechGaussianContactCertificate24 β f)
    {s : ℝ} (hs : 0 < s) (hs24 : s < 24) :
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 24 N,
      sphereRieszCoefficient24 s-η ≤
        (energyRpowD s X-(∫ p : SphereD 24 × SphereD 24, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 24).prod (sphereProbabilityD 24)))*(N:ℝ)^2)/(N:ℝ)^(1+s/24)) ∧
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 24 N,
      (energyRpowD s Y-(∫ p : SphereD 24 × SphereD 24, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 24).prod (sphereProbabilityD 24)))*(N:ℝ)^2)/(N:ℝ)^(1+s/24) ≤
        sphereRieszCoefficient24 s+η) :=
  ⟨sphere24_riesz_sharp_lower_conjecture_form hG24 hs hs24,
    sphere24_riesz_sharp_upper_conjecture_form hs hs24⟩

/-- The sharp upper bound at every large `N` with the Epstein coefficient `A₂₄^(-s/24) ζ_Λ(s)` of
the Leech lattice.  No hypothesis is used. -/
theorem sphere24_riesz_sharp_upper_epstein {s : ℝ} (hs : 0 < s) (hs24 : s < 24) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 24 N,
      (energyRpowD s Y-(∫ p : SphereD 24 × SphereD 24, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 24).prod (sphereProbabilityD 24)))*(N:ℝ)^2)/(N:ℝ)^(1+s/24) ≤
        ((sphereAreaD 24).real univ)^(-(s/24))*(leechEpsteinZeta ((s/2:ℝ):ℂ)).re+η := by
  rw [← sphereRieszCoefficient24_eq_epstein hs hs24]
  exact sphere24_riesz_sharp_upper_conjecture_form hs hs24

/-- Two-sided sharp asymptotics on S²⁴ for every `0 < s < 24` with the Epstein coefficient
`A₂₄^(-s/24) ζ_Λ(s)` of the Leech lattice (the conjectured form of the second-order term).  The
lower half assumes all-scale Leech contact certificates; the upper half is unconditional. -/
theorem sphere24_riesz_sharp_asymptotic_epstein
    (hG24 : ∀ β : ℝ, 0 < β → ∃ f, LeechGaussianContactCertificate24 β f)
    {s : ℝ} (hs : 0 < s) (hs24 : s < 24) :
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : ConfigurationD 24 N,
      ((sphereAreaD 24).real univ)^(-(s/24))*(leechEpsteinZeta ((s/2:ℝ):ℂ)).re-η ≤
        (energyRpowD s X-(∫ p : SphereD 24 × SphereD 24, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 24).prod (sphereProbabilityD 24)))*(N:ℝ)^2)/(N:ℝ)^(1+s/24)) ∧
    (∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ Y : ConfigurationD 24 N,
      (energyRpowD s Y-(∫ p : SphereD 24 × SphereD 24, (dist p.1 p.2)^(-s)
          ∂((sphereProbabilityD 24).prod (sphereProbabilityD 24)))*(N:ℝ)^2)/(N:ℝ)^(1+s/24) ≤
        ((sphereAreaD 24).real univ)^(-(s/24))*(leechEpsteinZeta ((s/2:ℝ):ℂ)).re+η) :=
  ⟨sphere24_riesz_sharp_lower_epstein hG24 hs hs24, sphere24_riesz_sharp_upper_epstein hs hs24⟩

end LeechSharpUpper

end SphericalRiesz
