import Riesz.LeechJointResidual24

/-! Common Gaussian budgets of an actual configuration on S²⁴.

A twelfth-order foreground family of one common scale and one point in every residual cell form
an actual configuration of `N = (d m)^24` distinct points.  One joint residual choice gives

* the small-alpha budget `N H_q(Z) ≤ B`,
* the weighted residual and residual/foreground short-range cost `w₂ (…) ≤ B`,
* the weighted Gaussian window among the residual points `w₃ (…) ≤ B`,

with the common explicit right side `B = N·Fg + n (4^q/q + w₃) + w₂ (2M+n)/(11-p) + w₃ n N B(t₀)`.
The foreground part `Fg` consists of a family-independent constant and a term which vanishes
under refinement.  The foreground short-range cost, the sharp foreground profile, the family
itself and the attaining sequence are not constructed here. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SphericalRiesz
open Boundary

theorem leechFamilyNodes24_injective {K : ℕ} (P : Fin K → SmallLeechCubePatch24)
    (hdisj : Pairwise (fun i j => Disjoint (smallLeechSpherePatch24 (P i))
      (smallLeechSpherePatch24 (P j)))) (n : ℕ) (hn : 74 ≤ n) :
    Function.Injective (leechFamilyNodes24 P n hn) := by
  rintro ⟨i,u⟩ ⟨j,w⟩ h
  change smallLeechPatchNodes24 (P i) n hn u = smallLeechPatchNodes24 (P j) n hn w at h
  have hij : i = j := by
    by_contra hne
    have hi := smallLeechPatchNodes24_mem (P i) n hn u
    have hj := smallLeechPatchNodes24_mem (P j) n hn w
    rw [← h] at hj
    exact Set.disjoint_left.mp (hdisj hne) hi hj
  subst hij
  rw [smallLeechPatchNodes24_injective (P i) n hn h]

/-- Foreground and residual points as one configuration of `N` points. -/
def combinedConfiguration24 {ι : Type*} [Fintype ι] {n N : ℕ} (x : ι → SphereD 24)
    (z : Fin n → SphereD 24) (hcard : Fintype.card ι+n = N) (hx : Function.Injective x)
    (hz : Function.Injective z) (havoid : ∀ j, z j ∉ range x) : ConfigurationD 24 N where
  toFun i := Sum.elim x z ((Fintype.equivFinOfCardEq
    (show Fintype.card (ι ⊕ Fin n) = N by
      rw [Fintype.card_sum, Fintype.card_fin, hcard])).symm i)
  inj' := (Function.Injective.sumElim hx hz (fun a b h => havoid b ⟨a, h⟩)).comp
    (Equiv.injective _)

/-- Pair sums of a combined configuration split into foreground, cross and residual pairs. -/
theorem combinedConfiguration24_sum {ι : Type*} [Fintype ι] {n N : ℕ} (x : ι → SphereD 24)
    (z : Fin n → SphereD 24) (hcard : Fintype.card ι+n = N) (hx : Function.Injective x)
    (hz : Function.Injective z) (havoid : ∀ j, z j ∉ range x)
    (k : SphereD 24 → SphereD 24 → ℝ) (hs : ∀ a b, k a b = k b a) :
    (∑ i, ∑ j, k (combinedConfiguration24 x z hcard hx hz havoid i)
      (combinedConfiguration24 x z hcard hx hz havoid j)) =
      (∑ a, ∑ b, k (x a) (x b))+residualCrossSum k x z := by
  set e := (Fintype.equivFinOfCardEq
    (show Fintype.card (ι ⊕ Fin n) = N by
      rw [Fintype.card_sum, Fintype.card_fin, hcard])).symm with he
  have h1 : ∀ f : ι ⊕ Fin n → ℝ, (∑ i : Fin N, f (e i)) = ∑ a, f a :=
    fun f => Equiv.sum_comp e f
  have h2 : (∑ i, ∑ j, k (combinedConfiguration24 x z hcard hx hz havoid i)
      (combinedConfiguration24 x z hcard hx hz havoid j)) =
      ∑ a : ι ⊕ Fin n, ∑ b : ι ⊕ Fin n, k (Sum.elim x z a) (Sum.elim x z b) :=
    (Finset.sum_congr rfl fun i _ =>
      h1 (fun b => k (Sum.elim x z (e i)) (Sum.elim x z b))).trans
      (h1 (fun a => ∑ b : ι ⊕ Fin n, k (Sum.elim x z a) (Sum.elim x z b)))
  rw [h2]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_add_distrib]
  have hsw : (∑ a, ∑ j, k (x a) (z j)) = ∑ j, ∑ a, k (z j) (x a) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => hs _ _
  unfold residualCrossSum cellPairSum
  rw [hsw]
  ring

/-- Foreground part of the small-alpha budget of one refinement. -/
def leechForegroundBudget24 (a d m : ℕ) (q : ℝ) : ℝ :=
  leechForegroundProfileConst24*(4^q/q)+
    leechForegroundProfileGain24 q*((d:ℝ)/(a:ℝ))^24*((d*m:ℕ):ℝ)^(-q)*(4^(q/2)/(q/2))

/-- The common right side of the three joint residual bounds. -/
def leechJointBound24 (N n : ℕ) (M Fg q p t₀ w₂ w₃ : ℝ) : ℝ :=
  (N:ℝ)*Fg+(n:ℝ)*(4^q/q+w₃)+w₂*((2*M+(n:ℝ))/(11-p))+
    w₃*((n:ℝ)*((N:ℝ)*sphereGaussianBackground24 t₀))

/-- One joint residual choice: the actual configuration has a common small-alpha budget, a
common residual short-range cost and a controlled residual Gaussian window. -/
theorem exists_leech_common_budget24 :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ {K : ℕ} (P : Fin K → SmallLeechCubePatch24),
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius24 ≤ ρ) →
      ∀ (hdisj : Pairwise (fun i j => Disjoint (smallLeechSpherePatch24 (P i))
        (smallLeechSpherePatch24 (P j)))) (a d m : ℕ), 0 < d → 0 < m →
      (∀ i, (P i).ε*(d:ℝ) = leechUnitDensityRadius24*(a:ℝ)) →
      ∀ (hn : 74 ≤ a*m) {n : ℕ}, 0 < n →
      ∀ (hcard : Fintype.card (Fin K × (Fin 24 → TwelveNodeIndex (a*m)))+n = (d*m)^24)
        (C : Fin n → Set (SphereD 24)), (∀ i, MeasurableSet (C i)) →
        Pairwise (fun i j => Disjoint (C i) (C j)) →
        (∀ i, (sphereProbabilityD 24) (C i) = (((d*m)^24:ℕ):ℝ≥0∞)⁻¹) →
        (⋃ j, C j) = (leechFamilyUnion24 P)ᶜ →
      ∀ {q p t₀ w₂ w₃ : ℝ}, 0 < q → q ≤ 24 → -1 ≤ p → p < 11 → 0 ≤ t₀ → 0 ≤ w₂ → 0 ≤ w₃ →
      ∃ (z : Fin n → SphereD 24) (hz : Function.Injective z)
        (havoid : ∀ j, z j ∉ range (leechFamilyNodes24 P (a*m) hn)),
        (∀ j, z j ∈ C j) ∧
        (((d*m)^24:ℕ):ℝ)*sphereGaussianSmallBudget24 q
          (combinedConfiguration24 (leechFamilyNodes24 P (a*m) hn) z hcard
            (leechFamilyNodes24_injective P hdisj (a*m) hn) hz havoid) ≤
          leechJointBound24 ((d*m)^24) n
            (Fintype.card (Fin K × (Fin 24 → TwelveNodeIndex (a*m))))
            (leechForegroundBudget24 a d m q) q p t₀ w₂ w₃ ∧
        w₂*residualCrossSum (shortRangeKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) p)
          (leechFamilyNodes24 P (a*m) hn) z ≤
          leechJointBound24 ((d*m)^24) n
            (Fintype.card (Fin K × (Fin 24 → TwelveNodeIndex (a*m))))
            (leechForegroundBudget24 a d m q) q p t₀ w₂ w₃ ∧
        w₃*cellPairSum (sphereGaussianKernel24 t₀) z ≤
          leechJointBound24 ((d*m)^24) n
            (Fintype.card (Fin K × (Fin 24 → TwelveNodeIndex (a*m))))
            (leechForegroundBudget24 a d m q) q p t₀ w₂ w₃ := by
  obtain ⟨ρ,hρ,hρ1,hfg⟩ := leechPatchFamily_mixedSmallBudget_le
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro K P hv hε hdisj a d m hd hm hratio hn n hnpos hcard C hCm hCd hCmass hCcover
    q p t₀ w₂ w₃ hq hq24 hp0 hp ht₀ hw₂ hw₃
  have hNpos : 0 < (d*m)^24 := by positivity
  have hNR : (((d*m)^24:ℕ):ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  -- exact mass of the residual region
  have hσR : (sphereProbabilityD 24) (⋃ j, C j) = (n:ℝ≥0∞)*(((d*m)^24:ℕ):ℝ≥0∞)⁻¹ := by
    rw [measure_iUnion (fun i j hij => hCd hij) hCm, tsum_fintype]
    simp [hCmass]
  have hσreal : (sphereProbabilityD 24).real (leechFamilyUnion24 P)ᶜ =
      (n:ℝ)/(((d*m)^24:ℕ):ℝ) := by
    rw [← hCcover, Measure.real, hσR, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, ENNReal.toReal_natCast, div_eq_mul_inv]
  have hcardR : ((Fintype.card (Fin K × (Fin 24 → TwelveNodeIndex (a*m))) : ℕ) : ℝ)+(n:ℝ) =
      (((d*m)^24:ℕ):ℝ) := by exact_mod_cast hcard
  have hmass : (Fintype.card (Fin K × (Fin 24 → TwelveNodeIndex (a*m))) : ℝ)+
      (((d*m)^24:ℕ):ℝ)*(sphereProbabilityD 24).real (leechFamilyUnion24 P)ᶜ =
        (((d*m)^24:ℕ):ℝ) := by
    rw [hσreal, mul_div_cancel₀ _ hNR]
    exact hcardR
  have hFg := hfg P hv hε hdisj a d m hd hm hratio hn hmass q hq hq24
  obtain ⟨z, hinj, hzC, hzB, hjoint⟩ := exists_leech_joint_residual24 hNpos hnpos hq hp0 hp ht₀
    hw₂ hw₃ (leechFamilyNodes24 P (a*m) hn) C hCm hCd hCmass
  refine ⟨z, hinj, hzB, hzC, ?_⟩
  have hbud := sphereGaussianSmallBudget24_eq_kernel hNpos hq
    (combinedConfiguration24 (leechFamilyNodes24 P (a*m) hn) z hcard
      (leechFamilyNodes24_injective P hdisj (a*m) hn) hinj hzB)
  rw [combinedConfiguration24_sum (leechFamilyNodes24 P (a*m) hn) z hcard
    (leechFamilyNodes24_injective P hdisj (a*m) hn) hinj hzB
    (smallBudgetKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) q)
    (smallBudgetKernel24_symm _ q)] at hbud
  have hmix : mixedSmallBudget24 (leechFamilyNodes24 P (a*m) hn) ((d*m)^24)
      (leechFamilyUnion24 P)ᶜ q =
      (∑ i, ∑ j, smallBudgetKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) q
        (leechFamilyNodes24 P (a*m) hn i) (leechFamilyNodes24 P (a*m) hn j))+
      (2*(((d*m)^24:ℕ):ℝ)*(∑ i, ∫ y in ⋃ j, C j,
          smallBudgetKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) q
            (leechFamilyNodes24 P (a*m) hn i) y ∂(sphereProbabilityD 24))+
        (((d*m)^24:ℕ):ℝ)^2*(∫ y in ⋃ j, C j, ∫ y' in ⋃ j, C j,
          smallBudgetKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) q y y'
            ∂(sphereProbabilityD 24) ∂(sphereProbabilityD 24)))-
      (((d*m)^24:ℕ):ℝ)^2*smallBudgetBackground24 ((d*m)^24) q := by
    unfold mixedSmallBudget24
    rw [← hCcover]
    ring
  have hH0 : 0 ≤ (((d*m)^24:ℕ):ℝ)*sphereGaussianSmallBudget24 q
      (combinedConfiguration24 (leechFamilyNodes24 P (a*m) hn) z hcard
        (leechFamilyNodes24_injective P hdisj (a*m) hn) hinj hzB) :=
    mul_nonneg (Nat.cast_nonneg _) (sphereGaussianSmallBudget24_nonneg hNpos q _)
  have hT0 : 0 ≤ residualCrossSum
      (shortRangeKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) p)
      (leechFamilyNodes24 P (a*m) hn) z :=
    residualCrossSum_nonneg _ (shortRangeKernel24_nonneg _ _) _ _
  have hG0 : 0 ≤ cellPairSum (sphereGaussianKernel24 t₀) z :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sphereGaussianKernel24_nonneg _ _ _
  have h2 := mul_nonneg hw₂ hT0
  have h3 := mul_nonneg hw₃ hG0
  rw [hmix] at hFg
  unfold leechJointBound24 leechForegroundBudget24
  refine ⟨?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith

end SphericalRiesz
