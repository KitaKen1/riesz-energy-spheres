import Riesz.LeechGaussianEnds24

/-! Concrete large-alpha budgets for physical Leech patches, including corrected nodes.
The constant below is computed from theta at one positive scale and a Gamma integral.
This supplies a foreground cost, not a small-alpha quadrature estimate. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
open Boundary

/-- The theta tail estimate can start at any positive scale. -/
theorem leechGaussianThetaReal24_tail_le_from {b t : ℝ} (hb : 0 < b) (hbt : b ≤ t) :
    leechGaussianThetaReal24 t-1 ≤
      Real.exp (-(2*Real.pi)*(t-b))*(leechGaussianThetaReal24 b-1) := by
  classical
  let f : ℝ → leechLattice → ℝ := fun u x => Real.exp (-(Real.pi*u*‖(x : LeechAmbient)‖^2))
  have hf : ∀ u, 0 < u → HasSum (f u) (leechGaussianThetaReal24 u) := fun u hu =>
    Complex.hasSum_ofReal.mp (leechLatticeGaussian_hasSum hu)
  have hf0 : ∀ u, f u 0 = 1 := fun u => by simp [f]
  have h1 := (hf t (hb.trans_le hbt)).update (0 : leechLattice) 0
  have h2 := ((hf b hb).update (0 : leechLattice) 0).mul_left (Real.exp (-(2*Real.pi)*(t-b)))
  rw [hf0] at h1 h2
  have hle : ∀ x, Function.update (f t) (0 : leechLattice) 0 x ≤
      Real.exp (-(2*Real.pi)*(t-b))*Function.update (f b) (0 : leechLattice) 0 x := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp
    · rw [Function.update_of_ne hx, Function.update_of_ne hx]
      have hn := leechLattice_norm_sq_ge_two x (fun h => hx (Subtype.ext h))
      simp only [f]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hn
        (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hbt))
      nlinarith
  have := hasSum_le hle h1 h2
  linarith

/-- Explicit normalized row cost at a fixed positive density scale. -/
def leechGaussianTailBudget24 (b p : ℝ) : ℝ :=
  (leechGaussianThetaReal24 b-1)*Real.exp (2*Real.pi*b)*
    ((1/(2*Real.pi*b))^(p+1)*Real.Gamma (p+1))

theorem leechGaussianTailBudget24_nonneg {b p : ℝ} (hb : 0 < b) (hp : -1 < p) :
    0 ≤ leechGaussianTailBudget24 b p := by
  have htheta : 0 ≤ leechGaussianThetaReal24 b-1 :=
    sub_nonneg.mpr (leechGaussianThetaReal24_ge_one hb)
  have hgamma : 0 < Real.Gamma (p+1) := Real.Gamma_pos_of_pos (by linarith)
  unfold leechGaussianTailBudget24
  positivity

/-- A uniform row bound, valid even when the initial theta scale is below one. -/
theorem leechPatchGaussian_row_exp_le_from {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : ι ↪ leechLattice) (Y : ι → SphereD 24) {ell c b α : ℝ}
    (hell : 0 < ell) (hc : 0 < c) (hb : 0 < b) (hscale : b ≤ c*ell^2/Real.pi)
    (hd : ∀ i j, ell*‖((U j-U i : leechLattice) : LeechAmbient)‖ ≤ dist (Y i) (Y j))
    (hα : 1 ≤ α) (i : ι) :
    (∑ j ∈ Finset.univ.erase i, sphereGaussianKernel24 (c*α) (Y i) (Y j)) ≤
      (leechGaussianThetaReal24 b-1)*Real.exp (2*Real.pi*b)*Real.exp (-(2*Real.pi*b*α)) := by
  have hα0 : 0 < α := zero_lt_one.trans_le hα
  have hβ : b ≤ c*α*ell^2/Real.pi := by
    calc b ≤ c*ell^2/Real.pi := hscale
      _ ≤ (c*ell^2/Real.pi)*α := by
        have hce : 0 ≤ c*ell^2/Real.pi := by positivity
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hα hce
      _ = c*α*ell^2/Real.pi := by ring
  refine (leechPatchGaussian_row_le U Y hell (mul_pos hc hα0) hd i).trans
    ((leechGaussianThetaReal24_tail_le_from hb hβ).trans ?_)
  have ht : 0 ≤ leechGaussianThetaReal24 b-1 :=
    sub_nonneg.mpr (leechGaussianThetaReal24_ge_one hb)
  have hβ' : b*α ≤ c*α*ell^2/Real.pi := by
    calc
      b*α ≤ (c*ell^2/Real.pi)*α := mul_le_mul_of_nonneg_right hscale hα0.le
      _ = _ := by ring
  calc
    _ ≤ Real.exp (-(2*Real.pi)*(b*α-b))*(leechGaussianThetaReal24 b-1) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
        (by
          have hm := mul_le_mul_of_nonneg_left hβ' (by positivity : 0 ≤ 2*Real.pi)
          nlinarith)) ht
    _ = _ := by
      rw [show (leechGaussianThetaReal24 b-1)*Real.exp (2*Real.pi*b)*Real.exp (-(2*Real.pi*b*α)) =
        (Real.exp (2*Real.pi*b)*Real.exp (-(2*Real.pi*b*α)))*(leechGaussianThetaReal24 b-1) by ring,
        ← Real.exp_add]
      congr 1
      congr 1
      ring

/-- The actual finite physical patch has the computed short-range row budget. -/
theorem leechPatch_shortRange_row_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : ι ↪ leechLattice) (Y : ι → SphereD 24) {ell c b p : ℝ}
    (hell : 0 < ell) (hc : 0 < c) (hb : 0 < b) (hp : -1 < p)
    (hscale : b ≤ c*ell^2/Real.pi)
    (hd : ∀ i j, ell*‖((U j-U i : leechLattice) : LeechAmbient)‖ ≤ dist (Y i) (Y j)) (i : ι) :
    (∑ j ∈ Finset.univ.erase i, shortRangeKernel24 c p (Y i) (Y j)) ≤
      leechGaussianTailBudget24 b p := by
  have hne : ∀ j ∈ Finset.univ.erase i, Y i ≠ Y j := by
    intro j hj he
    have hji : U j-U i ≠ 0 := fun h => (Finset.mem_erase.mp hj).1
      (U.injective (sub_eq_zero.mp h))
    have hn : 0 < ‖((U j-U i : leechLattice) : LeechAmbient)‖ :=
      norm_pos_iff.mpr (fun h => hji (Subtype.ext h))
    have := hd i j
    rw [he, dist_self] at this
    exact (not_lt_of_ge this) (mul_pos hell hn)
  have hi : ∀ j ∈ Finset.univ.erase i,
      IntegrableOn (fun α : ℝ => α^p*sphereGaussianKernel24 (c*α) (Y i) (Y j)) (Ioi 1) := by
    intro j hj
    simpa only [show 2*(p+1)/2-1=p by ring] using
      sphereGaussianPair24_scaled_tail_integrable (s := 2*(p+1)) hc
        (by linarith) zero_le_one (hne j hj)
  let A : ℝ := (leechGaussianThetaReal24 b-1)*Real.exp (2*Real.pi*b)
  have hA : 0 ≤ A := mul_nonneg
    (sub_nonneg.mpr (leechGaussianThetaReal24_ge_one hb)) (Real.exp_pos _).le
  have hGval : (∫ α in Ioi (0:ℝ), α^p*Real.exp (-(2*Real.pi*b*α))) =
      (1/(2*Real.pi*b))^(p+1)*Real.Gamma (p+1) := by
    simpa only [show p+1-1=p by ring] using
      Real.integral_rpow_mul_exp_neg_mul_Ioi (a := p+1) (r := 2*Real.pi*b)
        (by linarith) (by positivity)
  have hG : IntegrableOn (fun α : ℝ => α^p*Real.exp (-(2*Real.pi*b*α))) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [hGval]
    exact (mul_pos (Real.rpow_pos_of_pos (by positivity) _)
      (Real.Gamma_pos_of_pos (by linarith))).ne'
  unfold shortRangeKernel24
  rw [← integral_finsetSum _ hi]
  calc
    _ ≤ ∫ α in Ioi (1:ℝ), A*(α^p*Real.exp (-(2*Real.pi*b*α))) := by
      apply setIntegral_mono_on (integrable_finsetSum _ hi)
        ((hG.mono_set (Ioi_subset_Ioi zero_le_one)).const_mul A) measurableSet_Ioi
      intro α hα
      rw [← Finset.mul_sum]
      have hrow := leechPatchGaussian_row_exp_le_from U Y hell hc hb hscale hd hα.le i
      calc
        _ ≤ α^p*(A*Real.exp (-(2*Real.pi*b*α))) :=
          mul_le_mul_of_nonneg_left hrow (Real.rpow_nonneg (zero_le_one.trans hα.le) _)
        _ = _ := by ring
    _ ≤ ∫ α in Ioi (0:ℝ), A*(α^p*Real.exp (-(2*Real.pi*b*α))) := by
      apply setIntegral_mono_set (hG.const_mul A)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with α hα
        exact mul_nonneg hA (mul_nonneg (Real.rpow_nonneg hα.le _) (Real.exp_pos _).le)
      · exact (Ioi_subset_Ioi zero_le_one).eventuallyLE
    _ = leechGaussianTailBudget24 b p := by
      rw [integral_const_mul, hGval]
      rfl

/-- Full foreground cost, with the diagonal interpreted by the defined tail kernel. -/
theorem leechPatch_shortRange_budget_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : ι ↪ leechLattice) (Y : ι → SphereD 24) {ell c b p : ℝ}
    (hell : 0 < ell) (hc : 0 < c) (hb : 0 < b) (hp : -1 < p)
    (hscale : b ≤ c*ell^2/Real.pi)
    (hd : ∀ i j, ell*‖((U j-U i : leechLattice) : LeechAmbient)‖ ≤ dist (Y i) (Y j)) :
    (∑ i, ∑ j, shortRangeKernel24 c p (Y i) (Y j)) ≤
      (Fintype.card ι : ℝ)*leechGaussianTailBudget24 b p := by
  calc
    _ = ∑ i, ∑ j ∈ Finset.univ.erase i, shortRangeKernel24 c p (Y i) (Y j) := by
      apply Finset.sum_congr rfl
      intro i _
      have he := Finset.sum_erase_add Finset.univ
        (fun j => shortRangeKernel24 c p (Y i) (Y j)) (Finset.mem_univ i)
      rw [shortRangeKernel24_self c hp.le, add_zero] at he
      exact he.symm
    _ ≤ ∑ _i : ι, leechGaussianTailBudget24 b p :=
      Finset.sum_le_sum fun i _ => leechPatch_shortRange_row_le U Y hell hc hb hp hscale hd i
    _ = _ := by simp

/-- The actual boundary-corrected tensor rule in a sphere chart. -/
def leechCorrectedSphereNodes24 (n : ℕ) (hn : 8 ≤ n)
    (g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24) (v c : Fin 24 → ℝ)
    (hc : c ∈ UnitCube 24) (ε : ℝ) (hε : 0 < ε)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) :
    (Fin 24 → NodeIndex n) → SphereD 24 := fun u =>
  equalAreaLeechCubeEmbedding24 g v c ε hε hc hsmall
    ⟨cubeNode 24 n u,fun i =>
      ⟨(cubeNode_mem_open 24 n hn u i).1.le,(cubeNode_mem_open 24 n hn u i).2.le⟩⟩

/-- A computed common foreground budget for every refinement, including all corrected nodes.
Only the explicit density/mesh inequality is needed; no budget witness is assumed. -/
theorem equalAreaLeechCorrected24_shortRange_uniform :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24)
      (v c : Fin 24 → ℝ), ‖v‖ ≤ ρ → ∀ (hc : c ∈ UnitCube 24)
      (ε : ℝ) (hε : 0 < ε), ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) (n : ℕ) (hn : 8 ≤ n)
        (t b p : ℝ), 0 < t → 0 < b → -1 < p →
      b ≤ t*(ε/(4*(n:ℝ)*‖equalAreaFlatDerivative24‖*(1+‖leechInverseMap‖)))^2/Real.pi →
      (∑ u, ∑ w, shortRangeKernel24 t p
        (leechCorrectedSphereNodes24 n hn g v c hc ε hε hsmall u)
        (leechCorrectedSphereNodes24 n hn g v c hc ε hε hsmall w)) ≤
      (n:ℝ)^24*leechGaussianTailBudget24 b p := by
  obtain ⟨ρ,hρ,hρ1,hgeom⟩ := equalAreaNormalizedLeechPatch_lower_distance_uniform
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro g v c hv hc ε hε hs hsmall n hn t b p ht hb hp hscale
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hD := equalAreaFlatDerivative24_norm_pos
  let ell : ℝ := ε/(4*(n:ℝ)*‖equalAreaFlatDerivative24‖*(1+‖leechInverseMap‖))
  have hell : 0 < ell := by dsimp [ell]; positivity
  have hd : ∀ i j, ell*‖((leechCorrectedLabel24 n hn j-leechCorrectedLabel24 n hn i :
      leechLattice) : LeechAmbient)‖ ≤
      dist (leechCorrectedSphereNodes24 n hn g v c hc ε hε hsmall i)
        (leechCorrectedSphereNodes24 n hn g v c hc ε hε hsmall j) := by
    intro i j
    change _ ≤ dist (equalAreaLeechPatch g v c ε (cubeNode 24 n i))
      (equalAreaLeechPatch g v c ε (cubeNode 24 n j))
    rw [equalAreaLeechPatch_dist_eq g v c _ _ hε]
    have hi : cubeNode 24 n i ∈ UnitCube 24 := fun k =>
      ⟨(cubeNode_mem_open 24 n hn i k).1.le,(cubeNode_mem_open 24 n hn i k).2.le⟩
    have hj : cubeNode 24 n j ∈ UnitCube 24 := fun k =>
      ⟨(cubeNode_mem_open 24 n hn j k).1.le,(cubeNode_mem_open 24 n hn j k).2.le⟩
    have hg := hgeom v hv ε hε hs g c hc _ hi _ hj
    have hlabel := leechCorrectedLabel24_norm_le hn i j
    have hden : 0 < 2*(n:ℝ)*‖equalAreaFlatDerivative24‖ := by positivity
    have hdiv : ‖((leechCorrectedLabel24 n hn j-leechCorrectedLabel24 n hn i : leechLattice) :
        LeechAmbient)‖/(2*(n:ℝ)*‖equalAreaFlatDerivative24‖) ≤ ‖cubeNode 24 n i-cubeNode 24 n j‖ :=
      (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hlabel)
    calc
      _ = ε*(1/(2*(1+‖leechInverseMap‖)))*
          (‖((leechCorrectedLabel24 n hn j-leechCorrectedLabel24 n hn i : leechLattice) :
            LeechAmbient)‖/(2*(n:ℝ)*‖equalAreaFlatDerivative24‖)) := by
          dsimp [ell]
          field_simp
          ring
      _ ≤ ε*(1/(2*(1+‖leechInverseMap‖)))*‖cubeNode 24 n i-cubeNode 24 n j‖ :=
          mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ ≤ _ := by nlinarith
  have hcost := leechPatch_shortRange_budget_le (leechCorrectedLabel24 n hn)
    (leechCorrectedSphereNodes24 n hn g v c hc ε hε hsmall) hell ht hb hp hscale hd
  have hcard : Fintype.card (Fin 24 → NodeIndex n) = n^24 := by
    simp [nodeIndex_card hn]
  simpa only [hcard, Nat.cast_pow] using hcost

/-- The real density scale of the actual n^24 point count is exactly quadratic in n. -/
theorem sphereGaussianDensityFactor24_pow_twentyFour (n : ℕ) :
    sphereGaussianDensityFactor24 (n^24) = sphereGaussianDensityFactor24 1*(n:ℝ)^2 := by
  have hA : 0 ≤ (sphereAreaD 24).real univ := (sphereAreaD_univ_pos 24).le
  have hpow : ((n:ℝ)^24)^((1:ℝ)/12) = (n:ℝ)^2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  unfold sphereGaussianDensityFactor24 sphereGaussianScale24
  rw [Nat.cast_pow, Real.div_rpow (by positivity) hA, hpow]
  norm_num only [Nat.cast_one, mul_one, Real.div_rpow zero_le_one hA, Real.one_rpow]
  ring

/-- A positive theta scale computed from the fixed chart size, independent of its mesh. -/
def leechCorrectedDensityBudgetScale24 (ε : ℝ) : ℝ :=
  sphereGaussianDensityFactor24 1*
    (ε/(4*‖equalAreaFlatDerivative24‖*(1+‖leechInverseMap‖)))^2/Real.pi

theorem leechCorrectedDensityBudgetScale24_pos {ε : ℝ} (hε : 0 < ε) :
    0 < leechCorrectedDensityBudgetScale24 ε := by
  have hD := equalAreaFlatDerivative24_norm_pos
  have hc := sphereGaussianDensityFactor24_pos (N := 1) (by norm_num)
  unfold leechCorrectedDensityBudgetScale24
  positivity

/-- At the actual n^24 sphere density the corrected foreground has one explicit budget for
all n>=8.  This is an actual common large-alpha budget, without a budget-existence premise. -/
theorem equalAreaLeechCorrected24_actual_density_budget :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24)
      (v c : Fin 24 → ℝ), ‖v‖ ≤ ρ → ∀ (hc : c ∈ UnitCube 24)
      (ε : ℝ) (hε : 0 < ε), ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) (p : ℝ), -1 < p →
      ∀ (n : ℕ) (hn : 8 ≤ n),
      (∑ u, ∑ w, shortRangeKernel24 (sphereGaussianDensityFactor24 (n^24)) p
        (leechCorrectedSphereNodes24 n hn g v c hc ε hε hsmall u)
        (leechCorrectedSphereNodes24 n hn g v c hc ε hε hsmall w))/(n:ℝ)^24 ≤
      leechGaussianTailBudget24 (leechCorrectedDensityBudgetScale24 ε) p := by
  obtain ⟨ρ,hρ,hρ1,hcost⟩ := equalAreaLeechCorrected24_shortRange_uniform
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro g v c hv hc ε hε hs hsmall p hp n hn
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hD := equalAreaFlatDerivative24_norm_pos
  have hcN := sphereGaussianDensityFactor24_pos (N := n^24) (by positivity)
  have hscale : leechCorrectedDensityBudgetScale24 ε ≤
      sphereGaussianDensityFactor24 (n^24)*
        (ε/(4*(n:ℝ)*‖equalAreaFlatDerivative24‖*(1+‖leechInverseMap‖)))^2/Real.pi := by
    rw [sphereGaussianDensityFactor24_pow_twentyFour]
    unfold leechCorrectedDensityBudgetScale24
    apply le_of_eq
    field_simp <;> ring
  have hb := hcost g v c hv hc ε hε hs hsmall n hn
    (sphereGaussianDensityFactor24 (n^24)) (leechCorrectedDensityBudgetScale24 ε) p
    hcN (leechCorrectedDensityBudgetScale24_pos hε) hp hscale
  apply (div_le_iff₀ (pow_pos hnR 24)).mpr
  simpa only [mul_comm] using hb

/-- Rational allocation also removes the shrinking chart size from the budget: with n=a*m,
N=(d*m)^24 and epsilon=r*a/d, the positive theta scale depends only on r.
Thus the computed foreground bound is common across a,d,m, rather than merely a fixed chart. -/
theorem equalAreaLeechCorrected24_rational_density_budget :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24)
      (v c : Fin 24 → ℝ), ‖v‖ ≤ ρ → ∀ (hc : c ∈ UnitCube 24)
      (ε : ℝ) (hε : 0 < ε), ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) (r p : ℝ), 0 < r → -1 < p →
      ∀ (a d m : ℕ), 0 < a → 0 < d → 0 < m → ε*(d:ℝ)=r*(a:ℝ) →
      ∀ (hn : 8 ≤ a*m),
      (∑ u, ∑ w, shortRangeKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) p
        (leechCorrectedSphereNodes24 (a*m) hn g v c hc ε hε hsmall u)
        (leechCorrectedSphereNodes24 (a*m) hn g v c hc ε hε hsmall w))/(a*m:ℕ)^24 ≤
      leechGaussianTailBudget24 (leechCorrectedDensityBudgetScale24 r) p := by
  obtain ⟨ρ,hρ,hρ1,hcost⟩ := equalAreaLeechCorrected24_shortRange_uniform
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro g v c hv hc ε hε hs hsmall r p hr hp a d m ha hd hm hratio hn
  have haR : 0 < (a:ℝ) := by exact_mod_cast ha
  have hdR : 0 < (d:ℝ) := by exact_mod_cast hd
  have hmR : 0 < (m:ℝ) := by exact_mod_cast hm
  have hD := equalAreaFlatDerivative24_norm_pos
  have he : ε = r*(a:ℝ)/(d:ℝ) := (eq_div_iff hdR.ne').mpr hratio
  have hcN := sphereGaussianDensityFactor24_pos (N := (d*m)^24) (by positivity)
  have hscale : leechCorrectedDensityBudgetScale24 r ≤
      sphereGaussianDensityFactor24 ((d*m)^24)*
        (ε/(4*(a*m:ℕ)*‖equalAreaFlatDerivative24‖*(1+‖leechInverseMap‖)))^2/Real.pi := by
    rw [sphereGaussianDensityFactor24_pow_twentyFour, he]
    unfold leechCorrectedDensityBudgetScale24
    push_cast
    apply le_of_eq
    field_simp <;> ring
  have hb := hcost g v c hv hc ε hε hs hsmall (a*m) hn
    (sphereGaussianDensityFactor24 ((d*m)^24)) (leechCorrectedDensityBudgetScale24 r) p
    hcN (leechCorrectedDensityBudgetScale24_pos hr) hp hscale
  apply (div_le_iff₀ (by positivity : (0:ℝ) < (a*m:ℕ)^24)).mpr
  simpa only [Nat.cast_pow, mul_comm] using hb

end SphericalRiesz
