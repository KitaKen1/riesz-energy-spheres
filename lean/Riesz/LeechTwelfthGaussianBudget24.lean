import Riesz.LeechGaussianBudget24
import Riesz.BoundaryTwelveNodeGeometry

/-! The actual twelfth-order grid retains the existing Leech theta rows and
computed common rational-density large-alpha budgets. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
open Boundary

/-- Boundary corrections retain control by their distinct integer labels. -/
theorem twelveRule_label_sub_le {n : ℕ} (hn : 74 ≤ n) (u w : TwelveNodeIndex n) :
    |(twelveMidpointLabel n u:ℝ)-(twelveMidpointLabel n w:ℝ)| ≤
      2*|twelveUnscaledRuleNode n u-twelveUnscaledRuleNode n w| := by
  have haux : ∀ i j : TwelveNodeIndex n, twelveMidpointLabel n i < twelveMidpointLabel n j →
      |(twelveMidpointLabel n i:ℝ)-(twelveMidpointLabel n j:ℝ)| ≤
        2*|twelveUnscaledRuleNode n i-twelveUnscaledRuleNode n j| := by
    intro i j hij
    have hg : (twelveMidpointLabel n i:ℝ)+1 ≤ twelveMidpointLabel n j := by
      exact_mod_cast Nat.succ_le_of_lt hij
    have hi := abs_lt.mp (twelveUnscaledRuleNode_close_to_label hn i)
    have hj := abs_lt.mp (twelveUnscaledRuleNode_close_to_label hn j)
    rw [abs_of_nonpos (by linarith : (twelveMidpointLabel n i:ℝ)-(twelveMidpointLabel n j:ℝ) ≤ 0)]
    have hdiff : -(twelveMidpointLabel n i:ℝ)+(twelveMidpointLabel n j:ℝ) ≤
        2*(twelveUnscaledRuleNode n j-twelveUnscaledRuleNode n i) := by linarith
    calc
      _ ≤ 2*(twelveUnscaledRuleNode n j-twelveUnscaledRuleNode n i) := by linarith
      _ ≤ 2*|twelveUnscaledRuleNode n j-twelveUnscaledRuleNode n i| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
      _ = _ := by rw [abs_sub_comm]
  rcases lt_trichotomy (twelveMidpointLabel n u) (twelveMidpointLabel n w) with h | h | h
  · exact haux u w h
  · simp [h]
  · simpa only [abs_sub_comm] using haux w u h

def leechTwelfthLabel24 (n : ℕ) (hn : 74 ≤ n) :
    (Fin 24 → TwelveNodeIndex n) ↪ leechLattice where
  toFun u := ⟨leechIntegerPoint (fun i => (twelveMidpointLabel n (u i):ℤ)),
    (leechLattice_mem_iff _).mpr ⟨_,rfl⟩⟩
  inj' := by
    intro u w h
    have hc := leechMap_injective (congrArg (fun z : leechLattice => WithLp.ofLp (z : LeechAmbient)) h)
    funext i
    apply twelveMidpointLabel_injective hn
    have hi : (twelveMidpointLabel n (u i):ℝ) = (twelveMidpointLabel n (w i):ℝ) := by
      simpa using congrFun hc i
    exact_mod_cast hi

/-- All boundary-corrected nodes admit one lattice-label distance bound. -/
theorem leechTwelfthLabel24_norm_le {n : ℕ} (hn : 74 ≤ n)
    (u w : Fin 24 → TwelveNodeIndex n) :
    ‖((leechTwelfthLabel24 n hn w-leechTwelfthLabel24 n hn u : leechLattice) : LeechAmbient)‖ ≤
      (2*(n:ℝ)*‖equalAreaFlatDerivative24‖)*‖twelveCubeNode 24 n u-twelveCubeNode 24 n w‖ := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  let z : Fin 24 → ℝ := fun i => (twelveMidpointLabel n (u i):ℝ)-(twelveMidpointLabel n (w i):ℝ)
  have hz : ‖z‖ ≤ (2*(n:ℝ))*‖twelveCubeNode 24 n u-twelveCubeNode 24 n w‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    have h := twelveRule_label_sub_le hn (u i) (w i)
    have he : |twelveUnscaledRuleNode n (u i)-twelveUnscaledRuleNode n (w i)| =
        (n:ℝ)*|twelveCubeNode 24 n u i-twelveCubeNode 24 n w i| := by
      simp only [twelveCubeNode,twelveRuleNode,← sub_div,abs_div,abs_of_pos hnR]
      field_simp
    rw [he] at h
    calc ‖z i‖ ≤ 2*((n:ℝ)*|twelveCubeNode 24 n u i-twelveCubeNode 24 n w i|) := h
      _ ≤ (2*(n:ℝ))*‖twelveCubeNode 24 n u-twelveCubeNode 24 n w‖ := by
        have hi := norm_le_pi_norm (twelveCubeNode 24 n u-twelveCubeNode 24 n w) i
        simp only [Pi.sub_apply,Real.norm_eq_abs] at hi
        nlinarith
  have he : ‖((leechTwelfthLabel24 n hn w-leechTwelfthLabel24 n hn u : leechLattice) : LeechAmbient)‖ =
      ‖equalAreaFlatDerivative24 z‖ := by
    conv_rhs =>
      rw [← dist_zero_right, ← map_zero equalAreaFlatDerivative24,
        equalAreaFlatDerivative24_dist, map_zero, WithLp.toLp_zero, dist_zero_right]
    change ‖leechIntegerPoint (fun i => (twelveMidpointLabel n (w i):ℤ))-
      leechIntegerPoint (fun i => (twelveMidpointLabel n (u i):ℤ))‖ = ‖WithLp.toLp 2 (leechMap z)‖
    rw [norm_sub_rev,leechIntegerPoint,leechIntegerPoint,← WithLp.toLp_sub,← map_sub]
    rfl
  rw [he]
  calc
    _ ≤ ‖equalAreaFlatDerivative24‖*‖z‖ := equalAreaFlatDerivative24.le_opNorm z
    _ ≤ ‖equalAreaFlatDerivative24‖*((2*(n:ℝ))*‖twelveCubeNode 24 n u-twelveCubeNode 24 n w‖) :=
      mul_le_mul_of_nonneg_left hz (norm_nonneg _)
    _ = _ := by ring

/-- The actual boundary-corrected foreground rows have a uniform Gaussian theta bound. -/
theorem equalAreaLeechTwelfth24_gaussian_row {n : ℕ} (hn : 74 ≤ n)
    (g : (AmbientD 24) ≃ₗᵢ[ℝ] (AmbientD 24)) (v c : Fin 24 → ℝ)
    (hc : c ∈ UnitCube 24) {ε : ℝ} (hε : 0 < ε)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) {L t : ℝ} (hL : 0 < L) (ht : 0 < t)
    (hlower : ∀ x ∈ UnitCube 24, ∀ y ∈ UnitCube 24,
      L*‖x-y‖ ≤ dist (equalAreaNormalizedLeechPatch g v c ε x) (equalAreaNormalizedLeechPatch g v c ε y))
    (u : Fin 24 → TwelveNodeIndex n) :
    (∑ w ∈ Finset.univ.erase u, sphereGaussianKernel24 t
      (equalAreaLeechCubeEmbedding24 g v c ε hε hc hsmall
        ⟨twelveCubeNode 24 n u,fun i => ⟨(twelveCubeNode_mem_open 24 n hn u i).1.le,(twelveCubeNode_mem_open 24 n hn u i).2.le⟩⟩)
      (equalAreaLeechCubeEmbedding24 g v c ε hε hc hsmall
        ⟨twelveCubeNode 24 n w,fun i => ⟨(twelveCubeNode_mem_open 24 n hn w i).1.le,(twelveCubeNode_mem_open 24 n hn w i).2.le⟩⟩)) ≤
    leechGaussianThetaReal24 (t*(ε*L/(2*(n:ℝ)*‖equalAreaFlatDerivative24‖))^2/Real.pi)-1 := by
  have hflat := equalAreaFlatDerivative24_norm_pos
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  apply leechPatchGaussian_row_le (leechTwelfthLabel24 n hn) _ (by positivity) ht _ u
  intro i j
  change _ ≤ dist (equalAreaLeechPatch g v c ε (twelveCubeNode 24 n i))
    (equalAreaLeechPatch g v c ε (twelveCubeNode 24 n j))
  rw [equalAreaLeechPatch_dist_eq g v c _ _ hε]
  have hi : twelveCubeNode 24 n i ∈ UnitCube 24 := fun k => ⟨(twelveCubeNode_mem_open 24 n hn i k).1.le,(twelveCubeNode_mem_open 24 n hn i k).2.le⟩
  have hj : twelveCubeNode 24 n j ∈ UnitCube 24 := fun k => ⟨(twelveCubeNode_mem_open 24 n hn j k).1.le,(twelveCubeNode_mem_open 24 n hn j k).2.le⟩
  have hgeom := hlower _ hi _ hj
  have hlabel := leechTwelfthLabel24_norm_le hn i j
  have hden : 0 < 2*(n:ℝ)*‖equalAreaFlatDerivative24‖ := by positivity
  have hdiv : ‖((leechTwelfthLabel24 n hn j-leechTwelfthLabel24 n hn i : leechLattice) :
      LeechAmbient)‖/(2*(n:ℝ)*‖equalAreaFlatDerivative24‖) ≤ ‖twelveCubeNode 24 n i-twelveCubeNode 24 n j‖ :=
    (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hlabel)
  calc
    _ = ε*L*(‖((leechTwelfthLabel24 n hn j-leechTwelfthLabel24 n hn i : leechLattice) : LeechAmbient)‖ /
      (2*(n:ℝ)*‖equalAreaFlatDerivative24‖)) := by ring
    _ ≤ ε*L*‖twelveCubeNode 24 n i-twelveCubeNode 24 n j‖ := mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ ≤ _ := by nlinarith


/-- The actual boundary-corrected tensor rule in a sphere chart. -/
def leechTwelfthSphereNodes24 (n : ℕ) (hn : 74 ≤ n)
    (g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24) (v c : Fin 24 → ℝ)
    (hc : c ∈ UnitCube 24) (ε : ℝ) (hε : 0 < ε)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) :
    (Fin 24 → TwelveNodeIndex n) → SphereD 24 := fun u =>
  equalAreaLeechCubeEmbedding24 g v c ε hε hc hsmall
    ⟨twelveCubeNode 24 n u,fun i =>
      ⟨(twelveCubeNode_mem_open 24 n hn u i).1.le,(twelveCubeNode_mem_open 24 n hn u i).2.le⟩⟩

/-- The actual twelfth-order sphere nodes are all distinct. -/
theorem leechTwelfthSphereNodes24_injective (n : ℕ) (hn : 74 ≤ n)
    (g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24) (v c : Fin 24 → ℝ)
    (hc : c ∈ UnitCube 24) (ε : ℝ) (hε : 0 < ε)
    (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) :
    Function.Injective (leechTwelfthSphereNodes24 n hn g v c hc ε hε hsmall) := by
  intro u w h
  have hcube := (equalAreaLeechCubeEmbedding24 g v c ε hε hc hsmall).injective h
  exact twelveCubeNode_injective 24 n hn (congrArg Subtype.val hcube)

/-- A computed common foreground budget for every refinement, including all corrected nodes.
Only the explicit density/mesh inequality is needed; no budget witness is assumed. -/
theorem equalAreaLeechTwelfth24_shortRange_uniform :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24)
      (v c : Fin 24 → ℝ), ‖v‖ ≤ ρ → ∀ (hc : c ∈ UnitCube 24)
      (ε : ℝ) (hε : 0 < ε), ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) (n : ℕ) (hn : 74 ≤ n)
        (t b p : ℝ), 0 < t → 0 < b → -1 < p →
      b ≤ t*(ε/(4*(n:ℝ)*‖equalAreaFlatDerivative24‖*(1+‖leechInverseMap‖)))^2/Real.pi →
      (∑ u, ∑ w, shortRangeKernel24 t p
        (leechTwelfthSphereNodes24 n hn g v c hc ε hε hsmall u)
        (leechTwelfthSphereNodes24 n hn g v c hc ε hε hsmall w)) ≤
      (n:ℝ)^24*leechGaussianTailBudget24 b p := by
  obtain ⟨ρ,hρ,hρ1,hgeom⟩ := equalAreaNormalizedLeechPatch_lower_distance_uniform
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro g v c hv hc ε hε hs hsmall n hn t b p ht hb hp hscale
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hD := equalAreaFlatDerivative24_norm_pos
  let ell : ℝ := ε/(4*(n:ℝ)*‖equalAreaFlatDerivative24‖*(1+‖leechInverseMap‖))
  have hell : 0 < ell := by dsimp [ell]; positivity
  have hd : ∀ i j, ell*‖((leechTwelfthLabel24 n hn j-leechTwelfthLabel24 n hn i :
      leechLattice) : LeechAmbient)‖ ≤
      dist (leechTwelfthSphereNodes24 n hn g v c hc ε hε hsmall i)
        (leechTwelfthSphereNodes24 n hn g v c hc ε hε hsmall j) := by
    intro i j
    change _ ≤ dist (equalAreaLeechPatch g v c ε (twelveCubeNode 24 n i))
      (equalAreaLeechPatch g v c ε (twelveCubeNode 24 n j))
    rw [equalAreaLeechPatch_dist_eq g v c _ _ hε]
    have hi : twelveCubeNode 24 n i ∈ UnitCube 24 := fun k =>
      ⟨(twelveCubeNode_mem_open 24 n hn i k).1.le,(twelveCubeNode_mem_open 24 n hn i k).2.le⟩
    have hj : twelveCubeNode 24 n j ∈ UnitCube 24 := fun k =>
      ⟨(twelveCubeNode_mem_open 24 n hn j k).1.le,(twelveCubeNode_mem_open 24 n hn j k).2.le⟩
    have hg := hgeom v hv ε hε hs g c hc _ hi _ hj
    have hlabel := leechTwelfthLabel24_norm_le hn i j
    have hden : 0 < 2*(n:ℝ)*‖equalAreaFlatDerivative24‖ := by positivity
    have hdiv : ‖((leechTwelfthLabel24 n hn j-leechTwelfthLabel24 n hn i : leechLattice) :
        LeechAmbient)‖/(2*(n:ℝ)*‖equalAreaFlatDerivative24‖) ≤ ‖twelveCubeNode 24 n i-twelveCubeNode 24 n j‖ :=
      (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hlabel)
    calc
      _ = ε*(1/(2*(1+‖leechInverseMap‖)))*
          (‖((leechTwelfthLabel24 n hn j-leechTwelfthLabel24 n hn i : leechLattice) :
            LeechAmbient)‖/(2*(n:ℝ)*‖equalAreaFlatDerivative24‖)) := by
          dsimp [ell]
          field_simp
          ring
      _ ≤ ε*(1/(2*(1+‖leechInverseMap‖)))*‖twelveCubeNode 24 n i-twelveCubeNode 24 n j‖ :=
          mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ ≤ _ := by nlinarith
  have hcost := leechPatch_shortRange_budget_le (leechTwelfthLabel24 n hn)
    (leechTwelfthSphereNodes24 n hn g v c hc ε hε hsmall) hell ht hb hp hscale hd
  have hcard : Fintype.card (Fin 24 → TwelveNodeIndex n) = n^24 := by
    simp [twelveNodeIndex_card hn]
  simpa only [hcard, Nat.cast_pow] using hcost

/-- At the actual n^24 sphere density the corrected foreground has one explicit budget for
all n>=74.  This is an actual common large-alpha budget, without a budget-existence premise. -/
theorem equalAreaLeechTwelfth24_actual_density_budget :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24)
      (v c : Fin 24 → ℝ), ‖v‖ ≤ ρ → ∀ (hc : c ∈ UnitCube 24)
      (ε : ℝ) (hε : 0 < ε), ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) (p : ℝ), -1 < p →
      ∀ (n : ℕ) (hn : 74 ≤ n),
      (∑ u, ∑ w, shortRangeKernel24 (sphereGaussianDensityFactor24 (n^24)) p
        (leechTwelfthSphereNodes24 n hn g v c hc ε hε hsmall u)
        (leechTwelfthSphereNodes24 n hn g v c hc ε hε hsmall w))/(n:ℝ)^24 ≤
      leechGaussianTailBudget24 (leechCorrectedDensityBudgetScale24 ε) p := by
  obtain ⟨ρ,hρ,hρ1,hcost⟩ := equalAreaLeechTwelfth24_shortRange_uniform
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
theorem equalAreaLeechTwelfth24_rational_density_budget :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (g : AmbientD 24 ≃ₗᵢ[ℝ] AmbientD 24)
      (v c : Fin 24 → ℝ), ‖v‖ ≤ ρ → ∀ (hc : c ∈ UnitCube 24)
      (ε : ℝ) (hε : 0 < ε), ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ (hsmall : ‖v‖+ε*equalAreaScaleRadius24 ≤ 1/8) (r p : ℝ), 0 < r → -1 < p →
      ∀ (a d m : ℕ), 0 < a → 0 < d → 0 < m → ε*(d:ℝ)=r*(a:ℝ) →
      ∀ (hn : 74 ≤ a*m),
      (∑ u, ∑ w, shortRangeKernel24 (sphereGaussianDensityFactor24 ((d*m)^24)) p
        (leechTwelfthSphereNodes24 (a*m) hn g v c hc ε hε hsmall u)
        (leechTwelfthSphereNodes24 (a*m) hn g v c hc ε hε hsmall w))/(a*m:ℕ)^24 ≤
      leechGaussianTailBudget24 (leechCorrectedDensityBudgetScale24 r) p := by
  obtain ⟨ρ,hρ,hρ1,hcost⟩ := equalAreaLeechTwelfth24_shortRange_uniform
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
