import Riesz.LeechForegroundTail24
import Riesz.LeechForegroundBudget24

/-! Sharp Gaussian window of a twelfth-order foreground family at exact mass.

Inside one patch the nodes of the uncorrected middle block are lattice midpoints, so their
mutual Gaussian rows are Leech theta rows with the factor `(1-η)²` of the near-flat chart.  All
other nodes keep the conservative theta row.  A symmetric nonnegative pair sum is at most the
pair sum of a core plus twice the full rows outside the core, and the number of nodes outside
the middle block is `n²⁴ - (n-74)²⁴`.  Two patches are separated by a positive distance.  At the
exact-mass rational allocation the two theta arguments do not depend on the refinement:

`Σ_{fg,fg} G_t ≤ M (Θ(α(1-η)²) + 2 (1-(1-74/n)²⁴) Θ(κα)) + M² e^{-tδ²}`,  `M = K n²⁴`.

The residual points, the limit in the refinement and the attaining sequence are not part of
this file. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace SphericalRiesz
open Boundary

/-- The Leech theta function is nonincreasing on the positive axis. -/
theorem leechGaussianThetaReal24_anti {β₁ β₂ : ℝ} (h₁ : 0 < β₁) (h : β₁ ≤ β₂) :
    leechGaussianThetaReal24 β₂ ≤ leechGaussianThetaReal24 β₁ := by
  have hs : ∀ β : ℝ, 0 < β → Summable (fun x : leechLattice =>
      Real.exp (-(Real.pi*β*‖(x : LeechAmbient)‖^2))) := fun β hβ =>
    (Complex.hasSum_ofReal.mp (leechLatticeGaussian_hasSum hβ)).summable
  unfold leechGaussianThetaReal24
  refine Summable.tsum_le_tsum (fun x => ?_) (hs β₂ (h₁.trans_le h)) (hs β₁ h₁)
  apply Real.exp_le_exp.mpr
  have hx : 0 ≤ Real.pi*‖(x : LeechAmbient)‖^2 := by positivity
  nlinarith [mul_nonneg hx (sub_nonneg.mpr h)]

/-- A symmetric nonnegative pair sum is at most the pair sum of a core plus twice the full rows
outside the core. -/
theorem pairSum_le_core_add_rest {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (f : ι → ι → ℝ) (hf : ∀ u w, 0 ≤ f u w) (hs : ∀ u w, f u w = f w u) :
    (∑ u, ∑ w, f u w) ≤ (∑ u ∈ S, ∑ w ∈ S, f u w)+2*(∑ u ∈ Sᶜ, ∑ w, f u w) := by
  have h1 : (∑ u, ∑ w, f u w) = (∑ u ∈ S, ∑ w, f u w)+∑ u ∈ Sᶜ, ∑ w, f u w :=
    (Finset.sum_add_sum_compl S fun u => ∑ w, f u w).symm
  have h2 : (∑ u ∈ S, ∑ w, f u w) =
      (∑ u ∈ S, ∑ w ∈ S, f u w)+∑ u ∈ S, ∑ w ∈ Sᶜ, f u w := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => (Finset.sum_add_sum_compl S fun w => f u w).symm
  have h3 : (∑ u ∈ S, ∑ w ∈ Sᶜ, f u w) ≤ ∑ w ∈ Sᶜ, ∑ u, f w u := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun w _ => ?_
    calc (∑ u ∈ S, f u w) = ∑ u ∈ S, f w u := Finset.sum_congr rfl fun u _ => hs u w
      _ ≤ ∑ u, f w u :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun u _ _ => hf w u
  rw [h1, h2]
  linarith

/-- Indices of the uncorrected middle block of the twelfth-order tensor rule. -/
def twelveMiddleCube (n : ℕ) : (Fin 24 → Fin (n-74)) ↪ (Fin 24 → TwelveNodeIndex n) where
  toFun u := fun i => Sum.inr (Sum.inl (u i))
  inj' := by
    intro u w h
    funext i
    exact Sum.inl_injective (Sum.inr_injective (congrFun h i))

theorem twelveCubeNode_middle (n : ℕ) (u : Fin 24 → Fin (n-74)) (i : Fin 24) :
    twelveCubeNode 24 n (twelveMiddleCube n u) i = ((u i:ℝ)+37+1/2)/(n:ℝ) := rfl

/-- Middle nodes are lattice midpoints: their flat distances are lattice distances at scale
`1/n`. -/
theorem twelveMiddleCube_flat_distance (n : ℕ) (u w : Fin 24 → Fin (n-74)) :
    dist (WithLp.toLp 2 (leechMap (twelveCubeNode 24 n (twelveMiddleCube n u))) : LeechAmbient)
      (WithLp.toLp 2 (leechMap (twelveCubeNode 24 n (twelveMiddleCube n w)))) =
      (n:ℝ)⁻¹*‖((leechGridLattice24 (n-74) w-leechGridLattice24 (n-74) u : leechLattice) :
        LeechAmbient)‖ := by
  have he : twelveCubeNode 24 n (twelveMiddleCube n u)-twelveCubeNode 24 n (twelveMiddleCube n w) =
      (n:ℝ)⁻¹ • (fun i => (u i:ℝ)-(w i:ℝ)) := by
    funext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, twelveCubeNode_middle, div_eq_mul_inv]
    ring
  rw [dist_eq_norm, ← WithLp.toLp_sub, ← map_sub, he, map_smul, WithLp.toLp_smul, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)⁻¹)]
  congr 1
  change ‖WithLp.toLp 2 (leechMap (fun i => (u i:ℝ)-(w i:ℝ)))‖ =
    ‖leechIntegerPoint (fun i => (w i:ℤ))-leechIntegerPoint (fun i => (u i:ℤ))‖
  rw [norm_sub_rev]
  rw [leechIntegerPoint, leechIntegerPoint, ← WithLp.toLp_sub, ← map_sub]
  simp only [Int.cast_natCast]
  rfl

/-- Middle nodes of a small patch: sharp theta rows, uniformly in the refinement. -/
theorem smallLeechPatch_middle_row {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (p : SmallLeechCubePatch24), ‖p.v‖ ≤ ρ →
      p.ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ (n : ℕ) (hn : 74 ≤ n) (t : ℝ), 0 < t → ∀ u : Fin 24 → Fin (n-74),
      (∑ w, sphereGaussianKernel24 t
        (smallLeechPatchNodes24 p n hn (twelveMiddleCube n u))
        (smallLeechPatchNodes24 p n hn (twelveMiddleCube n w))) ≤
      leechGaussianThetaReal24 (t*((1-η)*p.ε/(n:ℝ))^2/Real.pi) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := equalAreaLeechPatch_gaussian_row_uniform hη hη1
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro p hv hε n hn t ht u
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  let x : (Fin 24 → Fin (n-74)) → UnitCube 24 := fun w =>
    ⟨twelveCubeNode 24 n (twelveMiddleCube n w), fun i =>
      ⟨(twelveCubeNode_mem_open 24 n hn (twelveMiddleCube n w) i).1.le,
        (twelveCubeNode_mem_open 24 n hn (twelveMiddleCube n w) i).2.le⟩⟩
  have hrow := hb p.g p.v p.c hv p.c_mem p.ε p.ε_pos hε p.small (leechGridLattice24 (n-74)) x
    (n:ℝ)⁻¹ (inv_pos.mpr hnR) (fun i j => twelveMiddleCube_flat_distance n i j) t ht u
  have hrow' : (∑ w ∈ Finset.univ.erase u, sphereGaussianKernel24 t
      (smallLeechPatchNodes24 p n hn (twelveMiddleCube n u))
      (smallLeechPatchNodes24 p n hn (twelveMiddleCube n w))) ≤
      leechGaussianThetaReal24 (t*((1-η)*p.ε*(n:ℝ)⁻¹)^2/Real.pi)-1 := hrow
  have hsplit : (∑ w, sphereGaussianKernel24 t
      (smallLeechPatchNodes24 p n hn (twelveMiddleCube n u))
      (smallLeechPatchNodes24 p n hn (twelveMiddleCube n w))) =
      sphereGaussianKernel24 t (smallLeechPatchNodes24 p n hn (twelveMiddleCube n u))
        (smallLeechPatchNodes24 p n hn (twelveMiddleCube n u))+
      ∑ w ∈ Finset.univ.erase u, sphereGaussianKernel24 t
        (smallLeechPatchNodes24 p n hn (twelveMiddleCube n u))
        (smallLeechPatchNodes24 p n hn (twelveMiddleCube n w)) :=
    (Finset.add_sum_erase Finset.univ (fun w => sphereGaussianKernel24 t
      (smallLeechPatchNodes24 p n hn (twelveMiddleCube n u))
      (smallLeechPatchNodes24 p n hn (twelveMiddleCube n w))) (Finset.mem_univ u)).symm
  have hθ : t*((1-η)*p.ε/(n:ℝ))^2/Real.pi = t*((1-η)*p.ε*(n:ℝ)⁻¹)^2/Real.pi := by
    rw [div_eq_mul_inv ((1-η)*p.ε) (n:ℝ)]
  rw [hsplit, sphereGaussianKernel24_self t, hθ]
  linarith

/-- The fraction of the density scale kept by the conservative rows of corrected nodes. -/
def leechConservativeRowFactor24 : ℝ := (patchChartLower24/(2*‖equalAreaFlatDerivative24‖))^2

theorem leechConservativeRowFactor24_pos : 0 < leechConservativeRowFactor24 := by
  have hD := equalAreaFlatDerivative24_norm_pos
  have hL := patchChartLower24_pos
  unfold leechConservativeRowFactor24
  positivity

/-- All nodes of a small patch: conservative theta rows, uniformly in the refinement. -/
theorem smallLeechPatch_all_row :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (p : SmallLeechCubePatch24), ‖p.v‖ ≤ ρ →
      p.ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ (n : ℕ) (hn : 74 ≤ n) (t : ℝ), 0 < t → ∀ u : Fin 24 → TwelveNodeIndex n,
      (∑ w, sphereGaussianKernel24 t (smallLeechPatchNodes24 p n hn u)
        (smallLeechPatchNodes24 p n hn w)) ≤
      leechGaussianThetaReal24
        (t*(p.ε*patchChartLower24/(2*(n:ℝ)*‖equalAreaFlatDerivative24‖))^2/Real.pi) := by
  obtain ⟨ρ,hρ,hρ1,hgeom⟩ := equalAreaNormalizedLeechPatch_lower_distance_uniform
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro p hv hε n hn t ht u
  have hrow := equalAreaLeechTwelfth24_gaussian_row hn p.g p.v p.c p.c_mem p.ε_pos p.small
    patchChartLower24_pos ht
    (fun x hx y hy => hgeom p.v hv p.ε p.ε_pos hε p.g p.c p.c_mem x hx y hy) u
  have hrow' : (∑ w ∈ Finset.univ.erase u, sphereGaussianKernel24 t
      (smallLeechPatchNodes24 p n hn u) (smallLeechPatchNodes24 p n hn w)) ≤
      leechGaussianThetaReal24
        (t*(p.ε*patchChartLower24/(2*(n:ℝ)*‖equalAreaFlatDerivative24‖))^2/Real.pi)-1 := hrow
  have hsplit : (∑ w, sphereGaussianKernel24 t (smallLeechPatchNodes24 p n hn u)
      (smallLeechPatchNodes24 p n hn w)) =
      sphereGaussianKernel24 t (smallLeechPatchNodes24 p n hn u)
        (smallLeechPatchNodes24 p n hn u)+
      ∑ w ∈ Finset.univ.erase u, sphereGaussianKernel24 t (smallLeechPatchNodes24 p n hn u)
        (smallLeechPatchNodes24 p n hn w) :=
    (Finset.add_sum_erase Finset.univ (fun w => sphereGaussianKernel24 t
      (smallLeechPatchNodes24 p n hn u) (smallLeechPatchNodes24 p n hn w))
      (Finset.mem_univ u)).symm
  rw [hsplit, sphereGaussianKernel24_self t]
  linarith

/-- The full Gaussian pair sum of one small patch: sharp theta rows on the middle block and
conservative rows for the `n²⁴-(n-74)²⁴` other nodes. -/
theorem smallLeechPatch_pairSum_le {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ (p : SmallLeechCubePatch24), ‖p.v‖ ≤ ρ →
      p.ε*equalAreaScaleRadius24 ≤ ρ →
      ∀ (n : ℕ) (hn : 74 ≤ n) (t : ℝ), 0 < t →
      (∑ u, ∑ w, sphereGaussianKernel24 t (smallLeechPatchNodes24 p n hn u)
        (smallLeechPatchNodes24 p n hn w)) ≤
      (n:ℝ)^24*leechGaussianThetaReal24 (t*((1-η)*p.ε/(n:ℝ))^2/Real.pi)+
        2*((n:ℝ)^24-((n:ℝ)-74)^24)*leechGaussianThetaReal24
          (t*(p.ε*patchChartLower24/(2*(n:ℝ)*‖equalAreaFlatDerivative24‖))^2/Real.pi) := by
  obtain ⟨ρ₁,hρ₁,hρ₁',hsharp⟩ := smallLeechPatch_middle_row hη hη1
  obtain ⟨ρ₂,hρ₂,_,hall⟩ := smallLeechPatch_all_row
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, (min_le_left _ _).trans hρ₁', ?_⟩
  intro p hv hε n hn t ht
  have hv₁ := hv.trans (min_le_left ρ₁ ρ₂)
  have hv₂ := hv.trans (min_le_right ρ₁ ρ₂)
  have hε₁ := hε.trans (min_le_left ρ₁ ρ₂)
  have hε₂ := hε.trans (min_le_right ρ₁ ρ₂)
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hD := equalAreaFlatDerivative24_norm_pos
  have hη0 : 0 < 1-η := by linarith
  obtain ⟨θs, hθs⟩ : ∃ θs : ℝ, θs =
      leechGaussianThetaReal24 (t*((1-η)*p.ε/(n:ℝ))^2/Real.pi) := ⟨_, rfl⟩
  obtain ⟨θc, hθc⟩ : ∃ θc : ℝ, θc = leechGaussianThetaReal24
      (t*(p.ε*patchChartLower24/(2*(n:ℝ)*‖equalAreaFlatDerivative24‖))^2/Real.pi) := ⟨_, rfl⟩
  have hθs0 : 0 ≤ θs := by
    rw [hθs]
    exact zero_le_one.trans (leechGaussianThetaReal24_ge_one
      (div_pos (mul_pos ht (pow_pos (div_pos (mul_pos hη0 p.ε_pos) hnR) 2)) Real.pi_pos))
  rw [← hθs, ← hθc]
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin 24 → TwelveNodeIndex n),
      S = Finset.univ.map (twelveMiddleCube n) := ⟨_, rfl⟩
  have h74 : ((n-74 : ℕ) : ℝ) = (n:ℝ)-74 := by
    rw [Nat.cast_sub hn]
    norm_num
  have hcardS : (S.card : ℝ) = ((n:ℝ)-74)^24 := by
    rw [hS, Finset.card_map, Finset.card_univ, Fintype.card_pi_const, Fintype.card_fin,
      Nat.cast_pow, h74]
  have hcardT : (Fintype.card (Fin 24 → TwelveNodeIndex n) : ℝ) = (n:ℝ)^24 := by
    rw [twelveCubeNode_card 24 n hn]
    exact Nat.cast_pow _ _
  have hcardC : (Sᶜ.card : ℝ) = (n:ℝ)^24-((n:ℝ)-74)^24 := by
    rw [Finset.card_compl, Nat.cast_sub (Finset.card_le_univ S), hcardT, hcardS]
  have hsplit : (∑ u, ∑ w, sphereGaussianKernel24 t (smallLeechPatchNodes24 p n hn u)
      (smallLeechPatchNodes24 p n hn w)) ≤
      (∑ u ∈ S, ∑ w ∈ S, sphereGaussianKernel24 t (smallLeechPatchNodes24 p n hn u)
        (smallLeechPatchNodes24 p n hn w))+
      2*(∑ u ∈ Sᶜ, ∑ w, sphereGaussianKernel24 t (smallLeechPatchNodes24 p n hn u)
        (smallLeechPatchNodes24 p n hn w)) :=
    pairSum_le_core_add_rest S (fun u w => sphereGaussianKernel24 t
      (smallLeechPatchNodes24 p n hn u) (smallLeechPatchNodes24 p n hn w))
      (fun u w => sphereGaussianKernel24_nonneg _ _ _)
      (fun u w => sphereGaussianKernel24_comm t _ _)
  have hcore : (∑ u ∈ S, ∑ w ∈ S, sphereGaussianKernel24 t (smallLeechPatchNodes24 p n hn u)
      (smallLeechPatchNodes24 p n hn w)) ≤ (n:ℝ)^24*θs := by
    have hrows : ∀ u : Fin 24 → Fin (n-74), (∑ w ∈ S, sphereGaussianKernel24 t
        (smallLeechPatchNodes24 p n hn (twelveMiddleCube n u))
        (smallLeechPatchNodes24 p n hn w)) ≤ θs := by
      intro u
      rw [hS, Finset.sum_map, hθs]
      exact hsharp p hv₁ hε₁ n hn t ht u
    have hpow : ((n:ℝ)-74)^24 ≤ (n:ℝ)^24 := by
      have h0 : 0 ≤ (n:ℝ)-74 := by
        rw [← h74]
        exact Nat.cast_nonneg _
      exact pow_le_pow_left₀ h0 (by linarith) 24
    calc (∑ u ∈ S, ∑ w ∈ S, sphereGaussianKernel24 t (smallLeechPatchNodes24 p n hn u)
          (smallLeechPatchNodes24 p n hn w))
        = ∑ u : Fin 24 → Fin (n-74), ∑ w ∈ S, sphereGaussianKernel24 t
            (smallLeechPatchNodes24 p n hn (twelveMiddleCube n u))
            (smallLeechPatchNodes24 p n hn w) := by
          rw [hS, Finset.sum_map]
      _ ≤ ∑ _u : Fin 24 → Fin (n-74), θs := Finset.sum_le_sum fun u _ => hrows u
      _ = ((n:ℝ)-74)^24*θs := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_pi_const,
            Fintype.card_fin, Nat.cast_pow, h74]
      _ ≤ (n:ℝ)^24*θs := mul_le_mul_of_nonneg_right hpow hθs0
  have hrest : (∑ u ∈ Sᶜ, ∑ w, sphereGaussianKernel24 t (smallLeechPatchNodes24 p n hn u)
      (smallLeechPatchNodes24 p n hn w)) ≤ ((n:ℝ)^24-((n:ℝ)-74)^24)*θc := by
    calc _ ≤ ∑ _u ∈ Sᶜ, θc := Finset.sum_le_sum fun u _ => by
            rw [hθc]
            exact hall p hv₂ hε₂ n hn t ht u
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcardC]
  calc _ ≤ _ := hsplit
    _ ≤ (n:ℝ)^24*θs+2*(((n:ℝ)^24-((n:ℝ)-74)^24)*θc) :=
        add_le_add hcore (mul_le_mul_of_nonneg_left hrest (by norm_num))
    _ = _ := by rw [mul_assoc]

/-- Pair sum of a separated family: the patch sums plus the squared cardinality times the cross
bound. -/
theorem leechFamily_pairSum_le_patches {K : ℕ} (P : Fin K → SmallLeechCubePatch24) (n : ℕ)
    (hn : 74 ≤ n) (k : SphereD 24 → SphereD 24 → ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    (hcross : ∀ i j, i ≠ j → ∀ u w, k (smallLeechPatchNodes24 (P i) n hn u)
      (smallLeechPatchNodes24 (P j) n hn w) ≤ τ) :
    (∑ q, ∑ q', k (leechFamilyNodes24 P n hn q) (leechFamilyNodes24 P n hn q')) ≤
      (∑ i, ∑ u, ∑ w, k (smallLeechPatchNodes24 (P i) n hn u)
        (smallLeechPatchNodes24 (P i) n hn w))+((K:ℝ)*(n:ℝ)^24)^2*τ := by
  classical
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hcardNodes : (Fintype.card (Fin 24 → TwelveNodeIndex n) : ℝ) = (n:ℝ)^24 := by
    rw [twelveCubeNode_card 24 n hn]
    exact Nat.cast_pow _ _
  have hrow : ∀ i u, (∑ j, ∑ w, k (smallLeechPatchNodes24 (P i) n hn u)
      (smallLeechPatchNodes24 (P j) n hn w)) ≤
      (∑ w, k (smallLeechPatchNodes24 (P i) n hn u) (smallLeechPatchNodes24 (P i) n hn w))+
        (K:ℝ)*((n:ℝ)^24*τ) := by
    intro i u
    have hstep : ∀ j, (∑ w, k (smallLeechPatchNodes24 (P i) n hn u)
        (smallLeechPatchNodes24 (P j) n hn w)) ≤
        (if j = i then ∑ w, k (smallLeechPatchNodes24 (P i) n hn u)
          (smallLeechPatchNodes24 (P i) n hn w) else 0)+(n:ℝ)^24*τ := by
      intro j
      by_cases hji : j = i
      · subst hji
        rw [if_pos rfl]
        exact le_add_of_nonneg_right (mul_nonneg (pow_pos hn0 24).le hτ)
      · rw [if_neg hji, zero_add]
        calc _ ≤ ∑ _w : Fin 24 → TwelveNodeIndex n, τ :=
              Finset.sum_le_sum fun w _ => hcross i j (Ne.symm hji) u w
          _ = (n:ℝ)^24*τ := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardNodes]
    calc _ ≤ ∑ j, ((if j = i then ∑ w, k (smallLeechPatchNodes24 (P i) n hn u)
            (smallLeechPatchNodes24 (P i) n hn w) else 0)+(n:ℝ)^24*τ) :=
          Finset.sum_le_sum fun j _ => hstep j
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ i),
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsplit : (∑ q, ∑ q', k (leechFamilyNodes24 P n hn q) (leechFamilyNodes24 P n hn q')) =
      ∑ i, ∑ u, ∑ j, ∑ w, k (smallLeechPatchNodes24 (P i) n hn u)
        (smallLeechPatchNodes24 (P j) n hn w) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun u _ => ?_
    exact Fintype.sum_prod_type _
  rw [hsplit]
  calc _ ≤ ∑ i, ∑ u, ((∑ w, k (smallLeechPatchNodes24 (P i) n hn u)
          (smallLeechPatchNodes24 (P i) n hn w))+(K:ℝ)*((n:ℝ)^24*τ)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun u _ => hrow i u
    _ = (∑ i, ∑ u, ∑ w, k (smallLeechPatchNodes24 (P i) n hn u)
          (smallLeechPatchNodes24 (P i) n hn w))+(K:ℝ)*((n:ℝ)^24*((K:ℝ)*((n:ℝ)^24*τ))) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, hcardNodes]
    _ = _ := by ring

/-- Gaussian window of a separated twelfth-order foreground family at exact mass. -/
theorem leechPatchFamily_gaussianWindow_le {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ {K : ℕ} (P : Fin K → SmallLeechCubePatch24),
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius24 ≤ ρ) →
      ∀ {δ : ℝ}, 0 < δ →
      (∀ i j, i ≠ j → ∀ x ∈ smallLeechSpherePatch24 (P i),
        ∀ y ∈ smallLeechSpherePatch24 (P j), δ ≤ dist x y) →
      ∀ (a d m : ℕ), 0 < a → 0 < d → 0 < m →
      (∀ i, (P i).ε*(d:ℝ) = leechUnitDensityRadius24*(a:ℝ)) →
      ∀ (hn : 74 ≤ a*m) (α : ℝ), 0 < α →
      (∑ q, ∑ q', sphereGaussianKernel24 (sphereGaussianScale24 ((d*m)^24) α)
          (leechFamilyNodes24 P (a*m) hn q) (leechFamilyNodes24 P (a*m) hn q')) ≤
        (K:ℝ)*((a*m:ℕ):ℝ)^24*(leechGaussianThetaReal24 (α*(1-η)^2)+
          2*(1-(1-74/((a*m:ℕ):ℝ))^24)*
            leechGaussianThetaReal24 (α*leechConservativeRowFactor24))+
        ((K:ℝ)*((a*m:ℕ):ℝ)^24)^2*
          Real.exp (-(sphereGaussianScale24 ((d*m)^24) α*δ^2)) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := smallLeechPatch_pairSum_le hη hη1
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro K P hv hε δ hδ hsep a d m ha hd hm hratio hn α hα
  have hNpos : 0 < (d*m)^24 := by positivity
  have ht0 : 0 < sphereGaussianScale24 ((d*m)^24) α := sphereGaussianScale24_pos hNpos hα
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = sphereGaussianScale24 ((d*m)^24) α := ⟨_, rfl⟩
  obtain ⟨n, hndef⟩ : ∃ n : ℝ, n = ((a*m:ℕ):ℝ) := ⟨_, rfl⟩
  rw [← htdef, ← hndef]
  have ht : 0 < t := by rw [htdef]; exact ht0
  have hn0 : 0 < n := by rw [hndef]; exact_mod_cast Nat.mul_pos ha hm
  have hn0' : n ≠ 0 := hn0.ne'
  have hD := equalAreaFlatDerivative24_norm_pos
  have hπ := Real.pi_pos
  have hnπ : n^2*Real.pi ≠ 0 := (mul_pos (pow_pos hn0 2) hπ).ne'
  -- theta arguments at exact mass
  have hte : ∀ i, t*(P i).ε^2 = Real.pi*n^2*α := by
    intro i
    have h := sphereGaussian_exact_mass_bump_scale24 a d m hd (P i).ε α (hratio i)
    rw [← htdef, ← hndef] at h
    linarith
  have hsharp : ∀ i, t*((1-η)*(P i).ε/n)^2/Real.pi = α*(1-η)^2 := by
    intro i
    have h1 : t*((1-η)*(P i).ε/n)^2/Real.pi =
        (t*(P i).ε^2)*(1-η)^2/(n^2*Real.pi) := by ring
    rw [h1, hte i, div_eq_iff hnπ]
    ring
  have hfac : leechConservativeRowFactor24 =
      patchChartLower24^2/(2*‖equalAreaFlatDerivative24‖)^2 := by
    unfold leechConservativeRowFactor24
    rw [div_pow]
  have hcons : ∀ i, t*((P i).ε*patchChartLower24/(2*n*‖equalAreaFlatDerivative24‖))^2/Real.pi =
      α*leechConservativeRowFactor24 := by
    intro i
    have h1 : t*((P i).ε*patchChartLower24/(2*n*‖equalAreaFlatDerivative24‖))^2/Real.pi =
        (t*(P i).ε^2)*(patchChartLower24^2/(2*‖equalAreaFlatDerivative24‖)^2)/
          (n^2*Real.pi) := by ring
    rw [h1, hte i, hfac, div_eq_iff hnπ]
    ring
  have hsub : n^24-(n-74)^24 = n^24*(1-(1-74/n)^24) := by
    have h74 : n-74 = n*(1-74/n) := by
      rw [mul_sub, mul_one, mul_div_cancel₀ _ hn0']
    rw [h74, mul_pow]
    ring
  -- one patch
  have hpatch : ∀ i, (∑ u, ∑ w, sphereGaussianKernel24 t
      (smallLeechPatchNodes24 (P i) (a*m) hn u) (smallLeechPatchNodes24 (P i) (a*m) hn w)) ≤
      n^24*(leechGaussianThetaReal24 (α*(1-η)^2)+
        2*(1-(1-74/n)^24)*leechGaussianThetaReal24 (α*leechConservativeRowFactor24)) := by
    intro i
    have h := hb (P i) (hv i) (hε i) (a*m) hn t ht
    rw [← hndef, hsharp i, hcons i, hsub] at h
    calc _ ≤ _ := h
      _ = _ := by ring
  -- two patches
  have hcross : ∀ i j, i ≠ j → ∀ u w, sphereGaussianKernel24 t
      (smallLeechPatchNodes24 (P i) (a*m) hn u) (smallLeechPatchNodes24 (P j) (a*m) hn w) ≤
      Real.exp (-(t*δ^2)) := by
    intro i j hij u w
    have hdist := hsep i j hij _ (smallLeechPatchNodes24_mem (P i) _ hn u) _
      (smallLeechPatchNodes24_mem (P j) _ hn w)
    unfold sphereGaussianKernel24
    apply Real.exp_le_exp.mpr
    have hsq : δ^2 ≤ dist (smallLeechPatchNodes24 (P i) (a*m) hn u)
        (smallLeechPatchNodes24 (P j) (a*m) hn w)^2 := pow_le_pow_left₀ hδ.le hdist 2
    have hmul := mul_le_mul_of_nonneg_left hsq ht.le
    linarith
  have hfam := leechFamily_pairSum_le_patches P (a*m) hn (sphereGaussianKernel24 t)
    (Real.exp_pos (-(t*δ^2))).le hcross
  rw [← hndef] at hfam
  calc _ ≤ (∑ i, ∑ u, ∑ w, sphereGaussianKernel24 t (smallLeechPatchNodes24 (P i) (a*m) hn u)
          (smallLeechPatchNodes24 (P i) (a*m) hn w))+((K:ℝ)*n^24)^2*Real.exp (-(t*δ^2)) := hfam
    _ ≤ (∑ _i : Fin K, n^24*(leechGaussianThetaReal24 (α*(1-η)^2)+
          2*(1-(1-74/n)^24)*leechGaussianThetaReal24 (α*leechConservativeRowFactor24)))+
          ((K:ℝ)*n^24)^2*Real.exp (-(t*δ^2)) :=
        add_le_add (Finset.sum_le_sum fun i _ => hpatch i) le_rfl
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end SphericalRiesz
