import Riesz.CurvedFullRow8

/-! Stability of the known flat full-row mean on every actual small
moving/rotated sphere patch. Choose R first and eta second. No new Epstein
or optimal discrete near-count computation is needed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalRiesz
open Boundary

theorem equalAreaNormalizedE8Patch_row_data_uniform (η : ℝ) (hη : 0 < η) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ v : Fin 8 → ℝ, ‖v‖ ≤ ρ →
      ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius ≤ ρ →
      ∀ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9, ∀ c ∈ UnitCube 8,
      CurvedAnnularData8 (equalAreaNormalizedE8Patch g v c ε) ∧
        CurvedRelativeE8DistanceTolerance8 (equalAreaNormalizedE8Patch g v c ε) η := by
  obtain ⟨ρA,hρA,hρAb,hA⟩ := equalAreaNormalizedE8Patch_annular_data_uniform
  obtain ⟨ρD,hρD,_hρDb,hD⟩ := equalAreaNormalizedE8Patch_relative_distance_uniform η hη
  refine ⟨min ρA ρD,lt_min hρA hρD,(min_le_left _ _).trans hρAb,?_⟩
  intro v hv ε hε hs g c hc
  exact ⟨hA v (hv.trans (min_le_left _ _)) ε hε (hs.trans (min_le_left _ _)) g c hc,
    hD v (hv.trans (min_le_right _ _)) ε hε (hs.trans (min_le_right _ _)) g c hc⟩

theorem equalAreaPatchFullRowMean8_uniform_difference (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ v : Fin 8 → ℝ, ‖v‖ ≤ ρ →
      ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius ≤ ρ →
      ∀ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9, ∀ c ∈ UnitCube 8,
      ∀ m : ℕ, 8 ≤ m →
      |curvedFullRowMean8 (equalAreaNormalizedE8Patch g v c ε) m-e8FullRowMean m| < δ := by
  obtain ⟨C,hC,hb⟩ := curvedFullRowMean8_comparison_bound
  have hk : Tendsto (fun k : ℕ => C/(k:ℝ)^2) atTop (𝓝 0) :=
    ((tendsto_pow_atTop (by decide : (2:ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop).const_div_atTop C
  obtain ⟨k,hk1,hka⟩ := ((eventually_ge_atTop (1:ℕ)).and
    (hk.eventually (gt_mem_nhds (half_pos hδ)))).exists
  have hkr : (1:ℝ) ≤ k := by exact_mod_cast hk1
  let K : ℝ := 64*curvedNearRowComparisonConstant8 (k:ℝ)
  have hK : 0 ≤ K := mul_nonneg (by norm_num) (curvedNearRowComparisonConstant8_nonneg _)
  let η : ℝ := min (1/2) (δ/(2*(K+1)))
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1/2 := min_le_left _ _
  have hηK : η*K < δ/2 := by
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right (min_le_right _ _) hK)
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2*(K+1))).mpr
    nlinarith
  obtain ⟨ρ,hρ,hρb,hdata⟩ := equalAreaNormalizedE8Patch_row_data_uniform η hη
  refine ⟨ρ,hρ,hρb,?_⟩
  intro v hv ε hε hs g c hc m hm
  obtain ⟨hF,hd⟩ := hdata v hv ε hε hs g c hc
  have h := hb _ hF η hη.le hη1 hd (k:ℝ) hkr m hm
  have hsK : 64*η*curvedNearRowComparisonConstant8 (k:ℝ) = η*K := by dsimp [K]; ring
  rw [hsK] at h
  exact h.trans_lt (by linarith)

theorem equalAreaPatchFullRowMean8_uniform_small (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∃ M : ℕ, 8 ≤ M ∧
      ∀ v : Fin 8 → ℝ, ‖v‖ ≤ ρ → ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius ≤ ρ →
      ∀ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9, ∀ c ∈ UnitCube 8,
      ∀ m : ℕ, M ≤ m →
      |curvedFullRowMean8 (equalAreaNormalizedE8Patch g v c ε) m-(-5*Real.pi^2/6)| < δ := by
  obtain ⟨ρ,hρ,hρb,hb⟩ := equalAreaPatchFullRowMean8_uniform_difference (δ/2) (half_pos hδ)
  have hf : ∀ᶠ m : ℕ in atTop, |e8FullRowMean m-(-5*Real.pi^2/6)| < δ/2 := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp e8FullRowMean_limit (δ/2) (half_pos hδ))
  obtain ⟨M,hM⟩ := eventually_atTop.mp hf
  refine ⟨ρ,hρ,hρb,max 8 M,le_max_left _ _,?_⟩
  intro v hv ε hε hs g c hc m hm
  have h1 := hb v hv ε hε hs g c hc m ((le_max_left 8 M).trans hm)
  have h2 := hM m ((le_max_right 8 M).trans hm)
  have ht := abs_sub_le (curvedFullRowMean8 (equalAreaNormalizedE8Patch g v c ε) m)
    (e8FullRowMean m) (-5*Real.pi^2/6)
  exact ht.trans_lt (by linarith)

theorem equalAreaPatchFullRowMean8_limit_along
    (g : ℕ → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (v c : ℕ → Fin 8 → ℝ) (e : ℕ → ℝ)
    (hv : Tendsto v atTop (𝓝 0)) (he : Tendsto e atTop (𝓝 0))
    (hp : ∀ᶠ m : ℕ in atTop, 0 < e m) (hc : ∀ᶠ m : ℕ in atTop, c m ∈ UnitCube 8) :
    Tendsto (fun m : ℕ => curvedFullRowMean8 (equalAreaNormalizedE8Patch (g m) (v m) (c m) (e m)) m)
      atTop (𝓝 (-5*Real.pi^2/6)) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  obtain ⟨ρ,hρ,_hρb,M,_hM,hb⟩ := equalAreaPatchFullRowMean8_uniform_small δ hδ
  have hnv : Tendsto (fun m => ‖v m‖) atTop (𝓝 0) := by simpa using hv.norm
  have hne : Tendsto (fun m => e m*equalAreaScaleRadius) atTop (𝓝 0) := by
    simpa using he.mul_const equalAreaScaleRadius
  filter_upwards [hnv.eventually (gt_mem_nhds hρ),hne.eventually (gt_mem_nhds hρ),hp,hc,
    eventually_ge_atTop M] with m hvm hem hpm hcm hm
  simpa only [Real.dist_eq] using hb (v m) hvm.le (e m) hpm hem.le (g m) (c m) hcm m hm

end SphericalRiesz
