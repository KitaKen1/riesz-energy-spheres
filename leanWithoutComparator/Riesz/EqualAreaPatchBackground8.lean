import Riesz.CurvedBackground8

/-! Full actual background of the moving, rotated equal-area sphere
patches. First choose the cutoff radius, then the patch tolerance, then
the mesh. The resulting estimate is uniform over every patch parameter.
The background is coordinate Lebesgue measure; global sphere recovery
and the sphere probability-density conversion remain separate. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalRiesz
open Boundary

theorem equalAreaNormalizedE8Patch_background_data_uniform :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ v : Fin 8 → ℝ, ‖v‖ ≤ ρ →
      ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius ≤ ρ →
      ∀ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9, ∀ c ∈ UnitCube 8,
      CurvedAnnularData8 (equalAreaNormalizedE8Patch g v c ε) ∧
        CurvedRelativeE8Distance8 (equalAreaNormalizedE8Patch g v c ε) := by
  obtain ⟨ρA,hρA,hρAb,hA⟩ := equalAreaNormalizedE8Patch_annular_data_uniform
  obtain ⟨ρD,hρD,_hρDb,hD⟩ := equalAreaNormalizedE8Patch_relative_distance_uniform (1/2) (by norm_num)
  refine ⟨min ρA ρD,lt_min hρA hρD,(min_le_left _ _).trans hρAb,?_⟩
  intro v hv ε hε hs g c hc
  exact ⟨hA v (hv.trans (min_le_left _ _)) ε hε (hs.trans (min_le_left _ _)) g c hc,
    hD v (hv.trans (min_le_right _ _)) ε hε (hs.trans (min_le_right _ _)) g c hc⟩

theorem equalAreaPatchPotential8_integrable_uniform :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ v : Fin 8 → ℝ, ‖v‖ ≤ ρ →
      ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius ≤ ρ →
      ∀ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9, ∀ c ∈ UnitCube 8,
      IntegrableOn (curvedPotential8 (equalAreaNormalizedE8Patch g v c ε)) (UnitCube 8) ∧
        ∀ x ∈ UnitCube 8, IntegrableOn (curvedRieszFour (equalAreaNormalizedE8Patch g v c ε) x) (UnitCube 8) := by
  obtain ⟨ρ,hρ,hρb,hdata⟩ := equalAreaNormalizedE8Patch_background_data_uniform
  refine ⟨ρ,hρ,hρb,?_⟩
  intro v hv ε hε hs g c hc
  obtain ⟨hF,hd⟩ := hdata v hv ε hε hs g c hc
  exact ⟨curvedPotential8_integrableOn _ hF hd,fun x hx => curvedRieszFour8_integrableOn _ hF hd x hx⟩

theorem equalAreaPatchBackground8_radius_uniform :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ v : Fin 8 → ℝ, ‖v‖ ≤ ρ → ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius ≤ ρ →
      ∀ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9, ∀ c ∈ UnitCube 8,
      ∀ R : ℝ, 1 ≤ R → ∀ m : ℕ, 8 ≤ m →
      |curvedBackground8 (equalAreaNormalizedE8Patch g v c ε) m| ≤
        C/R^2+|equalAreaPatchNearBackground g v c ε R m| := by
  obtain ⟨ρ,hρ,hρb,hdata⟩ := equalAreaNormalizedE8Patch_background_data_uniform
  obtain ⟨C,hC,hb⟩ := curvedBackground8_radius_bound
  refine ⟨ρ,hρ,hρb,C,hC,?_⟩
  intro v hv ε hε hs g c hc R hR m hm
  obtain ⟨hF,hd⟩ := hdata v hv ε hε hs g c hc
  exact hb _ hF hd R hR m hm

/-- The cutoff, patch tolerance and mesh are chosen in that order. Both
the patch radius and the mesh threshold are independent of rotations,
cube centers and all admissible moving patch parameters. -/
theorem equalAreaPatchBackground8_uniform_small (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∃ M : ℕ, 8 ≤ M ∧
      ∀ v : Fin 8 → ℝ, ‖v‖ ≤ ρ → ∀ ε : ℝ, 0 < ε → ε*equalAreaScaleRadius ≤ ρ →
      ∀ g : Ambient9 ≃ₗᵢ[ℝ] Ambient9, ∀ c ∈ UnitCube 8,
      ∀ m : ℕ, M ≤ m → |curvedBackground8 (equalAreaNormalizedE8Patch g v c ε) m| < δ := by
  obtain ⟨ρB,hρB,hρBb,C,hC,hb⟩ := equalAreaPatchBackground8_radius_uniform
  have hk : Tendsto (fun k : ℕ => C/(k:ℝ)^2) atTop (𝓝 0) :=
    ((tendsto_pow_atTop (by decide : (2:ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop).const_div_atTop C
  obtain ⟨k,hk1,hka⟩ := ((eventually_ge_atTop (1:ℕ)).and
    (hk.eventually (gt_mem_nhds (by positivity : (0:ℝ) < δ/3)))).exists
  have hkr : (1:ℝ) ≤ k := by exact_mod_cast hk1
  have hk0 : (0:ℝ) < k := by linarith
  let K : ℝ := 128*e8NearIntegralConstant*(k:ℝ)^4
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (by norm_num) e8NearIntegralConstant_nonneg) (by positivity)
  let η : ℝ := min (1/2) (δ/(3*(K+1)))
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1/2 := min_le_left _ _
  have hηK : η*K < δ/3 := by
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right (min_le_right _ _) hK)
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 3*(K+1))).mpr
    nlinarith
  obtain ⟨ρN,hρN,_hρNb,hN⟩ := equalAreaPatchNearBackgroundDifference_uniform η hη hη1
  have hflat : Tendsto (fun m : ℕ => (m:ℝ)^4*(cubeQuadrature 8 m (e8NearPotential ((k:ℝ)/(m:ℝ)))-
      ∫ x in UnitCube 8, e8NearPotential ((k:ℝ)/(m:ℝ)) x)) atTop (𝓝 0) := by
    simpa only [e8ScaledNearBackground_eq] using e8ScaledNearPotential_background_limit (k:ℝ) hk0
  have hf : ∀ᶠ m : ℕ in atTop,
      |(m:ℝ)^4*(cubeQuadrature 8 m (e8NearPotential ((k:ℝ)/(m:ℝ)))-
        ∫ x in UnitCube 8, e8NearPotential ((k:ℝ)/(m:ℝ)) x)| < δ/3 := by
    simpa only [Real.norm_eq_abs] using hflat.norm.eventually
      (gt_mem_nhds (by simpa only [norm_zero] using (div_pos hδ (by norm_num : (0:ℝ) < 3))))
  obtain ⟨M,hM⟩ := eventually_atTop.mp hf
  refine ⟨min ρB ρN,lt_min hρB hρN,(min_le_left _ _).trans hρBb,max 8 M,le_max_left _ _,?_⟩
  intro v hv ε hε hs g c hc m hm
  have hm8 : 8 ≤ m := (le_max_left 8 M).trans hm
  have hmM : M ≤ m := (le_max_right 8 M).trans hm
  have hnb := hN v (hv.trans (min_le_right _ _)) ε hε (hs.trans (min_le_right _ _)) g c hc
    (k:ℝ) hk0 m hm8
  have hdif : |equalAreaPatchNearBackgroundDifference g v c ε (k:ℝ) m| ≤ η*K := by
    simpa [K,mul_assoc,mul_left_comm,mul_comm] using hnb
  have heq : equalAreaPatchNearBackground g v c ε (k:ℝ) m =
      equalAreaPatchNearBackgroundDifference g v c ε (k:ℝ) m+
        (m:ℝ)^4*(cubeQuadrature 8 m (e8NearPotential ((k:ℝ)/(m:ℝ)))-
          ∫ x in UnitCube 8, e8NearPotential ((k:ℝ)/(m:ℝ)) x) := by
    unfold equalAreaPatchNearBackground equalAreaPatchNearBackgroundDifference
    ring
  have hnear : |equalAreaPatchNearBackground g v c ε (k:ℝ) m| < δ/3+δ/3 := by
    rw [heq]
    exact (abs_add_le _ _).trans_lt (add_lt_add (hdif.trans_lt hηK) (hM m hmM))
  exact (hb v (hv.trans (min_le_left _ _)) ε hε (hs.trans (min_le_left _ _)) g c hc
    (k:ℝ) hkr m hm8).trans_lt (by linarith)

theorem equalAreaPatchBackground8_limit_along
    (g : ℕ → Ambient9 ≃ₗᵢ[ℝ] Ambient9) (v c : ℕ → Fin 8 → ℝ) (e : ℕ → ℝ)
    (hv : Tendsto v atTop (𝓝 0)) (he : Tendsto e atTop (𝓝 0))
    (hp : ∀ᶠ m : ℕ in atTop, 0 < e m) (hc : ∀ᶠ m : ℕ in atTop, c m ∈ UnitCube 8) :
    Tendsto (fun m : ℕ => curvedBackground8 (equalAreaNormalizedE8Patch (g m) (v m) (c m) (e m)) m)
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro δ hδ
  obtain ⟨ρ,hρ,_hρb,M,_hM,hb⟩ := equalAreaPatchBackground8_uniform_small δ hδ
  have hnv : Tendsto (fun m => ‖v m‖) atTop (𝓝 0) := by simpa using hv.norm
  have hne : Tendsto (fun m => e m*equalAreaScaleRadius) atTop (𝓝 0) := by
    simpa using he.mul_const equalAreaScaleRadius
  filter_upwards [hnv.eventually (gt_mem_nhds hρ),hne.eventually (gt_mem_nhds hρ),hp,hc,
    eventually_ge_atTop M] with m hvm hem hpm hcm hm
  simpa only [Real.dist_eq,sub_zero] using hb (v m) hvm.le (e m) hpm hem.le (g m) (c m) hcm m hm

end SphericalRiesz
