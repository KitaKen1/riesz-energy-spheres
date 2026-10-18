import Riesz.RationalJointResidual8
import Riesz.RationalLongRangeResidual8
import Riesz.NegJointResidual8
import Riesz.NegMacroEndBounds8

/-! The rational NEG construction with the macroscopic bound at every cutoff (stage NEG, assembly).

Same configuration as `rationalCubeFamily8_exists_neg_joint` (patch nodes plus one residual point
per cell, selected jointly with `K'(δ)`), but the bound on the subtracted macroscopic kernel is
stated for every cutoff `0 ≤ t ≤ δ`: the union Cauchy–Schwarz at `t`, the monotonicity of the
residual `K'`-block in the cutoff (exact mass) and the selection bound at `δ`. With `δ = 1` one
construction controls every macroscopic end `∫_{(0,t]}`, `t ≤ 1`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace SphericalRiesz
open Boundary

theorem rationalCubeFamily8_exists_neg_joint_cutoff {K : ℕ}
    (P : Fin K → SmallE8CubePatch8)
    (hdis : Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i)) (smallE8CubeSet8 (P j))))
    (hu : sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i)) < 1)
    (a d m : ℕ) (ha : 0 < a) (hd : 0 < d) (hm : 8 ≤ m)
    (hbudget : K*a^8 ≤ d^8)
    (hmass : sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i)) = (K:ℝ)*((a:ℝ)/d)^8)
    {p w : ℝ} (hp1 : -1 ≤ p) (hp : p < 3) (hw : 0 < w)
    {c' p' δ lam : ℝ} (hc' : 0 ≤ c') (hp' : -2 < p') (hδ : 0 ≤ δ) (hlam : 0 < lam)
    (hr0 : 0 < (d^8-K*a^8)*m^8) (C : Fin ((d^8-K*a^8)*m^8) → Set Sphere8)
    (hCm : ∀ j, MeasurableSet (C j)) (hdisjC : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hunion : (⋃ j, C j) = (⋃ i, smallE8CubeSet8 (P i))ᶜ)
    (hmassC : ∀ j, sphereProbability8 (C j) =
      sphereProbability8 (⋃ i, smallE8CubeSet8 (P i))ᶜ/(((d^8-K*a^8)*m^8 : ℕ) : ℝ≥0∞))
    (dm : Fin ((d^8-K*a^8)*m^8) → ℝ) (hdiam : ∀ j, ∀ x ∈ C j, ∀ y ∈ C j, dist x y ≤ dm j) :
    ∃ Y : Configuration ((d*m)^8),
      (∃ e : rationalCubeNodeIndex8 K a d m ≃ Fin ((d*m)^8),
        ∀ t, Y (e (Sum.inl t)) = rationalCubePatchNodes8 P a m ha hm t) ∧
      energy4 Y-(7/16:ℝ)*(((d*m)^8:ℕ):ℝ)^2 ≤
        sphereFiniteBlock4 (rationalCubePatchNodes8 P a m ha hm)
          (⋃ i, smallE8CubeSet8 (P i)) (((d*m)^8:ℕ):ℝ)+w*(4*(((d*m)^8:ℕ):ℝ)/(3-p))+
          lam*∑ j, c'*(dm j)^2*(δ^(p'+2)/(p'+2)) ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ δ →
      kernelBlock8 (negMacroKernel8 c' p' t) (fun i => Y i) univ (((d*m)^8:ℕ):ℝ) ≤
        2*kernelBlock8 (negMacroKernel8 c' p' t) (rationalCubePatchNodes8 P a m ha hm)
            (⋃ i, smallE8CubeSet8 (P i)) (((d*m)^8:ℕ):ℝ)+
          2*((∑ j, c'*(dm j)^2*(δ^(p'+2)/(p'+2)))+
            ((sphereFiniteBlock4 (rationalCubePatchNodes8 P a m ha hm)
                (⋃ i, smallE8CubeSet8 (P i)) (((d*m)^8:ℕ):ℝ)-
              (energy4 Y-(7/16:ℝ)*(((d*m)^8:ℕ):ℝ)^2))+w*(4*(((d*m)^8:ℕ):ℝ)/(3-p)))/lam) := by
  classical
  set S := ⋃ i, smallE8CubeSet8 (P i) with hSdef
  set nodes := rationalCubePatchNodes8 P a m ha hm with hnodes
  set c := sphereGaussianDensityFactor8 ((d*m)^8) with hcdef
  let e0 := Fintype.equivFin (Fin K × (Fin 8 → NodeIndex (a*m)))
  set q := Fintype.card (Fin K × (Fin 8 → NodeIndex (a*m))) with hqdef
  let X : Fin q → Sphere8 := nodes ∘ e0.symm
  set M : ℝ := (((d*m)^8:ℕ):ℝ) with hMdef
  have hS : MeasurableSet S := MeasurableSet.iUnion
    (fun i => (smallE8CubeSet8_isCompact (P i)).isClosed.measurableSet)
  have hA := sphere8_complement_mass_ne_zero S hS hu
  have hr : (((d^8-K*a^8)*m^8 : ℕ):ℝ) = M*sphereProbability8.real Sᶜ :=
    rationalCubeFamily8_residual_mass_matching P a d m hd (by omega) hbudget hmass
  have hNpos : 0 < (d*m)^8 := pow_pos (Nat.mul_pos hd (by omega)) 8
  have hc : 0 < c := sphereGaussianDensityFactor8_pos hNpos
  obtain ⟨Z, hZ, havoid, hblock, hK'⟩ :=
    sphere8_neg_joint_residual_assembly X S hS hA M hr hr0 C hCm hdisjC hunion hmassC hc hp1 hp
      hw hc' hp' hδ hlam dm hdiam
  -- the configuration
  have hnodes_inj := rationalCubePatchNodes8_injective P hdis a m ha hm
  have hrange : ∀ j, Z j ∉ range nodes := by
    intro j hj
    apply (havoid j).2
    obtain ⟨t, ht⟩ := hj
    exact ⟨e0 t, by simp [X, ht]⟩
  have hinj : Function.Injective (Sum.elim nodes Z) := by
    intro u v huv
    cases u with
    | inl u =>
      cases v with
      | inl v => exact congrArg Sum.inl (hnodes_inj huv)
      | inr v => exact False.elim (hrange v ⟨u, huv⟩)
    | inr u =>
      cases v with
      | inl v => exact False.elim (hrange u ⟨v, huv.symm⟩)
      | inr v => exact congrArg Sum.inr (hZ huv)
  have hcard := rationalCubeNodeIndex8_card K a d m ha hm hbudget
  let e : rationalCubeNodeIndex8 K a d m ≃ Fin ((d*m)^8) := Fintype.equivFinOfCardEq hcard
  let Y : Configuration ((d*m)^8) := ⟨(Sum.elim nodes Z) ∘ e.symm, hinj.comp e.symm.injective⟩
  have hYfun : (fun i => Y i) ∘ e = Sum.elim nodes Z := by
    funext u
    simp [Y]
  let e1 := e0.sumCongr (Equiv.refl (Fin ((d^8-K*a^8)*m^8)))
  have he1 : (Sum.elim X Z) ∘ e1 = Sum.elim nodes Z := by
    funext u
    cases u with
    | inl t =>
      change nodes (e0.symm (e0 t)) = nodes t
      rw [e0.symm_apply_apply]
    | inr j => rfl
  -- the s = 4 block
  have hYe := sphereFiniteBlock4_reindex e (fun i => Y i) univ M
  rw [hYfun] at hYe
  have hjoin := sphereFiniteBlock4_reindex e1 (Sum.elim X Z) univ M
  rw [he1] at hjoin
  have hEY : energy4 Y-(7/16:ℝ)*M^2 = sphereFiniteBlock4 (Sum.elim X Z) univ M := by
    rw [← sphereFiniteBlock4_eq_energy4 Y]
    exact hYe.symm.trans hjoin
  have hXS : sphereFiniteBlock4 X S M = sphereFiniteBlock4 nodes S M :=
    sphereFiniteBlock4_reindex e0.symm nodes S M
  -- the K' blocks at a cutoff t
  have hYK : ∀ t : ℝ, kernelBlock8 (negMacroKernel8 c' p' t) (fun i => Y i) univ M =
      kernelBlock8 (negMacroKernel8 c' p' t) (Sum.elim X Z) univ M := by
    intro t
    have hKe := kernelBlock8_reindex (negMacroKernel8 c' p' t) e (fun i => Y i) univ M
    rw [hYfun] at hKe
    have hKjoin := kernelBlock8_reindex (negMacroKernel8 c' p' t) e1 (Sum.elim X Z) univ M
    rw [he1] at hKjoin
    exact hKe.symm.trans hKjoin
  have hKX : ∀ t : ℝ, kernelBlock8 (negMacroKernel8 c' p' t) X S M =
      kernelBlock8 (negMacroKernel8 c' p' t) nodes S M :=
    fun t => kernelBlock8_reindex _ e0.symm nodes S M
  -- the background constant
  have hσ : 0 < sphereProbability8.real Sᶜ := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos hA (measure_ne_top _ _)
  have hσ1 : sphereProbability8.real Sᶜ ≤ 1 := measureReal_le_one
  have hinv : ((sphereProbability8 Sᶜ)⁻¹).toReal = (sphereProbability8.real Sᶜ)⁻¹ := by
    rw [ENNReal.toReal_inv, measureReal_def]
  have hMpos : 0 < M := by
    rw [hMdef]
    exact_mod_cast hNpos
  have h1 : q+(d^8-K*a^8)*m^8 = (d*m)^8 := by
    rw [← hcard]
    change q+(d^8-K*a^8)*m^8 = Fintype.card ((Fin K × (Fin 8 → NodeIndex (a*m))) ⊕ Fin ((d^8-K*a^8)*m^8))
    rw [Fintype.card_sum, Fintype.card_fin]
  have hqM : (q:ℝ) ≤ M := by
    have h2 : q ≤ (d*m)^8 := by omega
    rw [hMdef]
    exact_mod_cast h2
  have hc4 : (105/32)/c^4 = 1/M := by
    rw [hcdef, sphereGaussianDensityFactor8_pow_four hNpos, sphereArea8_mass_real]
    have hp0 : Real.pi ≠ 0 := Real.pi_pos.ne'
    field_simp
    ring
  have hB := shortRange_background_le hMpos hσ hσ1 hp hr hqM hc4
  rw [← hinv] at hB
  -- exact masses of the two parts
  have hqmass : (Fintype.card (Fin q):ℝ) = M*sphereProbability8.real S := by
    have h3 : (q:ℝ)+(((d^8-K*a^8)*m^8 : ℕ):ℝ) = M := by
      rw [hMdef]
      exact_mod_cast h1
    have h4 := measureReal_add_measureReal_compl (μ := sphereProbability8) hS
    rw [probReal_univ] at h4
    rw [Fintype.card_fin]
    calc (q:ℝ) = M-(((d^8-K*a^8)*m^8 : ℕ):ℝ) := by linarith
      _ = M*(sphereProbability8.real S+sphereProbability8.real Sᶜ)-M*sphereProbability8.real Sᶜ := by
          rw [h4, hr]; ring
      _ = M*sphereProbability8.real S := by ring
  have hrmass : (Fintype.card (Fin ((d^8-K*a^8)*m^8)):ℝ) = M*sphereProbability8.real Sᶜ := by
    rw [Fintype.card_fin]
    exact hr
  have hwB := mul_le_mul_of_nonneg_left hB hw.le
  refine ⟨Y, ⟨e, fun t => ?_⟩, ?_, ?_⟩
  · simp [Y]
  · rw [hEY, ← hXS]
    linarith
  · have hcost : ((sphereFiniteBlock4 X S M-sphereFiniteBlock4 (Sum.elim X Z) univ M)+
        w*(2*(((d^8-K*a^8)*m^8 : ℕ):ℝ)^2*(((sphereProbability8 Sᶜ)⁻¹).toReal*((105/32)/c^4/(3-p)))+
          (((d^8-K*a^8)*m^8 : ℕ):ℝ)*(2*(q:ℝ)*(((sphereProbability8 Sᶜ)⁻¹).toReal*((105/32)/c^4/(3-p))))))/lam ≤
        ((sphereFiniteBlock4 nodes S M-(energy4 Y-(7/16:ℝ)*M^2))+w*(4*M/(3-p)))/lam := by
      apply div_le_div_of_nonneg_right _ hlam.le
      rw [hXS, hEY]
      linarith
    intro t ht htδ
    have hU := negMacroBlock8_union_le hc' hp' ht X Z hS M hqmass hrmass
    have hmono := negMacroBlock8_mono_cutoff hc' hp' ht htδ Z Sᶜ M hrmass
    rw [hYK t, ← hKX t]
    linarith

#print axioms rationalCubeFamily8_exists_neg_joint_cutoff

end SphericalRiesz
