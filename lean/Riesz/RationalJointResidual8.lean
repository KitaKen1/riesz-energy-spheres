import Riesz.RationalPatchSeparation8

/-! The rational near-full patch configuration with a jointly selected residual.

Compared with `rationalCubeFamily8_exists_energy_upper`, the residual points are chosen for the
combined kernel `sphereKernel4 + w·k_φ`.  The `s = 4` energy grows by at most `w·4N/(3-p)` and
the weighted short-range energy of the whole configuration is at most that of the patch nodes
plus `(block gap)/w + 4N/(3-p)`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
namespace SphericalRiesz
open Boundary

theorem shortRange_background_le {r q : ℕ} {M σ c p : ℝ} (hM : 0 < M) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hp : p < 3) (hr : (r:ℝ) = M*σ) (hq : (q:ℝ) ≤ M) (hc4 : (105/32)/c^4 = 1/M) :
    2*(r:ℝ)^2*(σ⁻¹*((105/32)/c^4/(3-p)))+(r:ℝ)*(2*(q:ℝ)*(σ⁻¹*((105/32)/c^4/(3-p)))) ≤
      4*M/(3-p) := by
  have h3 : 0 < 3-p := by linarith
  rw [hc4, hr]
  have e1 : 2*(M*σ)^2*(σ⁻¹*(1/M/(3-p))) = 2*M*σ/(3-p) := by
    field_simp
  have e2 : M*σ*(2*(q:ℝ)*(σ⁻¹*(1/M/(3-p)))) = 2*(q:ℝ)/(3-p) := by
    field_simp
  rw [e1, e2]
  have h4 : 2*M*σ/(3-p) ≤ 2*M/(3-p) := by
    apply div_le_div_of_nonneg_right _ h3.le
    nlinarith
  have h5 : 2*(q:ℝ)/(3-p) ≤ 2*M/(3-p) := div_le_div_of_nonneg_right (by linarith) h3.le
  have h6 : 4*M/(3-p) = 2*M/(3-p)+2*M/(3-p) := by ring
  linarith

theorem rationalCubeFamily8_exists_joint_shortRange {K : ℕ}
    (P : Fin K → SmallE8CubePatch8)
    (hdis : Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i)) (smallE8CubeSet8 (P j))))
    (hu : sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i)) < 1)
    (a d m : ℕ) (ha : 0 < a) (hd : 0 < d) (hm : 8 ≤ m)
    (hbudget : K*a^8 ≤ d^8)
    (hmass : sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i)) = (K:ℝ)*((a:ℝ)/d)^8)
    {p w : ℝ} (hp1 : -1 ≤ p) (hp : p < 3) (hw : 0 < w) :
    ∃ Y : Configuration ((d*m)^8),
      (∃ e : rationalCubeNodeIndex8 K a d m ≃ Fin ((d*m)^8),
        ∀ t, Y (e (Sum.inl t)) = rationalCubePatchNodes8 P a m ha hm t) ∧
      energy4 Y-(7/16:ℝ)*(((d*m)^8:ℕ):ℝ)^2 ≤
        sphereFiniteBlock4 (rationalCubePatchNodes8 P a m ha hm)
          (⋃ i, smallE8CubeSet8 (P i)) (((d*m)^8:ℕ):ℝ)+w*(4*(((d*m)^8:ℕ):ℝ)/(3-p)) ∧
      finitePairSum (shortRangeKernel8 (sphereGaussianDensityFactor8 ((d*m)^8)) p) (fun i => Y i) ≤
        finitePairSum (shortRangeKernel8 (sphereGaussianDensityFactor8 ((d*m)^8)) p)
            (rationalCubePatchNodes8 P a m ha hm)+
          (sphereFiniteBlock4 (rationalCubePatchNodes8 P a m ha hm)
              (⋃ i, smallE8CubeSet8 (P i)) (((d*m)^8:ℕ):ℝ)-
            (energy4 Y-(7/16:ℝ)*(((d*m)^8:ℕ):ℝ)^2))/w+4*(((d*m)^8:ℕ):ℝ)/(3-p) := by
  classical
  set S := ⋃ i, smallE8CubeSet8 (P i) with hSdef
  set nodes := rationalCubePatchNodes8 P a m ha hm with hnodes
  set c := sphereGaussianDensityFactor8 ((d*m)^8) with hcdef
  let e0 := Fintype.equivFin (Fin K × (Fin 8 → NodeIndex (a*m)))
  set q := Fintype.card (Fin K × (Fin 8 → NodeIndex (a*m))) with hqdef
  let X : Fin q → Sphere8 := nodes ∘ e0.symm
  set r := (d^8-K*a^8)*m^8 with hrdef
  set M : ℝ := (((d*m)^8:ℕ):ℝ) with hMdef
  have hS : MeasurableSet S := MeasurableSet.iUnion
    (fun i => (smallE8CubeSet8_isCompact (P i)).isClosed.measurableSet)
  have hA := sphere8_complement_mass_ne_zero S hS hu
  have hr : (r:ℝ) = M*sphereProbability8.real Sᶜ :=
    rationalCubeFamily8_residual_mass_matching P a d m hd (by omega) hbudget hmass
  have hNpos : 0 < (d*m)^8 := pow_pos (Nat.mul_pos hd (by omega)) 8
  have hc : 0 < c := sphereGaussianDensityFactor8_pos hNpos
  obtain ⟨Z, hZ, havoid, hblock, hpair⟩ :=
    sphere8_joint_residual_assembly X S hS hA M hr hc hp1 hp hw
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
  let e1 := e0.sumCongr (Equiv.refl (Fin r))
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
  -- the short-range sum
  have hYs := finitePairSum_reindex (shortRangeKernel8 c p) e (fun i => Y i)
  rw [hYfun] at hYs
  have hjs := finitePairSum_reindex (shortRangeKernel8 c p) e1 (Sum.elim X Z)
  rw [he1] at hjs
  have hXs : finitePairSum (shortRangeKernel8 c p) X = finitePairSum (shortRangeKernel8 c p) nodes :=
    finitePairSum_reindex (shortRangeKernel8 c p) e0.symm nodes
  have hsplit := finitePairSum_sum_elim_shortRange c p X Z
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
  have hqM : (q:ℝ) ≤ M := by
    have h1 : q+r = (d*m)^8 := by
      rw [← hcard]
      change q+r = Fintype.card ((Fin K × (Fin 8 → NodeIndex (a*m))) ⊕ Fin r)
      rw [Fintype.card_sum, Fintype.card_fin]
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
  refine ⟨Y, ⟨e, fun t => ?_⟩, ?_, ?_⟩
  · simp [Y]
  · rw [hEY, ← hXS]
    calc sphereFiniteBlock4 (Sum.elim X Z) univ M
        ≤ sphereFiniteBlock4 X S M+w*(2*(r:ℝ)^2*(((sphereProbability8 Sᶜ)⁻¹).toReal*
            ((105/32)/c^4/(3-p)))+(r:ℝ)*(2*(q:ℝ)*(((sphereProbability8 Sᶜ)⁻¹).toReal*
            ((105/32)/c^4/(3-p))))) := hblock
      _ ≤ sphereFiniteBlock4 X S M+w*(4*M/(3-p)) := by
          have := mul_le_mul_of_nonneg_left hB hw.le
          linarith
  · rw [hEY, ← hXS, ← hXs]
    calc finitePairSum (shortRangeKernel8 c p) (fun i => Y i)
        = finitePairSum (shortRangeKernel8 c p) (Sum.elim X Z) := hYs.symm.trans hjs
      _ = finitePairSum (shortRangeKernel8 c p) X+(residualPairEnergy (shortRangeKernel8 c p) Z+
            ∑ j, shortRangeCrossRow8 c p X (Z j)) := hsplit
      _ ≤ finitePairSum (shortRangeKernel8 c p) X+((sphereFiniteBlock4 X S M-
            sphereFiniteBlock4 (Sum.elim X Z) univ M)/w+(2*(r:ℝ)^2*(((sphereProbability8 Sᶜ)⁻¹).toReal*
            ((105/32)/c^4/(3-p)))+(r:ℝ)*(2*(q:ℝ)*(((sphereProbability8 Sᶜ)⁻¹).toReal*
            ((105/32)/c^4/(3-p)))))) := by linarith
      _ ≤ _ := by linarith

end SphericalRiesz
