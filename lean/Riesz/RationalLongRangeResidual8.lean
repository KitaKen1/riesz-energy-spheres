import Riesz.SphereLongRangeBlock8
import Riesz.RationalJointResidual8

/-! Joint residual selection for the `s = 4` kernel and the long-range kernel.

The residual points are chosen by the sequential first moment for `sphereKernel4 + w·K⁰`
(`K⁰` the off-diagonal long-range kernel).  With `NE₄ + w·NE⁰ ≤ 0`, the two assembly identities,
`NE⁰ = NE_K - r/(p+1)` and the nonnegativity of long-range blocks:

* the `s = 4` block grows by at most `w·(block_K(X,S) + r/(p+1))`;
* the long-range block of the whole configuration is at most
  `block_K(X,S) + (s = 4 block gap)/w + r/(p+1)`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
namespace SphericalRiesz
open Boundary

theorem kernelPair8_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] (k : Sphere8 → Sphere8 → ℝ)
    (e : ι ≃ κ) (X : κ → Sphere8) : kernelPair8 k (X ∘ e) = kernelPair8 k X := by
  have hi (x : Sphere8) : (∑ j, k x (X (e j))) = ∑ j, k x (X j) := e.sum_comp (fun j => k x (X j))
  unfold kernelPair8
  simp only [Function.comp_apply]
  simp_rw [hi]
  exact e.sum_comp (fun i => ∑ j, k (X i) (X j))

theorem kernelBlock8_reindex {ι κ : Type*} [Fintype ι] [Fintype κ] (k : Sphere8 → Sphere8 → ℝ)
    (e : ι ≃ κ) (X : κ → Sphere8) (S : Set Sphere8) (M : ℝ) :
    kernelBlock8 k (X ∘ e) S M = kernelBlock8 k X S M := by
  unfold kernelBlock8
  rw [kernelPair8_reindex k e X]
  have hs := e.sum_comp (fun i => kernelPotential8 k S (X i))
  simp only [Function.comp_apply]
  rw [hs]

theorem longRangeOffKernel8_le {c p : ℝ} (hc : 0 ≤ c) (hp : -1 < p) (x y : Sphere8) :
    longRangeOffKernel8 c p x y ≤ 1/(p+1) := by
  unfold longRangeOffKernel8
  by_cases h : y ∈ ({x}ᶜ : Set Sphere8)
  · rw [Set.indicator_of_mem h]
    exact longRangeKernel8_le hc hp x y
  · rw [Set.indicator_of_notMem h]
    have : 0 < p+1 := by linarith
    positivity

/-- Sphere form of the joint selection with the long-range kernel. -/
theorem sphere8_joint_longRange_assembly {q r : ℕ} (X : Fin q → Sphere8) (S : Set Sphere8)
    (hS : MeasurableSet S) (hA0 : sphereProbability8 Sᶜ ≠ 0) (M : ℝ)
    (hr : (r:ℝ) = M*sphereProbability8.real Sᶜ) {c p w : ℝ} (hc : 0 ≤ c) (hp : -1 < p)
    (hw : 0 < w) :
    ∃ Z : Fin r → Sphere8, Function.Injective Z ∧ (∀ i, Z i ∈ Sᶜ ∧ Z i ∉ range X) ∧
      sphereFiniteBlock4 (Sum.elim X Z) univ M ≤ sphereFiniteBlock4 X S M +
        w*(kernelBlock8 (longRangeKernel8 c p) X S M+(r:ℝ)/(p+1)) ∧
      kernelBlock8 (longRangeKernel8 c p) (Sum.elim X Z) univ M ≤
        kernelBlock8 (longRangeKernel8 c p) X S M +
          (sphereFiniteBlock4 X S M-sphereFiniteBlock4 (Sum.elim X Z) univ M)/w+(r:ℝ)/(p+1) := by
  let := sphereRestrictedProbability8_probability Sᶜ hA0
  have hk := longRangeKernel8_measurable c p
  have hb : ∀ x y, |longRangeKernel8 c p x y| ≤ 1/(p+1) := longRangeKernel8_abs_le hc hp
  have hp1 : 0 < p+1 := by linarith
  have hbad : sphereRestrictedProbability8 Sᶜ (Sᶜᶜ ∪ range X) = 0 :=
    measure_union_null (sphereRestrictedProbability8_compl Sᶜ hS.compl)
      ((finite_range X).measure_zero _)
  have hk2 : ∀ x, Integrable (longRangeOffKernel8 c p x) (sphereRestrictedProbability8 Sᶜ) :=
    fun x => (integrable_const (1/(p+1))).mono'
      (longRangeOffKernel8_row_measurable c p x).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (longRangeOffKernel8_nonneg c p x y)]
        exact longRangeOffKernel8_le hc hp x y)
  have hrow : residualRowPotential (sphereRestrictedProbability8 Sᶜ) (longRangeOffKernel8 c p) =
      residualRowPotential (sphereRestrictedProbability8 Sᶜ) (longRangeKernel8 c p) :=
    funext fun x => integral_congr_ae (longRangeOffKernel8_ae_eq c p _ x)
  have hV2 : Integrable (residualRowPotential (sphereRestrictedProbability8 Sᶜ)
      (longRangeOffKernel8 c p)) (sphereRestrictedProbability8 Sᶜ) := by
    rw [hrow]
    have hm : StronglyMeasurable (residualRowPotential (sphereRestrictedProbability8 Sᶜ)
        (longRangeKernel8 c p)) := hk.integral_prod_right'
    refine (integrable_const (1/(p+1))).mono' hm.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    unfold residualRowPotential
    rw [Real.norm_eq_abs]
    calc |∫ y, longRangeKernel8 c p x y ∂sphereRestrictedProbability8 Sᶜ|
        = ‖∫ y, longRangeKernel8 c p x y ∂sphereRestrictedProbability8 Sᶜ‖ := (Real.norm_eq_abs _).symm
      _ ≤ 1/(p+1)*(sphereRestrictedProbability8 Sᶜ).real univ :=
          norm_integral_le_of_norm_le_const (Eventually.of_forall fun y => by
            rw [Real.norm_eq_abs]; exact hb x y)
      _ = 1/(p+1) := by rw [probReal_univ, mul_one]
  have hL2 : Integrable (kernelCrossRow8 (longRangeKernel8 c p) X S M)
      (sphereRestrictedProbability8 Sᶜ) := by
    unfold kernelCrossRow8
    exact ((integrable_finsetSum _ fun i _ => kernel_row_integrable hk hb _ (X i)).sub
      ((kernelPotential8_integrable hk hb _ S).const_mul M)).const_mul 2
  obtain ⟨Z, hZ, hXB, hjoint⟩ := exists_residualNeutralizedEnergy_joint
    (μ := sphereRestrictedProbability8 Sᶜ) sphereKernel4 (longRangeOffKernel8 c p)
    (sphereResidualCrossRow8 X S M) (kernelCrossRow8 (longRangeKernel8 c p) X S M) hw.le
    sphereKernel4_symm (longRangeOffKernel8_symm c p) sphereKernel4_diagonal
    (longRangeOffKernel8_self c p) sphereKernel4_nonneg (longRangeOffKernel8_nonneg c p)
    (sphereKernel4_restricted_probability_integrable Sᶜ) hk2
    (sphereRestrictedProbability8_row_integrable Sᶜ) hV2
    (sphereResidualCrossRow8_integrable X Sᶜ S M) hL2 (Sᶜᶜ ∪ range X) hbad r
  have h4 := sphereFiniteBlock4_residual_assembly X Z S hS hA0 M hr
  have hL := kernelBlock8_residual_assembly hk hb (longRangeKernel8_symm c p) X Z S hS hA0 M hr
  have hoff := longRange_residual_off_eq (c := c) hp Sᶜ
    (kernelCrossRow8 (longRangeKernel8 c p) X S M) Z hZ
  have hpsd := longRangeBlock8_nonneg hc hp (Sum.elim X Z) univ M
  refine ⟨Z, hZ, fun i => ⟨fun h => hXB i (Or.inl (by rwa [compl_compl])), fun h => hXB i (Or.inr h)⟩,
    ?_, ?_⟩
  · have hlow : -(kernelBlock8 (longRangeKernel8 c p) X S M+(r:ℝ)/(p+1)) ≤
        residualNeutralizedEnergy (sphereRestrictedProbability8 Sᶜ) (longRangeOffKernel8 c p)
          (kernelCrossRow8 (longRangeKernel8 c p) X S M) Z := by
      rw [hoff]
      linarith
    have := mul_le_mul_of_nonneg_left hlow hw.le
    rw [h4]
    linarith
  · have hNE : residualNeutralizedEnergy (sphereRestrictedProbability8 Sᶜ) (longRangeOffKernel8 c p)
        (kernelCrossRow8 (longRangeKernel8 c p) X S M) Z ≤
        (sphereFiniteBlock4 X S M-sphereFiniteBlock4 (Sum.elim X Z) univ M)/w := by
      rw [le_div_iff₀ hw, h4]
      linarith
    rw [hL]
    linarith


/-- The rational near-full patch configuration with the residual chosen jointly for the `s = 4`
kernel and the long-range kernel. -/
theorem rationalCubeFamily8_exists_joint_longRange {K : ℕ}
    (P : Fin K → SmallE8CubePatch8)
    (hdis : Pairwise (fun i j => Disjoint (smallE8CubeSet8 (P i)) (smallE8CubeSet8 (P j))))
    (hu : sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i)) < 1)
    (a d m : ℕ) (ha : 0 < a) (hd : 0 < d) (hm : 8 ≤ m)
    (hbudget : K*a^8 ≤ d^8)
    (hmass : sphereProbability8.real (⋃ i, smallE8CubeSet8 (P i)) = (K:ℝ)*((a:ℝ)/d)^8)
    {c p w : ℝ} (hc : 0 ≤ c) (hp : -1 < p) (hw : 0 < w) :
    ∃ Y : Configuration ((d*m)^8),
      (∃ e : rationalCubeNodeIndex8 K a d m ≃ Fin ((d*m)^8),
        ∀ t, Y (e (Sum.inl t)) = rationalCubePatchNodes8 P a m ha hm t) ∧
      energy4 Y-(7/16:ℝ)*(((d*m)^8:ℕ):ℝ)^2 ≤
        sphereFiniteBlock4 (rationalCubePatchNodes8 P a m ha hm)
          (⋃ i, smallE8CubeSet8 (P i)) (((d*m)^8:ℕ):ℝ)+
          w*(kernelBlock8 (longRangeKernel8 c p) (rationalCubePatchNodes8 P a m ha hm)
            (⋃ i, smallE8CubeSet8 (P i)) (((d*m)^8:ℕ):ℝ)+(((d*m)^8:ℕ):ℝ)/(p+1)) ∧
      kernelBlock8 (longRangeKernel8 c p) (fun i => Y i) univ (((d*m)^8:ℕ):ℝ) ≤
        kernelBlock8 (longRangeKernel8 c p) (rationalCubePatchNodes8 P a m ha hm)
            (⋃ i, smallE8CubeSet8 (P i)) (((d*m)^8:ℕ):ℝ)+
          (sphereFiniteBlock4 (rationalCubePatchNodes8 P a m ha hm)
              (⋃ i, smallE8CubeSet8 (P i)) (((d*m)^8:ℕ):ℝ)-
            (energy4 Y-(7/16:ℝ)*(((d*m)^8:ℕ):ℝ)^2))/w+(((d*m)^8:ℕ):ℝ)/(p+1) := by
  classical
  set S := ⋃ i, smallE8CubeSet8 (P i) with hSdef
  set nodes := rationalCubePatchNodes8 P a m ha hm with hnodes
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
  obtain ⟨Z, hZ, havoid, hblock, hlong⟩ :=
    sphere8_joint_longRange_assembly X S hS hA M hr hc hp hw
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
  -- the long-range blocks
  have hYL := kernelBlock8_reindex (longRangeKernel8 c p) e (fun i => Y i) univ M
  rw [hYfun] at hYL
  have hjL := kernelBlock8_reindex (longRangeKernel8 c p) e1 (Sum.elim X Z) univ M
  rw [he1] at hjL
  have hXL : kernelBlock8 (longRangeKernel8 c p) X S M =
      kernelBlock8 (longRangeKernel8 c p) nodes S M :=
    kernelBlock8_reindex (longRangeKernel8 c p) e0.symm nodes S M
  have hp1 : 0 < p+1 := by linarith
  have hrM : (r:ℝ)/(p+1) ≤ M/(p+1) := by
    apply div_le_div_of_nonneg_right _ hp1.le
    have h1 : q+r = (d*m)^8 := by
      rw [← hcard]
      change q+r = Fintype.card ((Fin K × (Fin 8 → NodeIndex (a*m))) ⊕ Fin r)
      rw [Fintype.card_sum, Fintype.card_fin]
    have h2 : r ≤ (d*m)^8 := by omega
    rw [hMdef]
    exact_mod_cast h2
  have hL0 := longRangeBlock8_nonneg hc hp nodes S M
  refine ⟨Y, ⟨e, fun t => ?_⟩, ?_, ?_⟩
  · simp [Y]
  · rw [hEY, ← hXS, ← hXL]
    calc sphereFiniteBlock4 (Sum.elim X Z) univ M
        ≤ sphereFiniteBlock4 X S M+w*(kernelBlock8 (longRangeKernel8 c p) X S M+(r:ℝ)/(p+1)) :=
          hblock
      _ ≤ sphereFiniteBlock4 X S M+w*(kernelBlock8 (longRangeKernel8 c p) X S M+M/(p+1)) := by
          have := mul_le_mul_of_nonneg_left hrM hw.le
          nlinarith
  · rw [hEY, ← hXS, ← hXL]
    calc kernelBlock8 (longRangeKernel8 c p) (fun i => Y i) univ M
        = kernelBlock8 (longRangeKernel8 c p) (Sum.elim X Z) univ M := hYL.symm.trans hjL
      _ ≤ kernelBlock8 (longRangeKernel8 c p) X S M+
          (sphereFiniteBlock4 X S M-sphereFiniteBlock4 (Sum.elim X Z) univ M)/w+(r:ℝ)/(p+1) :=
          hlong
      _ ≤ _ := by linarith

end SphericalRiesz
