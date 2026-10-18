import E8Leech.SpectralSlackGap

/-!
# Nonnegative potential mixtures commute with anchored and lattice energies

Tonelli, not signed Fourier interchange, closes the positive-mixture gap.
A measurable family of checked gaps integrates to a checked mixture gap.
The actual CKMRV Gaussian certificates and a Riesz Laplace representation
remain separate proof obligations.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory
open scoped ENNReal Classical

def potentialMixture {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (ν : Measure Θ) (V : Θ → Ambient d → Ambient d → ℝ≥0∞)
    (x y : Ambient d) : ℝ≥0∞ := ∫⁻ θ, V θ x y ∂ν

def latticePotentialEnergy {d : ℕ} (Λ : Set (Ambient d))
    (V : Ambient d → Ambient d → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' y : Λ, if (y : Ambient d) = 0 then 0 else V 0 y

theorem latticePotentialEnergy_riesz {d : ℕ} (Λ : Set (Ambient d)) (s : ℝ) :
    latticePotentialEnergy Λ (rieszPotential s) = latticeRieszEnergy Λ s := rfl

theorem measurable_potentialMixture {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (ν : Measure Θ) [SFinite ν]
    (V : Θ → Ambient d → Ambient d → ℝ≥0∞)
    (hV : Measurable (fun p : Θ × (Ambient d × Ambient d) => V p.1 p.2.1 p.2.2)) :
    Measurable (Function.uncurry (potentialMixture ν V)) := by
  exact hV.lintegral_prod_left

theorem measurable_orderedWindowEnergy_param {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (V : Θ → Ambient d → Ambient d → ℝ≥0∞)
    (hV : Measurable (fun p : Θ × (Ambient d × Ambient d) => V p.1 p.2.1 p.2.2))
    {W : Set (Ambient d)} (hW : MeasurableSet W) :
    Measurable (fun p : Θ × Configuration (Ambient d) => orderedWindowEnergy (V p.1) p.2 W) := by
  have hi : Measurable (fun p : (Θ × Configuration (Ambient d)) × Ambient d =>
      ∫⁻ y, if y = p.2 then 0 else V p.1.1 p.2 y ∂countingKernel d p.1.2) := by
    apply measurable_countingKernel_lintegral_param (d := d)
      (f := fun p : ((Θ × Configuration (Ambient d)) × Ambient d) × Ambient d =>
        if p.2 = p.1.2 then 0 else V p.1.1.1 p.1.2 p.2)
      (g := fun p : (Θ × Configuration (Ambient d)) × Ambient d => p.1.2)
      (measurable_fst.snd)
    exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_fst.snd)
      measurable_const
      (hV.comp (measurable_fst.fst.fst.prodMk
        (measurable_fst.snd.prodMk measurable_snd)))
  simp_rw [orderedWindowEnergy_eq_kernel]
  apply measurable_countingKernel_lintegral_param (d := d)
    (f := fun p : (Θ × Configuration (Ambient d)) × Ambient d => if p.2 ∈ W then
      ∫⁻ y, if y = p.2 then 0 else V p.1.1 p.2 y ∂countingKernel d p.1.2 else 0)
    (g := fun p : Θ × Configuration (Ambient d) => p.2) measurable_snd
  exact Measurable.ite (hW.preimage measurable_snd) hi measurable_const

theorem orderedWindowEnergy_potentialMixture {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (ν : Measure Θ) (V : Θ → Ambient d → Ambient d → ℝ≥0∞)
    (hV : ∀ x y, Measurable (fun θ => V θ x y))
    (c : Configuration (Ambient d)) (W : Set (Ambient d)) :
    orderedWindowEnergy (potentialMixture ν V) c W =
      ∫⁻ θ, orderedWindowEnergy (V θ) c W ∂ν := by
  let : Countable c.support := (c.countable_support (0 : Ambient d)).to_subtype
  unfold orderedWindowEnergy potentialMixture
  rw [lintegral_tsum]
  · apply tsum_congr
    intro x
    by_cases hx : (x : Ambient d) ∈ W
    · simp only [if_pos hx]
      rw [lintegral_tsum]
      · apply tsum_congr
        intro y
        by_cases hy : (y : Ambient d) = (x : Ambient d) <;> simp [hy]
      · intro y
        by_cases hy : (y : Ambient d) = (x : Ambient d) <;>
          simp only [hy, ↓reduceIte]
        · exact measurable_const.aemeasurable
        · exact (hV x y).aemeasurable
    · simp [hx]
  · intro x
    by_cases hx : (x : Ambient d) ∈ W
    · simp only [if_pos hx]
      apply Measurable.aemeasurable
      apply Measurable.tsum
      intro y
      by_cases hy : (y : Ambient d) = (x : Ambient d) <;>
        simp only [hy, ↓reduceIte]
      · exact measurable_const
      · exact hV x y
    · simp only [if_neg hx]
      exact measurable_const.aemeasurable

theorem latticePotentialEnergy_potentialMixture {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (ν : Measure Θ) (V : Θ → Ambient d → Ambient d → ℝ≥0∞)
    (hV : ∀ x y, Measurable (fun θ => V θ x y))
    (Λ : Set (Ambient d)) (hΛ : Λ.Countable) :
    latticePotentialEnergy Λ (potentialMixture ν V) =
      ∫⁻ θ, latticePotentialEnergy Λ (V θ) ∂ν := by
  let : Countable Λ := hΛ.to_subtype
  unfold latticePotentialEnergy potentialMixture
  rw [lintegral_tsum]
  · apply tsum_congr
    intro y
    by_cases hy : (y : Ambient d) = 0 <;> simp [hy]
  · intro y
    by_cases hy : (y : Ambient d) = 0 <;> simp only [hy, ↓reduceIte]
    · exact measurable_const.aemeasurable
    · exact (hV 0 y).aemeasurable

theorem expected_orderedWindowEnergy_potentialMixture
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (ν : Measure Θ) [SFinite ν] (μ : Measure (Configuration (Ambient d))) [SFinite μ]
    (V : Θ → Ambient d → Ambient d → ℝ≥0∞)
    (hV : Measurable (fun p : Θ × (Ambient d × Ambient d) => V p.1 p.2.1 p.2.2))
    {W : Set (Ambient d)} (hW : MeasurableSet W) :
    (∫⁻ c, orderedWindowEnergy (potentialMixture ν V) c W ∂μ) =
      ∫⁻ θ, ∫⁻ c, orderedWindowEnergy (V θ) c W ∂μ ∂ν := by
  have hsec : ∀ x y, Measurable (fun θ => V θ x y) :=
    fun x y => hV.comp (measurable_id.prodMk (measurable_const.prodMk measurable_const))
  simp_rw [orderedWindowEnergy_potentialMixture ν V hsec]
  exact lintegral_lintegral_swap
    ((measurable_orderedWindowEnergy_param V hV hW).comp measurable_swap).aemeasurable

theorem expected_potentialMixture_gap
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (ν : Measure Θ) [SFinite ν] (μ : Measure (Configuration (Ambient d))) [SFinite μ]
    (P V : Θ → Ambient d → Ambient d → ℝ≥0∞)
    (hP : Measurable (fun p : Θ × (Ambient d × Ambient d) => P p.1 p.2.1 p.2.2))
    (hV : Measurable (fun p : Θ × (Ambient d × Ambient d) => V p.1 p.2.1 p.2.2))
    (Λ : Set (Ambient d)) (hΛ : Λ.Countable)
    (hgap : ∀ᵐ θ ∂ν, latticePotentialEnergy Λ (P θ) +
      (∫⁻ c, orderedWindowEnergy (V θ) c (unitWindow d) ∂μ) ≤
      ∫⁻ c, orderedWindowEnergy (P θ) c (unitWindow d) ∂μ) :
    latticePotentialEnergy Λ (potentialMixture ν P) +
      (∫⁻ c, orderedWindowEnergy (potentialMixture ν V) c (unitWindow d) ∂μ) ≤
      ∫⁻ c, orderedWindowEnergy (potentialMixture ν P) c (unitWindow d) ∂μ := by
  have hsec : ∀ x y, Measurable (fun θ => P θ x y) :=
    fun x y => hP.comp (measurable_id.prodMk (measurable_const.prodMk measurable_const))
  have hbase : Measurable (fun θ => latticePotentialEnergy Λ (P θ)) := by
    let : Countable Λ := hΛ.to_subtype
    apply Measurable.tsum
    intro y
    by_cases hy : (y : Ambient d) = 0 <;> simp only [hy, ↓reduceIte]
    · exact measurable_const
    · exact hsec 0 y
  rw [latticePotentialEnergy_potentialMixture ν P hsec Λ hΛ,
    expected_orderedWindowEnergy_potentialMixture ν μ V hV (measurable_unitWindow d),
    expected_orderedWindowEnergy_potentialMixture ν μ P hP (measurable_unitWindow d),
    ← lintegral_add_left hbase]
  exact lintegral_mono_ae hgap

theorem potentialMixture_lower_on_parameter_set
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (ν : Measure Θ) (V : Θ → Ambient d → Ambient d → ℝ≥0∞)
    {A : Set Θ} (hA : MeasurableSet A) (κ : ℝ≥0∞)
    (x y : Ambient d) (hlower : ∀ θ ∈ A, κ ≤ V θ x y) :
    κ * ν A ≤ potentialMixture ν V x y := by
  rw [← lintegral_indicator_const hA κ]
  apply lintegral_mono
  intro θ
  by_cases hθ : θ ∈ A
  · simpa only [indicator_of_mem hθ] using hlower θ hθ
  · simp [hθ]

end E8Leech
