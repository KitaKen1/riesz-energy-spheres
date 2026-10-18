import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.Basic

/-! A one-sided integral lower-limit argument using the known target as a
truncation. Real dominated convergence avoids ENNReal conversion and the
default value of an unbounded real liminf. -/

set_option autoImplicit false
noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace SphericalRiesz

theorem min_norm_le_of_lower_bound {g f M : ℝ} (hM : 0 ≤ M) (hf : -M ≤ f) :
    ‖min g f‖ ≤ |g|+M := by
  rw [Real.norm_eq_abs,abs_le]
  constructor
  · apply le_min
    · linarith [neg_abs_le g]
    · linarith [abs_nonneg g]
  · exact (min_le_left g f).trans (by linarith [le_abs_self g])

theorem min_tendsto_of_eventual_lower {ι : Type*} {l : Filter ι}
    {f : ι → ℝ} {g : ℝ}
    (hl : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in l, g-ε ≤ f n) :
    Tendsto (fun n => min g (f n)) l (𝓝 g) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [hl ((g-a)/2) (by linarith)] with n hn
    exact lt_min ha (by linarith)
  · intro a ha
    exact Eventually.of_forall (fun n => (min_le_left g (f n)).trans_lt ha)

theorem realMin_aestronglyMeasurable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g f : α → ℝ}
    (hg : AEStronglyMeasurable g μ) (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => min (g x) (f x)) μ := by
  have hm : Continuous (fun p : ℝ × ℝ => min p.1 p.2) := by fun_prop
  exact hm.comp_aestronglyMeasurable (hg.prodMk hf)

theorem realMin_integrable_of_lower {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g f M : α → ℝ}
    (hg : Integrable g μ) (hf : Integrable f μ) (hM : Integrable M μ)
    (hM0 : ∀ᵐ x ∂μ, 0 ≤ M x) (hl : ∀ᵐ x ∂μ, -M x ≤ f x) :
    Integrable (fun x => min (g x) (f x)) μ := by
  apply (hg.norm.add hM).mono'
    (realMin_aestronglyMeasurable hg.aestronglyMeasurable hf.aestronglyMeasurable)
  filter_upwards [hM0,hl] with x hx hxl
  simpa only [Real.norm_eq_abs,Pi.add_apply] using min_norm_le_of_lower_bound hx hxl

theorem realMin_integral_tendsto_of_lower {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g M : α → ℝ} {f : ℕ → α → ℝ}
    (hg : Integrable g μ) (hf : ∀ n, Integrable (f n) μ) (hM : Integrable M μ)
    (hM0 : ∀ᵐ x ∂μ, 0 ≤ M x) (hl : ∀ n, ∀ᵐ x ∂μ, -M x ≤ f n x)
    (hp : ∀ᵐ x ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, g x-ε ≤ f n x) :
    Tendsto (fun n => ∫ x, min (g x) (f n x) ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖g x‖+M x)
  · intro n
    exact realMin_aestronglyMeasurable hg.aestronglyMeasurable (hf n).aestronglyMeasurable
  · exact hg.norm.add hM
  · intro n
    filter_upwards [hM0,hl n] with x hx hxl
    simpa only [Real.norm_eq_abs] using min_norm_le_of_lower_bound hx hxl
  · filter_upwards [hp] with x hx
    exact min_tendsto_of_eventual_lower hx

theorem integral_le_of_eventual_lower_profile {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g M : α → ℝ} {f : ℕ → α → ℝ} {C : ℝ}
    (hg : Integrable g μ) (hf : ∀ n, Integrable (f n) μ) (hM : Integrable M μ)
    (hM0 : ∀ᵐ x ∂μ, 0 ≤ M x) (hl : ∀ n, ∀ᵐ x ∂μ, -M x ≤ f n x)
    (hp : ∀ᵐ x ∂μ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, g x-ε ≤ f n x)
    (hC : ∀ n, (∫ x, f n x ∂μ) ≤ C) : (∫ x, g x ∂μ) ≤ C := by
  apply le_of_tendsto (realMin_integral_tendsto_of_lower hg hf hM hM0 hl hp)
  apply Eventually.of_forall
  intro n
  exact (integral_mono (realMin_integrable_of_lower hg (hf n) hM hM0 (hl n))
    (hf n) (fun x => min_le_right _ _)).trans (hC n)

end SphericalRiesz
