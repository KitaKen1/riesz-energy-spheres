/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in licenses/Mathlib-Apache-2.0.txt.
Authors: Rémy Degenne; adapted for this project by Codex

The proof of `measurable_lintegral_of_finite_fibers` adapts the simple-function argument
in Mathlib/Probability/Kernel/MeasurableLIntegral.lean (Rémy Degenne, Apache 2.0),
at the project's pinned Mathlib revision. It uses the existing finite-fiber rectangle lemma.
-/
import E8Leech.StationaryProcess
import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Counting kernels and measurable integration without labelling points

Finite-on-compacts configurations yield a measurable counting kernel. Rather than assuming
uniform bounds on the number of points, we integrate in compact balls first and exhaust the
space. This avoids a measurable enumeration of points and a global s-finite-kernel assumption.
-/

noncomputable section

namespace E8Leech

open Set MeasureTheory ProbabilityTheory Function
open scoped ENNReal Classical

theorem measurable_lintegral_of_finite_fibers
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (κ : Kernel A B) (hκ : ∀ a, IsFiniteMeasure (κ a))
    {f : A × B → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun a => ∫⁻ b, f (a, b) ∂κ a) := by
  let F : ℕ → SimpleFunc (A × B) ℝ≥0∞ := SimpleFunc.eapprox f
  have h : ∀ a b, ⨆ n, F n (a, b) = f (a, b) := fun a b =>
    SimpleFunc.iSup_eapprox_apply hf (a, b)
  simp_rw [← h]
  have hi : ∀ a, (∫⁻ b, ⨆ n, F n (a, b) ∂κ a) = ⨆ n, ∫⁻ b, F n (a, b) ∂κ a := by
    intro a
    apply lintegral_iSup
    · exact fun n => (F n).measurable.comp measurable_prodMk_left
    · exact fun i j hij b => SimpleFunc.monotone_eapprox f hij _
  simp_rw [hi]
  refine Measurable.iSup fun n => ?_
  refine SimpleFunc.induction
    (motive := fun g => Measurable (fun a => ∫⁻ b, g (a, b) ∂κ a)) ?_ ?_ (F n)
  · intro v t ht
    simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
      SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
    change Measurable (fun a => ∫⁻ b, t.indicator (Function.const (A × B) v) (a, b) ∂κ a)
    unfold Function.const
    simp_rw [lintegral_indicator_const_comp measurable_prodMk_left ht _]
    exact (Kernel.measurable_kernel_prodMk_left_of_finite ht hκ).const_mul v
  · intro g₁ g₂ _ hm₁ hm₂
    simp only [SimpleFunc.coe_add, Pi.add_apply]
    have hadd : (fun a => ∫⁻ b, g₁ (a, b) + g₂ (a, b) ∂κ a) =
        (fun a => ∫⁻ b, g₁ (a, b) ∂κ a) + fun a => ∫⁻ b, g₂ (a, b) ∂κ a := by
      ext a
      rw [Pi.add_apply, lintegral_add_left (by fun_prop)]
    rw [hadd]
    exact hm₁.add hm₂

def countingKernel (d : ℕ) : Kernel (Configuration (Ambient d)) (Ambient d) where
  toFun c := Measure.count.restrict c.support
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun W hW => ?_
    simpa only [Measure.restrict_apply hW, Set.inter_comm, Configuration.count] using
      Configuration.measurable_count hW

@[simp] theorem countingKernel_apply {d : ℕ} (c : Configuration (Ambient d))
    {W : Set (Ambient d)} (hW : MeasurableSet W) : countingKernel d c W = c.count W := by
  simp only [countingKernel, Kernel.coe_mk, Measure.restrict_apply hW,
    Configuration.count, Set.inter_comm]

def boundedCountingKernel (d : ℕ) (R : ℝ) : Kernel (Configuration (Ambient d)) (Ambient d) :=
  (countingKernel d).restrict
    (measurableSet_closedBall : MeasurableSet (Metric.closedBall (0 : Ambient d) R))

theorem boundedCountingKernel_finite {d : ℕ} (R : ℝ) (c : Configuration (Ambient d)) :
    IsFiniteMeasure (boundedCountingKernel d R c) := by
  apply (isFiniteMeasure_iff _).mpr
  simpa only [boundedCountingKernel, Kernel.restrict_apply, Measure.restrict_apply_univ,
    countingKernel_apply c measurableSet_closedBall, lt_top_iff_ne_top] using
    c.count_ne_top_of_compact (isCompact_closedBall (0 : Ambient d) R)

theorem countingKernel_lintegral_eq_tsum {d : ℕ} (c : Configuration (Ambient d))
    (f : Ambient d → ℝ≥0∞) : (∫⁻ x, f x ∂countingKernel d c) = ∑' x : c.support, f x := by
  change (∫⁻ x in c.support, f x ∂Measure.count) = _
  simpa only [Measure.count_singleton, mul_one] using
    (lintegral_countable f (c.countable_support 0) (μ := Measure.count))

theorem closedBall_nat_cover (d : ℕ) : (⋃ n : ℕ, Metric.closedBall (0 : Ambient d) (n : ℝ)) = univ := by
  ext x
  simp only [Set.mem_iUnion, Metric.mem_closedBall, Set.mem_univ, iff_true]
  obtain ⟨n, hn⟩ := exists_nat_gt (dist x 0)
  exact ⟨n, hn.le⟩

theorem countingKernel_lintegral_eq_iSup {d : ℕ} (c : Configuration (Ambient d))
    (f : Ambient d → ℝ≥0∞) :
    (∫⁻ x, f x ∂countingKernel d c) =
      ⨆ n : ℕ, ∫⁻ x, f x ∂boundedCountingKernel d (n : ℝ) c := by
  change (∫⁻ x, f x ∂countingKernel d c) =
    ⨆ n : ℕ, ∫⁻ x in Metric.closedBall 0 (n : ℝ), f x ∂countingKernel d c
  rw [← setLIntegral_iUnion_of_directed f]
  · rw [closedBall_nat_cover, Measure.restrict_univ]
  · exact monotone_nat_of_le_succ (fun n => Metric.closedBall_subset_closedBall (by norm_num)) |>.directed_le

theorem measurable_countingKernel_lintegral {d : ℕ}
    {f : Configuration (Ambient d) × Ambient d → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun c => ∫⁻ x, f (c, x) ∂countingKernel d c) := by
  simp_rw [countingKernel_lintegral_eq_iSup]
  exact Measurable.iSup fun n => measurable_lintegral_of_finite_fibers
    (boundedCountingKernel d n) (boundedCountingKernel_finite n) hf

/-- Additional parameters (such as the anchored point) need no measurable enumeration. -/
theorem measurable_countingKernel_lintegral_param {d : ℕ}
    {A : Type*} [MeasurableSpace A] (g : A → Configuration (Ambient d)) (hg : Measurable g)
    {f : A × Ambient d → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun a => ∫⁻ x, f (a, x) ∂countingKernel d (g a)) := by
  simp_rw [countingKernel_lintegral_eq_iSup]
  refine Measurable.iSup fun n => ?_
  let κ : Kernel A (Ambient d) :=
    ⟨fun a => boundedCountingKernel d n (g a), (boundedCountingKernel d n).measurable.comp hg⟩
  exact measurable_lintegral_of_finite_fibers κ
    (fun a => boundedCountingKernel_finite n (g a)) hf

theorem measurable_count_query {d : ℕ}
    {A : Type*} [MeasurableSpace A] (g : A → Configuration (Ambient d)) (hg : Measurable g)
    {T : Set (A × Ambient d)} (hT : MeasurableSet T) :
    Measurable (fun a => (g a).count (Prod.mk a ⁻¹' T)) := by
  have hm := measurable_countingKernel_lintegral_param g hg
    (measurable_const.indicator hT : Measurable (T.indicator (fun _ => (1 : ℝ≥0∞))))
  have heq : (fun a => ∫⁻ x, T.indicator (fun _ => (1 : ℝ≥0∞)) (a, x)
      ∂countingKernel d (g a)) = fun a => (g a).count (Prod.mk a ⁻¹' T) := by
    ext a
    rw [lintegral_indicator_const_comp measurable_prodMk_left hT, one_mul]
    exact countingKernel_apply _ (measurable_prodMk_left hT)
  rwa [heq] at hm

end E8Leech
