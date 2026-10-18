import Riesz.CompactSchwartzBackground
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Order.Compact

/-!
Uniform approximate-identity rows for actual compact continuous cutoffs
and actual L1 kernels. Dominated convergence is applied along arbitrary
center sequences; selecting a bad center at each index upgrades this to a
uniform estimate. No compactification of the center variable, sup integral,
tail cutoff estimate, or assumed uniform convergence witness is needed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped Topology SchwartzMap FourierTransform
namespace SphericalRiesz

variable {d : ℕ}

def compactApproximateRow (q k : EuclideanSpace ℝ (Fin d) → ℝ) (a : ℝ)
    (u : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ h, q (u-a⁻¹ • h)*k h

theorem compactCutoff_norm_bound (q : EuclideanSpace ℝ (Fin d) → ℝ)
    (hq : Continuous q) (hqs : HasCompactSupport q) :
    ∃ M ≥ 0, ∀ u, ‖q u‖ ≤ M := by
  obtain ⟨M,hM⟩ := ((hqs.isCompact_range hq).image continuous_norm).bddAbove
  have hbound : ∀ u, ‖q u‖ ≤ M := fun u => hM (mem_image_of_mem norm (mem_range_self u))
  exact ⟨M,(norm_nonneg (q 0)).trans (hbound 0),hbound⟩

theorem compactApproximateRow_integrable (q : EuclideanSpace ℝ (Fin d) → ℝ)
    (hq : Continuous q) (hqs : HasCompactSupport q)
    {k : EuclideanSpace ℝ (Fin d) → ℝ} (hk : Integrable k)
    (a : ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun h => q (u-a⁻¹ • h)*k h) := by
  obtain ⟨M,hM,hbound⟩ := compactCutoff_norm_bound q hq hqs
  apply (hk.norm.const_mul M).mono'
    ((hq.comp (by fun_prop)).aestronglyMeasurable.mul hk.aestronglyMeasurable)
  filter_upwards [] with h
  change ‖q (u-a⁻¹ • h)*k h‖ ≤ M*‖k h‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hbound _) (norm_nonneg _)

theorem compactApproximateRow_error_eq_integral (q : EuclideanSpace ℝ (Fin d) → ℝ)
    (hq : Continuous q) (hqs : HasCompactSupport q)
    {k : EuclideanSpace ℝ (Fin d) → ℝ} (hk : Integrable k)
    (a : ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    compactApproximateRow q k a u-q u*(∫ h, k h) =
      ∫ h, (q (u-a⁻¹ • h)-q u)*k h := by
  calc
    _ = ∫ h, q (u-a⁻¹ • h)*k h-q u*k h := by
      rw [integral_sub (compactApproximateRow_integrable q hq hqs hk a u)
        (hk.const_mul (q u)), integral_const_mul]
      rfl
    _ = _ := integral_congr_ae (Eventually.of_forall (fun h => by ring))

theorem compactCutoff_translation_difference_tendsto (q : EuclideanSpace ℝ (Fin d) → ℝ)
    (hq : Continuous q) (hqs : HasCompactSupport q)
    (u v : ℕ → EuclideanSpace ℝ (Fin d)) (hv : Tendsto v atTop (𝓝 0)) :
    Tendsto (fun n => q (u n-v n)-q (u n)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuous_iff.mp
    (hqs.uniformContinuous_of_continuous hq) ε hε
  have he := Metric.tendsto_nhds.mp hv δ hδ
  filter_upwards [he] with n hn
  have hd : dist (u n-v n) (u n) < δ := by
    simpa only [dist_eq_norm, sub_sub_cancel_left, norm_neg, sub_zero] using hn
  simpa only [dist_zero_right, dist_eq_norm, sub_zero] using hclose hd

theorem compactApproximateRow_error_tendsto_any_centers
    (q : EuclideanSpace ℝ (Fin d) → ℝ) (hq : Continuous q) (hqs : HasCompactSupport q)
    {k : EuclideanSpace ℝ (Fin d) → ℝ} (hk : Integrable k)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) (u : ℕ → EuclideanSpace ℝ (Fin d)) :
    Tendsto (fun n => compactApproximateRow q k (a n) (u n)-q (u n)*(∫ h, k h))
      atTop (𝓝 0) := by
  simp_rw [compactApproximateRow_error_eq_integral q hq hqs hk]
  obtain ⟨M,hM,hbound⟩ := compactCutoff_norm_bound q hq hqs
  have ht : Tendsto (fun n => ∫ h, (q (u n-(a n)⁻¹ • h)-q (u n))*k h)
      atTop (𝓝 (∫ _h : EuclideanSpace ℝ (Fin d), (0 : ℝ))) := by
    apply tendsto_integral_of_dominated_convergence (fun h => (2*M)*‖k h‖)
    · intro n
      exact ((hq.comp (by fun_prop)).aestronglyMeasurable.sub
        aestronglyMeasurable_const).mul hk.aestronglyMeasurable
    · exact hk.norm.const_mul (2*M)
    · intro n
      filter_upwards [] with h
      change ‖(q (u n-(a n)⁻¹ • h)-q (u n))*k h‖ ≤ (2*M)*‖k h‖
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact (norm_sub_le _ _).trans (by linarith [hbound (u n-(a n)⁻¹ • h),hbound (u n)])
    · filter_upwards [] with h
      have hv : Tendsto (fun n => (a n)⁻¹ • h) atTop (𝓝 0) := by
        simpa only [Function.comp_apply, zero_smul] using
          (tendsto_inv_atTop_zero.comp ha).smul (tendsto_const_nhds (x := h))
      simpa only [zero_mul] using
        (compactCutoff_translation_difference_tendsto q hq hqs u _ hv).mul_const (k h)
  simpa only [integral_zero] using ht

theorem realError_uniform_of_all_centers {S : Type*} [Nonempty S]
    (e : ℕ → S → ℝ)
    (he : ∀ u : ℕ → S, Tendsto (fun n => e n (u n)) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x, |e n x| < ε := by
  classical
  intro ε hε
  let x0 : S := Classical.choice (inferInstance : Nonempty S)
  have hc : ∀ n, ∃ x : S, (∃ y, ε ≤ |e n y|) → ε ≤ |e n x| := by
    intro n
    by_cases h : ∃ y, ε ≤ |e n y|
    · exact ⟨h.choose,fun _ => h.choose_spec⟩
    · exact ⟨x0,fun hn => False.elim (h hn)⟩
  choose u hu using hc
  have ht : Tendsto (fun n => |e n (u n)|) atTop (𝓝 0) := by
    simpa only [abs_zero] using (he u).abs
  have hsmall : ∀ᶠ n in atTop, |e n (u n)| < ε := (tendsto_order.mp ht).2 ε hε
  filter_upwards [hsmall] with n hn
  intro x
  by_contra hx
  exact not_lt_of_ge (hu n ⟨x,not_lt.mp hx⟩) hn

theorem compactApproximateRow_uniform (q : EuclideanSpace ℝ (Fin d) → ℝ)
    (hq : Continuous q) (hqs : HasCompactSupport q)
    {k : EuclideanSpace ℝ (Fin d) → ℝ} (hk : Integrable k)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ u,
      |compactApproximateRow q k (a n) u-q u*(∫ h, k h)| < ε :=
  realError_uniform_of_all_centers _
    (compactApproximateRow_error_tendsto_any_centers q hq hqs hk ha)

theorem compactSchwartzApproximateRow_uniform (q : EuclideanSpace ℝ (Fin d) → ℝ)
    (hq : Continuous q) (hqs : HasCompactSupport q) (f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ))
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ u,
      |compactApproximateRow q (fun h => (f h).re) (a n) u-q u*((𝓕 f) 0).re| < ε := by
  rw [schwartzFourier_zero_re_eq_integral]
  exact compactApproximateRow_uniform q hq hqs (schwartzRealPart_integrable f) ha

end SphericalRiesz
