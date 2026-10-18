-- Modified for E8Leach (Lean 4.33.1 / pinned Mathlib port, 2026-10-10); see SpherePacking/PORTING.txt.
module
public import SpherePacking.ModularForms.E2.Transform
public import SpherePacking.ModularForms.CSqrt
public import SpherePacking.ModularForms.LogDerivLemmas
public import SpherePacking.ModularForms.MultipliableLemmas
public import Mathlib.NumberTheory.ModularForms.DedekindEta


/-!
# Dedekind eta function

This file defines the Dedekind eta function `etaSP` and establishes basic analytic properties on the
upper half-plane, including nonvanishing, differentiability, and a formula for its logarithmic
derivative in terms of the Eisenstein series `E₂`.

## Main declarations
* `etaSP`
* `eta_nonzero_on_UpperHalfPlane`
* `eta_DifferentiableAt_UpperHalfPlane`
* `eta_logDeriv`
* `eta_equality`
-/

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat
open scoped ArithmeticFunction.sigma


open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

/-- The Dedekind eta function on `ℂ`, defined by an exponential factor times an infinite product. -/
@[expose] public noncomputable def etaSP (z : ℂ) :=
  cexp (2 * π * Complex.I * z / 24) * ∏' (n : ℕ),
    (1 - cexp (2 * π * Complex.I * (n + 1) * z))


private lemma tendstoUniformlyOn_tprod' {α : Type*} [TopologicalSpace α] {f : ℕ → α → ℂ}
    {K : Set α} (hK : IsCompact K) {u : ℕ → ℝ} (hu : Summable u)
    (h : ∀ n x, x ∈ K → ‖f n x‖ ≤ u n) (hcts : ∀ n, ContinuousOn (fun x => f n x) K) :
    TendstoUniformlyOn (fun n : ℕ => fun a : α => ∏ i ∈ Finset.range n, (1 + (f i a)))
    (fun a => ∏' i, (1 + (f i a))) atTop K := by
  refine HasProdUniformlyOn.tendstoUniformlyOn_finsetRange ?_
  refine Summable.hasProdUniformlyOn_nat_one_add hK hu ?_ hcts
  exact Filter.Eventually.of_forall fun n x hx => h n x hx

/-- A uniform convergence lemma for finite products converging to a `tprod`.

This is a wrapper around `tendstoUniformlyOn_tprod'` with a product written over `Finset.range`.
-/
public lemma prod_tendstoUniformlyOn_tprod'
    {α : Type*} [TopologicalSpace α] {f : ℕ → α → ℂ} (K : Set α) (hK : IsCompact K)
    (u : ℕ → ℝ) (hu : Summable u) (h : ∀ n x, x ∈ K → ‖f n x‖ ≤ u n)
    (hcts : ∀ n, ContinuousOn (fun x => f n x) K) :
    TendstoUniformlyOn (fun n : ℕ => fun a : α => ∏ i ∈ Finset.range n, (1 + f i a))
      (fun a => ∏' i, (1 + f i a)) atTop K :=
  tendstoUniformlyOn_tprod' (K := K) (f := f) hK (u := u) hu h hcts

theorem eta_tprod_ne_zero (z : ℍ) :
  ∏' (n : ℕ), (1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑z)) ≠ 0 := by
  simpa [ModularForm.eta_q_eq_cexp, Nat.cast_add, Nat.cast_one] using
    (ModularForm.eta_tprod_ne_zero (z := (↑z : ℂ)) (hz := by simpa using z.2))

/-- The eta function does not vanish on the upper half-plane. -/
public lemma eta_nonzero_on_UpperHalfPlane (z : ℍ) : etaSP z ≠ 0 := by
  convert (postTransparency := .instances) mul_ne_zero (Complex.exp_ne_zero (2 * π * Complex.I * (z : ℂ) / 24)) (eta_tprod_ne_zero z) using 1 <;> first | rfl | simp [etaSP, Function.comp_def] | ring

lemma logDeriv_eta_factor (i : ℕ) (z : ℂ) :
    logDeriv (fun x ↦ 1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x)) z =
      -(2 * ↑π * Complex.I * (↑i + 1)) *
          cexp (2 * ↑π * Complex.I * (↑i + 1) * z) /
        (1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * z)) := by
  simpa [logDeriv_one_sub_exp_comp, deriv_const_mul, mul_assoc, mul_left_comm, mul_comm, Function.comp_def, Pi.add_def, Pi.sub_def, Pi.mul_def, Pi.neg_def, Pi.smul_def, Pi.div_def] using (congrArg (fun f => f z)
      (logDeriv_one_sub_exp_comp (r := (1 : ℂ))
        (fun x : ℂ => (2 * ↑π * Complex.I * (↑i + 1)) * x) (by fun_prop)))

lemma tsum_log_deriv_eqn (z : ℍ) :
  ∑' (i : ℕ), logDeriv (fun x ↦ 1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x)) ↑z =
  ∑' n : ℕ, -(2 * ↑π * Complex.I * (↑n + 1)) *
             cexp (2 * π * Complex.I * (n + 1) * z) /
             (1 - cexp (2 * π *  Complex.I * (n + 1) * z)) := by
  refine tsum_congr fun i => ?_
  simpa [UpperHalfPlane.coe, mul_assoc] using logDeriv_eta_factor i (↑z : ℂ)

lemma logDeriv_z_term (z : ℍ) : logDeriv (fun z ↦ cexp (2 * ↑π * Complex.I * z / 24)) ↑z =
    2* ↑π * Complex.I / 24 := by
  have hcomp :
      (fun z ↦ cexp (2 * ↑π * Complex.I * z / 24)) =
        (fun z ↦ cexp z) ∘ fun z => (2 * ↑π * Complex.I / 24) * z := by
    ext y; simp [Function.comp, mul_assoc, div_eq_mul_inv]; ring_nf
  rw [hcomp, logDeriv_comp, deriv_const_mul]
  · simp [Complex.logDeriv_exp]
  all_goals fun_prop


theorem eta_differentiableAt (z : ℍ) :
    DifferentiableAt ℂ
      (fun z ↦ ∏' n : ℕ, (1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * z))) ↑z := by
  simpa [ModularForm.eta_q_eq_cexp, Nat.cast_add, Nat.cast_one, sub_eq_add_neg] using
    (ModularForm.differentiableAt_eta_tprod (z := (↑z : ℂ)) (hz := by simpa using z.2))

/-- The eta function is complex differentiable at every point of the upper half-plane. -/
public lemma eta_DifferentiableAt_UpperHalfPlane (z : ℍ) : DifferentiableAt ℂ etaSP z := by
  unfold etaSP
  refine (DifferentiableAt.mul ?_ (eta_differentiableAt z))
  · have : DifferentiableAt ℂ (fun z : ℂ => 2 * ↑π * Complex.I * z / 24) z := by fun_prop
    simpa using DifferentiableAt.cexp this

lemma summable_logDeriv_eta_factor (z : ℍ) :
    Summable fun n : ℕ =>
      logDeriv (fun x ↦ 1 - cexp (2 * π * Complex.I * (n + 1) * x)) (↑z : ℂ) := by
  simpa [ModularForm.eta_q_eq_cexp, Nat.cast_add, Nat.cast_one] using
    (ModularForm.summable_logDeriv_one_sub_eta_q (z := (↑z : ℂ)) (hz := by simpa using z.2))

/-- The logarithmic derivative of `etaSP` is `(π * I / 12) * E₂`. -/
public lemma eta_logDeriv (z : ℍ) : logDeriv etaSP z = (π * Complex.I / 12) * E₂ z := by
  unfold etaSP
  rw [logDeriv_fun_mul]
  · let s : Set ℂ := UpperHalfPlane.upperHalfPlaneSet
    have hs : IsOpen s := UpperHalfPlane.isOpen_upperHalfPlaneSet
    have hz : (z : ℂ) ∈ s := by simpa [s, UpperHalfPlane.upperHalfPlaneSet] using z.2
    have htend :
        MultipliableLocallyUniformlyOn
          (fun (n : ℕ) (x : ℂ) ↦ 1 - cexp (2 * π * Complex.I * (n + 1) * x)) s := by
      have ht0 :
          MultipliableLocallyUniformlyOn
            (fun (n : ℕ) (x : ℂ) ↦ 1 - ModularForm.eta_q n x) s := by
        simpa [s] using ModularForm.multipliableLocallyUniformlyOn_eta
      refine
        MultipliableLocallyUniformlyOn_congr (s := s)
          (f := fun (n : ℕ) (x : ℂ) ↦ 1 - ModularForm.eta_q n x)
          (h := fun n x hx ↦ by simp only [ModularForm.eta_q_eq_cexp]) ht0
    have HG :=
      logDeriv_tprod_eq_tsum (ι := ℕ) (s := s) hs (x := (z : ℂ)) hz
        (f := fun (n : ℕ) (x : ℂ) ↦ 1 - cexp (2 * π * Complex.I * (n + 1) * x))
        (hf := by intro n; simpa [UpperHalfPlane.coe] using term_ne_zero z n)
        (hd := by intro n; fun_prop)
        (hm := summable_logDeriv_eta_factor z)
        (htend := htend)
        (hnez := by simpa [UpperHalfPlane.coe] using eta_tprod_ne_zero z)
    rw [HG]
    have := tsum_log_deriv_eqn z
    have h0 := logDeriv_z_term z
    rw [this, E₂, h0]
    simp only [neg_mul, one_div, mul_inv_rev, Pi.smul_apply, smul_eq_mul]
    rw [G2_q_exp]
    rw [riemannZeta_two]
    have hterm (n : ℕ) :
        -(2 * ↑π * Complex.I * (↑n + 1) * cexp (2 * ↑π * Complex.I * (↑n + 1) * z.1)) /
            (1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * z.1)) =
          (-2 * ↑π * Complex.I) *
            ((↑n + 1) * cexp (2 * ↑π * Complex.I * (↑n + 1) * z.1) /
              (1 - cexp (2 * ↑π * Complex.I * (n + 1) * z.1))) := by
      ring
    conv =>
      enter [1,2,1]
      ext n
      rw [hterm n]
    rw [tsum_mul_left (a := -2 * ↑π * Complex.I)]
    have := tsum_eq_tsum_sigma z
    rw [this, mul_sub]
    rw [sub_eq_add_neg, mul_add]
    congr 1
    · have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.pi_pos.ne')
      ring_nf
      field_simp
    · have hr :
          ↑π * Complex.I / 12 *
              -((↑π ^ 2 / (6 : ℂ))⁻¹ * 2⁻¹ *
                (8 * ↑π ^ 2 *
                  ∑' n : ℕ+,
                    ↑((σ 1) ↑n) * cexp (2 * ↑π * Complex.I * ↑↑n * ↑z))) =
            ↑π * Complex.I * (1 / 12) *
                -(((π : ℂ) ^ 2 * (1 / 6))⁻¹ * (1 / 2) * (↑π ^ 2 * 8)) *
              ∑' n : ℕ+, ↑((σ 1) ↑n) * cexp (↑π * Complex.I * 2 * ↑↑n * z.1) := by
        ring_nf
        simp only [mul_assoc, mul_left_comm, mul_comm]
      rw [hr]
      congr 1
      · have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.pi_pos.ne')
        field_simp
        ring
      have hcast (n : ℕ) : (n : ℂ) + 1 = (((n + 1) : ℕ) : ℂ) := by
        simp only [Nat.cast_add, Nat.cast_one]
      conv =>
        enter [1,1]
        ext n
        rw [hcast n]
      have hl := tsum_pnat_eq_tsum_succ3
        (fun n ↦ ↑((σ 1) (n)) * cexp (↑π * Complex.I * 2 * (↑n) * ↑z))
      rw [hl]
      apply tsum_congr
      intro b
      simp only [Nat.cast_add, Nat.cast_one, mul_eq_mul_left_iff, Nat.cast_eq_zero,
        ArithmeticFunction.sigma_eq_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false, or_false]
      congr 1
      ring
  · simp only [ne_eq, exp_ne_zero, not_false_eq_true]
  · exact eta_tprod_ne_zero z
  · fun_prop
  · apply eta_differentiableAt


lemma eta_logDeriv_eql (z : ℍ) : (logDeriv (etaSP ∘ (fun z : ℂ => -1/z))) z =
  (logDeriv ((csqrt) * etaSP)) z := by
  have h0 : (logDeriv (etaSP ∘ (fun z : ℂ => -1/z))) z =
            ((z :ℂ)^(2 : ℤ))⁻¹ *
              (logDeriv etaSP) (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ) := by
    rw [logDeriv_comp, mul_comm]
    · congr
      conv =>
        enter [1,1]
        intro z
        rw [neg_div]
      simp only [deriv.fun_neg', one_div]
      rw [deriv_inv]
      simp only [neg_neg]
      norm_cast
    · simpa only using
      eta_DifferentiableAt_UpperHalfPlane (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ)
    conv =>
      enter [2]
      ext z
      rw [neg_div]
    apply DifferentiableAt.neg
    have h : DifferentiableAt ℂ (fun z : ℂ => z)⁻¹ (↑z : ℂ) := by
      refine
        DifferentiableAt.inv (h := fun z : ℂ => z) (z := (↑z : ℂ))
          differentiableAt_fun_id (ne_zero z)
    change DifferentiableAt ℂ (fun z : ℂ => 1 / z) (↑z : ℂ)
    simp only [one_div]
    exact h
  rw [h0, show ((csqrt) * etaSP) = (fun x => (csqrt) x * etaSP x) by rfl, logDeriv_fun_mul]
  · nth_rw 2 [logDeriv_apply]
    unfold csqrt
    have := csqrt_deriv z
    rw [this]
    simp only [one_div, neg_mul, smul_eq_mul]
    nth_rw 2 [div_eq_mul_inv]
    · have hmul :
          2⁻¹ * cexp (-(2⁻¹ * Complex.log ↑z)) * cexp (-(2⁻¹ * Complex.log ↑z)) =
            (cexp (-(2⁻¹ * Complex.log ↑z)) * cexp (-(2⁻¹ * Complex.log ↑z))) *
              2⁻¹ := by
        ring
      rw [← Complex.exp_neg, hmul, ← Complex.exp_add, ← sub_eq_add_neg,
        show -(2⁻¹ * Complex.log ↑z) - 2⁻¹ * Complex.log ↑z = -Complex.log ↑z by ring,
        Complex.exp_neg, Complex.exp_log, eta_logDeriv z]
      · have Rb := eta_logDeriv (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ)
        rw [Rb]
        have E := E₂_transform z
        simp only [one_div, neg_mul, smul_eq_mul, SL_slash_def, modular_S_smul,
          ModularGroup.denom_S, Int.reduceNeg, zpow_neg] at *
        have h00 : UpperHalfPlane.mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos =
            (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ) := by
          ext1
          ring_nf
        rw [h00] at E
        rw [← mul_assoc, mul_comm, ← mul_assoc]
        rw [E, add_mul, add_comm]
        congr 1
        · have hzne := ne_zero z
          have hI : Complex.I ≠ 0 := I_ne_zero
          have hpi : (π : ℂ) ≠ 0 := by
            simp only [ne_eq, ofReal_eq_zero]
            exact Real.pi_ne_zero
          field_simp
          ring
        · rw [mul_comm]
      · simpa [ne_eq] using (ne_zero z)
  · simp only [csqrt, one_div, ne_eq, Complex.exp_ne_zero, not_false_eq_true]
  · apply eta_nonzero_on_UpperHalfPlane z
  · exact csqrt_differentiableAt z
  · apply eta_DifferentiableAt_UpperHalfPlane z

lemma eta_logderivs : {z : ℂ | 0 < z.im}.EqOn (logDeriv (etaSP ∘ (fun z : ℂ => -1/z)))
  (logDeriv ((csqrt) * etaSP)) := by
  intro z hz
  simpa using eta_logDeriv_eql (z := ⟨z, hz⟩)

lemma eta_logderivs_const :
    ∃ z : ℂ, z ≠ 0 ∧
      {z : ℂ | 0 < z.im}.EqOn (etaSP ∘ fun z : ℂ => -1 / z) (z • (csqrt * etaSP)) := by
  have h := eta_logderivs
  rw [logDeriv_eqOn_iff] at h
  · exact h
  · apply DifferentiableOn.comp
    pick_goal 4
    · use ({z : ℂ | 0 < z.im})
    · rw [DifferentiableOn]
      intro x hx
      apply DifferentiableAt.differentiableWithinAt
      apply eta_DifferentiableAt_UpperHalfPlane ⟨x, hx⟩
    · apply DifferentiableOn.div
      · fun_prop
      · fun_prop
      intro x hx
      have hx2 := ne_zero (⟨x, hx⟩ : ℍ)
      norm_cast at *
    · intro y hy
      simp only [mem_setOf_eq] at hy ⊢
      simpa [div_eq_mul_inv] using (UpperHalfPlane.im_inv_neg_coe_pos (⟨y, hy⟩ : ℍ))
  · apply DifferentiableOn.mul
    · simp only [DifferentiableOn, mem_setOf_eq]
      intro x hx
      apply (csqrt_differentiableAt ⟨x, hx⟩).differentiableWithinAt
    simp only [DifferentiableOn, mem_setOf_eq]
    intro x hx
    apply (eta_DifferentiableAt_UpperHalfPlane ⟨x, hx⟩).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_im
  · apply Convex.isPreconnected
    exact convex_halfSpace_im_gt 0
  · intro x hx
    simp only [Pi.mul_apply, ne_eq, mul_eq_zero, not_or]
    refine ⟨ ?_ , by apply eta_nonzero_on_UpperHalfPlane ⟨x, hx⟩⟩
    unfold csqrt
    simp only [one_div, Complex.exp_ne_zero, not_false_eq_true]
  · intro x hx
    simp only [comp_apply, ne_eq]
    have := eta_nonzero_on_UpperHalfPlane ⟨-1 / x, by simpa using pnat_div_upper 1 ⟨x, hx⟩⟩
    simpa [UpperHalfPlane.coe_mk] using this

/-- A functional equation for `etaSP` under `z ↦ -1/z` on the upper half-plane. -/
public lemma eta_equality : {z : ℂ | 0 < z.im}.EqOn ((etaSP ∘ (fun z : ℂ => -1 / z)))
    ((csqrt (Complex.I))⁻¹ • ((csqrt) * etaSP)) := by
  rcases eta_logderivs_const with ⟨z, hz0, hzEq⟩
  intro x hx
  have hI : (Complex.I) ∈ {z : ℂ | 0 < z.im} := by
    simp only [mem_setOf_eq, Complex.I_im, zero_lt_one]
  have h3 := hzEq hI
  have hIdiv : (-1 : ℂ) / Complex.I = Complex.I := by
    simp [div_eq_mul_inv, Complex.inv_I]
  have h3' : etaSP Complex.I = z * csqrt Complex.I * etaSP Complex.I := by
    simpa [hIdiv, comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, mul_assoc] using h3
  have he : etaSP Complex.I ≠ 0 := by
    simpa using eta_nonzero_on_UpperHalfPlane UpperHalfPlane.I
  have hcd : z * csqrt Complex.I = 1 :=
    (mul_eq_right₀ he).1 (by simpa [mul_assoc] using h3'.symm)
  have hzInv : z⁻¹ = csqrt Complex.I := (mul_eq_one_iff_inv_eq₀ hz0).1 hcd
  have hz' : z = (csqrt Complex.I)⁻¹ := (inv_eq_iff_eq_inv).1 hzInv
  simpa [hz'] using hzEq hx
