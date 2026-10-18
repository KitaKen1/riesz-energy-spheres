import Riesz.Asymptotics
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

/-! Sharp configuration bounds imply limits of actual infima and suprema.

Nonemptiness and boundedness are needed only eventually, and follow from the sharp
bounds themselves. The affine-normalization lemmas put the infimum/supremum outside
the physical energy before subtracting its continuous background. -/

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SphericalRiesz

theorem infimumTarget_tendsto {α : ℕ → Type*} {f : ∀ n, α n → ℝ} {c : ℝ}
    (h : InfimumTarget f c) :
    Tendsto (fun n => sInf (range (f n))) atTop (𝓝 c) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb
    obtain ⟨n₀, hn₀⟩ := h ((c-b)/2) (by linarith)
    apply eventually_atTop.2
    refine ⟨n₀, fun n hn => ?_⟩
    have := (hn₀ n hn).1
    linarith
  · intro b hb
    obtain ⟨n₀, hn₀⟩ := h ((b-c)/2) (by linarith)
    apply eventually_atTop.2
    refine ⟨n₀, fun n hn => ?_⟩
    have := (hn₀ n hn).2
    linarith

theorem infimumTarget_of_eventual_bounds {α : ℕ → Type*}
    {f : ∀ n, α n → ℝ} {c : ℝ}
    (hl : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ x, c-ε ≤ f n x)
    (hu : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∃ x, f n x ≤ c+ε) :
    InfimumTarget f c := by
  intro ε hε
  obtain ⟨nl, hnl⟩ := hl ε hε
  obtain ⟨nu, hnu⟩ := hu ε hε
  refine ⟨max nl nu, fun n hn => ?_⟩
  have hlow := hnl n ((le_max_left _ _).trans hn)
  obtain ⟨x, hx⟩ := hnu n ((le_max_right _ _).trans hn)
  have hb : BddBelow (range (f n)) := ⟨c-ε, by rintro _ ⟨y, rfl⟩; exact hlow y⟩
  exact ⟨le_csInf ⟨f n x, mem_range_self x⟩ (by rintro _ ⟨y, rfl⟩; exact hlow y),
    (csInf_le hb (mem_range_self x)).trans hx⟩

theorem tendsto_csInf_of_eventual_bounds {α : ℕ → Type*}
    {f : ∀ n, α n → ℝ} {c : ℝ}
    (hl : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ x, c-ε ≤ f n x)
    (hu : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∃ x, f n x ≤ c+ε) :
    Tendsto (fun n => sInf (range (f n))) atTop (𝓝 c) :=
  infimumTarget_tendsto (infimumTarget_of_eventual_bounds hl hu)

theorem tendsto_csInf_of_twoSidedTarget {α : ℕ → Type*}
    {f : ∀ n, α n → ℝ} {c : ℝ} (h : TwoSidedTarget f c) :
    Tendsto (fun n => sInf (range (f n))) atTop (𝓝 c) := by
  apply tendsto_csInf_of_eventual_bounds
  · intro ε hε
    obtain ⟨n₀, hn₀⟩ := h ε hε
    exact ⟨n₀, fun n hn => (hn₀ n hn).1⟩
  · intro ε hε
    obtain ⟨n₀, hn₀⟩ := h ε hε
    exact ⟨n₀, fun n hn => (hn₀ n hn).2⟩

theorem tendsto_csSup_of_eventual_bounds {α : ℕ → Type*}
    {f : ∀ n, α n → ℝ} {c : ℝ}
    (hu : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ x, f n x ≤ c+ε)
    (hl : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∃ x, c-ε ≤ f n x) :
    Tendsto (fun n => sSup (range (f n))) atTop (𝓝 c) := by
  have hbounds : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      c-ε ≤ sSup (range (f n)) ∧ sSup (range (f n)) ≤ c+ε := by
    intro ε hε
    obtain ⟨nu, hnu⟩ := hu ε hε
    obtain ⟨nl, hnl⟩ := hl ε hε
    apply eventually_atTop.2
    refine ⟨max nu nl, fun n hn => ?_⟩
    have hupp := hnu n ((le_max_left _ _).trans hn)
    obtain ⟨x, hx⟩ := hnl n ((le_max_right _ _).trans hn)
    have hb : BddAbove (range (f n)) := ⟨c+ε, by rintro _ ⟨y, rfl⟩; exact hupp y⟩
    exact ⟨hx.trans (le_csSup hb (mem_range_self x)),
      csSup_le ⟨f n x, mem_range_self x⟩ (by rintro _ ⟨y, rfl⟩; exact hupp y)⟩
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb
    filter_upwards [hbounds ((c-b)/2) (by linarith)] with n hn
    linarith [hn.1]
  · intro b hb
    filter_upwards [hbounds ((b-c)/2) (by linarith)] with n hn
    linarith [hn.2]

theorem csInf_affine_normalization {α : Type*} (f : α → ℝ) {a : ℝ} (ha : 0 < a)
    (b : ℝ) (hne : (range f).Nonempty) (hb : BddBelow (range f)) :
    sInf (range (fun x => (f x-b)/a)) = (sInf (range f)-b)/a := by
  obtain ⟨l, hl⟩ := hb
  have hbn : BddBelow (range (fun x => (f x-b)/a)) := by
    refine ⟨(l-b)/a, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact div_le_div_of_nonneg_right (sub_le_sub_right (hl (mem_range_self x)) b) ha.le
  obtain ⟨_, ⟨x₀, rfl⟩⟩ := hne
  apply le_antisymm
  · apply (le_div_iff₀ ha).2
    have h : sInf (range (fun x => (f x-b)/a))*a+b ≤ sInf (range f) := by
      apply le_csInf ⟨f x₀, mem_range_self x₀⟩
      rintro _ ⟨x, rfl⟩
      have := (le_div_iff₀ ha).1 (csInf_le hbn (mem_range_self x))
      linarith
    linarith
  · apply le_csInf ⟨(f x₀-b)/a, mem_range_self x₀⟩
    rintro _ ⟨x, rfl⟩
    exact div_le_div_of_nonneg_right (sub_le_sub_right
      (csInf_le ⟨l, hl⟩ (mem_range_self x)) b) ha.le

theorem csSup_affine_normalization {α : Type*} (f : α → ℝ) {a : ℝ} (ha : 0 < a)
    (b : ℝ) (hne : (range f).Nonempty) (hb : BddAbove (range f)) :
    sSup (range (fun x => (f x-b)/a)) = (sSup (range f)-b)/a := by
  obtain ⟨u, hu⟩ := hb
  have hbn : BddAbove (range (fun x => (f x-b)/a)) := by
    refine ⟨(u-b)/a, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact div_le_div_of_nonneg_right (sub_le_sub_right (hu (mem_range_self x)) b) ha.le
  obtain ⟨_, ⟨x₀, rfl⟩⟩ := hne
  apply le_antisymm
  · apply csSup_le ⟨(f x₀-b)/a, mem_range_self x₀⟩
    rintro _ ⟨x, rfl⟩
    exact div_le_div_of_nonneg_right (sub_le_sub_right
      (le_csSup ⟨u, hu⟩ (mem_range_self x)) b) ha.le
  · apply (div_le_iff₀ ha).2
    have h : sSup (range f) ≤ sSup (range (fun x => (f x-b)/a))*a+b := by
      apply csSup_le ⟨f x₀, mem_range_self x₀⟩
      rintro _ ⟨x, rfl⟩
      have := (div_le_iff₀ ha).1 (le_csSup hbn (mem_range_self x))
      linarith
    linarith

theorem tendsto_normalized_csInf_of_eventual_bounds {α : ℕ → Type*}
    (f : ∀ n, α n → ℝ) (a b : ℕ → ℝ) {c : ℝ} (ha : ∀ᶠ n in atTop, 0 < a n)
    (hl : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ x, c-ε ≤ (f n x-b n)/a n)
    (hu : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∃ x, (f n x-b n)/a n ≤ c+ε) :
    Tendsto (fun n => (sInf (range (f n))-b n)/a n) atTop (𝓝 c) := by
  have ht := tendsto_csInf_of_eventual_bounds hl hu
  obtain ⟨nl, hnl⟩ := hl 1 zero_lt_one
  obtain ⟨nu, hnu⟩ := hu 1 zero_lt_one
  apply ht.congr'
  filter_upwards [ha, eventually_ge_atTop nl, eventually_ge_atTop nu] with n han hn₁ hn₂
  obtain ⟨x, _⟩ := hnu n hn₂
  have hb : BddBelow (range (f n)) := by
    refine ⟨(c-1)*a n+b n, ?_⟩
    rintro _ ⟨y, rfl⟩
    have := (le_div_iff₀ han).1 (hnl n hn₁ y)
    linarith
  exact csInf_affine_normalization (f n) han (b n) ⟨f n x, mem_range_self x⟩ hb

theorem tendsto_normalized_csSup_of_eventual_bounds {α : ℕ → Type*}
    (f : ∀ n, α n → ℝ) (a b : ℕ → ℝ) {c : ℝ} (ha : ∀ᶠ n in atTop, 0 < a n)
    (hu : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ x, (f n x-b n)/a n ≤ c+ε)
    (hl : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∃ x, c-ε ≤ (f n x-b n)/a n) :
    Tendsto (fun n => (sSup (range (f n))-b n)/a n) atTop (𝓝 c) := by
  have ht := tendsto_csSup_of_eventual_bounds hu hl
  obtain ⟨nu, hnu⟩ := hu 1 zero_lt_one
  obtain ⟨nl, hnl⟩ := hl 1 zero_lt_one
  apply ht.congr'
  filter_upwards [ha, eventually_ge_atTop nu, eventually_ge_atTop nl] with n han hn₁ hn₂
  obtain ⟨x, _⟩ := hnl n hn₂
  have hb : BddAbove (range (f n)) := by
    refine ⟨(c+1)*a n+b n, ?_⟩
    rintro _ ⟨y, rfl⟩
    have := (div_le_iff₀ han).1 (hnu n hn₁ y)
    linarith
  exact csSup_affine_normalization (f n) han (b n) ⟨f n x, mem_range_self x⟩ hb

theorem eventually_natCast_rpow_pos (e : ℝ) :
    ∀ᶠ n : ℕ in atTop, 0 < (n:ℝ)^e := by
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  exact Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < n by omega)) e

theorem tendsto_scaled_csInf_of_twoSidedTarget {α : ℕ → Type*}
    (f : ∀ n, α n → ℝ) (e c : ℝ)
    (h : TwoSidedTarget (fun n x => (n:ℝ)^e*f n x) c) :
    Tendsto (fun n : ℕ => (n:ℝ)^e*sInf (range (f n))) atTop (𝓝 c) := by
  have ha : ∀ᶠ n : ℕ in atTop, 0 < ((n:ℝ)^e)⁻¹ :=
    (eventually_natCast_rpow_pos e).mono (fun _ hn => inv_pos.mpr hn)
  have hl : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ x,
      c-ε ≤ (f n x-0)/((n:ℝ)^e)⁻¹ := by
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := h ε hε
    refine ⟨n₀, fun n hn x => ?_⟩
    simpa only [sub_zero, div_eq_mul_inv, inv_inv, mul_comm] using (hn₀ n hn).1 x
  have hu : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∃ x,
      (f n x-0)/((n:ℝ)^e)⁻¹ ≤ c+ε := by
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := h ε hε
    refine ⟨n₀, fun n hn => ?_⟩
    simpa only [sub_zero, div_eq_mul_inv, inv_inv, mul_comm] using (hn₀ n hn).2
  simpa only [sub_zero, div_eq_mul_inv, inv_inv, mul_comm] using
    tendsto_normalized_csInf_of_eventual_bounds f (fun n => ((n:ℝ)^e)⁻¹) (fun _ => 0) ha hl hu

end SphericalRiesz
