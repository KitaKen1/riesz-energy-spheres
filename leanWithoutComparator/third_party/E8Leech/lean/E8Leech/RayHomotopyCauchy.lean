import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import SpherePacking.ForMathlib.ScalarOneForm
import SpherePacking.ForMathlib.ScalarOneFormFDeriv
import SpherePacking.ForMathlib.ScalarOneFormDiffContOnCl

/-!
# Cauchy's theorem for regions swept by rays

Known answer first: for a center `c` and two radial profiles `r₁, r₂` on `[a, b]`, the affine
homotopy between the polar curves `zₖ(θ) = c + rₖ(θ) e^{iθ}` moves along the rays from `c`.
Mathlib's Poincaré lemma for `C²` homotopies
(`ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_diffContOnCl`) then gives, for `g`
holomorphic on an open set containing the swept region,

  `∫_a^b z₂' g(z₂) dθ − ∫_a^b z₁' g(z₁) dθ = R(b) − R(a)`,
  `R(θ) = ∫₀¹ (r₂ − r₁)(θ) e^{iθ} g(c + ((1 − s) r₁(θ) + s r₂(θ)) e^{iθ}) ds`.

This is the tool for the CKMRV contour shift (**) on the ideal triangle `(0, 1, ∞)`: the center is
`1/2`, the inner curve is the semicircle `r₁ = 1/2`, and the outer curve runs along the two vertical
sides and a horizontal cut.
-/

noncomputable section

namespace E8Leech

open Complex Set MeasureTheory intervalIntegral MagicFunction Filter Topology
open scoped Real

/-- The polar curve `θ ↦ c + r(θ) e^{iθ}`. -/
def polarCurve (c : ℂ) (r : ℝ → ℝ) (θ : ℝ) : ℂ := c + (r θ : ℂ) * cexp (θ * I)

/-- The velocity `(r' + i r) e^{iθ}` of `polarCurve c r`. -/
def polarVelocity (r r' : ℝ → ℝ) (θ : ℝ) : ℂ := ((r' θ : ℂ) + (r θ : ℂ) * I) * cexp (θ * I)

/-- The point at parameter `s` on the ray segment from the inner to the outer curve. -/
def raySweep (c : ℂ) (r₁ r₂ : ℝ → ℝ) (s θ : ℝ) : ℂ :=
  c + (((1 - s) * r₁ θ + s * r₂ θ : ℝ) : ℂ) * cexp (θ * I)

/-- The integral of `g dz` along the ray segment at angle `θ`, from the inner to the outer curve. -/
def rayIntegral (c : ℂ) (r₁ r₂ : ℝ → ℝ) (g : ℂ → ℂ) (θ : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..1, (((r₂ θ - r₁ θ : ℝ) : ℂ) * cexp (θ * I)) * g (raySweep c r₁ r₂ s θ)

theorem hasDerivAt_cexp_mul_I (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => cexp (θ * I)) (cexp (θ * I) * I) θ := by
  have h := ((hasDerivAt_id θ).ofReal_comp.mul_const I).cexp
  simpa only [Function.comp_def, id, Complex.ofReal_one, one_mul] using h

theorem hasDerivAt_polarCurve (c : ℂ) {r : ℝ → ℝ} {r' : ℝ} {θ : ℝ} (hr : HasDerivAt r r' θ) :
    HasDerivAt (polarCurve c r) (((r' : ℂ) + (r θ : ℂ) * I) * cexp (θ * I)) θ := by
  have h := (hr.ofReal_comp.mul (hasDerivAt_cexp_mul_I θ)).const_add c
  unfold polarCurve
  exact h.congr_deriv (by ring)

theorem raySweep_eq_lineMap (c : ℂ) (r₁ r₂ : ℝ → ℝ) (s θ : ℝ) :
    raySweep c r₁ r₂ s θ = AffineMap.lineMap (polarCurve c r₁ θ) (polarCurve c r₂ θ) s := by
  rw [AffineMap.lineMap_apply_module, raySweep, polarCurve, polarCurve]
  simp only [Complex.real_smul]
  push_cast
  ring

theorem polarCurve_sub (c : ℂ) (r₁ r₂ : ℝ → ℝ) (θ : ℝ) :
    polarCurve c r₂ θ - polarCurve c r₁ θ = ((r₂ θ - r₁ θ : ℝ) : ℂ) * cexp (θ * I) := by
  simp only [polarCurve]
  push_cast
  ring

/-- The affine reparametrization `[0, 1] → [a, b]`. -/
def angleParam (a b u : ℝ) : ℝ := a + (b - a) * u

theorem angleParam_mem_Icc {a b u : ℝ} (hab : a ≤ b) (hu : u ∈ Icc (0 : ℝ) 1) :
    angleParam a b u ∈ Icc a b := by
  rcases hu with ⟨h0, h1⟩
  constructor <;> simp only [angleParam] <;> nlinarith

theorem angleParam_mem_Ioo {a b u : ℝ} (hab : a < b) (hu : u ∈ Ioo (0 : ℝ) 1) :
    angleParam a b u ∈ Ioo a b := by
  rcases hu with ⟨h0, h1⟩
  constructor <;> simp only [angleParam] <;> nlinarith

/-- The polar curve on `[a, b]` as a path parametrized by `[0, 1]`. -/
def polarPath (c : ℂ) (r : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) (hr : ContinuousOn r (Icc a b)) :
    Path (polarCurve c r a) (polarCurve c r b) where
  toFun u := polarCurve c r (angleParam a b u)
  continuous_toFun := by
    have hp : Continuous fun u : unitInterval => angleParam a b u := by
      unfold angleParam; fun_prop
    have hr' : Continuous fun u : unitInterval => r (angleParam a b u) :=
      hr.comp_continuous hp fun u => angleParam_mem_Icc hab u.2
    exact continuous_const.add ((Complex.continuous_ofReal.comp hr').mul
      (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp hp).mul continuous_const)))
  source' := by simp [angleParam]
  target' := by simp [angleParam]

theorem polarPath_apply (c : ℂ) (r : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hr : ContinuousOn r (Icc a b)) (u : unitInterval) :
    polarPath c r hab hr u = polarCurve c r (angleParam a b u) := rfl

/-- The curve integral of `g dz` along a polar path is the angular integral. -/
theorem curveIntegral_polarPath (c : ℂ) {r : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hr : ContDiffOn ℝ 2 r (Icc a b)) (g : ℂ → ℂ) :
    (∫ᶜ z in polarPath c r hab.le hr.continuousOn, scalarOneForm g z) =
      ∫ θ in a..b, polarVelocity r (deriv r) θ * g (polarCurve c r θ) := by
  rw [curveIntegral_eq_intervalIntegral_deriv]
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  have key : ∀ u ∈ Ioo (0 : ℝ) 1,
      scalarOneForm g ((polarPath c r hab.le hr.continuousOn).extend u)
          (deriv (polarPath c r hab.le hr.continuousOn).extend u) =
        (b - a) • (polarVelocity r (deriv r) (angleParam a b u) *
          g (polarCurve c r (angleParam a b u))) := by
    intro u hu
    have huI : u ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hu
    have hθ := angleParam_mem_Ioo hab hu
    have hev : (polarPath c r hab.le hr.continuousOn).extend =ᶠ[𝓝 u]
        fun v => polarCurve c r (angleParam a b v) := by
      filter_upwards [Icc_mem_nhds hu.1 hu.2] with v hv
      rw [Path.extend_apply _ hv]
      rfl
    have hdiff : DifferentiableAt ℝ r (angleParam a b u) :=
      (hr.differentiableOn (by norm_num)).differentiableAt (Icc_mem_nhds hθ.1 hθ.2)
    have hp : HasDerivAt (angleParam a b) (b - a) u := by
      have := ((hasDerivAt_id u).const_mul (b - a)).const_add a
      simp only [id, mul_one] at this
      exact this
    have hcomp : HasDerivAt (fun v => polarCurve c r (angleParam a b v))
        ((b - a) • polarVelocity r (deriv r) (angleParam a b u)) u :=
      (hasDerivAt_polarCurve c hdiff.hasDerivAt).scomp u hp
    rw [hev.deriv_eq, hcomp.deriv, Path.extend_apply _ huI, scalarOneForm_apply, smul_mul_assoc]
    rfl
  calc (∫ u in (0 : ℝ)..1, scalarOneForm g ((polarPath c r hab.le hr.continuousOn).extend u)
          (deriv (polarPath c r hab.le hr.continuousOn).extend u))
      = ∫ u in (0 : ℝ)..1, (b - a) • (polarVelocity r (deriv r) (angleParam a b u) *
          g (polarCurve c r (angleParam a b u))) := by
        apply intervalIntegral.integral_congr_ae_restrict
        rw [uIoc_of_le zero_le_one, ← restrict_Ioo_eq_restrict_Ioc]
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
        exact key u hu
    _ = (b - a) • ∫ u in (0 : ℝ)..1, polarVelocity r (deriv r) (angleParam a b u) *
          g (polarCurve c r (angleParam a b u)) := intervalIntegral.integral_smul _ _
    _ = ∫ θ in a..b, polarVelocity r (deriv r) θ * g (polarCurve c r θ) := by
        have h := intervalIntegral.smul_integral_comp_add_mul (a := (0 : ℝ)) (b := 1)
          (fun θ => polarVelocity r (deriv r) θ * g (polarCurve c r θ)) (b - a) a
        have e0 : a + (b - a) * 0 = a := by ring
        have e1 : a + (b - a) * 1 = b := by ring
        rw [e0, e1] at h
        simpa only [angleParam] using h

/-- **Cauchy's theorem for a region swept by rays.** -/
theorem ray_cauchy {c : ℂ} {a b : ℝ} (hab : a < b) {r₁ r₂ : ℝ → ℝ}
    (hr₁ : ContDiffOn ℝ 2 r₁ (Icc a b)) (hr₂ : ContDiffOn ℝ 2 r₂ (Icc a b))
    {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U)
    (hgc : ContinuousOn g (closure U))
    (hsweep : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ θ ∈ Ioo a b, raySweep c r₁ r₂ s θ ∈ U) :
    (∫ θ in a..b, polarVelocity r₂ (deriv r₂) θ * g (polarCurve c r₂ θ)) -
        ∫ θ in a..b, polarVelocity r₁ (deriv r₁) θ * g (polarCurve c r₁ θ) =
      rayIntegral c r₁ r₂ g b - rayIntegral c r₁ r₂ g a := by
  set γ₁ := polarPath c r₁ hab.le hr₁.continuousOn with hγ₁
  set γ₂ := polarPath c r₂ hab.le hr₂.continuousOn with hγ₂
  let ω : ℂ → ℂ →L[ℂ] ℂ := scalarOneForm g
  let φ : (γ₁ : C(unitInterval, ℂ)).Homotopy γ₂ :=
    ContinuousMap.Homotopy.affine (γ₁ : C(unitInterval, ℂ)) γ₂
  have hφapp : ∀ (s u : unitInterval), φ (s, u) = raySweep c r₁ r₂ s (angleParam a b u) := by
    intro s u
    rw [raySweep_eq_lineMap]
    simp only [φ, ContinuousMap.Homotopy.affine_apply]
    rfl
  have hφt : ∀ s ∈ Ioo (0 : unitInterval) 1, ∀ u ∈ Ioo (0 : unitInterval) 1, φ (s, u) ∈ U := by
    intro s hs u hu
    rw [hφapp]
    exact hsweep s ⟨hs.1, hs.2⟩ _ (angleParam_mem_Ioo hab ⟨hu.1, hu.2⟩)
  have hω : DiffContOnCl ℝ ω U :=
    SpherePacking.ForMathlib.diffContOnCl_scalarOneForm ⟨hg.restrictScalars ℝ, hgc⟩
  have hdω : ∀ x ∈ U, ∀ u ∈ tangentConeAt ℝ U x, ∀ v ∈ tangentConeAt ℝ U x,
      fderivWithin ℝ ω U x u v = fderivWithin ℝ ω U x v u := fun x hx u _ v _ =>
    SpherePacking.ForMathlib.fderivWithin_scalarOneForm_symm_of_isOpen hU hx
      (hg.differentiableAt (hU.mem_nhds hx))
  have hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ ↦ Set.IccExtend zero_le_one (φ.extend xy.1) xy.2) (Icc 0 1) := by
    let F : ℝ × ℝ → ℂ := fun xy => raySweep c r₁ r₂ xy.1 (angleParam a b xy.2)
    have hmaps : MapsTo (fun xy : ℝ × ℝ => angleParam a b xy.2) (Icc (0 : ℝ × ℝ) 1) (Icc a b) :=
      fun xy hxy => angleParam_mem_Icc hab.le ⟨hxy.1.2, hxy.2.2⟩
    have hpar : ContDiff ℝ 2 (fun xy : ℝ × ℝ => angleParam a b xy.2) := by
      unfold angleParam; fun_prop
    have h1 : ContDiffOn ℝ 2 (fun xy : ℝ × ℝ => r₁ (angleParam a b xy.2)) (Icc 0 1) :=
      hr₁.comp hpar.contDiffOn hmaps
    have h2 : ContDiffOn ℝ 2 (fun xy : ℝ × ℝ => r₂ (angleParam a b xy.2)) (Icc 0 1) :=
      hr₂.comp hpar.contDiffOn hmaps
    have hF : ContDiffOn ℝ 2 F (Icc 0 1) := by
      have hlin : ContDiffOn ℝ 2 (fun xy : ℝ × ℝ =>
          ((1 - xy.1) * r₁ (angleParam a b xy.2) + xy.1 * r₂ (angleParam a b xy.2))) (Icc 0 1) :=
        ((contDiffOn_const.sub contDiffOn_fst).mul h1).add (contDiffOn_fst.mul h2)
      have hexp : ContDiff ℝ 2 (fun xy : ℝ × ℝ => cexp ((angleParam a b xy.2 : ℂ) * I)) :=
        ((Complex.contDiff_exp (n := 2)).restrict_scalars (𝕜 := ℝ) (𝕜' := ℂ)).comp
          ((Complex.ofRealCLM.contDiff.comp hpar).mul contDiff_const)
      have := (contDiffOn_const (c := c)).add ((Complex.ofRealCLM.contDiff.comp_contDiffOn hlin).mul
        hexp.contDiffOn)
      simpa [F, raySweep] using this
    refine (contDiffOn_congr ?_).2 hF
    intro xy hxy
    rcases xy with ⟨x, y⟩
    rcases hxy with ⟨h0, h1⟩
    have hx : x ∈ Icc (0 : ℝ) 1 := ⟨h0.1, h1.1⟩
    have hy : y ∈ Icc (0 : ℝ) 1 := ⟨h0.2, h1.2⟩
    calc Set.IccExtend zero_le_one (φ.extend x) y = (φ.extend x) ⟨y, hy⟩ :=
          Set.IccExtend_of_mem _ _ hy
      _ = φ (⟨x, hx⟩, ⟨y, hy⟩) := ContinuousMap.Homotopy.extend_apply_of_mem_I _ hx _
      _ = F (x, y) := hφapp _ _
  have hmain := ContinuousMap.Homotopy.curveIntegral_add_curveIntegral_eq_of_diffContOnCl
    (𝕜 := ℂ) (E := ℂ) (F := ℂ) (γ₁ := γ₁) (γ₂ := γ₂) (t := U) (ω := ω) (φ := φ)
    hφt hω hdω hcontdiff
  have hseg : ∀ u : unitInterval, (∫ᶜ z in φ.evalAt u, ω z) = rayIntegral c r₁ r₂ g (angleParam a b u) := by
    intro u
    show (∫ᶜ z in (Path.segment (γ₁ u) (γ₂ u) : Path (γ₁ u) (γ₂ u)), ω z) = _
    rw [curveIntegral_segment]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [ω, scalarOneForm_apply]
    rw [show (γ₁ u : ℂ) = polarCurve c r₁ (angleParam a b u) from rfl,
      show (γ₂ u : ℂ) = polarCurve c r₂ (angleParam a b u) from rfl, polarCurve_sub,
      ← raySweep_eq_lineMap]
  have h0 : angleParam a b ((0 : unitInterval) : ℝ) = a := by simp [angleParam]
  have h1 : angleParam a b ((1 : unitInterval) : ℝ) = b := by simp [angleParam]
  rw [hseg, hseg, h0, h1] at hmain
  rw [← curveIntegral_polarPath c hab hr₂ g, ← curveIntegral_polarPath c hab hr₁ g]
  have e1 : (∫ᶜ z in polarPath c r₁ hab.le hr₁.continuousOn, scalarOneForm g z) =
      ∫ᶜ z in γ₁, ω z := rfl
  have e2 : (∫ᶜ z in polarPath c r₂ hab.le hr₂.continuousOn, scalarOneForm g z) =
      ∫ᶜ z in γ₂, ω z := rfl
  rw [e1, e2]
  linear_combination -hmain

end E8Leech
