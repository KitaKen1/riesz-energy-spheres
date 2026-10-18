import E8Leech.ThetaIdentities
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# The CKMRV logarithm branches `L = log λ` and `L_S = log (1 - λ)`

CKMRV (2.14)–(2.17) define `L(z) = ∫₀^z λ'/λ` and `L_S(z) = -∫_z^∞ λ_S'/λ_S` by vertical
contours and note `L(it) = log λ(it)`, `L_S(it) = log (1 - λ(it))`; these are not principal
branches in general. We fix the answer first instead of integrating: `L` is the holomorphic
logarithm of `λ` with `L(i) = -log 2`, because `λ(i) = 1/2`; `L_S` is the holomorphic logarithm
of `1 - λ` with `L_S(i) = -log 2`. Two continuous logarithms that agree at one point of a
preconnected set agree on it, since their difference takes values in the discrete set `2πiℤ`.
This removes every `2πik` ambiguity:

* `L` and `L_S` are real on the positive imaginary axis;
* `L ∘ S = L_S`, by agreement at the fixed point `i`;
* `L(τ) - πiτ → 4 log 2` and `L_S(τ) → 0` at `i∞`, by comparison with principal logarithms
  where `λ e^{-πiτ}` is near `16` and `1 - λ` is near `1`, anchored on the imaginary axis;
* `L_S ∘ T = -L_S` and `L ∘ T = L - L_S + πi`, the constants vanishing at `i∞`.

These are CKMRV (2.16) to first order and (2.17). The holomorphic upgrade of Mathlib's
continuous branch on a simply connected domain is local: a continuous logarithm equals a
translate of the principal logarithm near each point.
-/

set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace E8Leech
open Complex Filter Topology Set
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups

/-! ## Uniqueness and holomorphy of continuous logarithms -/

/-- `2πiℤ = {w | exp w = 1}` is discrete. -/
theorem isDiscrete_exp_eq_one : IsDiscrete {w : ℂ | cexp w = 1} := by
  rw [isDiscrete_iff_discreteTopology]
  refine DiscreteTopology.of_forall_le_dist (r := 2 * π) (by positivity) ?_
  intro a b hab
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp a.2
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp b.2
  have hmn : m - n ≠ 0 := by
    intro h
    apply hab
    apply Subtype.ext
    rw [hm, hn, sub_eq_zero.mp h]
  have hint : (1 : ℝ) ≤ |((m - n : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hmn
  have h2 : ‖(2 * π * I : ℂ)‖ = 2 * π := by
    simp [abs_of_pos Real.pi_pos]
  have h1 : ‖((m : ℂ) - n)‖ = |((m - n : ℤ) : ℝ)| := by
    rw [← Complex.norm_intCast]
    push_cast
    rfl
  rw [Subtype.dist_eq, hm, hn, dist_eq_norm, ← sub_mul, norm_mul, h1, h2]
  nlinarith [Real.pi_pos]

/-- Two continuous logarithms of the same function agreeing at one point of a preconnected
set agree on it. -/
theorem eqOn_of_exp_eq {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsPreconnected S)
    {f g : X → ℂ} (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hexp : ∀ x ∈ S, cexp (f x) = cexp (g x)) {x₀ : X} (hx₀ : x₀ ∈ S) (h₀ : f x₀ = g x₀) :
    ∀ x ∈ S, f x = g x := by
  intro x hx
  have hmaps : MapsTo (fun y => f y - g y) S {w | cexp w = 1} := by
    intro y hy
    show cexp (f y - g y) = 1
    rw [Complex.exp_sub, hexp y hy, div_self (Complex.exp_ne_zero _)]
  have h : f x - g x = f x₀ - g x₀ :=
    hS.constant_of_mapsTo isDiscrete_exp_eq_one (hf.sub hg) hmaps hx hx₀
  rw [h₀, sub_self] at h
  exact sub_eq_zero.mp h

/-- A continuous logarithm of a holomorphic function is holomorphic. -/
theorem differentiableAt_of_exp_eq {f g : ℂ → ℂ} {z₀ : ℂ} (hf : ContinuousAt f z₀)
    (hg : DifferentiableAt ℂ g z₀) (hfg : ∀ᶠ z in 𝓝 z₀, cexp (f z) = g z) :
    DifferentiableAt ℂ f z₀ := by
  have hz₀ : cexp (f z₀) = g z₀ := hfg.self_of_nhds
  have hg0 : g z₀ ≠ 0 := hz₀ ▸ Complex.exp_ne_zero _
  have hsmall : ∀ᶠ z in 𝓝 z₀, ‖f z - f z₀‖ < π := by
    have h : Tendsto (fun z => f z - f z₀) (𝓝 z₀) (𝓝 0) := by
      have h' : Tendsto (fun z => f z - f z₀) (𝓝 z₀) (𝓝 (f z₀ - f z₀)) :=
        hf.tendsto.sub tendsto_const_nhds
      rwa [sub_self] at h'
    exact (tendsto_zero_iff_norm_tendsto_zero.mp h).eventually (gt_mem_nhds Real.pi_pos)
  have heq : f =ᶠ[𝓝 z₀] fun z => f z₀ + Complex.log (g z / g z₀) := by
    filter_upwards [hsmall, hfg] with z hz hz'
    have he : cexp (f z - f z₀) = g z / g z₀ := by rw [Complex.exp_sub, hz', hz₀]
    have him := (Complex.abs_im_le_norm (f z - f z₀)).trans_lt hz
    rw [← he, Complex.log_exp (by linarith [(abs_lt.mp him).1]) (by linarith [(abs_lt.mp him).2])]
    ring
  have hd : DifferentiableAt ℂ (fun z => f z₀ + Complex.log (g z / g z₀)) z₀ := by
    refine (differentiableAt_const _).add ((hg.div_const _).clog ?_)
    rw [div_self hg0]
    exact Complex.one_mem_slitPlane
  exact hd.congr_of_eventuallyEq heq

private theorem isOpen_upper : IsOpen {z : ℂ | 0 < z.im} :=
  isOpen_lt continuous_const Complex.continuous_im

private theorem continuousOn_comp_ofComplex {f : ℍ → ℂ} (hf : Continuous f) :
    ContinuousOn (f ∘ ofComplex) {z : ℂ | 0 < z.im} := by
  intro z hz
  have h : ContinuousAt ofComplex z :=
    (UpperHalfPlane.mdifferentiableAt_ofComplex hz).continuousAt
  exact (hf.continuousAt.comp h).continuousWithinAt

/-- A nonvanishing holomorphic function on `ℍ` has a holomorphic logarithm. -/
theorem exists_mdifferentiable_log {g : ℍ → ℂ} (hg : MDiff g) (h0 : ∀ τ, g τ ≠ 0) :
    ∃ f : ℍ → ℂ, MDiff f ∧ ∀ τ, cexp (f τ) = g τ := by
  have : ContractibleSpace {z : ℂ | 0 < z.im} :=
    (convex_halfSpace_im_gt 0).contractibleSpace ⟨Complex.I, by simp⟩
  have hUc : IsSimplyConnected {z : ℂ | 0 < z.im} :=
    inferInstanceAs (SimplyConnectedSpace {z : ℂ | 0 < z.im})
  have hGd : DifferentiableOn ℂ (g ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp hg
  have hG0 : (0 : ℂ) ∉ (g ∘ ofComplex) '' {z : ℂ | 0 < z.im} := by
    rintro ⟨z, -, hz⟩
    exact h0 _ hz
  obtain ⟨F, hFc, hFe⟩ := Complex.exists_continuousOn_eqOn_exp_comp hUc isOpen_upper
    hGd.continuousOn hG0
  have hFd : DifferentiableOn ℂ F {z : ℂ | 0 < z.im} := by
    intro z hz
    have hn : {z : ℂ | 0 < z.im} ∈ 𝓝 z := isOpen_upper.mem_nhds hz
    refine (differentiableAt_of_exp_eq ((hFc z hz).continuousAt hn)
      ((hGd z hz).differentiableAt hn) ?_).differentiableWithinAt
    filter_upwards [hn] with w hw using hFe hw
  refine ⟨fun τ => F τ, ?_, fun τ => ?_⟩
  · rw [UpperHalfPlane.mdifferentiable_iff]
    refine hFd.congr fun z hz => ?_
    simp [Function.comp, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  · have h := hFe (show (τ : ℂ) ∈ {z : ℂ | 0 < z.im} from τ.im_pos)
    simpa [Function.comp, UpperHalfPlane.ofComplex_apply] using h

/-- The holomorphic logarithm with a prescribed value at one point. -/
theorem exists_mdifferentiable_log_eq {g : ℍ → ℂ} (hg : MDiff g) (h0 : ∀ τ, g τ ≠ 0)
    (τ₀ : ℍ) (w₀ : ℂ) (hw₀ : cexp w₀ = g τ₀) :
    ∃ f : ℍ → ℂ, MDiff f ∧ (∀ τ, cexp (f τ) = g τ) ∧ f τ₀ = w₀ := by
  obtain ⟨f, hf, hfe⟩ := exists_mdifferentiable_log hg h0
  refine ⟨fun τ => f τ + (w₀ - f τ₀), hf.add mdifferentiable_const, fun τ => ?_, by ring⟩
  rw [Complex.exp_add, Complex.exp_sub, hfe, hfe, hw₀, div_self (h0 τ₀), mul_one]

/-- Uniqueness of continuous logarithms on all of `ℍ`, through the convex set `Im z > 0`. -/
theorem eq_of_exp_eq_upperHalfPlane {f g : ℍ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hexp : ∀ τ, cexp (f τ) = cexp (g τ)) (τ₀ : ℍ) (h₀ : f τ₀ = g τ₀) (τ : ℍ) :
    f τ = g τ := by
  have h := eqOn_of_exp_eq (convex_halfSpace_im_gt 0).isPreconnected
    (continuousOn_comp_ofComplex hf) (continuousOn_comp_ofComplex hg)
    (fun z hz => by simp only [Function.comp, hexp]) (x₀ := (τ₀ : ℂ)) τ₀.im_pos
    (by simpa [Function.comp, UpperHalfPlane.ofComplex_apply] using h₀) (τ : ℂ) τ.im_pos
  simpa [Function.comp, UpperHalfPlane.ofComplex_apply] using h

/-- A continuous function with `exp d = 1` everywhere and limit `0` at `i∞` vanishes. -/
theorem eq_zero_of_exp_eq_one_of_tendsto {d : ℍ → ℂ} (hd : Continuous d)
    (hexp : ∀ τ, cexp (d τ) = 1) (hlim : Tendsto d atImInfty (𝓝 0)) (τ : ℍ) : d τ = 0 := by
  have hconst : ∀ σ, d σ = d τ := fun σ =>
    eq_of_exp_eq_upperHalfPlane hd continuous_const (fun σ' => by rw [hexp, hexp]) τ rfl σ
  have hc : Tendsto (fun _ : ℍ => d τ) atImInfty (𝓝 0) :=
    hlim.congr fun σ => hconst σ
  exact tendsto_nhds_unique tendsto_const_nhds hc

/-! ## Definitions of `L` and `L_S` -/

private theorem exp_neg_log_two : cexp (-(Real.log 2 : ℂ)) = 1 / 2 := by
  rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log two_pos]
  push_cast
  ring

theorem exists_ckmrvL : ∃ f : ℍ → ℂ, MDiff f ∧ (∀ τ, cexp (f τ) = modularLambda τ) ∧
    f UpperHalfPlane.I = -(Real.log 2 : ℂ) :=
  exists_mdifferentiable_log_eq mdifferentiable_modularLambda modularLambda_ne_zero _ _
    (by rw [exp_neg_log_two, modularLambda_I])

private theorem one_sub_modularLambda_ne_zero (τ : ℍ) : 1 - modularLambda τ ≠ 0 :=
  sub_ne_zero.mpr (Ne.symm (modularLambda_ne_one τ))

theorem exists_ckmrvLS : ∃ f : ℍ → ℂ, MDiff f ∧ (∀ τ, cexp (f τ) = 1 - modularLambda τ) ∧
    f UpperHalfPlane.I = -(Real.log 2 : ℂ) :=
  exists_mdifferentiable_log_eq (g := fun τ => 1 - modularLambda τ)
    (mdifferentiable_const.sub mdifferentiable_modularLambda)
    one_sub_modularLambda_ne_zero _ _
    (by
      show cexp _ = 1 - modularLambda UpperHalfPlane.I
      rw [exp_neg_log_two, modularLambda_I]
      norm_num)

/-- CKMRV's `L = log λ`, normalized by `L(i) = -log 2`. -/
def ckmrvL : ℍ → ℂ := Classical.choose exists_ckmrvL

/-- CKMRV's `L_S = log (1 - λ)`, normalized by `L_S(i) = -log 2`. -/
def ckmrvLS : ℍ → ℂ := Classical.choose exists_ckmrvLS

theorem mdifferentiable_ckmrvL : MDiff ckmrvL := (Classical.choose_spec exists_ckmrvL).1

theorem exp_ckmrvL (τ : ℍ) : cexp (ckmrvL τ) = modularLambda τ :=
  (Classical.choose_spec exists_ckmrvL).2.1 τ

theorem ckmrvL_I : ckmrvL UpperHalfPlane.I = -(Real.log 2 : ℂ) :=
  (Classical.choose_spec exists_ckmrvL).2.2

theorem mdifferentiable_ckmrvLS : MDiff ckmrvLS := (Classical.choose_spec exists_ckmrvLS).1

theorem exp_ckmrvLS (τ : ℍ) : cexp (ckmrvLS τ) = 1 - modularLambda τ :=
  (Classical.choose_spec exists_ckmrvLS).2.1 τ

theorem ckmrvLS_I : ckmrvLS UpperHalfPlane.I = -(Real.log 2 : ℂ) :=
  (Classical.choose_spec exists_ckmrvLS).2.2

theorem continuous_ckmrvL : Continuous ckmrvL := mdifferentiable_ckmrvL.continuous

theorem continuous_ckmrvLS : Continuous ckmrvLS := mdifferentiable_ckmrvLS.continuous

theorem continuous_modularLambda : Continuous modularLambda :=
  mdifferentiable_modularLambda.continuous

/-! ## The inversion `S` -/

private theorem continuous_S_smul : Continuous fun τ : ℍ => ModularGroup.S • τ :=
  continuous_const_smul ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)

private theorem continuous_T_smul : Continuous fun τ : ℍ => ModularGroup.T • τ :=
  continuous_const_smul ((ModularGroup.T : SL(2, ℤ)) : GL (Fin 2) ℝ)

/-- CKMRV (2.17): `L|S = L_S`. -/
theorem ckmrvL_S (τ : ℍ) : ckmrvL (ModularGroup.S • τ) = ckmrvLS τ :=
  eq_of_exp_eq_upperHalfPlane (continuous_ckmrvL.comp continuous_S_smul) continuous_ckmrvLS
    (fun σ => by simp only [Function.comp, exp_ckmrvL, exp_ckmrvLS, modularLambda_S])
    UpperHalfPlane.I (by simp only [Function.comp, S_smul_I, ckmrvL_I, ckmrvLS_I]) τ

theorem S_smul_S_smul (τ : ℍ) : ModularGroup.S • ModularGroup.S • τ = τ := by
  apply UpperHalfPlane.ext
  rw [coe_S_smul, coe_S_smul]
  field_simp [τ.ne_zero]

/-- CKMRV (2.17): `L_S|S = L`. -/
theorem ckmrvLS_S (τ : ℍ) : ckmrvLS (ModularGroup.S • τ) = ckmrvL τ := by
  have h := ckmrvL_S (ModularGroup.S • τ)
  rw [S_smul_S_smul] at h
  exact h.symm

/-! ## The positive imaginary axis -/

private theorem imagAxisPoint_eq_ofComplex {t : ℝ} (ht : 0 < t) :
    imagAxisPoint t ht = ofComplex (Complex.I * t) := by
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using ht)]
  rfl

/-- A continuous logarithm of a function that is positive on the imaginary axis is real there,
once it is real at `i`. -/
private theorem log_eq_real_on_imagAxis {f g : ℍ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfe : ∀ τ, cexp (f τ) = g τ)
    (hpos : ∀ (t : ℝ) (ht : 0 < t), ∃ l : ℝ, 0 < l ∧ g (imagAxisPoint t ht) = l)
    (hI : f UpperHalfPlane.I = (Real.log (g UpperHalfPlane.I).re : ℂ))
    {t : ℝ} (ht : 0 < t) :
    f (imagAxisPoint t ht) = (Real.log (g (imagAxisPoint t ht)).re : ℂ) := by
  let F : ℝ → ℂ := fun s => f (ofComplex (Complex.I * s))
  let G : ℝ → ℂ := fun s => (Real.log (g (ofComplex (Complex.I * s))).re : ℂ)
  have hmaps : MapsTo (fun s : ℝ => Complex.I * s) (Ioi 0) {z : ℂ | 0 < z.im} :=
    fun s hs => by simpa using hs
  have hline : Continuous fun s : ℝ => Complex.I * s :=
    continuous_const.mul Complex.continuous_ofReal
  have hF : ContinuousOn F (Ioi 0) :=
    (continuousOn_comp_ofComplex hf).comp hline.continuousOn hmaps
  have hgc : ContinuousOn (fun s : ℝ => g (ofComplex (Complex.I * s))) (Ioi 0) :=
    (continuousOn_comp_ofComplex hg).comp hline.continuousOn hmaps
  have hre : ∀ s ∈ Ioi (0 : ℝ), 0 < (g (ofComplex (Complex.I * s))).re ∧
      g (ofComplex (Complex.I * s)) = ((g (ofComplex (Complex.I * s))).re : ℂ) := by
    intro s hs
    obtain ⟨l, hl, hgl⟩ := hpos s hs
    rw [← imagAxisPoint_eq_ofComplex hs, hgl]
    simp [hl]
  have hG : ContinuousOn G (Ioi 0) := by
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    refine (Complex.continuous_re.comp_continuousOn hgc).log fun s hs => (hre s hs).1.ne'
  have hexp : ∀ s ∈ Ioi (0 : ℝ), cexp (F s) = cexp (G s) := by
    intro s hs
    simp only [F, G, hfe]
    rw [← Complex.ofReal_exp, Real.exp_log (hre s hs).1, ← (hre s hs).2]
  have h1 : (1 : ℝ) ∈ Ioi (0 : ℝ) := Set.mem_Ioi.mpr one_pos
  have hI' : ofComplex (Complex.I * ((1 : ℝ) : ℂ)) = UpperHalfPlane.I := by
    rw [← imagAxisPoint_eq_ofComplex one_pos]
    apply UpperHalfPlane.ext
    simp [imagAxisPoint]
  have h0 : F 1 = G 1 := by simp only [F, G, hI', hI]
  have h := eqOn_of_exp_eq isPreconnected_Ioi hF hG hexp h1 h0 t ht
  simpa only [F, G, ← imagAxisPoint_eq_ofComplex ht] using h

private theorem modularLambda_imagAxis_pos (t : ℝ) (ht : 0 < t) :
    ∃ l : ℝ, 0 < l ∧ modularLambda (imagAxisPoint t ht) = l := by
  obtain ⟨l, hl, h⟩ := modularLambda_imagAxis_mem_Ioo ht
  exact ⟨l, hl.1, h⟩

private theorem one_sub_modularLambda_imagAxis_pos (t : ℝ) (ht : 0 < t) :
    ∃ l : ℝ, 0 < l ∧ 1 - modularLambda (imagAxisPoint t ht) = l := by
  obtain ⟨l, hl, h⟩ := modularLambda_imagAxis_mem_Ioo ht
  exact ⟨1 - l, by linarith [hl.2], by rw [h]; push_cast; ring⟩

private theorem log_half_eq : (-(Real.log 2 : ℂ)) = (Real.log ((1 / 2 : ℂ)).re : ℂ) := by
  have h : ((1 / 2 : ℂ)).re = (2 : ℝ)⁻¹ := by norm_num
  rw [h, Real.log_inv]
  push_cast
  ring

private theorem log_one_sub_half_eq :
    (-(Real.log 2 : ℂ)) = (Real.log ((1 : ℂ) - 1 / 2).re : ℂ) := by
  have h : ((1 : ℂ) - 1 / 2).re = (2 : ℝ)⁻¹ := by norm_num
  rw [h, Real.log_inv]
  push_cast
  ring

/-- `L(it) = log λ(it)` is real. -/
theorem ckmrvL_imagAxis {t : ℝ} (ht : 0 < t) :
    ckmrvL (imagAxisPoint t ht) = (Real.log (modularLambda (imagAxisPoint t ht)).re : ℂ) :=
  log_eq_real_on_imagAxis continuous_ckmrvL continuous_modularLambda exp_ckmrvL
    modularLambda_imagAxis_pos (by rw [ckmrvL_I, modularLambda_I, log_half_eq]) ht

/-- `L_S(it) = log (1 - λ(it))` is real. -/
theorem ckmrvLS_imagAxis {t : ℝ} (ht : 0 < t) :
    ckmrvLS (imagAxisPoint t ht) =
      (Real.log (1 - modularLambda (imagAxisPoint t ht)).re : ℂ) :=
  log_eq_real_on_imagAxis (g := fun τ => 1 - modularLambda τ) continuous_ckmrvLS
    (continuous_const.sub continuous_modularLambda) exp_ckmrvLS
    one_sub_modularLambda_imagAxis_pos
    (by
      rw [ckmrvLS_I]
      show _ = ((Real.log (1 - modularLambda UpperHalfPlane.I).re : ℝ) : ℂ)
      rw [modularLambda_I, ← log_one_sub_half_eq]) ht

/-! ## Behaviour at `i∞` -/

theorem thetaV_eq_exp_mul (τ : ℍ) :
    thetaV τ = cexp (π * I * τ) * jacobiTheta₂ ((τ : ℂ) / 2) τ ^ 4 := by
  rw [thetaV, thetaTwo, mul_pow, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- `λ e^{-πiτ} → 16`, the known leading coefficient `λ = 16 q^{1/2} + ⋯`. -/
theorem tendsto_modularLambda_mul_exp_atImInfty :
    Tendsto (fun τ : ℍ => modularLambda τ * cexp (-(π * I * τ))) atImInfty (𝓝 16) := by
  have h := (tendsto_jacobiTheta₂_half_atImInfty.pow 4).div tendsto_thetaU_atImInfty one_ne_zero
  rw [show ((2 : ℂ) ^ 4 / 1) = 16 by norm_num] at h
  refine h.congr fun τ => ?_
  have he : cexp (π * I * τ) * cexp (-(π * I * τ)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  simp only [Pi.div_apply]
  rw [modularLambda, thetaV_eq_exp_mul]
  calc jacobiTheta₂ ((τ : ℂ) / 2) τ ^ 4 / thetaU τ
      = (cexp (π * I * τ) * cexp (-(π * I * τ))) * (jacobiTheta₂ ((τ : ℂ) / 2) τ ^ 4 / thetaU τ) := by
        rw [he, one_mul]
    _ = cexp (π * I * τ) * jacobiTheta₂ ((τ : ℂ) / 2) τ ^ 4 / thetaU τ *
          cexp (-(π * I * τ)) := by ring

/-- A continuous logarithm on `ℍ` equals the principal logarithm on a half-plane where the
function stays in the slit plane, once they agree at one point of it. -/
private theorem eq_log_of_im_gt {f g : ℍ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfe : ∀ τ, cexp (f τ) = g τ) {A : ℝ} (hA : 0 ≤ A)
    (hslit : ∀ τ : ℍ, A < τ.im → g τ ∈ slitPlane)
    (τ₀ : ℍ) (hτ₀ : A < τ₀.im) (h₀ : f τ₀ = Complex.log (g τ₀))
    (τ : ℍ) (hτ : A < τ.im) : f τ = Complex.log (g τ) := by
  have hsub : {z : ℂ | A < z.im} ⊆ {z : ℂ | 0 < z.im} := fun z hz => lt_of_le_of_lt hA hz
  have hslit' : ∀ z ∈ {z : ℂ | A < z.im}, (g ∘ ofComplex) z ∈ slitPlane := by
    intro z hz
    have hz0 : 0 < z.im := hsub hz
    have := hslit (ofComplex z) (by rwa [UpperHalfPlane.ofComplex_apply_of_im_pos hz0])
    exact this
  have hF := (continuousOn_comp_ofComplex hf).mono hsub
  have hG : ContinuousOn (fun z => Complex.log ((g ∘ ofComplex) z)) {z : ℂ | A < z.im} :=
    ((continuousOn_comp_ofComplex hg).mono hsub).clog hslit'
  have hexp : ∀ z ∈ {z : ℂ | A < z.im},
      cexp ((f ∘ ofComplex) z) = cexp (Complex.log ((g ∘ ofComplex) z)) := by
    intro z hz
    rw [Complex.exp_log (slitPlane_ne_zero (hslit' z hz))]
    exact hfe _
  have h := eqOn_of_exp_eq (convex_halfSpace_im_gt A).isPreconnected hF hG hexp
    (x₀ := (τ₀ : ℂ)) hτ₀ (by simpa [Function.comp, UpperHalfPlane.ofComplex_apply] using h₀)
    (τ : ℂ) hτ
  simpa [Function.comp, UpperHalfPlane.ofComplex_apply] using h

private theorem eventually_im_gt {P : ℍ → Prop} (h : ∀ᶠ τ in atImInfty, P τ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ τ : ℍ, A < τ.im → P τ := by
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp h
  exact ⟨max A 0, le_max_right _ _, fun τ hτ => hA τ ((le_max_left _ _).trans hτ.le)⟩

private theorem mem_slitPlane_of_norm_sub_lt {w c : ℂ} (hw : ‖w - c‖ < c.re) :
    w ∈ slitPlane := by
  left
  have h := (Complex.abs_re_le_norm (w - c)).trans_lt hw
  rw [Complex.sub_re] at h
  linarith [(abs_lt.mp h).1]

/-- `L(τ) - πiτ → 4 log 2` at `i∞` (CKMRV (2.16), first order). -/
theorem tendsto_ckmrvL_sub_atImInfty :
    Tendsto (fun τ : ℍ => ckmrvL τ - π * I * τ) atImInfty (𝓝 (4 * Real.log 2 : ℂ)) := by
  set μ : ℍ → ℂ := fun τ => modularLambda τ * cexp (-(π * I * τ)) with hμ
  have hμlim : Tendsto μ atImInfty (𝓝 16) := tendsto_modularLambda_mul_exp_atImInfty
  have hnear : ∀ᶠ τ in atImInfty, ‖μ τ - 16‖ < (16 : ℂ).re := by
    have := (tendsto_iff_norm_sub_tendsto_zero.mp hμlim).eventually (gt_mem_nhds
      (show (0 : ℝ) < (16 : ℂ).re by norm_num))
    exact this
  obtain ⟨A, hA, hAμ⟩ := eventually_im_gt hnear
  have hslit : ∀ τ : ℍ, A < τ.im → μ τ ∈ slitPlane := fun τ hτ =>
    mem_slitPlane_of_norm_sub_lt (hAμ τ hτ)
  have hcμ : Continuous μ := continuous_modularLambda.mul
    (Complex.continuous_exp.comp ((continuous_const.mul UpperHalfPlane.continuous_coe).neg))
  have hcf : Continuous fun τ : ℍ => ckmrvL τ - π * I * τ :=
    continuous_ckmrvL.sub (continuous_const.mul UpperHalfPlane.continuous_coe)
  have hfe : ∀ τ : ℍ, cexp (ckmrvL τ - π * I * τ) = μ τ := by
    intro τ
    show cexp (ckmrvL τ - π * I * τ) = modularLambda τ * cexp (-(π * I * τ))
    rw [Complex.exp_sub, exp_ckmrvL, Complex.exp_neg, div_eq_mul_inv]
  -- the anchor on the imaginary axis
  have ht : 0 < A + 1 := by linarith
  set τ₀ := imagAxisPoint (A + 1) ht
  have hτ₀ : A < τ₀.im := by
    show A < (Complex.I * ((A + 1 : ℝ) : ℂ)).im
    simp
  have h₀ : ckmrvL τ₀ - π * I * τ₀ = Complex.log (μ τ₀) := by
    obtain ⟨l, hl, hlam⟩ := modularLambda_imagAxis_pos (A + 1) ht
    have hL := ckmrvL_imagAxis ht
    rw [hlam] at hL
    have hcoe : ((τ₀ : ℍ) : ℂ) = Complex.I * ((A + 1 : ℝ) : ℂ) := rfl
    have hμ0 : μ τ₀ = ((l * Real.exp (π * (A + 1)) : ℝ) : ℂ) := by
      simp only [hμ, hcoe]
      push_cast
      congr 1
      ring_nf
      rw [Complex.I_sq]
      ring_nf
    rw [hL, hμ0, hcoe, ← Complex.ofReal_log (by positivity), Real.log_mul hl.ne'
      (Real.exp_pos _).ne', Real.log_exp]
    simp only [Complex.ofReal_re]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have heq : ∀ᶠ τ in atImInfty, ckmrvL τ - π * I * τ = Complex.log (μ τ) := by
    rw [Filter.eventually_iff, atImInfty_mem]
    refine ⟨A + 1, fun τ hτ => ?_⟩
    exact eq_log_of_im_gt hcf hcμ hfe hA hslit τ₀ hτ₀ h₀ τ (by linarith)
  have hlog : Tendsto (fun τ => Complex.log (μ τ)) atImInfty (𝓝 (Complex.log 16)) :=
    ((continuousAt_clog (by norm_num : (16 : ℂ) ∈ slitPlane)).tendsto).comp hμlim
  have h16 : Complex.log 16 = (4 * Real.log 2 : ℂ) := by
    rw [show (16 : ℂ) = ((2 ^ 4 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num),
      Real.log_pow]
    push_cast
    ring
  rw [← h16]
  exact hlog.congr' (heq.mono fun τ h => h.symm)

/-- `L_S → 0` at `i∞`. -/
theorem tendsto_ckmrvLS_atImInfty : Tendsto ckmrvLS atImInfty (𝓝 0) := by
  set ν : ℍ → ℂ := fun τ => 1 - modularLambda τ with hν
  have hνlim : Tendsto ν atImInfty (𝓝 1) := by
    have := tendsto_const_nhds (x := (1 : ℂ)) |>.sub tendsto_modularLambda_atImInfty
    simpa [hν] using this
  have hnear : ∀ᶠ τ in atImInfty, ‖ν τ - 1‖ < (1 : ℂ).re := by
    exact (tendsto_iff_norm_sub_tendsto_zero.mp hνlim).eventually (gt_mem_nhds
      (show (0 : ℝ) < (1 : ℂ).re by norm_num))
  obtain ⟨A, hA, hAν⟩ := eventually_im_gt hnear
  have hslit : ∀ τ : ℍ, A < τ.im → ν τ ∈ slitPlane := fun τ hτ =>
    mem_slitPlane_of_norm_sub_lt (hAν τ hτ)
  have ht : 0 < A + 1 := by linarith
  set τ₀ := imagAxisPoint (A + 1) ht
  have hτ₀ : A < τ₀.im := by
    show A < (Complex.I * ((A + 1 : ℝ) : ℂ)).im
    simp
  have h₀ : ckmrvLS τ₀ = Complex.log (ν τ₀) := by
    obtain ⟨l, hl, hν0⟩ := one_sub_modularLambda_imagAxis_pos (A + 1) ht
    rw [ckmrvLS_imagAxis ht]
    simp only [hν]
    rw [hν0, ← Complex.ofReal_log hl.le]
    simp
  have heq : ∀ᶠ τ in atImInfty, ckmrvLS τ = Complex.log (ν τ) := by
    rw [Filter.eventually_iff, atImInfty_mem]
    refine ⟨A + 1, fun τ hτ => ?_⟩
    exact eq_log_of_im_gt continuous_ckmrvLS (continuous_const.sub continuous_modularLambda)
      exp_ckmrvLS hA hslit τ₀ hτ₀ h₀ τ (by linarith)
  have hlog : Tendsto (fun τ => Complex.log (ν τ)) atImInfty (𝓝 (Complex.log 1)) :=
    ((continuousAt_clog Complex.one_mem_slitPlane).tendsto).comp hνlim
  rw [Complex.log_one] at hlog
  exact hlog.congr' (heq.mono fun τ h => h.symm)

/-! ## The translation `T` -/

theorem im_T_smul (τ : ℍ) : (ModularGroup.T • τ).im = τ.im := by
  change ((ModularGroup.T • τ : ℍ) : ℂ).im = (τ : ℂ).im
  rw [coe_T_smul]
  simp

theorem tendsto_T_smul_atImInfty :
    Tendsto (fun τ : ℍ => ModularGroup.T • τ) atImInfty atImInfty := by
  refine tendsto_comap_iff.mpr ?_
  have h : (UpperHalfPlane.im ∘ fun τ : ℍ => ModularGroup.T • τ) = UpperHalfPlane.im := by
    funext τ
    exact im_T_smul τ
  rw [h]
  exact tendsto_upperHalfPlaneIm_atImInfty

/-- CKMRV (2.17): `L_S|T = -L_S`. -/
theorem ckmrvLS_T (τ : ℍ) : ckmrvLS (ModularGroup.T • τ) = -ckmrvLS τ := by
  have hd := eq_zero_of_exp_eq_one_of_tendsto
    (d := fun σ => ckmrvLS (ModularGroup.T • σ) + ckmrvLS σ)
    ((continuous_ckmrvLS.comp continuous_T_smul).add continuous_ckmrvLS)
    (fun σ => by
      rw [Complex.exp_add, exp_ckmrvLS, exp_ckmrvLS, modularLambda_T]
      have h1 : modularLambda σ - 1 ≠ 0 := sub_ne_zero.mpr (modularLambda_ne_one σ)
      field_simp
      ring)
    (by
      have h := (tendsto_ckmrvLS_atImInfty.comp tendsto_T_smul_atImInfty).add
        tendsto_ckmrvLS_atImInfty
      rw [add_zero] at h
      exact h)
    τ
  linear_combination hd

/-- CKMRV (2.17): `L|T = L - L_S + πi`. -/
theorem ckmrvL_T (τ : ℍ) :
    ckmrvL (ModularGroup.T • τ) = ckmrvL τ - ckmrvLS τ + π * I := by
  have hlimT : Tendsto (fun σ : ℍ => ckmrvL (ModularGroup.T • σ) - π * I * (σ : ℂ) - π * I)
      atImInfty (𝓝 (4 * Real.log 2 : ℂ)) := by
    refine (tendsto_ckmrvL_sub_atImInfty.comp tendsto_T_smul_atImInfty).congr fun σ => ?_
    simp only [Function.comp, coe_T_smul]
    ring
  have hd := eq_zero_of_exp_eq_one_of_tendsto
    (d := fun σ => ckmrvL (ModularGroup.T • σ) - ckmrvL σ + ckmrvLS σ - π * I)
    ((((continuous_ckmrvL.comp continuous_T_smul).sub continuous_ckmrvL).add
      continuous_ckmrvLS).sub continuous_const)
    (fun σ => by
      rw [Complex.exp_sub, Complex.exp_add, Complex.exp_sub, exp_ckmrvL, exp_ckmrvL,
        exp_ckmrvLS, modularLambda_T, Complex.exp_pi_mul_I]
      have h0 : modularLambda σ ≠ 0 := modularLambda_ne_zero σ
      have h1 : modularLambda σ - 1 ≠ 0 := sub_ne_zero.mpr (modularLambda_ne_one σ)
      field_simp
      ring)
    (by
      have h := (hlimT.sub tendsto_ckmrvL_sub_atImInfty).add tendsto_ckmrvLS_atImInfty
      rw [sub_self, zero_add] at h
      refine h.congr fun σ => ?_
      ring)
    τ
  linear_combination hd

end E8Leech
