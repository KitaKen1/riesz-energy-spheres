import E8Leech.CKMRVLaplaceAxisClean
import E8Leech.CKMRVKernelResidues

/-!
# The minus kernels on the imaginary axis (CKMRV (5.1), P4d-2)

For `τ = iβ` the integrand `t ↦ K₋(τ, it)` has its only possible singularities at `t = β` and
`t = β⁻¹`, i.e. at `z = τ` and `z = Sτ`. Both are removable.

Known answer first: the residues `Res_{τ=z} K₋` and `Res_{τ=z} (K₋ ∣ S)` vanish (CKMRV
Theorem 4.3(3) with `φ₋(I) = φ₋(S) = 0`). In numerator form, write
`K₋(τ, z) = c⁻¹ N(τ, z) / (Δ(z) (j(τ) − j(z)))` (and `Δ(z)²` for `d = 24`). Then

* `N(τ, τ) = (E₄²E₆/Δ)(τ) · (L(ξ₂A + ξ₄B − 3456Δ) + L_S(ξ₂^S A + ξ₄^S B)) = 0`, by the two
  residue identities of `CKMRVKernelResidues`;
* the numerator `N^S` of `K₋ ∣ S` gives the bracket with `A' = −E₄²V − E₆(U² − W²)` and
  `B' = E₆V + E₄(U² − W²)`; the two new identities `ξ₂A' + ξ₄B' = 0` and
  `ξ₂^S A' + ξ₄^S B' = 3456Δ` are the `S`-transforms of the old ones and are checked by `ring`
  after `U = V + W` and `(UVW)² = 256Δ`.

The certificates were found by a Gröbner reduction (`research/check-minus-axis-certificates`).
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Asymptotics MeasureTheory Set
open UpperHalfPlane hiding I
open scoped Real Manifold MatrixGroups ModularForm

/-! ## The `S`-transformed residue identities -/

/-- `ξ₂ A' + ξ₄ B' = 0`. -/
theorem ckmrvMinusResidue_identity_three (z : ℍ) :
    ckmrvXiTwo z * (-(ModularForm.E₄ z ^ 2 * thetaV z) -
        ModularForm.E₆ z * (thetaU z ^ 2 - thetaW z ^ 2)) +
      ckmrvXiFour z * (ModularForm.E₆ z * thetaV z +
        ModularForm.E₄ z * (thetaU z ^ 2 - thetaW z ^ 2)) = 0 := by
  rw [eisensteinFour_eq_theta, eisensteinSix_eq_theta]
  simp only [ckmrvXiTwo, ckmrvXiFour, thetaU_eq_add]
  ring

/-- `ξ₂^S A' + ξ₄^S B' = 3456 Δ`. -/
theorem ckmrvMinusResidue_identity_four (z : ℍ) :
    ckmrvXiTwoS z * (-(ModularForm.E₄ z ^ 2 * thetaV z) -
        ModularForm.E₆ z * (thetaU z ^ 2 - thetaW z ^ 2)) +
      ckmrvXiFourS z * (ModularForm.E₆ z * thetaV z +
        ModularForm.E₄ z * (thetaU z ^ 2 - thetaW z ^ 2)) =
        3456 * ModularForm.discriminant z := by
  have hΔ := thetaProductSq_eq_discriminant z
  rw [eisensteinFour_eq_theta, eisensteinSix_eq_theta]
  simp only [ckmrvXiTwoS, ckmrvXiFourS, thetaProductSq] at hΔ ⊢
  simp only [thetaU_eq_add] at hΔ ⊢
  linear_combination (27 / 2 : ℂ) * hΔ

/-! ## Dimension eight -/

/-- The numerator of `K₋⁽⁸⁾(τ, z) = c⁻¹ N(τ, z) / (Δ(z) (j(τ) − j(z)))`. -/
def eightMinusSingNum (τ z : ℍ) : ℂ :=
  eightMinusTauCoeff 0 τ * (ModularForm.E₄ z * ModularForm.E₆ z * ckmrvL z) +
    eightMinusTauCoeff 1 τ * (ModularForm.E₄ z ^ 2 * thetaW z) +
      eightMinusTauCoeff 2 τ * (ModularForm.E₆ z * (thetaU z ^ 2 - thetaV z ^ 2))

/-- The numerator of `K₋⁽⁸⁾ ∣ S`. -/
def eightMinusSingNumS (τ z : ℍ) : ℂ :=
  eightMinusTauCoeff 0 τ * (ModularForm.E₄ z * ModularForm.E₆ z * ckmrvLS z) -
    eightMinusTauCoeff 1 τ * (ModularForm.E₄ z ^ 2 * thetaV z) +
      eightMinusTauCoeff 2 τ * (ModularForm.E₆ z * (thetaU z ^ 2 - thetaW z ^ 2))

theorem ckmrvEightMinusKernel_eq_sing (τ z : ℍ) :
    ckmrvEightMinusKernel τ z = ckmrvMinusScale⁻¹ *
      (eightMinusSingNum τ z / ModularForm.discriminant z /
        (kleinModularJ τ - kleinModularJ z)) := by
  rw [ckmrvEightMinusKernel_eq_z, eightMinusDenZ_eq_mul, eightMinusSingNum, div_div]
  ring

theorem ckmrvEightMinusKernel_S_eq_sing (τ w : ℍ) :
    ckmrvEightMinusKernel τ (ModularGroup.S • w) * (w : ℂ) ^ 2 = ckmrvMinusScale⁻¹ *
      (eightMinusSingNumS τ w / ModularForm.discriminant w /
        (kleinModularJ τ - kleinModularJ w)) := by
  rw [ckmrvEightMinusKernel_S_right, eightMinusDenZ_eq_mul, eightMinusSingNumS, div_div]
  ring

theorem eightMinusSingNum_self (τ : ℍ) : eightMinusSingNum τ τ = 0 := by
  have h1 := ckmrvMinusResidue_identity_one τ
  have h2 := ckmrvMinusResidue_identity_two τ
  have hD := eisenstein_cubic_square_discriminant τ
  have hu : ModularForm.discriminant τ * (ModularForm.discriminant τ)⁻¹ = 1 :=
    mul_inv_cancel₀ (ModularForm.discriminant_ne_zero τ)
  have hJ : kleinModularJ τ = ModularForm.E₄ τ ^ 3 * (ModularForm.discriminant τ)⁻¹ := by
    rw [kleinModularJ, div_eq_mul_inv]
  have hp1 : ckmrvPsiBasis τ 1 = ckmrvXiTwo τ * ckmrvL τ + ckmrvXiTwoS τ * ckmrvLS τ := rfl
  have hp2 : ckmrvPsiBasis τ 2 = ckmrvXiFour τ * ckmrvL τ + ckmrvXiFourS τ * ckmrvLS τ := rfl
  rw [eightMinusSingNum, eightMinusTauCoeff_zero, eightMinusTauCoeff_one, eightMinusTauCoeff_two,
    ckmrvModularFactor_two_eq, hJ, hp1, hp2]
  linear_combination
    (ModularForm.E₄ τ ^ 2 * ModularForm.E₆ τ * (ModularForm.discriminant τ)⁻¹ * ckmrvL τ) * h1 +
    (ModularForm.E₄ τ ^ 2 * ModularForm.E₆ τ * (ModularForm.discriminant τ)⁻¹ * ckmrvLS τ) * h2 +
    (-(ModularForm.E₄ τ ^ 2) * (ModularForm.discriminant τ)⁻¹ * thetaW τ *
      (ckmrvL τ * ckmrvXiFour τ + ckmrvLS τ * ckmrvXiFourS τ)) * hD +
    (-1728 * ModularForm.E₄ τ ^ 2 * (-2 * ModularForm.E₆ τ * ckmrvL τ +
      ckmrvL τ * thetaW τ * ckmrvXiFour τ + ckmrvLS τ * thetaW τ * ckmrvXiFourS τ)) * hu

theorem eightMinusSingNumS_self (τ : ℍ) : eightMinusSingNumS τ τ = 0 := by
  have h3 := ckmrvMinusResidue_identity_three τ
  have h4 := ckmrvMinusResidue_identity_four τ
  have hD := eisenstein_cubic_square_discriminant τ
  have hu : ModularForm.discriminant τ * (ModularForm.discriminant τ)⁻¹ = 1 :=
    mul_inv_cancel₀ (ModularForm.discriminant_ne_zero τ)
  have hJ : kleinModularJ τ = ModularForm.E₄ τ ^ 3 * (ModularForm.discriminant τ)⁻¹ := by
    rw [kleinModularJ, div_eq_mul_inv]
  have hp1 : ckmrvPsiBasis τ 1 = ckmrvXiTwo τ * ckmrvL τ + ckmrvXiTwoS τ * ckmrvLS τ := rfl
  have hp2 : ckmrvPsiBasis τ 2 = ckmrvXiFour τ * ckmrvL τ + ckmrvXiFourS τ * ckmrvLS τ := rfl
  rw [eightMinusSingNumS, eightMinusTauCoeff_zero, eightMinusTauCoeff_one, eightMinusTauCoeff_two,
    ckmrvModularFactor_two_eq, hJ, hp1, hp2]
  linear_combination
    (ModularForm.E₄ τ ^ 2 * ModularForm.E₆ τ * (ModularForm.discriminant τ)⁻¹ * ckmrvL τ) * h3 +
    (ModularForm.E₄ τ ^ 2 * ModularForm.E₆ τ * (ModularForm.discriminant τ)⁻¹ * ckmrvLS τ) * h4 +
    (ModularForm.E₄ τ ^ 2 * (ModularForm.discriminant τ)⁻¹ * thetaV τ *
      (ckmrvL τ * ckmrvXiFour τ + ckmrvLS τ * ckmrvXiFourS τ)) * hD +
    (1728 * ModularForm.E₄ τ ^ 2 * (2 * ModularForm.E₆ τ * ckmrvLS τ +
      ckmrvL τ * thetaV τ * ckmrvXiFour τ + ckmrvLS τ * thetaV τ * ckmrvXiFourS τ)) * hu

theorem mdifferentiable_eightMinusSingNum (τ : ℍ) : MDiff (fun z => eightMinusSingNum τ z) := by
  have h4 := ModularFormClass.holo ModularForm.E₄
  have h6 := ModularFormClass.holo ModularForm.E₆
  exact ((mdifferentiable_const.mul ((h4.mul h6).mul mdifferentiable_ckmrvL)).add
    (mdifferentiable_const.mul ((h4.pow 2).mul mdifferentiable_thetaW))).add
    (mdifferentiable_const.mul (h6.mul ((mdifferentiable_thetaU.pow 2).sub
      (mdifferentiable_thetaV.pow 2))))

theorem mdifferentiable_eightMinusSingNumS (τ : ℍ) :
    MDiff (fun z => eightMinusSingNumS τ z) := by
  have h4 := ModularFormClass.holo ModularForm.E₄
  have h6 := ModularFormClass.holo ModularForm.E₆
  exact ((mdifferentiable_const.mul ((h4.mul h6).mul mdifferentiable_ckmrvLS)).sub
    (mdifferentiable_const.mul ((h4.pow 2).mul mdifferentiable_thetaV))).add
    (mdifferentiable_const.mul (h6.mul ((mdifferentiable_thetaU.pow 2).sub
      (mdifferentiable_thetaW.pow 2))))

/-- `w ↦ K₋⁽⁸⁾(τ, ofComplex w)` has a finite limit at `w = τ`. -/
theorem exists_tendsto_ckmrvEightMinusKernel_right (τ : ℍ)
    (hj : kleinModularJDerivative τ ≠ 0) :
    ∃ L : ℂ, Tendsto (fun w : ℂ => ckmrvEightMinusKernel τ (UpperHalfPlane.ofComplex w))
      (𝓝[≠] (τ : ℂ)) (𝓝 L) := by
  obtain ⟨L₀, hL₀⟩ := exists_tendsto_div_kleinModularJ_sub (F := fun z => eightMinusSingNum τ z /
    ModularForm.discriminant z) ((mdifferentiable_eightMinusSingNum τ).div
      mdifferentiable_modularDiscriminant ModularForm.discriminant_ne_zero)
    (by simp [eightMinusSingNum_self]) hj
  refine ⟨_, (hL₀.const_mul ckmrvMinusScale⁻¹).congr' (Eventually.of_forall fun w => ?_)⟩
  beta_reduce
  rw [ckmrvEightMinusKernel_eq_sing]

/-- `w ↦ K₋⁽⁸⁾(τ, S • ofComplex w) · w²` has a finite limit at `w = τ`. -/
theorem exists_tendsto_ckmrvEightMinusKernel_S_right (τ : ℍ)
    (hj : kleinModularJDerivative τ ≠ 0) :
    ∃ L : ℂ, Tendsto (fun w : ℂ => ckmrvEightMinusKernel τ
      (ModularGroup.S • UpperHalfPlane.ofComplex w) * ((UpperHalfPlane.ofComplex w : ℍ) : ℂ) ^ 2)
      (𝓝[≠] (τ : ℂ)) (𝓝 L) := by
  obtain ⟨L₀, hL₀⟩ := exists_tendsto_div_kleinModularJ_sub (F := fun z => eightMinusSingNumS τ z /
    ModularForm.discriminant z) ((mdifferentiable_eightMinusSingNumS τ).div
      mdifferentiable_modularDiscriminant ModularForm.discriminant_ne_zero)
    (by simp [eightMinusSingNumS_self]) hj
  refine ⟨_, (hL₀.const_mul ckmrvMinusScale⁻¹).congr' (Eventually.of_forall fun w => ?_)⟩
  beta_reduce
  rw [ckmrvEightMinusKernel_S_eq_sing]

theorem continuousOn_ckmrvEightMinusKernel_imagPt' (τ : ℍ) {s : Set ℝ} (hs : s ⊆ Ioi 0)
    (hτ : ∀ t ∈ s, kleinModularJ τ ≠ kleinModularJ (imagPt t)) :
    ContinuousOn (fun t => ckmrvEightMinusKernel τ (imagPt t)) s := by
  have h4 := (ModularFormClass.holo ModularForm.E₄).continuous
  have h6 := (ModularFormClass.holo ModularForm.E₆).continuous
  have hL := continuous_ckmrvL
  have hU := mdifferentiable_thetaU.continuous
  have hV := mdifferentiable_thetaV.continuous
  have hW := mdifferentiable_thetaW.continuous
  have hN : Continuous fun z : ℍ =>
      eightMinusTauCoeff 0 τ * (ModularForm.E₄ z * ModularForm.E₆ z * ckmrvL z) +
        eightMinusTauCoeff 1 τ * (ModularForm.E₄ z ^ 2 * thetaW z) +
          eightMinusTauCoeff 2 τ * (ModularForm.E₆ z * (thetaU z ^ 2 - thetaV z ^ 2)) := by
    fun_prop
  have hD := ((continuousOn_comp_imagPt (continuous_eightMinusDenZ τ)).mono hs).inv₀
    fun t ht => eightMinusDenZ_ne_zero (hτ t ht)
  have h := (continuousOn_const (c := ckmrvMinusScale⁻¹)).mul hD |>.mul
    ((continuousOn_comp_imagPt hN).mono hs)
  refine h.congr fun t _ => ?_
  rw [ckmrvEightMinusKernel_eq_z]
  rfl

/-- **CKMRV (5.1) on the imaginary axis, `d = 8`, minus kernel.** For `τ = iβ`, `β ≠ 1`, the
Laplace integral converges absolutely for `r ≠ 0`; the singularities at `t = β, 1/β` are
removable. -/
theorem integrableOn_ckmrvEightMinusKernel_laplace_imagAxis {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1)
    {r : ℝ} (hr : r ≠ 0) :
    IntegrableOn (fun t => ckmrvEightMinusKernel (imagPt β) (imagPt t) *
      (Real.exp (-(π * r ^ 2) * t) : ℂ)) (Ioi 0) := by
  have hj := kleinModularJDerivative_imagPt_ne_zero hβ hβ1
  have hpole : ∀ t : ℝ, 0 < t → t ≠ β → t ≠ β⁻¹ →
      kleinModularJ (imagPt β) ≠ kleinModularJ (imagPt t) :=
    fun _ ht h1 h2 => kleinModularJ_imagPt_ne hβ ht h1 h2
  set τ := imagPt β with hτdef
  have hτc : (τ : ℂ) = I * β := coe_imagPt hβ
  refine integrableOn_Ioi_mul_exp_of_isBigO_two (a := 0) (p := β) (q := β⁻¹) (by positivity) hβ
    (inv_pos.mpr hβ) (ne_inv_of_ne_one hβ hβ1) ?_ ?_ ?_
    (isBigO_ckmrvEightMinusKernel_imagPt_zero τ) (isBigO_ckmrvEightMinusKernel_imagPt_atTop τ)
  · intro x hx hxp hxq
    set s : Set ℝ := Ioi 0 ∩ ({β}ᶜ ∩ {β⁻¹}ᶜ)
    have hsopen : IsOpen s := isOpen_Ioi.inter (isOpen_compl_singleton.inter isOpen_compl_singleton)
    have hxs : x ∈ s := ⟨hx, hxp, hxq⟩
    exact (continuousOn_ckmrvEightMinusKernel_imagPt' τ (fun t ht => ht.1)
      (fun t ht => hpole t ht.1 ht.2.1 ht.2.2)).continuousAt (hsopen.mem_nhds hxs)
  · obtain ⟨L, hL⟩ := exists_tendsto_ckmrvEightMinusKernel_right τ hj
    rw [hτc] at hL
    exact ⟨L, hL.comp tendsto_I_mul_punctured⟩
  · obtain ⟨L, hL⟩ := exists_tendsto_ckmrvEightMinusKernel_S_right τ hj
    rw [hτc] at hL
    have hsq : Tendsto (fun t : ℝ => -((t : ℂ) ^ 2)) (𝓝[≠] β⁻¹) (𝓝 (-((β⁻¹ : ℝ) : ℂ) ^ 2)) :=
      ((Continuous.tendsto (by fun_prop) _).mono_left nhdsWithin_le_nhds)
    refine ⟨_, ((hL.comp (tendsto_I_mul_inv_punctured hβ)).mul hsq).congr' ?_⟩
    filter_upwards [(nhdsWithin_le_nhds (Ioi_mem_nhds (inv_pos.mpr hβ)) :
      Ioi (0 : ℝ) ∈ 𝓝[≠] β⁻¹)] with t ht
    have ht0 : (0 : ℝ) < t := ht
    simp only [Function.comp_apply]
    have hS := S_smul_imagPt_inv ht0
    have hsq1 := coe_imagPt_inv_sq ht0
    simp only [imagPt] at hS hsq1 ⊢
    rw [hS, mul_assoc]
    rw [show ((UpperHalfPlane.ofComplex (I * ((t⁻¹ : ℝ) : ℂ)) : ℍ) : ℂ) ^ 2 * -((t : ℂ) ^ 2) = 1
      from by simpa [neg_mul] using hsq1, mul_one]

/-! ## The Leech lattice -/

/-- The numerator of `K₋⁽²⁴⁾(τ, z) = c⁻¹ N(τ, z) / (Δ(z)² (j(τ) − j(z)))`. -/
def leechMinusSingNum (τ z : ℍ) : ℂ := ckmrvEll z * leechMinusNEll τ z + leechMinusNZero τ z

theorem ckmrvLeechMinusKernel_eq_sing (τ z : ℍ) :
    ckmrvLeechMinusKernel τ z = ckmrvMinusScale⁻¹ *
      (leechMinusSingNum τ z / ModularForm.discriminant z ^ 2 /
        (kleinModularJ τ - kleinModularJ z)) := by
  rw [ckmrvLeechMinusKernel_eq_z, eightMinusDenZ_eq_mul, mul_inv (ModularForm.discriminant z),
    leechMinusSingNum]
  ring

theorem ckmrvLeechMinusKernel_S_eq_sing (τ w : ℍ) :
    ckmrvLeechMinusKernel τ (ModularGroup.S • w) * (w : ℂ) ^ 10 = ckmrvMinusScale⁻¹ *
      (leechMinusNS τ w / ModularForm.discriminant w ^ 2 /
        (kleinModularJ τ - kleinModularJ w)) := by
  rw [ckmrvLeechMinusKernel_S_right, eightMinusDenZ_eq_mul, mul_inv (ModularForm.discriminant w)]
  ring

theorem leechMinusSingNum_self (τ : ℍ) : leechMinusSingNum τ τ = 0 := by
  have h1 := ckmrvMinusResidue_identity_one τ
  have h2 := ckmrvMinusResidue_identity_two τ
  have hD := eisenstein_cubic_square_discriminant τ
  have hJ := kleinModularJ_mul_discriminant τ
  have hp1 : ckmrvPsiBasis τ 1 = ckmrvXiTwo τ * ckmrvL τ + ckmrvXiTwoS τ * ckmrvLS τ := rfl
  have hp2 : ckmrvPsiBasis τ 2 = ckmrvXiFour τ * ckmrvL τ + ckmrvXiFourS τ * ckmrvLS τ := rfl
  simp only [leechMinusSingNum, leechMinusNEll, leechMinusNZero, eightMinusDenZ, leechMinusBeta,
    leechMinusGamma, leechMinusAlpha, ckmrvEll, hp1, hp2]
  linear_combination
    (ModularForm.E₄ τ ^ 2 * ModularForm.E₆ τ * ckmrvL τ) * h1 +
    (ModularForm.E₄ τ ^ 2 * ModularForm.E₆ τ * ckmrvLS τ) * h2 +
    (3 * thetaW τ * (-(ModularForm.E₄ τ ^ 2) * ckmrvL τ * ckmrvXiFour τ -
      ModularForm.E₄ τ ^ 2 * ckmrvLS τ * ckmrvXiFourS τ +
      ModularForm.E₄ τ * ModularForm.E₆ τ * ckmrvL τ * ckmrvXiTwo τ +
      ModularForm.E₄ τ * ModularForm.E₆ τ * ckmrvLS τ * ckmrvXiTwoS τ -
      1152 * ModularForm.discriminant τ)) * hJ +
    (-(ModularForm.E₄ τ ^ 2) * thetaW τ *
      (ckmrvL τ * ckmrvXiFour τ + ckmrvLS τ * ckmrvXiFourS τ)) * hD

theorem leechMinusNS_self (τ : ℍ) : leechMinusNS τ τ = 0 := by
  have h3 := ckmrvMinusResidue_identity_three τ
  have h4 := ckmrvMinusResidue_identity_four τ
  have hD := eisenstein_cubic_square_discriminant τ
  have hJ := kleinModularJ_mul_discriminant τ
  have hp1 : ckmrvPsiBasis τ 1 = ckmrvXiTwo τ * ckmrvL τ + ckmrvXiTwoS τ * ckmrvLS τ := rfl
  have hp2 : ckmrvPsiBasis τ 2 = ckmrvXiFour τ * ckmrvL τ + ckmrvXiFourS τ * ckmrvLS τ := rfl
  simp only [leechMinusNS, eightMinusDenZ, leechMinusBeta, leechMinusGamma, leechMinusAlpha,
    hp1, hp2]
  linear_combination
    (ModularForm.E₄ τ ^ 2 * ModularForm.E₆ τ * ckmrvL τ) * h3 +
    (ModularForm.E₄ τ ^ 2 * ModularForm.E₆ τ * ckmrvLS τ) * h4 +
    (-3 * thetaV τ * (-(ModularForm.E₄ τ ^ 2) * ckmrvL τ * ckmrvXiFour τ -
      ModularForm.E₄ τ ^ 2 * ckmrvLS τ * ckmrvXiFourS τ +
      ModularForm.E₄ τ * ModularForm.E₆ τ * ckmrvL τ * ckmrvXiTwo τ +
      ModularForm.E₄ τ * ModularForm.E₆ τ * ckmrvLS τ * ckmrvXiTwoS τ -
      1152 * ModularForm.discriminant τ)) * hJ +
    (ModularForm.E₄ τ ^ 2 * thetaV τ *
      (ckmrvL τ * ckmrvXiFour τ + ckmrvLS τ * ckmrvXiFourS τ)) * hD

theorem mdifferentiable_eightMinusDenZ (τ : ℍ) : MDiff (fun z => eightMinusDenZ τ z) :=
  (mdifferentiable_modularDiscriminant.mul mdifferentiable_const).sub
    ((ModularFormClass.holo ModularForm.E₄).pow 3)

theorem mdifferentiable_leechMinusSingNum (τ : ℍ) :
    MDiff (fun z => leechMinusSingNum τ z) := by
  have h4 := ModularFormClass.holo ModularForm.E₄
  have h6 := ModularFormClass.holo ModularForm.E₆
  have hΔ := mdifferentiable_modularDiscriminant
  have hz := UpperHalfPlane.mdifferentiable_coe
  have hEll : MDiff (fun z => ckmrvEll z) :=
    (mdifferentiable_const.mul hz).add mdifferentiable_const
  have hNEll : MDiff (fun z => leechMinusNEll τ z) :=
    mdifferentiable_const.mul ((h4.pow 2).mul h6)
  have hNZero : MDiff (fun z => leechMinusNZero τ z) :=
    (((mdifferentiable_const.mul (((h4.pow 2).mul h6).mul
      ((mdifferentiable_ckmrvL.sub (mdifferentiable_const.mul hz)).sub mdifferentiable_const))).add
      ((mdifferentiable_thetaW.mul (mdifferentiable_eightMinusDenZ τ)).mul
        mdifferentiable_const)).add
      ((hΔ.mul mdifferentiable_thetaW).mul mdifferentiable_const)).sub
      (mdifferentiable_const.mul ((h4.mul h6).mul ((mdifferentiable_thetaU.pow 2).sub
        (mdifferentiable_thetaV.pow 2))))
  exact (hEll.mul hNEll).add hNZero

theorem mdifferentiable_leechMinusNS (τ : ℍ) : MDiff (fun z => leechMinusNS τ z) := by
  have h4 := ModularFormClass.holo ModularForm.E₄
  have h6 := ModularFormClass.holo ModularForm.E₆
  have hΔ := mdifferentiable_modularDiscriminant
  exact ((mdifferentiable_const.mul (((h4.pow 2).mul h6).mul mdifferentiable_ckmrvLS)).sub
    (mdifferentiable_thetaV.mul (((mdifferentiable_eightMinusDenZ τ).mul mdifferentiable_const).add
      (hΔ.mul mdifferentiable_const)))).sub
    (mdifferentiable_const.mul ((h4.mul h6).mul ((mdifferentiable_thetaU.pow 2).sub
      (mdifferentiable_thetaW.pow 2))))

theorem exists_tendsto_ckmrvLeechMinusKernel_right (τ : ℍ)
    (hj : kleinModularJDerivative τ ≠ 0) :
    ∃ L : ℂ, Tendsto (fun w : ℂ => ckmrvLeechMinusKernel τ (UpperHalfPlane.ofComplex w))
      (𝓝[≠] (τ : ℂ)) (𝓝 L) := by
  obtain ⟨L₀, hL₀⟩ := exists_tendsto_div_kleinModularJ_sub (F := fun z => leechMinusSingNum τ z /
    ModularForm.discriminant z ^ 2) ((mdifferentiable_leechMinusSingNum τ).div
      (mdifferentiable_modularDiscriminant.pow 2)
      (fun z => pow_ne_zero 2 (ModularForm.discriminant_ne_zero z)))
    (by simp [leechMinusSingNum_self]) hj
  refine ⟨_, (hL₀.const_mul ckmrvMinusScale⁻¹).congr' (Eventually.of_forall fun w => ?_)⟩
  beta_reduce
  rw [ckmrvLeechMinusKernel_eq_sing]

theorem exists_tendsto_ckmrvLeechMinusKernel_S_right (τ : ℍ)
    (hj : kleinModularJDerivative τ ≠ 0) :
    ∃ L : ℂ, Tendsto (fun w : ℂ => ckmrvLeechMinusKernel τ
      (ModularGroup.S • UpperHalfPlane.ofComplex w) *
        ((UpperHalfPlane.ofComplex w : ℍ) : ℂ) ^ 10) (𝓝[≠] (τ : ℂ)) (𝓝 L) := by
  obtain ⟨L₀, hL₀⟩ := exists_tendsto_div_kleinModularJ_sub (F := fun z => leechMinusNS τ z /
    ModularForm.discriminant z ^ 2) ((mdifferentiable_leechMinusNS τ).div
      (mdifferentiable_modularDiscriminant.pow 2)
      (fun z => pow_ne_zero 2 (ModularForm.discriminant_ne_zero z)))
    (by simp [leechMinusNS_self]) hj
  refine ⟨_, (hL₀.const_mul ckmrvMinusScale⁻¹).congr' (Eventually.of_forall fun w => ?_)⟩
  beta_reduce
  rw [ckmrvLeechMinusKernel_S_eq_sing]

theorem continuousOn_ckmrvLeechMinusKernel_imagPt' (τ : ℍ) {s : Set ℝ} (hs : s ⊆ Ioi 0)
    (hτ : ∀ t ∈ s, kleinModularJ τ ≠ kleinModularJ (imagPt t)) :
    ContinuousOn (fun t => ckmrvLeechMinusKernel τ (imagPt t)) s := by
  have hΔ := mdifferentiable_modularDiscriminant.continuous
  have hN : Continuous fun z : ℍ => ckmrvEll z * leechMinusNEll τ z + leechMinusNZero τ z :=
    (mdifferentiable_leechMinusSingNum τ).continuous
  have hD := ((continuousOn_comp_imagPt (continuous_eightMinusDenZ τ)).mono hs).inv₀
    fun t ht => eightMinusDenZ_ne_zero (hτ t ht)
  have hΔi := ((continuousOn_comp_imagPt hΔ).mono hs).inv₀
    fun t _ => ModularForm.discriminant_ne_zero _
  have h := (((continuousOn_const (c := ckmrvMinusScale⁻¹)).mul hD).mul hΔi).mul
    ((continuousOn_comp_imagPt hN).mono hs)
  refine h.congr fun t _ => ?_
  rw [ckmrvLeechMinusKernel_eq_z]
  rfl

/-- **CKMRV (5.1) on the imaginary axis, Leech minus kernel, for `r² > 2`.** -/
theorem integrableOn_ckmrvLeechMinusKernel_laplace_imagAxis {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1)
    {r : ℝ} (hr : 2 < r ^ 2) :
    IntegrableOn (fun t => ckmrvLeechMinusKernel (imagPt β) (imagPt t) *
      (Real.exp (-(π * r ^ 2) * t) : ℂ)) (Ioi 0) := by
  have hj := kleinModularJDerivative_imagPt_ne_zero hβ hβ1
  have hpole : ∀ t : ℝ, 0 < t → t ≠ β → t ≠ β⁻¹ →
      kleinModularJ (imagPt β) ≠ kleinModularJ (imagPt t) :=
    fun _ ht h1 h2 => kleinModularJ_imagPt_ne hβ ht h1 h2
  set τ := imagPt β with hτdef
  have hτc : (τ : ℂ) = I * β := coe_imagPt hβ
  refine integrableOn_Ioi_mul_exp_of_isBigO_two (a := 2 * π) (p := β) (q := β⁻¹)
    (by nlinarith [Real.pi_pos]) hβ (inv_pos.mpr hβ) (ne_inv_of_ne_one hβ hβ1) ?_ ?_ ?_
    (isBigO_ckmrvLeechMinusKernel_imagPt_zero τ) (isBigO_ckmrvLeechMinusKernel_imagPt_atTop τ)
  · intro x hx hxp hxq
    set s : Set ℝ := Ioi 0 ∩ ({β}ᶜ ∩ {β⁻¹}ᶜ)
    have hsopen : IsOpen s := isOpen_Ioi.inter (isOpen_compl_singleton.inter isOpen_compl_singleton)
    have hxs : x ∈ s := ⟨hx, hxp, hxq⟩
    exact (continuousOn_ckmrvLeechMinusKernel_imagPt' τ (fun t ht => ht.1)
      (fun t ht => hpole t ht.1 ht.2.1 ht.2.2)).continuousAt (hsopen.mem_nhds hxs)
  · obtain ⟨L, hL⟩ := exists_tendsto_ckmrvLeechMinusKernel_right τ hj
    rw [hτc] at hL
    exact ⟨L, hL.comp tendsto_I_mul_punctured⟩
  · obtain ⟨L, hL⟩ := exists_tendsto_ckmrvLeechMinusKernel_S_right τ hj
    rw [hτc] at hL
    have hpow : Tendsto (fun t : ℝ => -((t : ℂ) ^ 10)) (𝓝[≠] β⁻¹) (𝓝 (-((β⁻¹ : ℝ) : ℂ) ^ 10)) :=
      ((Continuous.tendsto (by fun_prop) _).mono_left nhdsWithin_le_nhds)
    refine ⟨_, ((hL.comp (tendsto_I_mul_inv_punctured hβ)).mul hpow).congr' ?_⟩
    filter_upwards [(nhdsWithin_le_nhds (Ioi_mem_nhds (inv_pos.mpr hβ)) :
      Ioi (0 : ℝ) ∈ 𝓝[≠] β⁻¹)] with t ht
    have ht0 : (0 : ℝ) < t := ht
    simp only [Function.comp_apply]
    have hS := S_smul_imagPt_inv ht0
    have hp10 := coe_imagPt_inv_pow_ten ht0
    simp only [imagPt] at hS hp10 ⊢
    rw [hS, mul_assoc]
    rw [show ((UpperHalfPlane.ofComplex (I * ((t⁻¹ : ℝ) : ℂ)) : ℍ) : ℂ) ^ 10 * -((t : ℂ) ^ 10) = 1
      from by simpa [neg_mul] using hp10, mul_one]

end E8Leech
