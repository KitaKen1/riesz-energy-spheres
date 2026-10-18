import Riesz.SphereCapDiscrepancy8

/-! The absolute first moment of the actual S⁸ probability and the Stolarsky constant (stage DISC).

`∫_{ℝ⁹} |x₀| e^(-|x|²) dx` equals `(∫ |t| e^(-t²) dt) (∫ e^(-t²) dt)^8 = π⁴` by the product
structure of Lebesgue measure, and equals `(∫_{S⁸} |u₀| dA(u)) ∫₀^∞ r^9 e^(-r²) dr = 12 ∫ |u₀| dA`
by the polar decomposition of Lebesgue measure (`measurePreserving_homeomorphUnitSphereProd`).
With the actual area `A₈ = 32π⁴/105` this gives `m = ∫ |⟪e, z⟫| dσ(z) = 35/128`, so the
Stolarsky constant is `m/2 = 35/256`. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
namespace SphericalRiesz

theorem real_abs_mul_gaussian_integral : (∫ t : ℝ, |t| * Real.exp (-t^2)) = 1 := by
  have h := integral_comp_abs (f := fun u : ℝ => u * Real.exp (-u^2))
  simp only [sq_abs] at h
  rw [h]
  have h2 := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 1) (b := 1) (by norm_num)
    (by norm_num) (by norm_num)
  have he : (∫ x in Ioi (0:ℝ), x * Real.exp (-x^2)) =
      ∫ x in Ioi (0:ℝ), x^(1:ℝ) * Real.exp (-1 * x^(2:ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    dsimp only
    rw [Real.rpow_one, show (x:ℝ)^(2:ℝ) = x^2 by norm_cast, neg_mul, one_mul]
  rw [he, h2, Real.one_rpow, show ((1:ℝ)+1)/2 = 1 by norm_num, Real.Gamma_one]
  norm_num

theorem real_gaussian_integral_one : (∫ t : ℝ, Real.exp (-t^2)) = Real.sqrt Real.pi := by
  have h := integral_gaussian 1
  simp only [neg_mul, one_mul, div_one] at h
  exact h

theorem ambient9_abs_coord_gaussian_integral :
    (∫ x : Ambient9, |x 0| * Real.exp (-‖x‖^2)) = Real.pi^4 := by
  have hmp := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 9)
  set f : Fin 9 → ℝ → ℝ := fun i t => (if i = 0 then |t| else 1) * Real.exp (-t^2) with hf
  have hg : ∀ x : Ambient9, |x 0| * Real.exp (-‖x‖^2) =
      ∏ i, f i ((MeasurableEquiv.toLp 2 (Fin 9 → ℝ)).symm x i) := by
    intro x
    have hn : ‖x‖^2 = ∑ i : Fin 9, (x i)^2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [Real.norm_eq_abs, sq_abs]
    rw [MeasurableEquiv.coe_toLp_symm, hn, ← Finset.sum_neg_distrib, Real.exp_sum]
    simp only [hf, Finset.prod_mul_distrib, Fintype.prod_ite_eq']
  simp_rw [hg]
  rw [hmp.integral_comp' (fun y : Fin 9 → ℝ => ∏ i, f i (y i)),
    integral_fintype_prod_volume_eq_prod, Fin.prod_univ_succ]
  have h0 : (∫ t : ℝ, f 0 t) = 1 := by
    simp only [hf, if_true]
    exact real_abs_mul_gaussian_integral
  have hs : ∀ i : Fin 8, (∫ t : ℝ, f i.succ t) = Real.sqrt Real.pi := by
    intro i
    simp only [hf, Fin.succ_ne_zero, if_false, one_mul]
    exact real_gaussian_integral_one
  rw [h0, Finset.prod_congr rfl (fun i _ => hs i), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, one_mul]
  have hsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  calc Real.sqrt Real.pi ^ 8 = (Real.sqrt Real.pi ^ 2)^4 := by ring
    _ = Real.pi^4 := by rw [hsq]

theorem volumeIoiPow8_integral (g : ℝ → ℝ) :
    (∫ r : Ioi (0:ℝ), g r ∂(Measure.volumeIoiPow 8)) = ∫ r in Ioi (0:ℝ), r^8 * g r := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul
      ((measurable_subtype_coe.pow_const _).real_toNNReal),
    integral_subtype_comap measurableSet_Ioi (fun a => Real.toNNReal (a^8) • g a)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg (le_of_lt hx) _), smul_eq_mul]

theorem ambient9_abs_coord_gaussian_polar :
    (∫ x : Ambient9, |x 0| * Real.exp (-‖x‖^2)) =
      (∫ u : Sphere8, |(u:Ambient9) 0| ∂sphereArea8) * 12 := by
  set F : Ambient9 → ℝ := fun x => |x 0| * Real.exp (-‖x‖^2) with hF
  set G : Sphere8 × Ioi (0:ℝ) → ℝ :=
    fun p => |(p.1:Ambient9) 0| * ((p.2:ℝ) * Real.exp (-(p.2:ℝ)^2)) with hG
  have h1 : (∫ x : Ambient9, F x) =
      ∫ x : ({0}ᶜ : Set Ambient9), F x ∂((volume : Measure Ambient9).comap Subtype.val) := by
    rw [integral_subtype_comap (measurableSet_singleton _).compl F,
      restrict_compl_singleton]
  have hdim : Module.finrank ℝ Ambient9 - 1 = 8 := by simp [Ambient9]
  have hmp := (volume : Measure Ambient9).measurePreserving_homeomorphUnitSphereProd
  rw [hdim] at hmp
  have h2 := hmp.integral_comp (Homeomorph.measurableEmbedding _) G
  have hpt : ∀ x : ({0}ᶜ : Set Ambient9), G (homeomorphUnitSphereProd Ambient9 x) = F x := by
    intro x
    have hx : (x:Ambient9) ≠ 0 := x.2
    have hn : 0 < ‖(x:Ambient9)‖ := norm_pos_iff.mpr hx
    have hfst : (((homeomorphUnitSphereProd Ambient9 x).1 : Sphere8) : Ambient9) =
        ‖(x:Ambient9)‖⁻¹ • (x:Ambient9) := sphereDirection8_coe x
    simp only [hG, hF, hfst, homeomorphUnitSphereProd_apply_snd_coe]
    rw [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_norm]
    field_simp
  simp_rw [hpt] at h2
  rw [h1, h2]
  change (∫ p, |(p.1:Ambient9) 0| * ((p.2:ℝ) * Real.exp (-(p.2:ℝ)^2))
    ∂(sphereArea8.prod (Measure.volumeIoiPow 8))) = _
  rw [integral_prod_mul (fun u : Sphere8 => |(u:Ambient9) 0|)
    (fun r : Ioi (0:ℝ) => (r:ℝ) * Real.exp (-(r:ℝ)^2)),
    volumeIoiPow8_integral (fun r => r * Real.exp (-r^2))]
  congr 1
  have h5 := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 9) (b := 1) (by norm_num)
    (by norm_num) (by norm_num)
  have he : (∫ r in Ioi (0:ℝ), r^8 * (r * Real.exp (-r^2))) =
      ∫ x in Ioi (0:ℝ), x^(9:ℝ) * Real.exp (-1 * x^(2:ℝ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    dsimp only
    rw [show (x:ℝ)^(2:ℝ) = x^2 by norm_cast, show (x:ℝ)^(9:ℝ) = x^9 by norm_cast, neg_mul, one_mul]
    ring
  rw [he, h5, Real.one_rpow, show ((9:ℝ)+1)/2 = 5 by norm_num]
  have hΓ : Real.Gamma 5 = 24 := by
    rw [show (5:ℝ) = (4:ℕ)+1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  rw [hΓ]
  norm_num

/-- The absolute first moment of the actual sphere probability is `35/128`. -/
theorem sphereAbsMoment8_eq : sphereAbsMoment8 = 35/128 := by
  have hA : sphereArea8.real univ = 32*Real.pi^4/105 := sphereArea8_mass_real
  have hpole : ∀ z : Sphere8, |⟪(spherePole8:Ambient9), (z:Ambient9)⟫| = |(z:Ambient9) 0| := by
    intro z
    simp [spherePole8, EuclideanSpace.inner_single_left]
  have harea : (∫ u : Sphere8, |(u:Ambient9) 0| ∂sphereArea8) = Real.pi^4/12 := by
    have h := ambient9_abs_coord_gaussian_polar
    rw [ambient9_abs_coord_gaussian_integral] at h
    linarith
  unfold sphereAbsMoment8
  simp_rw [hpole]
  rw [sphereProbability8, integral_smul_measure, harea, ENNReal.toReal_inv]
  change (sphereArea8.real univ)⁻¹ • (Real.pi^4/12) = _
  rw [hA, smul_eq_mul]
  have hπ : 0 < Real.pi := Real.pi_pos
  field_simp
  ring

/-- Stolarsky's constant for S⁸: `m/2 = 35/256`. -/
theorem sphereStolarskyConst8_eq : sphereAbsMoment8/2 = 35/256 := by
  rw [sphereAbsMoment8_eq]
  norm_num

/-- The sharp one-sided cap discrepancy bound with the explicit Stolarsky constant `35/256`. -/
theorem sphere8_cap_discrepancy_lower_explicit (D : E8LaplaceSineData8) :
    ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ X : Configuration N,
      (35/256:ℝ)*(-((sphereArea8.real univ)^((1:ℝ)/8)*
          (e8EpsteinCandidate ((-1/2:ℝ):ℂ)).re))-η ≤
        (N:ℝ)^(1+(1:ℝ)/8)*capDiscrepancyL2Sq8 X := by
  rw [← sphereStolarskyConst8_eq]
  exact sphere8_cap_discrepancy_lower_conjecture_form D

#print axioms real_abs_mul_gaussian_integral
#print axioms real_gaussian_integral_one
#print axioms ambient9_abs_coord_gaussian_integral
#print axioms volumeIoiPow8_integral
#print axioms ambient9_abs_coord_gaussian_polar
#print axioms sphereAbsMoment8_eq
#print axioms sphereStolarskyConst8_eq
#print axioms sphere8_cap_discrepancy_lower_explicit

end SphericalRiesz
