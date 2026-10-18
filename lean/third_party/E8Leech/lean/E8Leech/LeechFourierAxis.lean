import E8Leech.LeechFourierProfile

/-!
# The Fourier transform of the Leech profile functions on the axis

For `τ = iβ` (`β ≠ 1`), `K = (K₊ + s K₋)/2 (iβ, i·)` and the growing part
`f(t) = e^{2πt}(A t + B)` of its cusp profile, the Schwartz function `φ(x) = P_s(π|x|²)` has, for
every cut `p > 0`, the Fourier transform

`𝓕φ(w) = ∫₀^∞ K°(t) (2γ(t) − γ(t − i) − γ(t + i)) dt
          + ∫₀¹ (W₋(u) γ(p − iu) + W₊(u) γ(p + iu)) du`,

where `γ(a) = a⁻¹² e^{−π|w|²/a}` is the Fourier transform of the Gaussian `e^{−πa|x|²}`, `K° = K` on
`(0, p]` and `K − f` on `(p, ∞)`, and `W∓(u) = (A(1 − u) ∓ i(B + pA)) e^{2π(p ∓ iu)}`
(`fourier_leechAxisRadialProfile`). This holds for all `w`; no Fourier identity is used.
-/

noncomputable section

namespace E8Leech

open Complex Filter Topology Asymptotics MeasureTheory Set
open UpperHalfPlane hiding I
open scoped Real FourierTransform RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The growing part `e^{2πt}(A t + B)` of the cusp profile of `(K₊ + s K₋)/2 (iβ, ·)`. -/
def leechAxisGrowth (s : ℂ) (β t : ℝ) : ℂ :=
  leechAxisCusp s β 0 * ((t : ℂ) * (Real.exp (2 * π * t) : ℂ)) +
    leechAxisCusp s β 1 * (Real.exp (2 * π * t) : ℂ)

theorem continuous_leechAxisGrowth (s : ℂ) (β : ℝ) : Continuous (leechAxisGrowth s β) := by
  unfold leechAxisGrowth
  fun_prop

/-- The kernel on the axis with its growing part removed beyond the cut `p`. -/
def leechAxisTruncKernel (s : ℂ) (β p t : ℝ) : ℂ :=
  truncAt (leechAxisKernel s β) (leechAxisGrowth s β) p t

/-- Off the growing part the kernel is `O(t)` at `∞`. -/
theorem isBigO_leechAxis_sub_growth {s : ℂ} {β : ℝ} {g : ℝ → ℂ}
    (hsub : (fun t => g t - leechAxisProfile s β t) =O[atTop]
      fun t => t * Real.exp ((-π + π / 4) * t)) :
    (fun t => g t - leechAxisGrowth s β t) =O[atTop] fun t => t * Real.exp (0 * t) := by
  have h1 : (fun t : ℝ => t * Real.exp ((-π + π / 4) * t)) =O[atTop]
      fun t => t * Real.exp (0 * t) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [one_mul, Real.norm_of_nonneg (mul_nonneg ht (Real.exp_pos _).le),
      Real.norm_of_nonneg (mul_nonneg ht (Real.exp_pos _).le)]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) ht
    nlinarith [Real.pi_pos]
  have h2 : (fun t : ℝ => leechAxisCusp s β 2 * (t : ℂ) + leechAxisCusp s β 3) =O[atTop]
      fun t => t * Real.exp (0 * t) := by
    refine IsBigO.of_bound (‖leechAxisCusp s β 2‖ + ‖leechAxisCusp s β 3‖) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [zero_mul, Real.exp_zero, mul_one, Real.norm_of_nonneg (by linarith)]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    nlinarith [norm_nonneg (leechAxisCusp s β 2), norm_nonneg (leechAxisCusp s β 3)]
  refine ((hsub.trans h1).add h2).congr_left fun t => ?_
  simp only [leechAxisProfile, cuspProfile, leechAxisGrowth]
  ring

/-- **The Fourier transform of the Leech profile function on the axis**, for every cut `p > 0`
and every `w`. -/
theorem fourier_leechAxisRadialProfile [Nontrivial V] (hd : Module.finrank ℝ V = 24) (s : ℂ)
    {β : ℝ} (hβ : 0 < β) (hβ1 : β ≠ 1) (φ : SchwartzMap V ℂ)
    (hφ : ∀ x : V, φ x = leechAxisRadialProfile s β (π * ‖x‖ ^ 2)) {p : ℝ} (hp : 0 < p) (w : V) :
    IntegrableOn (fun t : ℝ => leechAxisTruncKernel s β p t *
        (2 * gaussHat 24 t ‖w‖ - gaussHat 24 (t - I) ‖w‖ - gaussHat 24 (t + I) ‖w‖)) (Ioi 0) ∧
      𝓕 (⇑φ) w =
        (∫ t in Ioi 0, leechAxisTruncKernel s β p t *
          (2 * gaussHat 24 t ‖w‖ - gaussHat 24 (t - I) ‖w‖ - gaussHat 24 (t + I) ‖w‖)) +
        ∫ u in (0 : ℝ)..1,
          (explicitWeightMinus (leechAxisCusp s β 0) (leechAxisCusp s β 1) p u *
              gaussHat 24 ((p : ℂ) - (u : ℂ) * I) ‖w‖ +
            explicitWeightPlus (leechAxisCusp s β 0) (leechAxisCusp s β 1) p u *
              gaussHat 24 ((p : ℂ) + (u : ℂ) * I) ‖w‖) := by
  obtain ⟨g, hg, hgK, hg0, hg01, hginf, hsub⟩ := exists_leechAxis s hβ hβ1
  have hfc := continuous_leechAxisGrowth s β
  -- the difference `g − f`
  have hsubc : ContinuousOn (fun t => g t - leechAxisGrowth s β t) (Ioi 0) :=
    hg.sub hfc.continuousOn
  have hsub01 : (fun t => g t - leechAxisGrowth s β t) =O[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) :=
    hg01.sub ((hfc.tendsto 0).mono_left nhdsWithin_le_nhds |>.isBigO_one ℝ)
  have hsubinf := isBigO_leechAxis_sub_growth hsub
  -- the truncated continuous representative
  have hIoc : ∀ t ∈ Ioc (0 : ℝ) p, truncAt g (leechAxisGrowth s β) p t = g t :=
    fun t ht => truncAt_of_le g _ ht.2
  have hIoi : ∀ t ∈ Ioi p, truncAt g (leechAxisGrowth s β) p t = g t - leechAxisGrowth s β t :=
    fun t ht => truncAt_of_lt g _ ht
  have hmeas : AEStronglyMeasurable (truncAt g (leechAxisGrowth s β) p)
      (volume.restrict (Ioi 0)) :=
    (hg.aestronglyMeasurable measurableSet_Ioi).sub
      (hfc.aestronglyMeasurable.indicator measurableSet_Ioi)
  have hint : IntegrableOn (fun t : ℝ => ‖truncAt g (leechAxisGrowth s β) p t‖ *
      (π / (π * t)) ^ ((Module.finrank ℝ V : ℝ) / 2)) (Ioi 0) := by
    have hw : ∀ t : ℝ, (π / (π * t)) ^ ((Module.finrank ℝ V : ℝ) / 2) = (t ^ 12)⁻¹ := fun t => by
      rw [hd, show ((24 : ℕ) : ℝ) / 2 = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        div_mul_cancel_left₀ Real.pi_ne_zero, inv_pow]
    rw [← Ioc_union_Ioi_eq_Ioi hp.le]
    refine IntegrableOn.union ?_ ?_
    · refine (integrableOn_Ioc_norm_mul_inv_pow hg hg0 (n := 12) (by norm_num) hp).congr_fun
        (fun t ht => ?_) measurableSet_Ioc
      simp only [hw, hIoc t ht]
    · refine (integrableOn_Ioi_norm_mul_inv_pow hsubc hsubinf (n := 12) (by norm_num) hp).congr_fun
        (fun t ht => ?_) measurableSet_Ioi
      simp only [hw, hIoi t ht]
  -- the profile off the explicit term
  have hprofA : ∀ v : V, v ≠ 0 →
      φ v - explicitProfileTerm (leechAxisCusp s β 0) (leechAxisCusp s β 1) p (π * ‖v‖ ^ 2) =
        ((4 * Real.sin (π * ‖v‖ ^ 2 / 2) ^ 2 : ℝ) : ℂ) *
          ∫ t in Ioi 0, truncAt g (leechAxisGrowth s β) p t *
            (Real.exp (-(π * ‖v‖ ^ 2) * t) : ℂ) := by
    intro v hv
    have hb : 0 < π * ‖v‖ ^ 2 := mul_pos Real.pi_pos (pow_pos (norm_pos_iff.mpr hv) 2)
    have i1 : IntegrableOn (fun t => truncAt g (leechAxisGrowth s β) p t *
        (Real.exp (-(π * ‖v‖ ^ 2) * t) : ℂ)) (Ioc 0 p) :=
      (integrableOn_Ioc_mul_exp hg hg01 hb hp).congr_fun
        (fun t ht => by simp only [hIoc t ht]) measurableSet_Ioc
    have i2 : IntegrableOn (fun t => truncAt g (leechAxisGrowth s β) p t *
        (Real.exp (-(π * ‖v‖ ^ 2) * t) : ℂ)) (Ioi p) :=
      ((integrableOn_Ioi_mul_exp_of_isBigO hb hsubc hsub01 hsubinf).mono_set
        (Ioi_subset_Ioi hp.le)).congr_fun (fun t ht => by simp only [hIoi t ht]) measurableSet_Ioi
    have hsplit : ∫ t in Ioi 0, truncAt g (leechAxisGrowth s β) p t *
          (Real.exp (-(π * ‖v‖ ^ 2) * t) : ℂ) =
        (∫ t in Ioc 0 p, g t * (Real.exp (-(π * ‖v‖ ^ 2) * t) : ℂ)) +
          ∫ t in Ioi p, (g t - leechAxisGrowth s β t) * (Real.exp (-(π * ‖v‖ ^ 2) * t) : ℂ) := by
      rw [← Ioc_union_Ioi_eq_Ioi hp.le,
        setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi i1 i2]
      congr 1
      · exact setIntegral_congr_fun measurableSet_Ioc fun t ht => by simp only [hIoc t ht]
      · exact setIntegral_congr_fun measurableSet_Ioi fun t ht => by simp only [hIoi t ht]
    rw [hφ v, ← radialProfile_eq_leechAxisRadialProfile s hgK,
      leechAxis_radialProfile_truncated s hg hg01 hsub hb hp.le, hsplit]
    simp only [explicitProfileTerm, leechAxisGrowth]
    ring
  -- the two Fourier transforms
  have hEint := integrable_explicitProfileTerm (V := V) (leechAxisCusp s β 0)
    (leechAxisCusp s β 1) hp
  have hAint : Integrable (fun v : V => φ v -
      explicitProfileTerm (leechAxisCusp s β 0) (leechAxisCusp s β 1) p (π * ‖v‖ ^ 2)) :=
    φ.integrable.sub hEint
  obtain ⟨hI, hFA⟩ := fourier_sin_sq_laplace_meas_full hmeas hint hprofA w
  have hsum : 𝓕 (⇑φ) w = 𝓕 (fun v : V => φ v -
        explicitProfileTerm (leechAxisCusp s β 0) (leechAxisCusp s β 1) p (π * ‖v‖ ^ 2)) w +
      𝓕 (fun v : V =>
        explicitProfileTerm (leechAxisCusp s β 0) (leechAxisCusp s β 1) p (π * ‖v‖ ^ 2)) w := by
    rw [← fourier_add_of_integrable hAint hEint w]
    exact congrArg (fun f : V → ℂ => 𝓕 f w) (funext fun v => (sub_add_cancel _ _).symm)
  -- back to the kernel
  have hae : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), x ≠ β ∧ x ≠ β⁻¹ := by
    have hfin : volume ({β, β⁻¹} : Set ℝ) = 0 := (Set.toFinite {β, β⁻¹}).measure_zero _
    have h : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({β, β⁻¹} : Set ℝ) :=
      measure_eq_zero_iff_ae_notMem.mp hfin
    filter_upwards [ae_restrict_of_ae h] with x hx
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hx
  have hker : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      truncAt g (leechAxisGrowth s β) p t *
        (2 * gaussHat (Module.finrank ℝ V) t ‖w‖ - gaussHat (Module.finrank ℝ V) (t - I) ‖w‖ -
          gaussHat (Module.finrank ℝ V) (t + I) ‖w‖) =
      leechAxisTruncKernel s β p t *
        (2 * gaussHat 24 t ‖w‖ - gaussHat 24 (t - I) ‖w‖ - gaussHat 24 (t + I) ‖w‖) := by
    filter_upwards [hae] with t ht
    rw [hd, leechAxisTruncKernel, truncAt, truncAt, hgK t ht.1 ht.2]
  refine ⟨hI.congr hker, ?_⟩
  rw [hsum, hFA, fourier_explicitProfileTerm _ _ hp w, integral_congr_ae hker, hd]

end E8Leech
