import Riesz.ExactMassSlices
import Riesz.PatchSupportD
import Riesz.SphereMeasureD

/-! Equal-mass residual cells on S²⁴.

The level sets of the first coordinate are null for the sphere probability: the cone over
`{x₀ = c}` lies in `{v₀ = c ‖v‖}`, whose sections over a nonzero transverse vector have at most
one point.  Slicing a measurable region of probability `n/N` by the first coordinate therefore
gives `n` measurable pairwise disjoint cells of probability exactly `1/N` whose union is the
region.  No diameter bound is asserted; the Gaussian budgets of the residual points do not need
one. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped Pointwise ENNReal
namespace SphericalRiesz

theorem ambientConsD_norm (n : ℕ) (p : ℝ × (Fin (n+1) → ℝ)) :
    ‖ambientConsD n p‖ =
      Real.sqrt (p.1^2+‖(WithLp.toLp 2 p.2 : EuclideanSpace ℝ (Fin (n+1)))‖^2) := by
  rw [← ambientConsD_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem ambientD24_cone_level_null (c : ℝ) :
    (volume : Measure (AmbientD 24)) {v | v 0 = c*‖v‖} = 0 := by
  have hmeas : MeasurableSet {v : AmbientD 24 | v 0 = c*‖v‖} :=
    measurableSet_eq_fun (by fun_prop) (by fun_prop)
  have hmp : MeasurePreserving (ambientConsD 23) (volume : Measure (ℝ × (Fin 24 → ℝ)))
      (volume : Measure (AmbientD 24)) := ambientConsD_measurePreserving
  rw [← hmp.map_eq, Measure.map_apply (ambientConsD 23).measurable hmeas]
  have hE : MeasurableSet ((ambientConsD 23) ⁻¹' {v : AmbientD 24 | v 0 = c*‖v‖}) :=
    (ambientConsD 23).measurable hmeas
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hE]
  have ht : ∀ᵐ w ∂(volume : Measure (Fin 24 → ℝ)), w ≠ 0 := by simp [ae_iff]
  have hzero : (fun w : Fin 24 → ℝ => (volume : Measure ℝ)
      ((fun a => (a, w)) ⁻¹' ((ambientConsD 23) ⁻¹' {v : AmbientD 24 | v 0 = c*‖v‖}))) =ᵐ[volume]
      0 := by
    filter_upwards [ht] with w hw
    simp only [Pi.zero_apply]
    apply Set.Subsingleton.measure_zero
    set s := ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin 24))‖^2 with hsdef
    have hs : 0 < s := by
      rw [hsdef]
      have : (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin 24)) ≠ 0 := by
        intro h
        apply hw
        have := congrArg WithLp.ofLp h
        simpa using this
      positivity
    have hsec : ∀ a, a ∈ (fun a => (a, w)) ⁻¹'
        ((ambientConsD 23) ⁻¹' {v : AmbientD 24 | v 0 = c*‖v‖}) ↔
        a = c*Real.sqrt (a^2+s) := by
      intro a
      simp only [mem_preimage, mem_ofPred_eq]
      rw [ambientConsD_norm 23 (a, w)]
      have h0 : (ambientConsD 23 (a, w)) 0 = a := by simp [ambientConsD_apply]
      rw [h0]
    intro a ha b hb
    rw [hsec] at ha hb
    have hA := Real.sqrt_pos.mpr (show 0 < a^2+s by positivity)
    have hB := Real.sqrt_pos.mpr (show 0 < b^2+s by positivity)
    have hA2 := Real.sq_sqrt (show 0 ≤ a^2+s by positivity)
    have hB2 := Real.sq_sqrt (show 0 ≤ b^2+s by positivity)
    by_cases hc : c = 0
    · rw [hc, zero_mul] at ha hb
      rw [ha, hb]
    have ha2 : a^2 = c^2*(a^2+s) := by
      rw [← hA2]
      nth_rewrite 1 [ha]
      ring
    have hb2 : b^2 = c^2*(b^2+s) := by
      rw [← hB2]
      nth_rewrite 1 [hb]
      ring
    have hc2 : c^2 ≠ 1 := by
      intro h1
      rw [h1] at ha2
      linarith
    have hsq : a^2 = b^2 := by
      have h1 : (a^2-b^2)*(1-c^2) = 0 := by linear_combination ha2-hb2
      rcases mul_eq_zero.mp h1 with h | h
      · linarith
      · exact absurd (by linarith : c^2 = 1) hc2
    have hab : 0 < a*b := by
      rw [ha, hb]
      have : 0 < c^2 := by positivity
      nlinarith [mul_pos hA hB]
    have hfac : (a-b)*(a+b) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · have : b = -a := by linarith
      rw [this] at hab
      nlinarith [sq_nonneg a]
  rw [lintegral_congr_ae hzero]
  simp

/-- The level sets of the first coordinate are null for the sphere probability on S²⁴. -/
theorem sphereProbability24_coord_level_null (c : ℝ) :
    (sphereProbabilityD 24) {x : SphereD 24 | (x : AmbientD 24) 0 = c} = 0 := by
  have hmeas : MeasurableSet {x : SphereD 24 | (x : AmbientD 24) 0 = c} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have hcone : Ioo (0:ℝ) 1 • (Subtype.val '' {x : SphereD 24 | (x : AmbientD 24) 0 = c}) ⊆
      {v : AmbientD 24 | v 0 = c*‖v‖} := by
    rintro z ⟨r, hr, w, ⟨y, hy, rfl⟩, rfl⟩
    simp only [mem_ofPred_eq] at hy ⊢
    have hy1 : ‖(y : AmbientD 24)‖ = 1 := by simp
    have hsm : (r • (y : AmbientD 24)) 0 = r*(y : AmbientD 24) 0 := by simp
    rw [hsm, norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, hy1, hy]
    ring
  simp only [sphereProbabilityD, Measure.smul_apply, smul_eq_mul]
  unfold sphereAreaD
  rw [Measure.toSphere_apply' _ hmeas, measure_mono_null hcone (ambientD24_cone_level_null c),
    mul_zero, mul_zero]

theorem sphere24_abs_first_coord_le_one (x : SphereD 24) : |(x : AmbientD 24) 0| ≤ 1 := by
  have hx : ‖(x : AmbientD 24)‖ = 1 := by simp
  calc |(x : AmbientD 24) 0| = ‖(x : AmbientD 24) 0‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖(x : AmbientD 24)‖ := PiLp.norm_apply_le _ 0
    _ = 1 := hx

/-- A measurable region of probability `n/N` splits into `n` measurable pairwise disjoint cells
of probability exactly `1/N`. -/
theorem exists_sphere24_equal_mass_cells {N n : ℕ} (hN : 0 < N) (hn : 0 < n)
    {S : Set (SphereD 24)} (hS : MeasurableSet S)
    (hmass : (sphereProbabilityD 24).real S = (n:ℝ)/(N:ℝ)) :
    ∃ C : Fin n → Set (SphereD 24), (∀ j, MeasurableSet (C j)) ∧
      Pairwise (fun i j => Disjoint (C i) (C j)) ∧ (⋃ j, C j) = S ∧
      ∀ j, (sphereProbabilityD 24) (C j) = (N:ℝ≥0∞)⁻¹ := by
  have hf : Measurable (fun x : SphereD 24 => (x : AmbientD 24) 0) := by fun_prop
  have hnull : ∀ c, (sphereProbabilityD 24)
      ((fun x : SphereD 24 => (x : AmbientD 24) 0) ⁻¹' {c} ∩ S) = 0 := fun c =>
    measure_mono_null inter_subset_left (sphereProbability24_coord_level_null c)
  obtain ⟨C, hCm, hCd, hCu, hCmass⟩ := exists_exact_mass_slices (sphereProbabilityD 24) hS hf
    sphere24_abs_first_coord_le_one hnull hn
  refine ⟨C, hCm, hCd, hCu, fun j => ?_⟩
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hreal : (sphereProbabilityD 24).real (C j) = (N:ℝ)⁻¹ := by
    rw [hCmass j, hmass]
    field_simp
  have hof : (sphereProbabilityD 24) (C j) =
      ENNReal.ofReal ((sphereProbabilityD 24).real (C j)) :=
    (ENNReal.ofReal_toReal (measure_ne_top (sphereProbabilityD 24) (C j))).symm
  rw [hof, hreal, ENNReal.ofReal_inv_of_pos hNR, ENNReal.ofReal_natCast]

end SphericalRiesz
