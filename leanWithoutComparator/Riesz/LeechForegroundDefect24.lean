import Riesz.LeechForegroundBump24

/-! Neutralized Gaussian defect of a foreground family against the smooth residual background.

The foreground points together with `N σ` restricted to the complement `R` of the patches form
a finite measure of total charge `N`.  Its neutralized Gaussian energy against `N σ` is the
squared `L²` norm of the foreground bump error, so the twelfth-order family bound gives

`defect(α) ≤ N (C₀ + G (d/a)²⁴ (d m)^(-q) α^(-q/2))`  for every `α ∈ (0,4]`.

The first constant is independent of the family; the second term vanishes as `m → ∞`.  The
residual points, the common budget of an actual configuration and the attaining sequence are
not constructed here. -/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace SphericalRiesz
open Boundary

/-- `L²` norm of the softened sphere bump field. -/
theorem bumpField25_sphere_sq_integral {t : ℝ} (ht : 0 < t) :
    ∫ z, (bumpField25 t ambientSphereProbability24 z)^2 =
      (Real.pi/(4*t))^((25:ℝ)/2)*sphereGaussianBackground24 t := by
  have h := gaussianMeasurePair_eq_bump25 ht ambientSphereProbability24 ambientSphereProbability24
  rw [ambientSphereProbability24_kernel_pair] at h
  have hc : (Real.pi/(4*t))^((25:ℝ)/2)*(4*t/Real.pi)^((25:ℝ)/2) = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    have : Real.pi/(4*t)*(4*t/Real.pi) = 1 := by field_simp
    rw [this, Real.one_rpow]
  simp_rw [sq]
  rw [h, ← mul_assoc, hc, one_mul]

/-- Foreground points together with the smooth background `N σ` restricted to `R`. -/
def mixedForegroundMeasure24 {ι : Type*} [Fintype ι] (x : ι → SphereD 24) (N : ℕ)
    (R : Set (SphereD 24)) : Measure (AmbientD 24) :=
  finitePointMeasure (fun i => (x i : AmbientD 24)) +
    (N : ℝ≥0) • ((sphereProbabilityD 24).restrict R).map (fun y : SphereD 24 => (y : AmbientD 24))

instance mixedForegroundMeasure24_finite {ι : Type*} [Fintype ι] (x : ι → SphereD 24) (N : ℕ)
    (R : Set (SphereD 24)) : IsFiniteMeasure (mixedForegroundMeasure24 x N R) := by
  unfold mixedForegroundMeasure24
  infer_instance

theorem ambientBump25_integrable_finite {t : ℝ} (ht : 0 ≤ t) (z : AmbientD 24)
    (μ : Measure (AmbientD 24)) [IsFiniteMeasure μ] :
    Integrable (fun x => ambientBump25 t x z) μ := by
  apply (integrable_const (1 : ℝ)).mono' (by unfold ambientBump25; fun_prop)
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (ambientBump25_nonneg _ _ _)]
  exact ambientBump25_le_one ht _ _

theorem bumpField25_mixedForeground {ι : Type*} [Fintype ι] (x : ι → SphereD 24) (N : ℕ)
    (R : Set (SphereD 24)) {t : ℝ} (ht : 0 ≤ t) (z : AmbientD 24) :
    bumpField25 t (mixedForegroundMeasure24 x N R) z =
      (∑ i, ambientBump25 t (x i : AmbientD 24) z)+
        (N:ℝ)*∫ y in R, ambientBump25 t (y : AmbientD 24) z ∂(sphereProbabilityD 24) := by
  unfold bumpField25 mixedForegroundMeasure24
  rw [integral_add_measure (ambientBump25_integrable_finite ht z _)
    (ambientBump25_integrable_finite ht z _), finitePointMeasure_integral,
    integral_smul_nnreal_measure, integral_map (by fun_prop) (by unfold ambientBump25; fun_prop),
    NNReal.smul_def, NNReal.coe_natCast, smul_eq_mul]

/-- The bump error of the mixed measure is the foreground error against `N σ` on the patches. -/
theorem mixedForeground_bumpError_eq {ι : Type*} [Fintype ι] (x : ι → SphereD 24) (N : ℕ)
    (A : Set (SphereD 24)) (hA : MeasurableSet A) {t : ℝ} (ht : 0 ≤ t) (z : AmbientD 24) :
    bumpField25 t (mixedForegroundMeasure24 x N Aᶜ) z-
        (N:ℝ)*bumpField25 t ambientSphereProbability24 z =
      (∑ i, ambientBump25 t (x i : AmbientD 24) z)-
        (N:ℝ)*∫ y in A, ambientBump25 t (y : AmbientD 24) z ∂(sphereProbabilityD 24) := by
  rw [bumpField25_mixedForeground x N Aᶜ ht, bumpField25_sphere_eq,
    ← integral_add_compl hA (ambientBump25_sphere_integrable ht z)]
  ring

/-- All twelfth-order nodes of a patch family of one common scale. -/
def leechFamilyNodes24 {K : ℕ} (P : Fin K → SmallLeechCubePatch24) (n : ℕ) (hn : 74 ≤ n) :
    Fin K × (Fin 24 → TwelveNodeIndex n) → SphereD 24 :=
  fun q => smallLeechPatchNodes24 (P q.1) n hn q.2

/-- The union of the physical patches of a family. -/
def leechFamilyUnion24 {K : ℕ} (P : Fin K → SmallLeechCubePatch24) : Set (SphereD 24) :=
  ⋃ i, smallLeechSpherePatch24 (P i)

theorem leechFamilyUnion24_measurable {K : ℕ} (P : Fin K → SmallLeechCubePatch24) :
    MeasurableSet (leechFamilyUnion24 P) :=
  MeasurableSet.iUnion fun i => smallLeechSpherePatch24_measurable (P i)

theorem bumpErrorConst24_patch_nonneg :
    0 ≤ bumpErrorConst24 patchChartUpper24 patchChartLower24 := by
  unfold bumpErrorConst24 twelfthConst
  have := one_le_patchChartUpper24
  have := gaussRuleConst12_nonneg
  positivity

/-- Neutralized Gaussian defect of the foreground family with smooth residual background. -/
theorem leechPatchFamily_mixed_defect_le :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ {K : ℕ} (P : Fin K → SmallLeechCubePatch24),
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius24 ≤ ρ) →
      Pairwise (fun i j => Disjoint (smallLeechSpherePatch24 (P i))
        (smallLeechSpherePatch24 (P j))) →
      ∀ (a d m : ℕ), 0 < d → 0 < m →
      (∀ i, (P i).ε*(d:ℝ) = leechUnitDensityRadius24*(a:ℝ)) →
      ∀ (hn : 74 ≤ a*m), ∀ α ∈ Ioc (0:ℝ) 4,
      gaussianMeasureDefect (sphereGaussianScale24 ((d*m)^24) α) (((d*m)^24:ℕ):ℝ)
        (mixedForegroundMeasure24 (leechFamilyNodes24 P (a*m) hn) ((d*m)^24)
          (leechFamilyUnion24 P)ᶜ) ambientSphereProbability24 ≤
      (8:ℝ)^((25:ℝ)/2)*(bumpErrorConst24 patchChartUpper24 patchChartLower24*
        (1/((a*m:ℕ):ℝ)^12+(2*Real.pi*α)^6))^2*(((d*m)^24:ℕ):ℝ)^2*
        sphereGaussianBackground24 (sphereGaussianScale24 ((d*m)^24) α/8) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := leechPatchFamily_bump_error24
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro K P hv hε hdisj a d m hd hm hratio hn α hα
  have hts : 0 < sphereGaussianScale24 ((d*m)^24) α :=
    sphereGaussianScale24_pos (by positivity) hα.1
  set t := sphereGaussianScale24 ((d*m)^24) α with ht
  set C := bumpErrorConst24 patchChartUpper24 patchChartLower24*
    (1/((a*m:ℕ):ℝ)^12+(2*Real.pi*α)^6) with hC
  set NR : ℝ := (((d*m)^24:ℕ):ℝ) with hNR
  have ht8 : 0 < t/8 := by positivity
  let W : AmbientD 24 → ℝ := fun z => C*(NR*bumpField25 (t/8) ambientSphereProbability24 z)
  have hWsq : (fun z => W z^2) = fun z => (C*NR)^2*
      (bumpField25 (t/8) ambientSphereProbability24 z*
        bumpField25 (t/8) ambientSphereProbability24 z) := by
    funext z
    simp only [W]
    ring
  have hWi : Integrable (fun z => W z^2) := by
    rw [hWsq]
    exact (bumpField25_mul_integrable ht8 ambientSphereProbability24
      ambientSphereProbability24).const_mul _
  have hle : ∀ z, |bumpField25 t (mixedForegroundMeasure24 (leechFamilyNodes24 P (a*m) hn)
      ((d*m)^24) (leechFamilyUnion24 P)ᶜ) z-NR*bumpField25 t ambientSphereProbability24 z| ≤ W z := by
    intro z
    rw [hNR, mixedForeground_bumpError_eq _ _ _ (leechFamilyUnion24_measurable P) hts.le,
      Fintype.sum_prod_type]
    exact hb P hv hε hdisj a d m hd hm hratio hn α hα z
  have hmain := gaussianMeasureDefect_le_of_bump25 hts NR _ ambientSphereProbability24 hWi hle
  have hint : (∫ z, W z^2) = (C*NR)^2*((Real.pi/(4*(t/8)))^((25:ℝ)/2)*
      sphereGaussianBackground24 (t/8)) := by
    rw [hWsq, integral_const_mul, ← bumpField25_sphere_sq_integral ht8]
    simp_rw [sq]
  have hconst : (4*t/Real.pi)^((25:ℝ)/2)*(Real.pi/(4*(t/8)))^((25:ℝ)/2) = (8:ℝ)^((25:ℝ)/2) := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
  calc
    _ ≤ (4*t/Real.pi)^((25:ℝ)/2)*∫ z, W z^2 := hmain
    _ = ((4*t/Real.pi)^((25:ℝ)/2)*(Real.pi/(4*(t/8)))^((25:ℝ)/2))*(C*NR)^2*
        sphereGaussianBackground24 (t/8) := by rw [hint]; ring
    _ = _ := by rw [hconst]; ring

/-- Interpolation between two upper bounds. -/
theorem le_rpow_mul_rpow_of_le {x A B θ : ℝ} (hx : 0 ≤ x) (hA : x ≤ A) (hB : x ≤ B)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : x ≤ A^(1-θ)*B^θ := by
  rcases hx.eq_or_lt with h | h
  · rw [← h]
    exact mul_nonneg (Real.rpow_nonneg (h ▸ hA) _) (Real.rpow_nonneg (h ▸ hB) _)
  · calc
      x = x^(1-θ)*x^θ := by
        rw [← Real.rpow_add h]
        simp
      _ ≤ A^(1-θ)*B^θ :=
        mul_le_mul (Real.rpow_le_rpow hx hA (by linarith)) (Real.rpow_le_rpow hx hB hθ0)
          (Real.rpow_nonneg hx _) (Real.rpow_nonneg (hx.trans hA) _)

/-- Family-independent part of the foreground small-alpha profile. -/
def leechForegroundProfileConst24 : ℝ :=
  2*(8:ℝ)^((25:ℝ)/2)*(bumpErrorConst24 patchChartUpper24 patchChartLower24)^2*(16*Real.pi)^12

/-- Gain of the refinement-dependent part of the foreground small-alpha profile. -/
def leechForegroundProfileGain24 (q : ℝ) : ℝ :=
  2*(8:ℝ)^((25:ℝ)/2)*(bumpErrorConst24 patchChartUpper24 patchChartLower24)^2*(8:ℝ)^(q/2)

theorem leechForegroundProfileConst24_nonneg : 0 ≤ leechForegroundProfileConst24 := by
  unfold leechForegroundProfileConst24
  positivity

theorem leechForegroundProfileGain24_nonneg (q : ℝ) : 0 ≤ leechForegroundProfileGain24 q := by
  unfold leechForegroundProfileGain24
  positivity

/-- Small-alpha profile of the foreground defect: a family-independent constant plus a term
which vanishes under refinement. -/
theorem leechPatchFamily_mixed_defect_profile :
    ∃ ρ > 0, ρ ≤ 1/16 ∧ ∀ {K : ℕ} (P : Fin K → SmallLeechCubePatch24),
      (∀ i, ‖(P i).v‖ ≤ ρ) → (∀ i, (P i).ε*equalAreaScaleRadius24 ≤ ρ) →
      Pairwise (fun i j => Disjoint (smallLeechSpherePatch24 (P i))
        (smallLeechSpherePatch24 (P j))) →
      ∀ (a d m : ℕ), 0 < d → 0 < m →
      (∀ i, (P i).ε*(d:ℝ) = leechUnitDensityRadius24*(a:ℝ)) →
      ∀ (hn : 74 ≤ a*m) (q : ℝ), 0 < q → q ≤ 24 → ∀ α ∈ Ioc (0:ℝ) 4,
      gaussianMeasureDefect (sphereGaussianScale24 ((d*m)^24) α) (((d*m)^24:ℕ):ℝ)
        (mixedForegroundMeasure24 (leechFamilyNodes24 P (a*m) hn) ((d*m)^24)
          (leechFamilyUnion24 P)ᶜ) ambientSphereProbability24 ≤
      (((d*m)^24:ℕ):ℝ)*(leechForegroundProfileConst24+
        leechForegroundProfileGain24 q*((d:ℝ)/(a:ℝ))^24*((d*m:ℕ):ℝ)^(-q)*α^(-(q/2))) := by
  obtain ⟨ρ,hρ,hρ1,hb⟩ := leechPatchFamily_mixed_defect_le
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro K P hv hε hdisj a d m hd hm hratio hn q hq hq24 α hα
  have hmain := hb P hv hε hdisj a d m hd hm hratio hn α hα
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · simp [h] at hn
    · exact h
  have hα0 : 0 < α := hα.1
  have hNpos : 0 < (d*m)^24 := by positivity
  set K₀ := bumpErrorConst24 patchChartUpper24 patchChartLower24 with hK₀
  have hK₀0 : 0 ≤ K₀ := bumpErrorConst24_patch_nonneg
  set D : ℝ := ((d*m:ℕ):ℝ) with hD
  set n : ℝ := ((a*m:ℕ):ℝ) with hndef
  have hDpos : 0 < D := by rw [hD]; exact_mod_cast Nat.mul_pos hd hm
  have hnpos : 0 < n := by rw [hndef]; exact_mod_cast Nat.mul_pos ha hm
  have hNR : (((d*m)^24:ℕ):ℝ) = D^24 := by rw [hD]; push_cast; ring
  rw [hNR] at hmain ⊢
  -- the scaled background
  have hscale : sphereGaussianScale24 ((d*m)^24) α/8 = sphereGaussianScale24 ((d*m)^24) (α/8) := by
    unfold sphereGaussianScale24
    ring
  set B := sphereGaussianBackground24 (sphereGaussianScale24 ((d*m)^24) α/8) with hBdef
  have hB0 : 0 ≤ B := sphereGaussianBackground24_nonneg _
  have hB1 : B ≤ 1 := sphereGaussianBackground24_le_one
    (by rw [hscale]; exact (sphereGaussianScale24_pos hNpos (by positivity)).le)
  have hcap : D^24*B ≤ (8:ℝ)^12/α^12 := by
    have h := sphereGaussianBackground24_scaled_cap hNpos (α := α/8) (by positivity)
    rw [← hscale, ← hBdef, hNR] at h
    calc D^24*B ≤ ((α/8)^12)⁻¹ := h
      _ = _ := by rw [div_pow, inv_div]
  have hx0 : 0 ≤ D^24*B := by positivity
  have hxN : D^24*B ≤ D^24 := by nlinarith [pow_pos hDpos 24]
  have hθ0 : 0 ≤ q/24 := by positivity
  have hθ1 : q/24 ≤ 1 := by linarith
  have hinterp := le_rpow_mul_rpow_of_le hx0 hxN hcap hθ0 hθ1
  -- the two rpow simplifications
  have hpowN : (D^24)^(1-q/24) = D^24*D^(-q) := by
    calc (D^24)^(1-q/24) = (D^(24:ℝ))^(1-q/24) := by
          rw [show (24:ℝ) = ((24:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      _ = D^((24:ℝ)*(1-q/24)) := (Real.rpow_mul hDpos.le _ _).symm
      _ = D^((24:ℝ)+(-q)) := by congr 1; ring
      _ = D^(24:ℝ)*D^(-q) := Real.rpow_add hDpos _ _
      _ = D^24*D^(-q) := by rw [show (24:ℝ) = ((24:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have hpowU : ((8:ℝ)^12/α^12)^(q/24) = (8:ℝ)^(q/2)*α^(-(q/2)) := by
    have h8 : (0:ℝ) ≤ 8/α := by positivity
    calc ((8:ℝ)^12/α^12)^(q/24) = (((8:ℝ)/α)^(12:ℝ))^(q/24) := by
          rw [show (12:ℝ) = ((12:ℕ):ℝ) by norm_num, Real.rpow_natCast, div_pow]
      _ = ((8:ℝ)/α)^((12:ℝ)*(q/24)) := (Real.rpow_mul h8 _ _).symm
      _ = ((8:ℝ)/α)^(q/2) := by congr 1; ring
      _ = (8:ℝ)^(q/2)/α^(q/2) := Real.div_rpow (by norm_num) hα0.le _
      _ = _ := by rw [Real.rpow_neg hα0.le, div_eq_mul_inv]
  rw [hpowN, hpowU] at hinterp
  have hDq : 0 < D^(-q) := Real.rpow_pos_of_pos hDpos _
  have hαq : 0 < α^(-(q/2)) := Real.rpow_pos_of_pos hα0 _
  have h8q : 0 < (8:ℝ)^(q/2) := Real.rpow_pos_of_pos (by norm_num) _
  have hT : 0 < (8:ℝ)^((25:ℝ)/2) := Real.rpow_pos_of_pos (by norm_num) _
  have hsq : (K₀*(1/n^12+(2*Real.pi*α)^6))^2 ≤
      K₀^2*(2/n^24+2*(2*Real.pi)^12*α^12) := by
    have h : (1/n^12+(2*Real.pi*α)^6)^2 ≤ 2/n^24+2*(2*Real.pi)^12*α^12 := by
      have h1 : (1/n^12+(2*Real.pi*α)^6)^2 ≤ 2*(1/n^12)^2+2*((2*Real.pi*α)^6)^2 := by
        nlinarith [sq_nonneg (1/n^12-(2*Real.pi*α)^6)]
      calc _ ≤ 2*(1/n^12)^2+2*((2*Real.pi*α)^6)^2 := h1
        _ = _ := by field_simp
    calc _ = K₀^2*(1/n^12+(2*Real.pi*α)^6)^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h (sq_nonneg _)
  have hratio' : D^24/n^24 = ((d:ℝ)/(a:ℝ))^24 := by
    rw [hD, hndef]
    push_cast
    have haR : (a:ℝ) ≠ 0 := by exact_mod_cast ha.ne'
    have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  -- assemble
  have hfirst : α^12*(D^24*B) ≤ (8:ℝ)^12 := by
    have h := mul_le_mul_of_nonneg_left hcap (pow_pos hα0 12).le
    calc α^12*(D^24*B) ≤ α^12*((8:ℝ)^12/α^12) := h
      _ = _ := by field_simp
  calc
    _ ≤ (8:ℝ)^((25:ℝ)/2)*(K₀*(1/n^12+(2*Real.pi*α)^6))^2*(D^24)^2*B := hmain
    _ = (8:ℝ)^((25:ℝ)/2)*(K₀*(1/n^12+(2*Real.pi*α)^6))^2*D^24*(D^24*B) := by ring
    _ ≤ (8:ℝ)^((25:ℝ)/2)*(K₀^2*(2/n^24+2*(2*Real.pi)^12*α^12))*D^24*(D^24*B) := by
      gcongr
    _ = D^24*((8:ℝ)^((25:ℝ)/2)*K₀^2*(2*(2*Real.pi)^12*(α^12*(D^24*B))+
        2/n^24*(D^24*B))) := by ring
    _ ≤ D^24*((8:ℝ)^((25:ℝ)/2)*K₀^2*(2*(2*Real.pi)^12*(8:ℝ)^12+
        2/n^24*(D^24*D^(-q)*((8:ℝ)^(q/2)*α^(-(q/2)))))) := by
      gcongr
    _ = _ := by
      unfold leechForegroundProfileConst24 leechForegroundProfileGain24
      rw [← hK₀, ← hratio']
      field_simp
      ring

end SphericalRiesz
