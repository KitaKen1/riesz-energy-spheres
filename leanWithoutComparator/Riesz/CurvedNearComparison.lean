import Riesz.E8NearPotentialMean

/-!
# An actual curved near potential compared with the flat E8 potential

A relative chordal-distance error at most η<=1/2 implies a Riesz
kernel error at most 64η times the actual flat kernel. Multiplication
by the SAME coordinate cutoff and actual integration gives a near
potential error at most 64η C_near r^4. The map G can take values in
R^9, as a spherical chart will. Measurability and the relative-distance
estimate are explicit inputs; no actual sphere chart supplies them yet.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
namespace SphericalRiesz
open Boundary

theorem inverseFourth_relative_error (a b η : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hη : 0 ≤ η) (hη1 : η ≤ 1/2) (hab : |b-a| ≤ η*a) :
    |b⁻¹^4-a⁻¹^4| ≤ 64*η*a⁻¹^4 := by
  by_cases ha0 : a = 0
  · have hb0 : b = 0 := by
      have hz : |b| ≤ 0 := by simpa only [ha0,sub_zero,mul_zero] using hab
      exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg b))
    simp [ha0,hb0]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hlow : a/2 ≤ b := by nlinarith [(abs_le.mp hab).1]
  have hbp : 0 < b := by linarith
  have hi : |b⁻¹-a⁻¹| ≤ 2*η/a := by
    have heq : b⁻¹-a⁻¹ = (a-b)/(a*b) := by field_simp
    rw [heq,abs_div,abs_of_pos (mul_pos hap hbp),abs_sub_comm]
    calc
      _ ≤ (η*a)/(a*b) := div_le_div_of_nonneg_right hab (by positivity)
      _ ≤ (η*a)/(a*(a/2)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left hlow ha)
      _ = _ := by field_simp
  have hia : |a⁻¹| ≤ 2/a := by
    rw [abs_of_nonneg (inv_nonneg.mpr ha),div_eq_mul_inv]
    linarith [inv_nonneg.mpr ha]
  have hib : |b⁻¹| ≤ 2/a := by
    rw [abs_of_nonneg (inv_nonneg.mpr hb)]
    simpa only [one_div,inv_div] using one_div_le_one_div_of_le (by positivity : 0 < a/2) hlow
  calc
    _ ≤ |b⁻¹-a⁻¹| * 4*(max |b⁻¹| |a⁻¹|)^3 := by
      simpa only [Nat.cast_ofNat] using (abs_pow_sub_pow_le (a := b⁻¹) (b := a⁻¹) (n := 4))
    _ ≤ (2*η/a)*4*(2/a)^3 := by gcongr; exact max_le hib hia
    _ = _ := by field_simp; ring

def curvedRieszFour {d : ℕ} (G : (Fin 8 → ℝ) → EuclideanSpace ℝ (Fin d))
    (x y : Fin 8 → ℝ) : ℝ := (dist (G x) (G y))⁻¹^4

def curvedNearRieszFour {d : ℕ} (G : (Fin 8 → ℝ) → EuclideanSpace ℝ (Fin d))
    (r : ℝ) (x y : Fin 8 → ℝ) : ℝ :=
  curvedRieszFour G x y*outerUnitBump 8 (r⁻¹ • (y-x))

def curvedNearPotential {d : ℕ} (G : (Fin 8 → ℝ) → EuclideanSpace ℝ (Fin d))
    (r : ℝ) (x : Fin 8 → ℝ) : ℝ := ∫ y in UnitCube 8, curvedNearRieszFour G r x y

theorem curvedRieszFour_relative_error {d : ℕ}
    (G : (Fin 8 → ℝ) → EuclideanSpace ℝ (Fin d)) (x y : Fin 8 → ℝ)
    (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1/2)
    (hd : |dist (G x) (G y)-
      dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y))|
      ≤ η*dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y))) :
    |curvedRieszFour G x y-obliqueRieszFour 8 e8Map x y| ≤
      64*η*obliqueRieszFour 8 e8Map x y := by
  rw [obliqueRieszFour_eq_dist]
  exact inverseFourth_relative_error _ _ η dist_nonneg dist_nonneg hη hη1 hd

theorem curvedNearRieszFour_relative_error {d : ℕ}
    (G : (Fin 8 → ℝ) → EuclideanSpace ℝ (Fin d)) (r : ℝ) (x y : Fin 8 → ℝ)
    (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1/2)
    (hd : |dist (G x) (G y)-
      dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y))|
      ≤ η*dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y))) :
    |curvedNearRieszFour G r x y-nearObliqueRieszFour 8 e8Map r x y| ≤
      64*η*nearObliqueRieszFour 8 e8Map r x y := by
  unfold curvedNearRieszFour nearObliqueRieszFour
  rw [← sub_mul,abs_mul,abs_of_nonneg (outerUnitBump 8).nonneg]
  calc
    _ ≤ (64*η*obliqueRieszFour 8 e8Map x y)*outerUnitBump 8 (r⁻¹ • (y-x)) :=
      mul_le_mul_of_nonneg_right (curvedRieszFour_relative_error G x y η hη hη1 hd)
        (outerUnitBump 8).nonneg
    _ = _ := by ring

theorem curvedNearPotential_relative_error {d : ℕ}
    (G : (Fin 8 → ℝ) → EuclideanSpace ℝ (Fin d)) (hG : Measurable G)
    (r : ℝ) (hr : 0 < r) (x : Fin 8 → ℝ) (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1/2)
    (hd : ∀ y ∈ UnitCube 8, |dist (G x) (G y)-
      dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y))|
      ≤ η*dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y))) :
    |curvedNearPotential G r x-e8NearPotential r x| ≤
      64*η*e8NearIntegralConstant*r^4 := by
  have hi := (e8Near_integrable r hr x).integrableOn (s := UnitCube 8)
  have hdom := hi.const_mul (64*η)
  have hm : Measurable (fun y => curvedNearRieszFour G r x y-nearObliqueRieszFour 8 e8Map r x y) := by
    have hb := (outerUnitBump 8).continuous.measurable
    have hA := e8Map.continuous.measurable
    unfold curvedNearRieszFour curvedRieszFour nearObliqueRieszFour
      obliqueRieszFour flatRieszFour squaredDistance
    fun_prop
  have he : ∀ᵐ y ∂volume.restrict (UnitCube 8),
      ‖curvedNearRieszFour G r x y-nearObliqueRieszFour 8 e8Map r x y‖ ≤
        64*η*nearObliqueRieszFour 8 e8Map r x y := by
    filter_upwards [ae_restrict_mem (unitCube_measurableSet 8)] with y hy
    simpa only [Real.norm_eq_abs] using curvedNearRieszFour_relative_error G r x y η hη hη1 (hd y hy)
  have hid := hdom.mono' hm.aestronglyMeasurable.restrict he
  have hiG : IntegrableOn (curvedNearRieszFour G r x) (UnitCube 8) := by
    apply (hid.add hi).congr
    exact Eventually.of_forall (fun y => sub_add_cancel _ _)
  unfold curvedNearPotential e8NearPotential
  rw [← integral_sub hiG hi]
  calc
    _ ≤ ∫ y in UnitCube 8, 64*η*nearObliqueRieszFour 8 e8Map r x y := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_of_norm_le hdom he
    _ = 64*η*(∫ y in UnitCube 8, nearObliqueRieszFour 8 e8Map r x y) := integral_const_mul _ _
    _ ≤ 64*η*(e8NearIntegralConstant*r^4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (le_abs_self _).trans (e8Near_cubeIntegral_bound r hr x)
    _ = _ := by ring

theorem curvedNearPotential_measurable {d : ℕ}
    (G : (Fin 8 → ℝ) → EuclideanSpace ℝ (Fin d)) (hG : Measurable G) (r : ℝ) :
    Measurable (curvedNearPotential G r) := by
  have hm : Measurable (fun p : (Fin 8 → ℝ) × (Fin 8 → ℝ) =>
      curvedNearRieszFour G r p.1 p.2) := by
    have hb := (outerUnitBump 8).continuous.measurable
    unfold curvedNearRieszFour curvedRieszFour
    fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem curvedNearPotential_background_error {d : ℕ}
    (G : (Fin 8 → ℝ) → EuclideanSpace ℝ (Fin d)) (hG : Measurable G)
    (r : ℝ) (hr : 0 < r) (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1/2)
    (hd : ∀ x ∈ UnitCube 8, ∀ y ∈ UnitCube 8, |dist (G x) (G y)-
      dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y))|
      ≤ η*dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y)))
    (m : ℕ) (hm : 8 ≤ m) :
    |(cubeQuadrature 8 m (curvedNearPotential G r)-∫ x in UnitCube 8, curvedNearPotential G r x)-
      (cubeQuadrature 8 m (e8NearPotential r)-∫ x in UnitCube 8, e8NearPotential r x)| ≤
      128*η*e8NearIntegralConstant*r^4 := by
  let M : ℝ := 64*η*e8NearIntegralConstant*r^4
  have hb (x : Fin 8 → ℝ) (hx : x ∈ UnitCube 8) :
      |curvedNearPotential G r x-e8NearPotential r x| ≤ M :=
    curvedNearPotential_relative_error G hG r hr x η hη hη1 (hd x hx)
  have hdf := (curvedNearPotential_measurable G hG r).sub
    (e8NearPotential_continuous r hr).measurable
  have he : ∀ᵐ x ∂volume.restrict (UnitCube 8),
      ‖curvedNearPotential G r x-e8NearPotential r x‖ ≤ M := by
    filter_upwards [ae_restrict_mem (unitCube_measurableSet 8)] with x hx
    simpa only [Real.norm_eq_abs] using hb x hx
  have hconst : Integrable (fun _ : Fin 8 → ℝ => M) (volume.restrict (UnitCube 8)) :=
    continuousOn_const.integrableOn_compact (unitCube_isCompact 8)
  have hid := hconst.mono' hdf.aestronglyMeasurable.restrict he
  have hiA : IntegrableOn (e8NearPotential r) (UnitCube 8) :=
    (e8NearPotential_continuous r hr).continuousOn.integrableOn_compact (unitCube_isCompact 8)
  have hiG : IntegrableOn (curvedNearPotential G r) (UnitCube 8) := by
    apply (hid.add hiA).congr
    exact Eventually.of_forall (fun x => sub_add_cancel _ _)
  have hq : |cubeQuadrature 8 m (curvedNearPotential G r)-
      cubeQuadrature 8 m (e8NearPotential r)| ≤ M := by
    rw [← cubeQuadrature_sub]
    exact cubeQuadrature_abs_le 8 m hm _ M hb
  have hi : |(∫ x in UnitCube 8, curvedNearPotential G r x)-
      (∫ x in UnitCube 8, e8NearPotential r x)| ≤ M := by
    rw [← integral_sub hiG hiA]
    have h := norm_integral_le_of_norm_le hconst he
    simpa only [Real.norm_eq_abs,integral_const,Measure.real,Measure.restrict_apply_univ,
      unitCube_volume,ENNReal.toReal_one,smul_eq_mul,one_mul] using h
  calc
    _ = |(cubeQuadrature 8 m (curvedNearPotential G r)-cubeQuadrature 8 m (e8NearPotential r))-
        ((∫ x in UnitCube 8, curvedNearPotential G r x)-(∫ x in UnitCube 8, e8NearPotential r x))| := by
      congr 1
      ring
    _ ≤ _ := abs_sub _ _
    _ ≤ M+M := add_le_add hq hi
    _ = _ := by dsimp only [M]; ring

theorem curvedNearPotential_scaled_background_error {d : ℕ}
    (G : (Fin 8 → ℝ) → EuclideanSpace ℝ (Fin d)) (hG : Measurable G)
    (R : ℝ) (hR : 0 < R) (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1/2)
    (hd : ∀ x ∈ UnitCube 8, ∀ y ∈ UnitCube 8, |dist (G x) (G y)-
      dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y))|
      ≤ η*dist (WithLp.toLp 2 (e8Map x) : EuclideanSpace ℝ (Fin 8)) (WithLp.toLp 2 (e8Map y)))
    (m : ℕ) (hm : 8 ≤ m) :
    |(m:ℝ)^4*((cubeQuadrature 8 m (curvedNearPotential G (R/(m:ℝ)))-
        ∫ x in UnitCube 8, curvedNearPotential G (R/(m:ℝ)) x)-
      (cubeQuadrature 8 m (e8NearPotential (R/(m:ℝ)))-
        ∫ x in UnitCube 8, e8NearPotential (R/(m:ℝ)) x))| ≤
      128*η*e8NearIntegralConstant*R^4 := by
  have hmr : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  rw [abs_mul,abs_of_nonneg (pow_nonneg hmr.le 4)]
  calc
    _ ≤ (m:ℝ)^4*(128*η*e8NearIntegralConstant*(R/(m:ℝ))^4) :=
      mul_le_mul_of_nonneg_left (curvedNearPotential_background_error G hG _ (div_pos hR hmr)
        η hη hη1 hd m hm) (by positivity)
    _ = _ := by field_simp

#print axioms inverseFourth_relative_error
#print axioms curvedRieszFour_relative_error
#print axioms curvedNearRieszFour_relative_error
#print axioms curvedNearPotential_relative_error
#print axioms curvedNearPotential_measurable
#print axioms curvedNearPotential_background_error
#print axioms curvedNearPotential_scaled_background_error

end SphericalRiesz
