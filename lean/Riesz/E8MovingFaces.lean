import Riesz.E8PotentialRegularity
import Riesz.MovingInterval

/-!
# The actual E8 coordinate integral and its sixth derivative

Each original coordinate direction is retained, including the oblique
E8 basis. Translating both endpoints gives the same one-variable kernel
profile. FTC then identifies the sixth derivative of the actual normal
interval integral with two fifth derivatives on the actual faces.
Passing the derivative through the remaining seven-dimensional integral
and proving a bound uniform in the cutoff radius are still separate.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace SphericalRiesz

theorem e8InsertNth_sub (i : Fin 8) (s t : ℝ) (z v : Fin 7 → ℝ) :
    i.insertNth (α := fun _ : Fin 8 => ℝ) s z-i.insertNth t v =
      i.insertNth (α := fun _ : Fin 8 => ℝ) (s-t) (z-v) := by
  funext j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · simp
  · simp

def e8CoordinateFarProfile (r : ℝ) (i : Fin 8) (a : Fin 7 → ℝ) (s : ℝ) : ℝ :=
  e8FarProfile r (i.insertNth s a)

theorem e8CoordinateFarProfile_contDiff (r : ℝ) (hr : 0 < r) (i : Fin 8)
    (a : Fin 7 → ℝ) : ContDiff ℝ ∞ (e8CoordinateFarProfile r i a) := by
  have heq : (fun s : ℝ => i.insertNth (α := fun _ : Fin 8 => ℝ) s a) =
      (fun s : ℝ => Function.update (i.insertNth (α := fun _ : Fin 8 => ℝ) 0 a) i s) := by
    funext s
    exact (Fin.update_insertNth (α := fun _ : Fin 8 => ℝ) i 0 s a).symm
  have hu : ContDiff ℝ ∞ (fun s : ℝ => i.insertNth (α := fun _ : Fin 8 => ℝ) s a) := by
    rw [heq]
    exact contDiff_update ∞ (i.insertNth (α := fun _ : Fin 8 => ℝ) 0 a) i
  exact (e8FarProfile_contDiff r hr).comp hu

theorem e8Far_coordinate_translation (r : ℝ) (i : Fin 8) (s t : ℝ)
    (z v : Fin 7 → ℝ) :
    farObliqueRieszFour 8 e8Map r (i.insertNth t v) (i.insertNth s z) =
      e8CoordinateFarProfile r i (z-v) (s-t) := by
  rw [e8Far_translation, e8InsertNth_sub]
  rfl

def e8FarCoordinateUnitIntegral (r : ℝ) (i : Fin 8) (v z : Fin 7 → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..1, farObliqueRieszFour 8 e8Map r (i.insertNth t v) (i.insertNth s z)

theorem e8Far_coordinate_integral_sixth (r : ℝ) (hr : 0 < r) (i : Fin 8)
    (v z : Fin 7 → ℝ) (t : ℝ) :
    iteratedDeriv 6 (e8FarCoordinateUnitIntegral r i v z) t =
      iteratedDeriv 5 (e8CoordinateFarProfile r i (z-v)) (1-t)-
        iteratedDeriv 5 (e8CoordinateFarProfile r i (z-v)) (-t) := by
  have heq : e8FarCoordinateUnitIntegral r i v z =
      movingUnitIntegral (e8CoordinateFarProfile r i (z-v)) := by
    funext t
    unfold e8FarCoordinateUnitIntegral movingUnitIntegral
    simp_rw [e8Far_coordinate_translation]
  rw [heq]
  exact movingUnitIntegral_sixth ((e8CoordinateFarProfile_contDiff r hr i (z-v)).of_le (by simp)) t

#print axioms e8InsertNth_sub
#print axioms e8CoordinateFarProfile_contDiff
#print axioms e8Far_coordinate_translation
#print axioms e8Far_coordinate_integral_sixth

end SphericalRiesz
