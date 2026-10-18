import Riesz.SphereArea8
import Riesz.SphereRieszMellinRpow8
import Riesz.SphereLogEnergy8

/-! The unit sphere `S^d ⊂ ℝ^(d+1)` in every dimension (stage P24, dimension-generic layer).

The area measure is the `toSphere` measure of ambient Lebesgue volume, the probability measure
its normalization; isometries of the ambient space act on the sphere preserving both. Ordered
off-diagonal Riesz and logarithmic energies of `N`-point configurations are defined as for `S⁸`.
The total area is `(d+1)` times the volume of the unit ball; for `d = 24` it is
`2^13 π^12 / 23‼`. For `d = 8` every definition agrees with the `S⁸` one. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open scoped Pointwise
namespace SphericalRiesz

/-- The ambient space `ℝ^(d+1)`. -/
abbrev AmbientD (d : ℕ) := EuclideanSpace ℝ (Fin (d+1))

/-- The unit sphere `S^d ⊂ ℝ^(d+1)`. -/
abbrev SphereD (d : ℕ) := Metric.sphere (0 : AmbientD d) 1

/-- Configurations of `N` distinct points on `S^d`. -/
abbrev ConfigurationD (d N : ℕ) := Fin N ↪ SphereD d

def sphereAreaD (d : ℕ) : Measure (SphereD d) := (volume : Measure (AmbientD d)).toSphere

theorem sphereAreaD_ne_zero (d : ℕ) : sphereAreaD d ≠ 0 :=
  Measure.toSphere_ne_zero (volume : Measure (AmbientD d))

instance sphereAreaD_nonzero (d : ℕ) : NeZero (sphereAreaD d) := ⟨sphereAreaD_ne_zero d⟩

instance sphereAreaD_finite (d : ℕ) : IsFiniteMeasure (sphereAreaD d) := by
  unfold sphereAreaD
  infer_instance

def sphereProbabilityD (d : ℕ) : Measure (SphereD d) := (sphereAreaD d univ)⁻¹ • sphereAreaD d

instance sphereProbabilityD_probability (d : ℕ) : IsProbabilityMeasure (sphereProbabilityD d) := by
  unfold sphereProbabilityD
  infer_instance

/-- The total area is `(d+1)` times the volume of the unit ball. -/
theorem sphereAreaD_univ (d : ℕ) :
    sphereAreaD d univ = (d+1:ℕ)*volume (ball (0 : AmbientD d) 1) := by
  rw [sphereAreaD, Measure.toSphere_apply_univ]
  simp only [AmbientD, finrank_euclideanSpace_fin]

theorem sphereAreaD_univ_real (d : ℕ) :
    (sphereAreaD d).real univ = (d+1)*(Real.sqrt Real.pi^(d+1)/Real.Gamma ((d+1:ℕ)/2+1)) := by
  rw [Measure.real, sphereAreaD_univ, EuclideanSpace.volume_ball, ENNReal.ofReal_one, one_pow,
    one_mul, Fintype.card_fin, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity)]
  push_cast
  ring

theorem sphereAreaD_univ_pos (d : ℕ) : 0 < (sphereAreaD d).real univ := by
  rw [sphereAreaD_univ_real]
  have := Real.Gamma_pos_of_pos (show (0:ℝ) < ((d+1:ℕ):ℝ)/2+1 by positivity)
  positivity

/-- The area of `S^24`. -/
theorem sphereArea24_univ_real :
    (sphereAreaD 24).real univ = 2^13*Real.pi^12/316234143225 := by
  rw [Measure.real, sphereAreaD_univ,
    InnerProductSpace.volume_ball_of_dim_odd (k := 12) (by simp [AmbientD])]
  simp only [AmbientD, finrank_euclideanSpace_fin, ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)]
  norm_num [Nat.doubleFactorial]
  ring

/-- `S^8` in the generic layer is the `S⁸` of the `d = 8` development. -/
theorem sphereAreaD_eight : sphereAreaD 8 = sphereArea8 := rfl

theorem sphereProbabilityD_eight : sphereProbabilityD 8 = sphereProbability8 := rfl

/-- Ambient isometries act on `S^d`. -/
def sphereRotationD {d : ℕ} (g : AmbientD d ≃ₗᵢ[ℝ] AmbientD d) : SphereD d ≃ₜ SphereD d where
  toFun x := ⟨g x, by simpa only [mem_sphere_zero_iff_norm, g.norm_map] using x.property⟩
  invFun x := ⟨g.symm x, by simpa only [mem_sphere_zero_iff_norm, g.symm.norm_map] using x.property⟩
  left_inv x := Subtype.ext (g.symm_apply_apply x)
  right_inv x := Subtype.ext (g.apply_symm_apply x)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem sphereRotationD_dist {d : ℕ} (g : AmbientD d ≃ₗᵢ[ℝ] AmbientD d) (x y : SphereD d) :
    dist (sphereRotationD g x) (sphereRotationD g y) = dist x y :=
  g.dist_map x y

theorem sphereRotationD_cone_preimage {d : ℕ} (g : AmbientD d ≃ₗᵢ[ℝ] AmbientD d)
    (s : Set (SphereD d)) :
    g ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) =
      Ioo (0 : ℝ) 1 • (Subtype.val '' ((sphereRotationD g) ⁻¹' s)) := by
  ext z
  constructor
  · rintro ⟨r, hr, w, ⟨y, hy, rfl⟩, h⟩
    refine ⟨r, hr, g.symm y, ⟨sphereRotationD g.symm y, ?_, rfl⟩, ?_⟩
    · change sphereRotationD g (sphereRotationD g.symm y) ∈ s
      convert hy using 1
      apply Subtype.ext
      exact g.apply_symm_apply y
    · simpa only [map_smul, g.symm_apply_apply] using congrArg g.symm h
  · rintro ⟨r, hr, w, ⟨y, hy, rfl⟩, h⟩
    refine ⟨r, hr, g y, ⟨sphereRotationD g y, hy, rfl⟩, ?_⟩
    simpa only [map_smul] using congrArg g h

theorem sphereAreaD_rotation_preserving {d : ℕ} (g : AmbientD d ≃ₗᵢ[ℝ] AmbientD d) :
    MeasurePreserving (sphereRotationD g) (sphereAreaD d) (sphereAreaD d) := by
  refine ⟨(sphereRotationD g).measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (sphereRotationD g).measurable hs]
  change (volume : Measure (AmbientD d)).toSphere ((sphereRotationD g) ⁻¹' s) =
    (volume : Measure (AmbientD d)).toSphere s
  rw [Measure.toSphere_apply' _ (hs.preimage (sphereRotationD g).measurable),
    Measure.toSphere_apply' _ hs, ← sphereRotationD_cone_preimage g s,
    g.measurePreserving.measure_preimage_emb g.toHomeomorph.measurableEmbedding]

theorem sphereProbabilityD_rotation_preserving {d : ℕ} (g : AmbientD d ≃ₗᵢ[ℝ] AmbientD d) :
    MeasurePreserving (sphereRotationD g) (sphereProbabilityD d) (sphereProbabilityD d) :=
  (sphereAreaD_rotation_preserving g).smul_measure (sphereAreaD d univ)⁻¹

/-- Ordered off-diagonal Riesz `s`-energy on `S^d` (`-s` for negative exponents). -/
def energyRpowD (s : ℝ) {d N : ℕ} (X : ConfigurationD d N) : ℝ :=
  ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, (dist (X i) (X j))^(-s)

/-- Ordered off-diagonal logarithmic energy on `S^d`. -/
def energyLogD {d N : ℕ} (X : ConfigurationD d N) : ℝ :=
  ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, -Real.log (dist (X i) (X j))

theorem energyRpowD_eight (s : ℝ) {N : ℕ} (X : ConfigurationD 8 N) :
    energyRpowD s X = energyRpow s X := rfl

theorem energyLogD_eight {N : ℕ} (X : ConfigurationD 8 N) : energyLogD X = energyLog X := rfl

theorem offDiagonal_dist_posD {d N : ℕ} (X : ConfigurationD d N) {i j : Fin N} (hij : i ≠ j) :
    0 < dist (X i) (X j) :=
  dist_pos.mpr (fun h => hij (X.injective h))

#print axioms sphereAreaD_ne_zero
#print axioms sphereAreaD_univ
#print axioms sphereAreaD_univ_real
#print axioms sphereAreaD_univ_pos
#print axioms sphereArea24_univ_real
#print axioms sphereAreaD_eight
#print axioms sphereProbabilityD_eight
#print axioms sphereRotationD_dist
#print axioms sphereRotationD_cone_preimage
#print axioms sphereAreaD_rotation_preserving
#print axioms sphereProbabilityD_rotation_preserving
#print axioms energyRpowD_eight
#print axioms energyLogD_eight
#print axioms offDiagonal_dist_posD

end SphericalRiesz
