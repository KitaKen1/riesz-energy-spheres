import Riesz.SphereMain8

/-! Dimension 8: the sharp second-order asymptotics in the form of a Formal Conjectures entry.

The statements below use Mathlib only: the unit sphere `S⁸ ⊂ ℝ⁹` as `Metric.sphere 0 1` in
`EuclideanSpace ℝ (Fin 9)`, its uniform probability measure as the normalized surface measure
`Measure.toSphere`, configurations as injective maps `Fin N ↪ S⁸`, energies as sums over ordered
pairs `i ≠ j`, the extremal values as `sInf` / `sSup` over all configurations, and the Riemann
zeta function.  The two definitions `S8` and `uniformS8` are the only bespoke ones.

Each statement is the limit of the normalized extremal energy:

* `riesz_energy_four_sphere8`: exponent `4`, with the explicit constants `7/16` and `-5√210/48`
  (the main target of this project);
* `riesz_energy_sphere8`: `0 < s < 8`, `s ≠ 2`, with the coefficient
  `|S⁸|^(-s/8) · 240 · 2^(-s/2) ζ(s/2) ζ(s/2 - 3)`, `|S⁸| = 32π⁴/105` (the Epstein zeta function
  of the `E8` lattice at `s`);
* `riesz_energy_two_sphere8`: `s = 2`, where that expression has a removable point; the
  coefficient is `|S⁸|^(-1/4) · 120 ζ'(-2)`;
* `riesz_energy_neg_sphere8`: `-2 < s < 0`, the maximal sum of the powers `|x_i - x_j|^(-s)`;
* `log_energy_sphere8`: the logarithmic energy.

All of them are proved here from the theorems of `Riesz/SphereMain8.lean`, without hypotheses. -/

set_option autoImplicit false
noncomputable section
namespace SphericalRiesz.Statement
open Filter MeasureTheory Set
open scoped Topology

/-- The unit sphere `S⁸ ⊂ ℝ⁹`. -/
abbrev S8 : Set (EuclideanSpace ℝ (Fin 9)) := Metric.sphere 0 1

/-- The uniform probability measure on `S⁸`: the surface measure divided by the total area. -/
def uniformS8 : Measure S8 :=
  ((volume : Measure (EuclideanSpace ℝ (Fin 9))).toSphere univ)⁻¹ •
    (volume : Measure (EuclideanSpace ℝ (Fin 9))).toSphere

/-- The exponent `4` on `S⁸`: `(𝓔₄(N) - (7/16) N²)/N^(3/2) → -5√210/48`, where `𝓔₄(N)` is the
minimum over `N`-point configurations of the sum of `|x_i - x_j|^(-4)` over ordered pairs. -/
theorem riesz_energy_four_sphere8 :
    Tendsto (fun N : ℕ =>
      (sInf (range fun X : Fin N ↪ S8 =>
          ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, (dist (X i) (X j))⁻¹^4)-
        7/16*(N:ℝ)^2)/((N:ℝ)*Real.sqrt N)) atTop (𝓝 (-5*Real.sqrt 210/48)) := by
  have h := S8s4Target_unconditional
  refine tendsto_normalized_csInf_of_eventual_bounds
    (fun N (X : Configuration N) => energy4 X) (fun N => (N:ℝ)*Real.sqrt N)
    (fun N => (7/16:ℝ)*(N:ℝ)^2) ?_ ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hNR : (0:ℝ) < N := by exact_mod_cast hN
    exact mul_pos hNR (Real.sqrt_pos.mpr hNR)
  · intro ε hε
    obtain ⟨N₀, _, hN₀⟩ := h ε hε
    exact ⟨N₀, fun N hN X => (hN₀ N hN).1 X⟩
  · intro ε hε
    obtain ⟨N₀, _, hN₀⟩ := h ε hε
    exact ⟨N₀, fun N hN => (hN₀ N hN).2⟩

/-- Exponents `0 < s < 8`, `s ≠ 2`, on `S⁸`: the normalized minimal Riesz energy tends to
`|S⁸|^(-s/8) ζ_{E8}(s)`, `ζ_{E8}(s) = 240 · 2^(-s/2) ζ(s/2) ζ(s/2 - 3)`. -/
theorem riesz_energy_sphere8 {s : ℝ} (hs : 0 < s) (hs8 : s < 8) (hs2 : s ≠ 2) :
    Tendsto (fun N : ℕ =>
      (sInf (range fun X : Fin N ↪ S8 =>
          ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, (dist (X i) (X j))^(-s))-
        (∫ p : S8 × S8, (dist p.1 p.2)^(-s) ∂(uniformS8.prod uniformS8))*(N:ℝ)^2)/
          (N:ℝ)^(1+s/8)) atTop
      (𝓝 ((32*Real.pi^4/105)^(-(s/8))*
        ((2:ℂ)^(-((s/2:ℝ):ℂ))*(240*riemannZeta ((s/2:ℝ):ℂ)*riemannZeta (((s/2:ℝ):ℂ)-3))).re)) := by
  have h := sphere8_riesz_sharp_asymptotic_unconditional hs hs8 hs2
  rw [sphereArea8_mass_real] at h
  exact tendsto_normalized_csInf_of_eventual_bounds
    (fun N (X : Configuration N) => energyRpow s X) (fun N => (N:ℝ)^(1+s/8))
    (fun N => (∫ p : Sphere8 × Sphere8, (dist p.1 p.2)^(-s)
      ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2)
    (eventually_natCast_rpow_pos _) h.1 h.2

/-- The exponent `2` on `S⁸`: the coefficient is `|S⁸|^(-1/4) · 120 ζ'(-2)`. -/
theorem riesz_energy_two_sphere8 :
    Tendsto (fun N : ℕ =>
      (sInf (range fun X : Fin N ↪ S8 =>
          ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, (dist (X i) (X j))^(-(2:ℝ)))-
        (∫ p : S8 × S8, (dist p.1 p.2)^(-(2:ℝ)) ∂(uniformS8.prod uniformS8))*(N:ℝ)^2)/
          (N:ℝ)^(1+(2:ℝ)/8)) atTop
      (𝓝 ((32*Real.pi^4/105)^(-((2:ℝ)/8))*(120*(deriv riemannZeta (-2)).re))) := by
  have h := sphere8_riesz_sharp_asymptotic_two_unconditional
  rw [sphereArea8_mass_real] at h
  exact tendsto_normalized_csInf_of_eventual_bounds
    (fun N (X : Configuration N) => energyRpow 2 X) (fun N => (N:ℝ)^(1+(2:ℝ)/8))
    (fun N => (∫ p : Sphere8 × Sphere8, (dist p.1 p.2)^(-(2:ℝ))
      ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2)
    (eventually_natCast_rpow_pos _) h.1 h.2

/-- Exponents `-2 < s < 0` on `S⁸`: the normalized maximal sum of the powers `|x_i - x_j|^(-s)`
tends to `|S⁸|^(-s/8) ζ_{E8}(s)` (the continued Epstein zeta function, same closed form). -/
theorem riesz_energy_neg_sphere8 {s : ℝ} (hs : -2 < s) (hs0 : s < 0) :
    Tendsto (fun N : ℕ =>
      (sSup (range fun X : Fin N ↪ S8 =>
          ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, (dist (X i) (X j))^(-s))-
        (∫ p : S8 × S8, (dist p.1 p.2)^(-s) ∂(uniformS8.prod uniformS8))*(N:ℝ)^2)/
          (N:ℝ)^(1+s/8)) atTop
      (𝓝 ((32*Real.pi^4/105)^(-(s/8))*
        ((2:ℂ)^(-((s/2:ℝ):ℂ))*(240*riemannZeta ((s/2:ℝ):ℂ)*riemannZeta (((s/2:ℝ):ℂ)-3))).re)) := by
  have h := sphere8_riesz_neg_sharp_unconditional hs hs0
  rw [sphereArea8_mass_real] at h
  exact tendsto_normalized_csSup_of_eventual_bounds
    (fun N (X : Configuration N) => energyRpow s X) (fun N => (N:ℝ)^(1+s/8))
    (fun N => (∫ p : Sphere8 × Sphere8, (dist p.1 p.2)^(-s)
      ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2)
    (eventually_natCast_rpow_pos _) h.1 h.2

/-- The logarithmic energy on `S⁸`: with `𝓔_log(N)` the minimum over `N`-point configurations of
the sum of `-log |x_i - x_j|` over ordered pairs and `W` the double integral of `-log |x - y|`,
`(𝓔_log(N) - W N² + (N/8) log N)/N → -60 ζ'(-3) + (5/8) log 2 - (1/8) log 105`. -/
theorem log_energy_sphere8 :
    Tendsto (fun N : ℕ =>
      (sInf (range fun X : Fin N ↪ S8 =>
          ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, -Real.log (dist (X i) (X j)))-
        (∫ p : S8 × S8, -Real.log (dist p.1 p.2) ∂(uniformS8.prod uniformS8))*(N:ℝ)^2+
          (N:ℝ)/8*Real.log N)/(N:ℝ)) atTop
      (𝓝 (-60*(deriv riemannZeta (-3)).re+(5/8)*Real.log 2-(1/8)*Real.log 105)) := by
  have h := sphere8_log_sharp_unconditional
  have hW : ∀ (N : ℕ) (X : Configuration N),
      (energyLog X-(∫ p : Sphere8 × Sphere8, -Real.log (dist p.1 p.2)
        ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2+(N:ℝ)/8*Real.log N)/(N:ℝ) =
      (energyLog X-((∫ p : Sphere8 × Sphere8, -Real.log (dist p.1 p.2)
        ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2-(N:ℝ)/8*Real.log N))/(N:ℝ) :=
    fun N X => by ring
  have ht := tendsto_normalized_csInf_of_eventual_bounds
    (fun N (X : Configuration N) => energyLog X) (fun N => (N:ℝ))
    (fun N => (∫ p : Sphere8 × Sphere8, -Real.log (dist p.1 p.2)
      ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2-(N:ℝ)/8*Real.log N)
    (by filter_upwards [eventually_gt_atTop 0] with N hN; exact_mod_cast hN)
    (fun ε hε => by
      obtain ⟨N₀, hN₀⟩ := h.1 ε hε
      exact ⟨N₀, fun N hN X => by rw [← hW]; exact hN₀ N hN X⟩)
    (fun ε hε => by
      obtain ⟨N₀, hN₀⟩ := h.2 ε hε
      refine ⟨N₀, fun N hN => ?_⟩
      obtain ⟨Y, hY⟩ := hN₀ N hN
      exact ⟨Y, by rw [← hW]; exact hY⟩)
  have ht' : Tendsto (fun N : ℕ =>
      (sInf (range fun X : Configuration N => energyLog X)-
        (∫ p : Sphere8 × Sphere8, -Real.log (dist p.1 p.2)
          ∂(sphereProbability8.prod sphereProbability8))*(N:ℝ)^2+(N:ℝ)/8*Real.log N)/(N:ℝ)) atTop
      (𝓝 (-60*(deriv riemannZeta (-3)).re+(5/8)*Real.log 2-(1/8)*Real.log 105)) :=
    ht.congr fun N => by ring
  exact ht'

end SphericalRiesz.Statement
