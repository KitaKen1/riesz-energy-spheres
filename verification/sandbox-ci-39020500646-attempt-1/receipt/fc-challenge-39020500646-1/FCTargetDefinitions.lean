import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Prod

/-! Trusted mathematical definitions for the publication targets.
This file imports Mathlib only. There are no axioms or definition holes.
The lattices are explicitly the integer spans of the displayed scaled rows.
The complex argument of `epstein` is half the distance exponent.
The value at zero is defined by the analytic continuation `epsteinCont`.
-/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology RealInnerProductSpace
namespace RieszSphereFC

abbrev Sphere (d : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1
abbrev Config (d N : ℕ) := Fin N ↪ Sphere d
def areaMeasure (d : ℕ) : Measure (Sphere d) :=
  (volume : Measure (EuclideanSpace ℝ (Fin (d+1)))).toSphere
def uniform (d : ℕ) : Measure (Sphere d) :=
  (areaMeasure d univ)⁻¹ • areaMeasure d
def area (d : ℕ) : ℝ := (areaMeasure d).real univ
def energy (d : ℕ) (s : ℝ) {N : ℕ} (X : Config d N) : ℝ :=
  ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, (dist (X i) (X j))^(-s)
def logEnergy (d : ℕ) {N : ℕ} (X : Config d N) : ℝ :=
  ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, -Real.log (dist (X i) (X j))
def background (d : ℕ) (s : ℝ) : ℝ :=
  ∫ p : Sphere d × Sphere d, (dist p.1 p.2)^(-s) ∂((uniform d).prod (uniform d))
def logBackground (d : ℕ) : ℝ :=
  ∫ p : Sphere d × Sphere d, -Real.log (dist p.1 p.2) ∂((uniform d).prod (uniform d))
def normalizedMin (d : ℕ) (s : ℝ) (N : ℕ) : ℝ :=
  (sInf (range (fun X : Config d N => energy d s X))-background d s*(N:ℝ)^2)/
    (N:ℝ)^(1+s/d)
def normalizedMax (d : ℕ) (s : ℝ) (N : ℕ) : ℝ :=
  (sSup (range (fun X : Config d N => energy d s X))-background d s*(N:ℝ)^2)/
    (N:ℝ)^(1+s/d)
def normalizedLogMin (d N : ℕ) : ℝ :=
  (sInf (range (fun X : Config d N => logEnergy d X))-logBackground d*(N:ℝ)^2+
    (N:ℝ)/d*Real.log N)/(N:ℝ)

def hexMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  (Real.sqrt (Real.sqrt 3/2))⁻¹ • !![1, 0; 1/2, Real.sqrt 3/2]
def triangular : Submodule ℤ (EuclideanSpace ℝ (Fin 2)) :=
  Submodule.span ℤ (range (fun i : Fin 2 => WithLp.toLp 2 (hexMatrix.row i)))

-- The Conway--Sloane generator, scaled by 1/sqrt(8), has covolume one.
-- Matrix data adapted from Sphere-Packing-Lean (Apache-2.0); see THIRD_PARTY.md.
def leechMatrixInt : Matrix (Fin 24) (Fin 24) ℤ :=
  ![
    ![8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 2, 2, 2, 0, 0, 0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0],
    ![2, 0, 2, 0, 2, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0],
    ![2, 0, 0, 2, 2, 2, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0],
    ![2, 2, 0, 0, 2, 0, 2, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0],
    ![0, 2, 2, 2, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0],
    ![-3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  ]

def leechMatrix : Matrix (Fin 24) (Fin 24) ℝ :=
  (Real.sqrt 8)⁻¹ • leechMatrixInt.map (fun z : ℤ => (z:ℝ))
def leech : Submodule ℤ (EuclideanSpace ℝ (Fin 24)) :=
  Submodule.span ℤ (range (fun i : Fin 24 => WithLp.toLp 2 (leechMatrix.row i)))

def theta {d : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin d))) (t : ℝ) : ℂ :=
  ∑' x : L, Complex.exp ((Real.pi : ℂ)*Complex.I*
    (‖(x : EuclideanSpace ℝ (Fin d))‖^2 : ℝ)*((t:ℂ)*Complex.I))
def modifiedTheta (k : ℝ) (θ : ℝ → ℂ) : ℝ → ℂ :=
  (Ioi 1).indicator (fun x => θ x - 1) +
    (Ioo 0 1).indicator (fun x => θ x - ((1:ℂ) * ↑(x ^ (-k))) • (1:ℂ))
def lambdaZero (k : ℝ) (θ : ℝ → ℂ) : ℂ → ℂ := mellin (modifiedTheta k θ)
def epstein (k : ℝ) (θ : ℝ → ℂ) (u : ℂ) : ℂ :=
  (Real.pi:ℂ)^u * (lambdaZero k θ u - (1/u) • (1:ℂ) - (1/((k:ℂ)-u)) • (1:ℂ)) /
    Complex.Gamma u
def epsteinCont (k : ℝ) (θ : ℝ → ℂ) (u : ℂ) : ℂ :=
  (Real.pi:ℂ)^u*(lambdaZero k θ u*(Complex.Gamma u)⁻¹-(Complex.Gamma (u+1))⁻¹-
    ((k:ℂ)-u)⁻¹*(Complex.Gamma u)⁻¹)
def hexZeta : ℂ → ℂ := epstein 1 (theta triangular)
def leechZeta : ℂ → ℂ := epstein 12 (theta leech)
def hexZetaCont : ℂ → ℂ := epsteinCont 1 (theta triangular)
def leechZetaCont : ℂ → ℂ := epsteinCont 12 (theta leech)
def e8Zeta (u : ℂ) : ℂ := (2:ℂ)^(-u)*(240*riemannZeta u*riemannZeta (u-3))

def capIndicator {d : ℕ} (z : Sphere d) (t : ℝ) (x : Sphere d) : ℝ :=
  if t ≤ ⟪(x : EuclideanSpace ℝ (Fin (d+1))), (z : EuclideanSpace ℝ (Fin (d+1)))⟫
    then 1 else 0
def capSquared (d : ℕ) {N : ℕ} (X : Config d N) : ℝ :=
  ∫ q, ((∑ i : Fin N, capIndicator q.1 q.2 (X i))/(N:ℝ) -
    ∫ y, capIndicator q.1 q.2 y ∂(uniform d))^2
    ∂((uniform d).prod (volume.restrict (Icc (-1:ℝ) 1)))
def minimumCap (d N : ℕ) : ℝ :=
  sInf (range (fun X : Config d N => Real.sqrt (capSquared d X)))
end RieszSphereFC
