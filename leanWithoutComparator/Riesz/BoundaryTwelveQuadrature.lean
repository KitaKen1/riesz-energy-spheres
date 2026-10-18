import Riesz.BoundaryTwelveMoments
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The actual positive equal-weight twelfth-order rule.  Only the ten sparse
left labels and their right reflections are moved; all other midpoints stay. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace SphericalRiesz.Boundary

def twelveStripNode : Fin 37 → ℝ := ![twelveCandidateNode 0, (3/2), (5/2), (7/2), twelveCandidateNode 1, (11/2), (13/2), (15/2), twelveCandidateNode 2, (19/2), (21/2), (23/2), twelveCandidateNode 3, (27/2), (29/2), (31/2), twelveCandidateNode 4, (35/2), (37/2), (39/2), twelveCandidateNode 5, (43/2), (45/2), (47/2), twelveCandidateNode 6, (51/2), (53/2), (55/2), twelveCandidateNode 7, (59/2), (61/2), (63/2), twelveCandidateNode 8, (67/2), (69/2), (71/2), twelveCandidateNode 9]

def twelveStripPowerSum (k : ℕ) : ℝ := ∑ i : Fin 37, twelveStripNode i ^ k

theorem twelveStripPowerSum_eq (k : ℕ) :
    twelveStripPowerSum k = ∑ i : Fin 37, twelveStripNode i ^ k := rfl

theorem twelveStripPowerSum_0 : twelveStripPowerSum 0 = (37:ℝ) := by
  norm_num [twelveStripPowerSum, Fin.sum_univ_succ]

theorem twelveStripPowerSum_1 : twelveStripPowerSum 1 = ((16427/24):ℝ) := by
  have h := twelvePowerSum_1
  simp [twelvePowerSum, Fin.sum_univ_succ] at h
  norm_num [twelveStripPowerSum, twelveStripNode, Fin.sum_univ_succ]
  linear_combination h

theorem twelveStripPowerSum_2 : twelveStripPowerSum 2 = ((67525/4):ℝ) := by
  have h := twelvePowerSum_2
  simp [twelvePowerSum, Fin.sum_univ_succ] at h
  norm_num [twelveStripPowerSum, twelveStripNode, Fin.sum_univ_succ]
  linear_combination h

theorem twelveStripPowerSum_3 : twelveStripPowerSum 3 = ((449634367/960):ℝ) := by
  have h := twelvePowerSum_3
  simp [twelvePowerSum, Fin.sum_univ_succ] at h
  norm_num [twelveStripPowerSum, twelveStripNode, Fin.sum_univ_succ]
  linear_combination h

theorem twelveStripPowerSum_4 : twelveStripPowerSum 4 = ((221765605/16):ℝ) := by
  have h := twelvePowerSum_4
  simp [twelvePowerSum, Fin.sum_univ_succ] at h
  norm_num [twelveStripPowerSum, twelveStripNode, Fin.sum_univ_succ]
  linear_combination h

theorem twelveStripPowerSum_5 : twelveStripPowerSum 5 = ((3445188508157/8064):ℝ) := by
  have h := twelvePowerSum_5
  simp [twelvePowerSum, Fin.sum_univ_succ] at h
  norm_num [twelveStripPowerSum, twelveStripNode, Fin.sum_univ_succ]
  linear_combination h

theorem twelveStripPowerSum_6 : twelveStripPowerSum 6 = ((866839560325/64):ℝ) := by
  have h := twelvePowerSum_6
  simp [twelvePowerSum, Fin.sum_univ_succ] at h
  norm_num [twelveStripPowerSum, twelveStripNode, Fin.sum_univ_succ]
  linear_combination h

theorem twelveStripPowerSum_7 : twelveStripPowerSum 7 = ((13464946884459247/30720):ℝ) := by
  have h := twelvePowerSum_7
  simp [twelvePowerSum, Fin.sum_univ_succ] at h
  norm_num [twelveStripPowerSum, twelveStripNode, Fin.sum_univ_succ]
  linear_combination h

theorem twelveStripPowerSum_8 : twelveStripPowerSum 8 = ((3688595879952805/256):ℝ) := by
  have h := twelvePowerSum_8
  simp [twelvePowerSum, Fin.sum_univ_succ] at h
  norm_num [twelveStripPowerSum, twelveStripNode, Fin.sum_univ_succ]
  linear_combination h

theorem twelveStripPowerSum_9 : twelveStripPowerSum 9 = ((32409422490687697637/67584):ℝ) := by
  have h := twelvePowerSum_9
  simp [twelvePowerSum, Fin.sum_univ_succ] at h
  norm_num [twelveStripPowerSum, twelveStripNode, Fin.sum_univ_succ]
  linear_combination h

theorem twelveStripPowerSum_10 : twelveStripPowerSum 10 = ((16507147802628365125/1024):ℝ) := by
  have h := twelvePowerSum_10
  simp [twelvePowerSum, Fin.sum_univ_succ] at h
  norm_num [twelveStripPowerSum, twelveStripNode, Fin.sum_univ_succ]
  linear_combination h

def twelveMidpointPrimitive : Fin 12 → ℝ → ℝ := fun k x =>
  match k.val with
  | 0 => 1*x^1
  | 1 => (1/2)*x^2
  | 2 => (1/3)*x^3 + (-1/12)*x^1
  | 3 => (1/4)*x^4 + (-1/8)*x^2
  | 4 => (1/5)*x^5 + (-1/6)*x^3 + (7/240)*x^1
  | 5 => (1/6)*x^6 + (-5/24)*x^4 + (7/96)*x^2
  | 6 => (1/7)*x^7 + (-1/4)*x^5 + (7/48)*x^3 + (-31/1344)*x^1
  | 7 => (1/8)*x^8 + (-7/24)*x^6 + (49/192)*x^4 + (-31/384)*x^2
  | 8 => (1/9)*x^9 + (-1/3)*x^7 + (49/120)*x^5 + (-31/144)*x^3 + (127/3840)*x^1
  | 9 => (1/10)*x^10 + (-3/8)*x^8 + (49/80)*x^6 + (-31/64)*x^4 + (381/2560)*x^2
  | 10 => (1/11)*x^11 + (-5/12)*x^9 + (7/8)*x^7 + (-31/32)*x^5 + (127/256)*x^3 + (-2555/33792)*x^1
  | _ => (1/12)*x^12 + (-11/24)*x^10 + (77/64)*x^8 + (-341/192)*x^6 + (1397/1024)*x^4 + (-2555/6144)*x^2

theorem twelveMidpointPrimitive_step (k : Fin 12) (x : ℝ) :
    twelveMidpointPrimitive k (x+1)-twelveMidpointPrimitive k x = (x+1/2)^k.val := by
  fin_cases k <;> norm_num [twelveMidpointPrimitive] <;> ring

theorem twelve_shifted_midpoint_sum (k : Fin 12) (a : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, ((j:ℝ)+a+1/2)^k.val) =
      twelveMidpointPrimitive k ((n:ℝ)+a)-twelveMidpointPrimitive k a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    push_cast
    have h := twelveMidpointPrimitive_step k ((n:ℝ)+a)
    rw [show (n:ℝ)+1+a = ((n:ℝ)+a)+1 by ring]
    linarith

private def twelvePairMonomial : Fin 12 → ℝ → ℝ → ℝ := fun k m x =>
  match k.val with
  | 0 => (2:ℝ)*m^0*x^0
  | 1 => (1:ℝ)*m^1*x^0
  | 2 => (1:ℝ)*m^2*x^0 + (-2:ℝ)*m^1*x^1 + (2:ℝ)*m^0*x^2
  | 3 => (1:ℝ)*m^3*x^0 + (-3:ℝ)*m^2*x^1 + (3:ℝ)*m^1*x^2
  | 4 => (1:ℝ)*m^4*x^0 + (-4:ℝ)*m^3*x^1 + (6:ℝ)*m^2*x^2 + (-4:ℝ)*m^1*x^3 + (2:ℝ)*m^0*x^4
  | 5 => (1:ℝ)*m^5*x^0 + (-5:ℝ)*m^4*x^1 + (10:ℝ)*m^3*x^2 + (-10:ℝ)*m^2*x^3 + (5:ℝ)*m^1*x^4
  | 6 => (1:ℝ)*m^6*x^0 + (-6:ℝ)*m^5*x^1 + (15:ℝ)*m^4*x^2 + (-20:ℝ)*m^3*x^3 + (15:ℝ)*m^2*x^4 + (-6:ℝ)*m^1*x^5 + (2:ℝ)*m^0*x^6
  | 7 => (1:ℝ)*m^7*x^0 + (-7:ℝ)*m^6*x^1 + (21:ℝ)*m^5*x^2 + (-35:ℝ)*m^4*x^3 + (35:ℝ)*m^3*x^4 + (-21:ℝ)*m^2*x^5 + (7:ℝ)*m^1*x^6
  | 8 => (1:ℝ)*m^8*x^0 + (-8:ℝ)*m^7*x^1 + (28:ℝ)*m^6*x^2 + (-56:ℝ)*m^5*x^3 + (70:ℝ)*m^4*x^4 + (-56:ℝ)*m^3*x^5 + (28:ℝ)*m^2*x^6 + (-8:ℝ)*m^1*x^7 + (2:ℝ)*m^0*x^8
  | 9 => (1:ℝ)*m^9*x^0 + (-9:ℝ)*m^8*x^1 + (36:ℝ)*m^7*x^2 + (-84:ℝ)*m^6*x^3 + (126:ℝ)*m^5*x^4 + (-126:ℝ)*m^4*x^5 + (84:ℝ)*m^3*x^6 + (-36:ℝ)*m^2*x^7 + (9:ℝ)*m^1*x^8
  | 10 => (1:ℝ)*m^10*x^0 + (-10:ℝ)*m^9*x^1 + (45:ℝ)*m^8*x^2 + (-120:ℝ)*m^7*x^3 + (210:ℝ)*m^6*x^4 + (-252:ℝ)*m^5*x^5 + (210:ℝ)*m^4*x^6 + (-120:ℝ)*m^3*x^7 + (45:ℝ)*m^2*x^8 + (-10:ℝ)*m^1*x^9 + (2:ℝ)*m^0*x^10
  | _ => (1:ℝ)*m^11*x^0 + (-11:ℝ)*m^10*x^1 + (55:ℝ)*m^9*x^2 + (-165:ℝ)*m^8*x^3 + (330:ℝ)*m^7*x^4 + (-462:ℝ)*m^6*x^5 + (462:ℝ)*m^5*x^6 + (-330:ℝ)*m^4*x^7 + (165:ℝ)*m^3*x^8 + (-55:ℝ)*m^2*x^9 + (11:ℝ)*m^1*x^10

private def twelvePairFormula : Fin 12 → ℝ → ℝ := fun k m =>
  match k.val with
  | 0 => (2:ℝ)*m^0*37
  | 1 => (1:ℝ)*m^1*37
  | 2 => (1:ℝ)*m^2*37 + (-2:ℝ)*m^1*(16427/24) + (2:ℝ)*m^0*(67525/4)
  | 3 => (1:ℝ)*m^3*37 + (-3:ℝ)*m^2*(16427/24) + (3:ℝ)*m^1*(67525/4)
  | 4 => (1:ℝ)*m^4*37 + (-4:ℝ)*m^3*(16427/24) + (6:ℝ)*m^2*(67525/4) + (-4:ℝ)*m^1*(449634367/960) + (2:ℝ)*m^0*(221765605/16)
  | 5 => (1:ℝ)*m^5*37 + (-5:ℝ)*m^4*(16427/24) + (10:ℝ)*m^3*(67525/4) + (-10:ℝ)*m^2*(449634367/960) + (5:ℝ)*m^1*(221765605/16)
  | 6 => (1:ℝ)*m^6*37 + (-6:ℝ)*m^5*(16427/24) + (15:ℝ)*m^4*(67525/4) + (-20:ℝ)*m^3*(449634367/960) + (15:ℝ)*m^2*(221765605/16) + (-6:ℝ)*m^1*(3445188508157/8064) + (2:ℝ)*m^0*(866839560325/64)
  | 7 => (1:ℝ)*m^7*37 + (-7:ℝ)*m^6*(16427/24) + (21:ℝ)*m^5*(67525/4) + (-35:ℝ)*m^4*(449634367/960) + (35:ℝ)*m^3*(221765605/16) + (-21:ℝ)*m^2*(3445188508157/8064) + (7:ℝ)*m^1*(866839560325/64)
  | 8 => (1:ℝ)*m^8*37 + (-8:ℝ)*m^7*(16427/24) + (28:ℝ)*m^6*(67525/4) + (-56:ℝ)*m^5*(449634367/960) + (70:ℝ)*m^4*(221765605/16) + (-56:ℝ)*m^3*(3445188508157/8064) + (28:ℝ)*m^2*(866839560325/64) + (-8:ℝ)*m^1*(13464946884459247/30720) + (2:ℝ)*m^0*(3688595879952805/256)
  | 9 => (1:ℝ)*m^9*37 + (-9:ℝ)*m^8*(16427/24) + (36:ℝ)*m^7*(67525/4) + (-84:ℝ)*m^6*(449634367/960) + (126:ℝ)*m^5*(221765605/16) + (-126:ℝ)*m^4*(3445188508157/8064) + (84:ℝ)*m^3*(866839560325/64) + (-36:ℝ)*m^2*(13464946884459247/30720) + (9:ℝ)*m^1*(3688595879952805/256)
  | 10 => (1:ℝ)*m^10*37 + (-10:ℝ)*m^9*(16427/24) + (45:ℝ)*m^8*(67525/4) + (-120:ℝ)*m^7*(449634367/960) + (210:ℝ)*m^6*(221765605/16) + (-252:ℝ)*m^5*(3445188508157/8064) + (210:ℝ)*m^4*(866839560325/64) + (-120:ℝ)*m^3*(13464946884459247/30720) + (45:ℝ)*m^2*(3688595879952805/256) + (-10:ℝ)*m^1*(32409422490687697637/67584) + (2:ℝ)*m^0*(16507147802628365125/1024)
  | _ => (1:ℝ)*m^11*37 + (-11:ℝ)*m^10*(16427/24) + (55:ℝ)*m^9*(67525/4) + (-165:ℝ)*m^8*(449634367/960) + (330:ℝ)*m^7*(221765605/16) + (-462:ℝ)*m^6*(3445188508157/8064) + (462:ℝ)*m^5*(866839560325/64) + (-330:ℝ)*m^4*(13464946884459247/30720) + (165:ℝ)*m^3*(3688595879952805/256) + (-55:ℝ)*m^2*(32409422490687697637/67584) + (11:ℝ)*m^1*(16507147802628365125/1024)

private theorem twelvePairMonomial_eq (k : Fin 12) (m x : ℝ) :
    x^k.val+(m-x)^k.val=twelvePairMonomial k m x := by
  fin_cases k <;> norm_num [twelvePairMonomial] <;> ring

theorem twelveStrip_pair_sum (k : Fin 12) (m : ℝ) :
    (∑ i : Fin 37, ((twelveStripNode i)^k.val+(m-twelveStripNode i)^k.val)) =
      twelvePairFormula k m := by
  simp_rw [twelvePairMonomial_eq]
  fin_cases k <;>
    simp only [twelvePairMonomial, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← twelveStripPowerSum_eq] <;>
    norm_num [twelvePairFormula, twelveStripPowerSum_0, twelveStripPowerSum_1, twelveStripPowerSum_2, twelveStripPowerSum_3, twelveStripPowerSum_4, twelveStripPowerSum_5, twelveStripPowerSum_6, twelveStripPowerSum_7, twelveStripPowerSum_8, twelveStripPowerSum_9, twelveStripPowerSum_10]

abbrev TwelveNodeIndex (m : ℕ) := Fin 37 ⊕ (Fin (m-74) ⊕ Fin 37)

def twelveUnscaledRuleNode (m : ℕ) : TwelveNodeIndex m → ℝ :=
  Sum.elim twelveStripNode (Sum.elim (fun j => (j:ℝ)+37+1/2) (fun i => (m:ℝ)-twelveStripNode i))

def twelveRuleNode (m : ℕ) (i : TwelveNodeIndex m) : ℝ := twelveUnscaledRuleNode m i / m

def twelveQuadrature (m : ℕ) (f : ℝ → ℝ) : ℝ :=
  ((∑ i : Fin 37, f (twelveStripNode i/m)) +
    (∑ j ∈ Finset.range (m-74), f (((j:ℝ)+37+1/2)/m)) +
    (∑ i : Fin 37, f (((m:ℝ)-twelveStripNode i)/m))) / m

theorem twelveNodeIndex_card {m : ℕ} (hm : 74 ≤ m) : Fintype.card (TwelveNodeIndex m) = m := by
  simp only [TwelveNodeIndex, Fintype.card_sum, Fintype.card_fin]
  omega

theorem twelveQuadrature_as_node_sum (m : ℕ) (f : ℝ → ℝ) :
    twelveQuadrature m f = (∑ i : TwelveNodeIndex m, f (twelveRuleNode m i))/m := by
  simp [twelveQuadrature,TwelveNodeIndex,twelveRuleNode,twelveUnscaledRuleNode,
    Fintype.sum_sum_type, ← Fin.sum_univ_eq_sum_range,add_assoc]

theorem twelveQuadrature_add (m : ℕ) (f g : ℝ → ℝ) :
    twelveQuadrature m (fun x => f x+g x) = twelveQuadrature m f+twelveQuadrature m g := by
  simp only [twelveQuadrature,Finset.sum_add_distrib]
  ring

theorem twelveQuadrature_mul_const (m : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    twelveQuadrature m (fun x => c*f x) = c*twelveQuadrature m f := by
  simp only [twelveQuadrature,← Finset.mul_sum]
  ring

theorem twelveQuadrature_finset_sum {ι : Type*} (m : ℕ) (s : Finset ι) (f : ι → ℝ → ℝ) :
    twelveQuadrature m (fun x => ∑ i ∈ s, f i x)=∑ i ∈ s,twelveQuadrature m (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [twelveQuadrature]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [twelveQuadrature_add,ih]

theorem twelve_unscaled_power_sum {m : ℕ} (hm : 74 ≤ m) (k : Fin 12) :
    (∑ i : Fin 37,(twelveStripNode i)^k.val) +
    (∑ j ∈ Finset.range (m-74),((j:ℝ)+37+1/2)^k.val) +
    (∑ i : Fin 37,((m:ℝ)-twelveStripNode i)^k.val) = (m:ℝ)^(k.val+1)/(k.val+1) := by
  rw [twelve_shifted_midpoint_sum]
  have hn : ((m-74:ℕ):ℝ)=(m:ℝ)-74 := by rw [Nat.cast_sub hm]; norm_num
  have hp := twelveStrip_pair_sum k (m:ℝ)
  rw [Finset.sum_add_distrib] at hp
  rw [hn]
  have heq : (∑ i : Fin 37,(twelveStripNode i)^k.val) +
      (twelveMidpointPrimitive k ((m:ℝ)-74+37)-twelveMidpointPrimitive k 37) +
      (∑ i : Fin 37,((m:ℝ)-twelveStripNode i)^k.val) =
      twelvePairFormula k m + (twelveMidpointPrimitive k ((m:ℝ)-74+37)-twelveMidpointPrimitive k 37) := by linarith
  rw [heq]
  fin_cases k <;> norm_num [twelveMidpointPrimitive,twelvePairFormula] <;> ring

theorem twelveQuadrature_monomial {m : ℕ} (hm : 74 ≤ m) (k : Fin 12) :
    twelveQuadrature m (fun x => x^k.val) = 1/(k.val+1:ℝ) := by
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  unfold twelveQuadrature
  simp only [div_pow, ← Finset.sum_div]
  rw [← add_div,← add_div,twelve_unscaled_power_sum hm,pow_succ]
  field_simp

theorem twelveQuadrature_monomial_integral {m : ℕ} (hm : 74 ≤ m) (k : Fin 12) :
    twelveQuadrature m (fun x => x^k.val) = ∫ x in (0:ℝ)..1,x^k.val := by
  rw [twelveQuadrature_monomial hm,integral_pow]
  simp

theorem twelveQuadrature_degree_eleven {m : ℕ} (hm : 74 ≤ m) (a : Fin 12 → ℝ) :
    twelveQuadrature m (fun x => ∑ k : Fin 12,a k*x^k.val) =
      ∫ x in (0:ℝ)..1,∑ k : Fin 12,a k*x^k.val := by
  rw [twelveQuadrature_finset_sum,intervalIntegral.integral_finsetSum]
  · simp_rw [twelveQuadrature_mul_const,twelveQuadrature_monomial_integral hm,
      intervalIntegral.integral_const_mul]
  · intro k _
    exact (by fun_prop : Continuous (fun x : ℝ => a k*x^k.val)).intervalIntegrable _ _

theorem twelveStripNode_bounds (i : Fin 37) :
    (i:ℝ)+1/4 < twelveStripNode i ∧ twelveStripNode i < (i:ℝ)+3/4 := by
  fin_cases i <;> norm_num [twelveStripNode]
  · have h := twelveCandidateNode_spec 0
    norm_num [twelveCandidateLower,twelveCandidateUpper] at h
    exact ⟨h.1,h.2.1⟩
  · have h := twelveCandidateNode_spec 1
    norm_num [twelveCandidateLower,twelveCandidateUpper] at h
    exact ⟨h.1,h.2.1⟩
  · have h := twelveCandidateNode_spec 2
    norm_num [twelveCandidateLower,twelveCandidateUpper] at h
    exact ⟨h.1,h.2.1⟩
  · have h := twelveCandidateNode_spec 3
    norm_num [twelveCandidateLower,twelveCandidateUpper] at h
    exact ⟨h.1,h.2.1⟩
  · have h := twelveCandidateNode_spec 4
    norm_num [twelveCandidateLower,twelveCandidateUpper] at h
    exact ⟨h.1,h.2.1⟩
  · have h := twelveCandidateNode_spec 5
    norm_num [twelveCandidateLower,twelveCandidateUpper] at h
    exact ⟨h.1,h.2.1⟩
  · have h := twelveCandidateNode_spec 6
    norm_num [twelveCandidateLower,twelveCandidateUpper] at h
    exact ⟨h.1,h.2.1⟩
  · have h := twelveCandidateNode_spec 7
    norm_num [twelveCandidateLower,twelveCandidateUpper] at h
    exact ⟨h.1,h.2.1⟩
  · have h := twelveCandidateNode_spec 8
    norm_num [twelveCandidateLower,twelveCandidateUpper] at h
    exact ⟨h.1,h.2.1⟩
  · have h := twelveCandidateNode_spec 9
    norm_num [twelveCandidateLower,twelveCandidateUpper] at h
    exact ⟨h.1,h.2.1⟩

theorem twelveStripNode_strictMono : StrictMono twelveStripNode := by
  intro i j hij
  have hi := (twelveStripNode_bounds i).2
  have hj := (twelveStripNode_bounds j).1
  have hle : (i:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hij
  linarith

theorem twelveStripNode_between (i : Fin 37) : 0 < twelveStripNode i ∧ twelveStripNode i < 37 := by
  have h := twelveStripNode_bounds i
  have hi : (i:ℝ) < 37 := by exact_mod_cast i.isLt
  have hi' : (i:ℝ) ≤ 36 := by exact_mod_cast (show i.val ≤ 36 by omega)
  have h0 : (0:ℝ) ≤ i := by positivity
  constructor <;> linarith

private theorem twelve_middle_between {m : ℕ} (hm : 74 ≤ m) (j : Fin (m-74)) :
    37 < (j:ℝ)+37+1/2 ∧ (j:ℝ)+37+1/2 < (m:ℝ)-37 := by
  have hj : (j:ℕ)+75 ≤ m := by have := j.isLt; omega
  have hr : (j:ℝ)+75 ≤ (m:ℝ) := by exact_mod_cast hj
  have h0 : (0:ℝ) ≤ j := by positivity
  constructor <;> linarith

theorem twelveUnscaledRuleNode_injective {m : ℕ} (hm : 74 ≤ m) :
    Function.Injective (twelveUnscaledRuleNode m) := by
  rw [twelveUnscaledRuleNode,Sum.elim_injective]
  refine ⟨twelveStripNode_strictMono.injective,?_,?_⟩
  · rw [Sum.elim_injective]
    refine ⟨?_,?_,?_⟩
    · intro i j h
      apply Fin.ext
      have : (i:ℝ)=(j:ℝ) := by linarith
      exact_mod_cast this
    · intro i j h
      apply twelveStripNode_strictMono.injective
      linarith
    · intro j i h
      have hj := (twelve_middle_between hm j).2
      have hi := (twelveStripNode_between i).2
      linarith
  · intro i x h
    have hi := (twelveStripNode_between i).2
    rcases x with j | j
    · have hj := (twelve_middle_between hm j).1
      change twelveStripNode i = (j:ℝ)+37+1/2 at h
      linarith
    · have hj := (twelveStripNode_between j).2
      have hr : (74:ℝ) ≤ m := by exact_mod_cast hm
      change twelveStripNode i = (m:ℝ)-twelveStripNode j at h
      linarith

theorem twelveRuleNode_injective {m : ℕ} (hm : 74 ≤ m) : Function.Injective (twelveRuleNode m) := by
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  intro i j h
  exact twelveUnscaledRuleNode_injective hm ((div_left_inj' hm0).mp h)

theorem twelveRuleNode_mem_unit {m : ℕ} (hm : 74 ≤ m) (i : TwelveNodeIndex m) :
    twelveRuleNode m i ∈ Set.Ioo (0:ℝ) 1 := by
  have hr : (74:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := by linarith
  unfold twelveRuleNode
  rw [Set.mem_Ioo,div_pos_iff_of_pos_right hm0,div_lt_one hm0]
  rcases i with i | (i | i)
  · have hi := twelveStripNode_between i
    change 0 < twelveStripNode i ∧ twelveStripNode i < (m:ℝ)
    constructor <;> linarith
  · have hi := twelve_middle_between hm i
    change 0 < (i:ℝ)+37+1/2 ∧ (i:ℝ)+37+1/2 < (m:ℝ)
    constructor <;> linarith
  · have hi := twelveStripNode_between i
    change 0 < (m:ℝ)-twelveStripNode i ∧ (m:ℝ)-twelveStripNode i < (m:ℝ)
    constructor <;> linarith

end SphericalRiesz.Boundary
