import Riesz.Boundary

/-! Actual real nodes for a candidate twelfth-order equal-weight boundary correction.
The ten modified midpoint labels are 0,4,...,36 within a 37-cell strip.
Root existence and quarter-cell localization are proved here.  The ten power-sum
identities, the full corrected rule and its twelfth-order error bound remain separate. -/

set_option autoImplicit false
noncomputable section
namespace SphericalRiesz.Boundary

def twelveCandidateP (x : ℝ) : ℝ :=
  88580102706155225088000*x^10
  - 16383628163025960173568000*x^9
  + 1305098710951201031061504000*x^8
  - 58595821582661129791025971200*x^7
  + 1628674182455459972494078771200*x^6
  - 28955939893651903339943401881600*x^5
  + 328054656551266082828093090365440*x^4
  - 2278162143669404848060135276093440*x^3
  + 8842999522732027085544585105582720*x^2
  - 15431811328675648799843640757655952*x
  + 5287828609222057732836140870456497

def twelveCandidateLower (i : Fin 10) : ℝ := 4*(i:ℝ)+1/4
def twelveCandidateUpper (i : Fin 10) : ℝ := 4*(i:ℝ)+3/4

theorem twelveCandidateP_continuous : Continuous twelveCandidateP := by
  unfold twelveCandidateP
  fun_prop

theorem twelveCandidateNode_exists (i : Fin 10) :
    ∃ x, twelveCandidateLower i < x ∧ x < twelveCandidateUpper i ∧ twelveCandidateP x = 0 := by
  have hab : twelveCandidateLower i < twelveCandidateUpper i := by
    unfold twelveCandidateLower twelveCandidateUpper
    linarith
  have hs : (twelveCandidateP (twelveCandidateLower i) < 0 ∧
      0 < twelveCandidateP (twelveCandidateUpper i)) ∨
      (twelveCandidateP (twelveCandidateUpper i) < 0 ∧
      0 < twelveCandidateP (twelveCandidateLower i)) := by
    fin_cases i <;> norm_num [twelveCandidateLower,twelveCandidateUpper,twelveCandidateP]
  rcases hs with hs | hs
  · obtain ⟨x,hx,hz⟩ := intermediate_value_Ioo hab.le twelveCandidateP_continuous.continuousOn hs
    exact ⟨x,hx.1,hx.2,hz⟩
  · obtain ⟨x,hx,hz⟩ := intermediate_value_Ioo' hab.le twelveCandidateP_continuous.continuousOn hs
    exact ⟨x,hx.1,hx.2,hz⟩

def twelveCandidateNode (i : Fin 10) : ℝ := Classical.choose (twelveCandidateNode_exists i)

theorem twelveCandidateNode_spec (i : Fin 10) :
    twelveCandidateLower i < twelveCandidateNode i ∧
      twelveCandidateNode i < twelveCandidateUpper i ∧ twelveCandidateP (twelveCandidateNode i) = 0 :=
  Classical.choose_spec (twelveCandidateNode_exists i)

theorem twelveCandidateNode_strictMono : StrictMono twelveCandidateNode := by
  intro i j hij
  have hi := (twelveCandidateNode_spec i).2.1
  have hj := (twelveCandidateNode_spec j).1
  have hle : (i:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hij
  dsimp [twelveCandidateLower,twelveCandidateUpper] at hi hj
  linarith

theorem twelveCandidateNode_injective : Function.Injective twelveCandidateNode :=
  twelveCandidateNode_strictMono.injective

theorem twelveCandidateNode_close_to_label (i : Fin 10) :
    |twelveCandidateNode i-((4*(i:ℕ):ℕ):ℝ)-1/2| < 1/4 := by
  have h := twelveCandidateNode_spec i
  simp only [twelveCandidateLower,twelveCandidateUpper,Nat.cast_mul,Nat.cast_ofNat] at *
  rw [abs_lt]
  constructor <;> linarith

end SphericalRiesz.Boundary
