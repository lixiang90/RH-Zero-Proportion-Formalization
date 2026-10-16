/- SPDX-License-Identifier: Apache-2.0
Actual k and k' point intervals from the already proved normalized K table.
These are needed for value-LP constant supports, which use |k''| <= 4.
-/
import StructuralGoal20261016.WindowFixedTablesAll
import StructuralGoal20261016.WindowFixedPolynomial
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real
namespace StructuralGoal20261016.WindowKernelPoint
open WindowKernel WindowDerivative WindowTaylorBridge WindowConvexityCertificate WindowNormalizedJets
open WindowRationalInterval (Holds)
open WindowFixedInterval WindowFixedRational WindowFixedPolynomial WindowJetTableData

abbrev f : ℝ → ℝ := k 24 d24
def coeff (n j : ℕ) : FI := ofQI (K n j)
def slopeCoeff (n j : ℕ) : FI := scale (coeff n (j+1)) (j+1)
def valuePoly (n : ℕ) (q : ℚ) : FI := poly (coeff n) (q-n) 23
def slopePoly (n : ℕ) (q : ℚ) : FI := poly (slopeCoeff n) (q-n) 22
def valueError (d : ℚ) : ℚ := (22/7)^24*|d|^24/((24:ℕ).factorial:ℚ)
def slopeError (d : ℚ) : ℚ := (22/7)^24*|d|^23/((23:ℕ).factorial:ℚ)

theorem k_iterated_contDiff (q n : ℕ) : ContDiff ℝ n (iteratedDeriv q f) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro r _
  rw [iterated_iterated,iterated_k_eq_jet]
  exact fun x => (jet_hasDerivAt 24 d24 (r+q) x).differentiableAt

theorem derivative_abs (r : ℕ) (x : ℝ) : |iteratedDeriv r f x| ≤ (22/7:ℝ)^r := by
  rw [iterated_k_eq_jet]
  have hp : π ≤ (22/7:ℝ) := Opeth.AMMajorant.pi_coarse.2
  exact (jet24_abs_le r x).trans (pow_le_pow_left₀ pi_pos.le hp r)

theorem coeff_sound {n : ℕ} (hn0 : 1 ≤ n) (hn1 : n ≤ 32) :
    ∀ j ≤ 23, Holds (decode (coeff n j)) (iteratedDeriv j f (n:ℝ)/(j.factorial:ℝ)) := by
  intro j hj
  have hc := ofQI_sound (WindowFixedTablesAll.k_sound hn0 hn1 j hj)
  simpa only [coeff,kc,iterated_k_eq_jet] using hc

theorem first_coeff (j : ℕ) (x : ℝ) :
    iteratedDeriv j (iteratedDeriv 1 f) x/(j.factorial:ℝ) = kc 24 d24 (j+1) x*(j+1:ℕ) := by
  rw [iterated_iterated,iterated_k_eq_jet]
  unfold kc
  rw [Nat.factorial_succ]
  have h0 : (j.factorial:ℝ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have h1 : ((j+1:ℕ):ℝ) ≠ 0 := by positivity
  push_cast
  field_simp [h0,h1] <;> ring

theorem slopeCoeff_sound {n : ℕ} (hn0 : 1 ≤ n) (hn1 : n ≤ 32) :
    ∀ j ≤ 22, Holds (decode (slopeCoeff n j))
      (iteratedDeriv j (iteratedDeriv 1 f) (n:ℝ)/(j.factorial:ℝ)) := by
  intro j hj
  rw [first_coeff]
  unfold slopeCoeff coeff
  convert scale_sound (ofQI_sound (WindowFixedTablesAll.k_sound hn0 hn1 (j+1) (by omega))) (j+1) using 1 <;> push_cast <;> ring

def check (n : ℕ) (q L U D E : ℚ) : Bool := decide (1 ≤ n ∧ n ≤ 32 ∧
  lowerCheck (valuePoly n q) (L+valueError (q-n)) = true ∧
  upperCheck (valuePoly n q) (U-valueError (q-n)) = true ∧
  lowerCheck (slopePoly n q) (D+slopeError (q-n)) = true ∧
  upperCheck (slopePoly n q) (E-slopeError (q-n)) = true)

theorem sound {n : ℕ} {q L U D E : ℚ} (hc : check n q L U D E = true) :
    (L:ℝ) ≤ f q ∧ f q ≤ (U:ℝ) ∧
    (D:ℝ) ≤ iteratedDeriv 1 f q ∧ iteratedDeriv 1 f q ≤ (E:ℝ) := by
  have hh : 1 ≤ n ∧ n ≤ 32 ∧
      lowerCheck (valuePoly n q) (L+valueError (q-n)) = true ∧
      upperCheck (valuePoly n q) (U-valueError (q-n)) = true ∧
      lowerCheck (slopePoly n q) (D+slopeError (q-n)) = true ∧
      upperCheck (slopePoly n q) (E-slopeError (q-n)) = true := of_decide_eq_true hc
  rcases hh with ⟨hn0,hn1,hL,hU,hD,hE⟩
  have hv := poly_sound f (n:ℝ) (coeff n) (q-n) 23 (coeff_sound hn0 hn1)
  have hs := poly_sound (iteratedDeriv 1 f) (n:ℝ) (slopeCoeff n) (q-n) 22 (slopeCoeff_sound hn0 hn1)
  have he : (n:ℝ)+((q-n:ℚ):ℝ) = q := by push_cast; ring
  rw [he] at hv hs
  have hvL := lowerCheck_sound hL hv
  have hvU := upperCheck_sound hU hv
  have hsL := lowerCheck_sound hD hs
  have hsU := upperCheck_sound hE hs
  have vr := taylor_remainder f (k_contDiff 24 d24) 23 (derivative_abs 24) (n:ℝ) (q:ℝ)
  have sr := taylor_remainder (iteratedDeriv 1 f) (k_iterated_contDiff 1) 22
    (by intro x; rw [iterated_iterated]; exact derivative_abs 24 x) (n:ℝ) (q:ℝ)
  have hve : (valueError (q-n):ℝ) = (22/7:ℝ)^24*|(q:ℝ)-(n:ℝ)|^24/((24:ℕ).factorial:ℝ) := by
    unfold valueError
    push_cast
    rfl
  have hse : (slopeError (q-n):ℝ) = (22/7:ℝ)^24*|(q:ℝ)-(n:ℝ)|^23/((23:ℕ).factorial:ℝ) := by
    unfold slopeError
    push_cast
    rfl
  rw [← hve] at vr
  rw [← hse] at sr
  push_cast at hvL hvU hsL hsU
  exact ⟨by linarith [(abs_le.mp vr).1],by linarith [(abs_le.mp vr).2],
    by linarith [(abs_le.mp sr).1],by linarith [(abs_le.mp sr).2]⟩

set_option pp.fullNames true
#print axioms derivative_abs
#print axioms sound
end StructuralGoal20261016.WindowKernelPoint
end
