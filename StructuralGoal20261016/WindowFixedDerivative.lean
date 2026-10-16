/- SPDX-License-Identifier: Apache-2.0
Actual arbitrary derivative point enclosures using fixed-integer Horner
evaluation and the proved order-24 Fourier remainder.
-/
import StructuralGoal20261016.WindowFixedPoint
import StructuralGoal20261016.WindowFixedTablesAll
import StructuralGoal20261016.WindowRawCoefficients
import StructuralGoal20261016.WindowDerivativeTableArithmetic
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real
namespace StructuralGoal20261016.WindowFixedDerivative
open WindowRationalInterval (Holds)
open WindowFixedInterval WindowFixedRational WindowFixedPolynomial
open WindowJetTableData WindowNormalizedJets WindowScalarMinorant WindowConvexityCertificate
open WindowDerivativeTableArithmetic (error derivative_remainder shifted_coeff)

def coeff (n q j : ℕ) : FI := scale (WindowRawCoefficientData.W n (j+q)) (((j+q).factorial:ℚ)/(j.factorial:ℚ))

theorem coeff_sound {n q d : ℕ} (hn0 : 1 ≤ n) (hn1 : n ≤ 32) (hqd : q+d ≤ 23) :
 ∀ j ≤ d, Holds (decode (coeff n q j))
   (iteratedDeriv j (iteratedDeriv q f) (n:ℝ)/(j.factorial:ℝ)) := by
 intro j hj
 rw [shifted_coeff]
 have h := scale_sound (WindowRawCoefficients.sound hn0 hn1 (j+q) (by omega))
   (((j+q).factorial:ℚ)/(j.factorial:ℚ))
 unfold coeff
 convert h using 1 <;> push_cast <;> ring

def check (n q d : ℕ) (x L U : ℚ) : Bool :=
 lowerCheck (poly (coeff n q) (x-n) d) (L+error (x-n) d) &&
 upperCheck (poly (coeff n q) (x-n) d) (U-error (x-n) d)

theorem interval {n q d : ℕ} {x L U : ℚ}
 (hn0 : 1 ≤ n) (hn1 : n ≤ 32) (hqd : q+d+1 = 24) (hc : check n q d x L U = true) :
 (L:ℝ) ≤ iteratedDeriv q f x ∧ iteratedDeriv q f x ≤ (U:ℝ) := by
 have hh : lowerCheck (poly (coeff n q) (x-n) d) (L+error (x-n) d) = true ∧
     upperCheck (poly (coeff n q) (x-n) d) (U-error (x-n) d) = true := by
   simpa only [check,Bool.and_eq_true] using hc
 have hp := poly_sound (iteratedDeriv q f) (n:ℝ) (coeff n q) (x-n) d
   (coeff_sound hn0 hn1 (by omega))
 have he : (n:ℝ)+((x-n:ℚ):ℝ) = x := by push_cast; ring
 rw [he] at hp
 have hr := derivative_remainder q d hqd (n:ℝ) x
 have herr : (44/7:ℝ)^24*|((x:ℝ)-n)|^(d+1)/((d+1).factorial:ℝ) = (error (x-n) d:ℝ) := by
   unfold error
   push_cast
   rfl
 rw [herr] at hr
 have hl := lowerCheck_sound hh.1 hp
 have hu := upperCheck_sound hh.2 hp
 push_cast at hl hu
 exact ⟨by linarith [(abs_le.mp hr).1],by linarith [(abs_le.mp hr).2]⟩

set_option pp.fullNames true
#print axioms coeff_sound
#print axioms interval
end StructuralGoal20261016.WindowFixedDerivative
end
