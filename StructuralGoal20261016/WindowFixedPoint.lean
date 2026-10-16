/- SPDX-License-Identifier: Apache-2.0
Actual value and slope certificates using the fraction-free Horner checker.
The Taylor remainder is supplied by the proved global Fourier derivative
bound, rather than by a numerical smoothness assumption.
-/
import StructuralGoal20261016.WindowFixedPolynomial
import StructuralGoal20261016.WindowJetTableData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real
namespace StructuralGoal20261016.WindowFixedPoint
open WindowRationalInterval (Holds)
open WindowFixedInterval WindowFixedRational WindowFixedPolynomial
open WindowNormalizedJets WindowScalarMinorant WindowConvexityCertificate
open WindowPointTableArithmetic (valueError slopeError)
open WindowJetTableData

def coeff (n j : ℕ) : FI := ofQI (W n j)
def slopeCoeff (n j : ℕ) : FI := scale (coeff n (j+1)) (j+1)
def valuePoly (n : ℕ) (q : ℚ) : FI := poly (coeff n) (q-n) 23
def slopePoly (n : ℕ) (q : ℚ) : FI := poly (slopeCoeff n) (q-n) 22
def valueCheck (n : ℕ) (q V : ℚ) : Bool := lowerCheck (valuePoly n q) (V+valueError (q-n))
def slopeCheck (n : ℕ) (q T ε : ℚ) : Bool :=
 lowerCheck (slopePoly n q) (T-ε+slopeError (q-n)) &&
 upperCheck (slopePoly n q) (T+ε-slopeError (q-n))

theorem slopeCoeff_sound {n : ℕ}
 (hW : ∀ j ≤ 23, Holds (W n j) (wc 24 WindowKernel.d24 j (n:ℝ))) :
 ∀ j ≤ 22, Holds (decode (slopeCoeff n j))
   (iteratedDeriv j (iteratedDeriv 1 f) (n:ℝ)/(j.factorial:ℝ)) := by
 intro j hj
 rw [WindowConvexityArithmetic.first_coeff]
 have h := scale_sound (ofQI_sound (hW (j+1) (by omega))) (j+1)
 unfold slopeCoeff coeff
 convert h using 1 <;> push_cast <;> ring

theorem value_sound {n : ℕ} {q V : ℚ}
 (hW : ∀ j ≤ 23, Holds (W n j) (wc 24 WindowKernel.d24 j (n:ℝ)))
 (hc : valueCheck n q V = true) : (V:ℝ) ≤ f q := by
 have hp := poly_sound f (n:ℝ) (coeff n) (q-n) 23 (fun j hj => ofQI_sound (hW j hj))
 have he : (n:ℝ)+((q-n:ℚ):ℝ) = q := by push_cast; ring
 rw [he] at hp
 have hl := lowerCheck_sound hc hp
 apply value_lower_from_taylor (p := (n:ℝ)) (x := (q:ℝ)) (R := (valueError (q-n):ℝ))
 · unfold valueError
   push_cast
   exact le_rfl
 · simpa only [Rat.cast_add] using hl

theorem slope_sound {n : ℕ} {q T ε : ℚ}
 (hW : ∀ j ≤ 23, Holds (W n j) (wc 24 WindowKernel.d24 j (n:ℝ)))
 (hc : slopeCheck n q T ε = true) : |iteratedDeriv 1 f q-(T:ℝ)| ≤ (ε:ℝ) := by
 have hc' : lowerCheck (slopePoly n q) (T-ε+slopeError (q-n)) = true ∧
     upperCheck (slopePoly n q) (T+ε-slopeError (q-n)) = true := by
   simpa only [slopeCheck,Bool.and_eq_true] using hc
 have hp := poly_sound (iteratedDeriv 1 f) (n:ℝ) (slopeCoeff n) (q-n) 22 (slopeCoeff_sound hW)
 have he : (n:ℝ)+((q-n:ℚ):ℝ) = q := by push_cast; ring
 rw [he] at hp
 have hl := lowerCheck_sound hc'.1 hp
 have hu := upperCheck_sound hc'.2 hp
 have hi : ((T-ε:ℚ):ℝ) ≤ iteratedDeriv 1 f q ∧ iteratedDeriv 1 f q ≤ ((T+ε:ℚ):ℝ) := by
   apply slope_interval_from_taylor (p := (n:ℝ)) (x := (q:ℝ)) (R := (slopeError (q-n):ℝ))
   · unfold slopeError
     push_cast
     exact le_rfl
   · simpa only [Rat.cast_add] using hl
   · simpa only [Rat.cast_sub] using hu
 push_cast at hi
 rw [abs_le]
 constructor <;> linarith [hi.1,hi.2]

set_option pp.fullNames true
#print axioms value_sound
#print axioms slope_sound
end StructuralGoal20261016.WindowFixedPoint
end
