/- SPDX-License-Identifier: Apache-2.0
The eight relative-cell Bernstein weight functions, evaluated by the proved
integer numerator formula. No separate rational weight table is required.
-/
import StructuralGoal20261016.WindowBernsteinIntegerWeights
set_option Elab.async false
set_option maxHeartbeats 0
namespace StructuralGoal20261016.WindowBernsteinFastWeights
open WindowBernsteinLinear
def weights0 (u i : ℕ) : ℚ := WindowBernsteinIntegerWeights.weights (-84) u i
theorem weights0_eq (u i : ℕ) :
 weights0 u i = weightQ (-21/100:ℚ) (21/400) u i := by
 have h := WindowBernsteinIntegerWeights.weights_eq (-84) u i
 simpa only [weights0,show ((-84:ℤ):ℚ)/400 = (-21/100:ℚ) by norm_num] using h
def weights1 (u i : ℕ) : ℚ := WindowBernsteinIntegerWeights.weights (-63) u i
theorem weights1_eq (u i : ℕ) :
 weights1 u i = weightQ (-63/400:ℚ) (21/400) u i := by
 have h := WindowBernsteinIntegerWeights.weights_eq (-63) u i
 simpa only [weights1,show ((-63:ℤ):ℚ)/400 = (-63/400:ℚ) by norm_num] using h
def weights2 (u i : ℕ) : ℚ := WindowBernsteinIntegerWeights.weights (-42) u i
theorem weights2_eq (u i : ℕ) :
 weights2 u i = weightQ (-21/200:ℚ) (21/400) u i := by
 have h := WindowBernsteinIntegerWeights.weights_eq (-42) u i
 simpa only [weights2,show ((-42:ℤ):ℚ)/400 = (-21/200:ℚ) by norm_num] using h
def weights3 (u i : ℕ) : ℚ := WindowBernsteinIntegerWeights.weights (-21) u i
theorem weights3_eq (u i : ℕ) :
 weights3 u i = weightQ (-21/400:ℚ) (21/400) u i := by
 have h := WindowBernsteinIntegerWeights.weights_eq (-21) u i
 simpa only [weights3,show ((-21:ℤ):ℚ)/400 = (-21/400:ℚ) by norm_num] using h
def weights4 (u i : ℕ) : ℚ := WindowBernsteinIntegerWeights.weights (0) u i
theorem weights4_eq (u i : ℕ) :
 weights4 u i = weightQ (0/1:ℚ) (21/400) u i := by
 have h := WindowBernsteinIntegerWeights.weights_eq (0) u i
 simpa only [weights4,show ((0:ℤ):ℚ)/400 = (0/1:ℚ) by norm_num] using h
def weights5 (u i : ℕ) : ℚ := WindowBernsteinIntegerWeights.weights (21) u i
theorem weights5_eq (u i : ℕ) :
 weights5 u i = weightQ (21/400:ℚ) (21/400) u i := by
 have h := WindowBernsteinIntegerWeights.weights_eq (21) u i
 simpa only [weights5,show ((21:ℤ):ℚ)/400 = (21/400:ℚ) by norm_num] using h
def weights6 (u i : ℕ) : ℚ := WindowBernsteinIntegerWeights.weights (42) u i
theorem weights6_eq (u i : ℕ) :
 weights6 u i = weightQ (21/200:ℚ) (21/400) u i := by
 have h := WindowBernsteinIntegerWeights.weights_eq (42) u i
 simpa only [weights6,show ((42:ℤ):ℚ)/400 = (21/200:ℚ) by norm_num] using h
def weights7 (u i : ℕ) : ℚ := WindowBernsteinIntegerWeights.weights (63) u i
theorem weights7_eq (u i : ℕ) :
 weights7 u i = weightQ (63/400:ℚ) (21/400) u i := by
 have h := WindowBernsteinIntegerWeights.weights_eq (63) u i
 simpa only [weights7,show ((63:ℤ):ℚ)/400 = (63/400:ℚ) by norm_num] using h
set_option pp.fullNames true
#print axioms weights0_eq
#print axioms weights7_eq
end StructuralGoal20261016.WindowBernsteinFastWeights
