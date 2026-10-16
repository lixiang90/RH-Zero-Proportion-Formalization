/- SPDX-License-Identifier: Apache-2.0
Actual upper point bounds for the new kernel, using the already proved
fixed-integer polynomial evaluator and the same order-24 Taylor remainder.
-/
import StructuralGoal20261016.WindowFixedPoint
import StructuralGoal20261016.WindowFixedTablesAll
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real
namespace StructuralGoal20261016.WindowFixedUpperPoint
open WindowRationalInterval (Holds)
open WindowFixedPolynomial WindowFixedRational WindowFixedPoint
open WindowNormalizedJets WindowScalarMinorant WindowConvexityCertificate WindowJetTableData
open WindowPointTableArithmetic (valueError)

def valueCheck (n : ℕ) (q U : ℚ) : Bool := upperCheck (valuePoly n q) (U-valueError (q-n))

theorem value_sound {n : ℕ} {q U : ℚ}
 (hW : ∀ j ≤ 23, Holds (W n j) (wc 24 WindowKernel.d24 j (n:ℝ)))
 (hc : valueCheck n q U = true) : f q ≤ (U:ℝ) := by
 have hp := poly_sound f (n:ℝ) (coeff n) (q-n) 23 (fun j hj => ofQI_sound (hW j hj))
 have he : (n:ℝ)+((q-n:ℚ):ℝ) = q := by push_cast; ring
 rw [he] at hp
 have hu := upperCheck_sound hc hp
 have hr := value_remainder (n:ℝ) q
 have herr : (44/7:ℝ)^24*|((q:ℝ)-n)|^24/((24:ℕ).factorial:ℝ) = (valueError (q-n):ℝ) := by
   unfold valueError
   push_cast
   rfl
 rw [herr] at hr
 push_cast at hu
 linarith [(abs_le.mp hr).2]

theorem actual_upper {n : ℕ} {q U : ℚ} (hn0 : 1 ≤ n) (hn1 : n ≤ 32)
 (hc : valueCheck n q U = true) : f q ≤ (U:ℝ) :=
 value_sound (fun j hj => WindowFixedTablesAll.w_sound hn0 hn1 j hj) hc

set_option pp.fullNames true
#print axioms value_sound
#print axioms actual_upper
end StructuralGoal20261016.WindowFixedUpperPoint
end
