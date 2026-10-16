/- SPDX-License-Identifier: Apache-2.0
A compact certificate row for an actual value and slope of the new kernel.
The row is untrusted data; the final finite checker verifies its centre
range and both Taylor inequalities before the analytic soundness theorem.
-/
import StructuralGoal20261016.WindowFixedTablesAll
import StructuralGoal20261016.WindowFixedPoint
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real
namespace StructuralGoal20261016.WindowAnchorCertificate
open WindowFixedPoint WindowScalarMinorant

structure Row where
 center : ℕ
 anchor : ℚ
 lower : ℚ
 slope : ℚ
 error : ℚ

def defaultRow : Row := ⟨1,1,0,0,0⟩
def check (r : Row) : Bool := decide (1 ≤ r.center ∧ r.center ≤ 32 ∧
 valueCheck r.center r.anchor r.lower = true ∧
 slopeCheck r.center r.anchor r.slope r.error = true)
def Valid (r : Row) : Prop := (r.lower:ℝ) ≤ f r.anchor ∧
 |iteratedDeriv 1 f r.anchor-(r.slope:ℝ)| ≤ (r.error:ℝ)

theorem sound {r : Row} (hc : check r = true) : Valid r := by
 have h : 1 ≤ r.center ∧ r.center ≤ 32 ∧
     valueCheck r.center r.anchor r.lower = true ∧
     slopeCheck r.center r.anchor r.slope r.error = true := of_decide_eq_true hc
 have hw := fun j hj => WindowFixedTablesAll.w_sound h.1 h.2.1 j hj
 exact ⟨WindowFixedPoint.value_sound hw h.2.2.1,WindowFixedPoint.slope_sound hw h.2.2.2⟩

set_option pp.fullNames true
#print axioms sound
end StructuralGoal20261016.WindowAnchorCertificate
end
