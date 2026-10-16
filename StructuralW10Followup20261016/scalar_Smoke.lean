/- SPDX-License-Identifier: Apache-2.0
Generated concrete scalar data; check the matching kernel receipts.
No global coverage is asserted.
-/
import StructuralW10Followup20261016.scalar_Data
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralW10Followup20261016.Scalar
def q7_0 : Quad := ⟨(17729401 : ℚ)/1000000000, (-51429201123203 : ℚ)/524288000000000, (10786852369244352949168637 : ℚ)/85899345920000000000000000⟩
theorem scalar7_0 {x : ℝ}
    (hl : (low2 : ℝ)≤x) (hu : x≤(top2 : ℝ)) : evalR q7_0 x≤AMW.Cert.wfun x := by
  apply check_sound q7_0 base2 top2 low2 hull2
  · norm_num [q7_0]
  · decide +kernel
  · exact (by norm_num [base2,low2] : (base2 : ℝ)≤(low2 : ℝ)).trans hl
  · exact hl
  · exact hu
#print axioms scalar7_0
end StructuralW10Followup20261016.Scalar
end
