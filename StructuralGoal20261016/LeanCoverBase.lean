/- SPDX-License-Identifier: Apache-2.0
Checkpointable composition of the complete frozen W10 tree.  Each terminal
module proves its actual finite subtree with the ordinary Lean kernel. -/
import StructuralW10Unconditional20261016.FixedGeometry
import StructuralW10Cert20261016.ForcedCoverage2
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
open StructuralW10Cert20261016.TreeCoverage
namespace StructuralGoal20261016.LeanCoverBase
def SL : List ℕ := [0, 0, 9, 10, 11, 12, 13, 14, 15, 16, 0, 0, 1, 17, 18, 19, 20, 21, 22, 23, 9, 1, 0, 2, 24, 25, 26, 27, 28, 29, 10, 17, 2, 0, 3, 30, 31, 32, 33, 34, 11, 18, 24, 3, 0, 4, 35, 36, 37, 38, 12, 19, 25, 30, 4, 0, 5, 39, 40, 41, 13, 20, 26, 31, 35, 5, 0, 6, 42, 43, 14, 21, 27, 32, 36, 39, 6, 0, 7, 44, 15, 22, 28, 33, 37, 40, 42, 7, 0, 8, 16, 23, 29, 34, 38, 41, 43, 44, 8, 0]
theorem hSL : SLok 9 PR SL := by decide +kernel
theorem branch {c normal left right : Cl} (i j q : ℕ)
    (hi : i < j) (hj : j ≤ 9)
    (hn : StructuralW10Cert20261016.AdaptiveCoverage.normalize SL c = normal)
    (hl : leftChild 9 PR SL normal i j q = left)
    (hr : rightChild 9 PR SL normal i j q = right)
    (hleft : CovBy 9 PR (Pg cN 9 BS TS) left)
    (hright : CovBy 9 PR (Pg cN 9 BS TS) right) :
    CovBy 9 PR (Pg cN 9 BS TS) c := by
  apply StructuralW10Cert20261016.AdaptiveCoverage.normalize_sound hSL
  rw [hn]
  have hl' : CovBy 9 PR (Pg cN 9 BS TS) (leftChild 9 PR SL normal i j q) := by
    rw [hl]
    exact hleft
  have hr' : CovBy 9 PR (Pg cN 9 BS TS) (rightChild 9 PR SL normal i j q) := by
    rw [hr]
    exact hright
  exact cov_splitB hSL hPR hi hj q hl' hr'
#print axioms branch
end StructuralGoal20261016.LeanCoverBase
end
