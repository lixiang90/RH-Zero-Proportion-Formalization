/- SPDX-License-Identifier: Apache-2.0
Finite dispatch of the 24 local OBBT payloads; no decoder is trusted.
-/
import StructuralGoal20261016.WindowCurvatureSubtreeData
import StructuralGoal20261016.WindowMixedCover
set_option Elab.async false
set_option maxHeartbeats 0
namespace StructuralGoal20261016.WindowCurvatureOBBTDispatch
open WindowCurvatureSubtreeData
def bound (i : ℕ) : WindowMixedContractions.OBBTBound :=
 match i with
 | 0 => bound00
 | 1 => bound01
 | 2 => bound02
 | 3 => bound03
 | 4 => bound04
 | 5 => bound05
 | 6 => bound06
 | 7 => bound07
 | 8 => bound08
 | 9 => bound09
 | 10 => bound10
 | 11 => bound11
 | 12 => bound12
 | 13 => bound13
 | 14 => bound14
 | 15 => bound15
 | 16 => bound16
 | 17 => bound17
 | 18 => bound18
 | 19 => bound19
 | 20 => bound20
 | 21 => bound21
 | 22 => bound22
 | 23 => bound23
 | _ => bound00
def input (i : ℕ) : DifferenceCell.Cell 10 := if i < 14 then parent else leftParent
end StructuralGoal20261016.WindowCurvatureOBBTDispatch
