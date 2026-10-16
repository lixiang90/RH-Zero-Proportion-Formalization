/- SPDX-License-Identifier: Apache-2.0
The actual second derivative is bounded below on every required integer well.
-/
import StructuralGoal20261016.WindowLinearConvexityPiece01
import StructuralGoal20261016.WindowLinearConvexityPiece02
import StructuralGoal20261016.WindowLinearConvexityPiece03
import StructuralGoal20261016.WindowLinearConvexityPiece04
import StructuralGoal20261016.WindowLinearConvexityPiece05
import StructuralGoal20261016.WindowLinearConvexityPiece06
import StructuralGoal20261016.WindowLinearConvexityPiece07
import StructuralGoal20261016.WindowLinearConvexityPiece08
import StructuralGoal20261016.WindowLinearConvexityPiece09
import StructuralGoal20261016.WindowLinearConvexityPiece10
import StructuralGoal20261016.WindowLinearConvexityPiece11
import StructuralGoal20261016.WindowLinearConvexityPiece12
import StructuralGoal20261016.WindowLinearConvexityPiece13
import StructuralGoal20261016.WindowLinearConvexityPiece14
import StructuralGoal20261016.WindowLinearConvexityPiece15
import StructuralGoal20261016.WindowLinearConvexityPiece16
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowConvexityAll
open WindowLinearConvexityPieces WindowConvexityCertificate
def lower (n : ℕ) : ℚ := match n with
 | 1 => (3873922399/20000000000:ℚ)
 | 2 => (74465922661/1000000000000:ℚ)
 | 3 => (13320248721/500000000000:ℚ)
 | 4 => (1855049847/200000000000:ℚ)
 | 5 => (757401027/100000000000:ℚ)
 | 6 => (154987711/50000000000:ℚ)
 | 7 => (1672223599/1000000000000:ℚ)
 | 8 => (405269201/200000000000:ℚ)
 | 9 => (810151971/1000000000000:ℚ)
 | 10 => (166439793/250000000000:ℚ)
 | 11 => (920206897/1000000000000:ℚ)
 | 12 => (658634521/1000000000000:ℚ)
 | 13 => (126662011/100000000000:ℚ)
 | 14 => (1391207459/1000000000000:ℚ)
 | 15 => (788462003/500000000000:ℚ)
 | 16 => (1367944761/1000000000000:ℚ)
 | _ => 0

theorem lower_sound {n : ℕ} (hn0 : 1 ≤ n) (hn1 : n ≤ 16) :
 ∀ x ∈ Icc ((n:ℝ)-21/100) ((n:ℝ)+21/100), (lower n:ℝ) ≤ wSecond x := by
 interval_cases n
 · convert second_lower_1 using 1 <;> norm_num [lower]
 · convert second_lower_2 using 1 <;> norm_num [lower]
 · convert second_lower_3 using 1 <;> norm_num [lower]
 · convert second_lower_4 using 1 <;> norm_num [lower]
 · convert second_lower_5 using 1 <;> norm_num [lower]
 · convert second_lower_6 using 1 <;> norm_num [lower]
 · convert second_lower_7 using 1 <;> norm_num [lower]
 · convert second_lower_8 using 1 <;> norm_num [lower]
 · convert second_lower_9 using 1 <;> norm_num [lower]
 · convert second_lower_10 using 1 <;> norm_num [lower]
 · convert second_lower_11 using 1 <;> norm_num [lower]
 · convert second_lower_12 using 1 <;> norm_num [lower]
 · convert second_lower_13 using 1 <;> norm_num [lower]
 · convert second_lower_14 using 1 <;> norm_num [lower]
 · convert second_lower_15 using 1 <;> norm_num [lower]
 · convert second_lower_16 using 1 <;> norm_num [lower]
set_option pp.fullNames true
#print axioms lower_sound
end StructuralGoal20261016.WindowConvexityAll
end
