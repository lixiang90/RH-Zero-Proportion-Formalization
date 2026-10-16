/- SPDX-License-Identifier: Apache-2.0
Transfer checked rational inputs into the fixed integer arithmetic, and
transfer a fixed-integer computation back to a rational output interval.
-/
import StructuralGoal20261016.WindowFixedInterval
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
namespace StructuralGoal20261016.WindowFixedRational
open WindowRationalInterval WindowFixedInterval

def ofQI (I : QI) : FI := (⌊I.1*(S:ℚ)⌋,⌈I.2*(S:ℚ)⌉)
def coversQ (I : FI) (J : QI) : Bool :=
 decide (J.1*(S:ℚ) ≤ (I.1:ℚ) ∧ (I.2:ℚ) ≤ J.2*(S:ℚ))

theorem decode_ofQI (I : QI) : decode (ofQI I) = WindowRationalInterval.round I := by
 unfold decode ofQI WindowRationalInterval.round WindowRationalInterval.floorQ WindowRationalInterval.ceilQ
 norm_num [S,WindowRationalInterval.scale]

theorem ofQI_sound {I : QI} {x : ℝ} (h : Holds I x) : Holds (decode (ofQI I)) x := by
 rw [decode_ofQI]
 exact WindowRationalInterval.round_sound h

theorem coversQ_sound {I : FI} {J : QI} {x : ℝ}
 (h : coversQ I J = true) (hx : Holds (decode I) x) : Holds J x := by
 have he : J.1*(S:ℚ) ≤ (I.1:ℚ) ∧ (I.2:ℚ) ≤ J.2*(S:ℚ) := of_decide_eq_true h
 apply WindowRationalInterval.widen hx
 · exact (le_div_iff₀ SQ_pos).mpr he.1
 · exact (div_le_iff₀ SQ_pos).mpr he.2

set_option pp.fullNames true
#print axioms ofQI_sound
#print axioms coversQ_sound
end StructuralGoal20261016.WindowFixedRational
end
