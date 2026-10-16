/- SPDX-License-Identifier: Apache-2.0
Assemble the checked elementary moment tables over the required finite range.
-/
import StructuralGoal20261016.WindowJetTableBase00
import StructuralGoal20261016.WindowJetTableBase01
import StructuralGoal20261016.WindowJetTableBase02
import StructuralGoal20261016.WindowJetTableBase03
import StructuralGoal20261016.WindowJetTableBase04
import StructuralGoal20261016.WindowJetTableBase05
import StructuralGoal20261016.WindowJetTableBase06
import StructuralGoal20261016.WindowJetTableBase07
import StructuralGoal20261016.WindowJetTableCos00
import StructuralGoal20261016.WindowJetTableCos01
import StructuralGoal20261016.WindowJetTableCos02
import StructuralGoal20261016.WindowJetTableCos03
import StructuralGoal20261016.WindowJetTableCos04
import StructuralGoal20261016.WindowJetTableCos05
import StructuralGoal20261016.WindowJetTableCos06
import StructuralGoal20261016.WindowJetTableCos07
import StructuralGoal20261016.WindowJetTableCos08
import StructuralGoal20261016.WindowJetTableCos09
import StructuralGoal20261016.WindowJetTableCos10

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowJetTablesAll
set_option pp.fullNames true
open WindowRationalInterval WindowNormalizedJets WindowIntegerJetRecipe
open WindowIntegerKernelRecipe WindowJetTableData WindowJetTableBounds
theorem base_sound {n : ℕ} (hn0 : 1 ≤ n) (hn1 : n ≤ 32)
 (s : Bool) : ∀ r ≤ 23, Holds (Base n s r) (b r (baseZ n s)) := by
 intro r hr
 interval_cases n <;> cases s <;> first
 | exact base_1_false r hr
 | exact base_1_true r hr
 | exact base_2_false r hr
 | exact base_2_true r hr
 | exact base_3_false r hr
 | exact base_3_true r hr
 | exact base_4_false r hr
 | exact base_4_true r hr
 | exact base_5_false r hr
 | exact base_5_true r hr
 | exact base_6_false r hr
 | exact base_6_true r hr
 | exact base_7_false r hr
 | exact base_7_true r hr
 | exact base_8_false r hr
 | exact base_8_true r hr
 | exact base_9_false r hr
 | exact base_9_true r hr
 | exact base_10_false r hr
 | exact base_10_true r hr
 | exact base_11_false r hr
 | exact base_11_true r hr
 | exact base_12_false r hr
 | exact base_12_true r hr
 | exact base_13_false r hr
 | exact base_13_true r hr
 | exact base_14_false r hr
 | exact base_14_true r hr
 | exact base_15_false r hr
 | exact base_15_true r hr
 | exact base_16_false r hr
 | exact base_16_true r hr
 | exact base_17_false r hr
 | exact base_17_true r hr
 | exact base_18_false r hr
 | exact base_18_true r hr
 | exact base_19_false r hr
 | exact base_19_true r hr
 | exact base_20_false r hr
 | exact base_20_true r hr
 | exact base_21_false r hr
 | exact base_21_true r hr
 | exact base_22_false r hr
 | exact base_22_true r hr
 | exact base_23_false r hr
 | exact base_23_true r hr
 | exact base_24_false r hr
 | exact base_24_true r hr
 | exact base_25_false r hr
 | exact base_25_true r hr
 | exact base_26_false r hr
 | exact base_26_true r hr
 | exact base_27_false r hr
 | exact base_27_true r hr
 | exact base_28_false r hr
 | exact base_28_true r hr
 | exact base_29_false r hr
 | exact base_29_true r hr
 | exact base_30_false r hr
 | exact base_30_true r hr
 | exact base_31_false r hr
 | exact base_31_true r hr
 | exact base_32_false r hr
 | exact base_32_true r hr

theorem cos_sound {m : ℤ} (hm0 : -24 ≤ m) (hm1 : m ≤ 56) :
 ∀ r ≤ 23, Holds (Cos m r) (b r (Real.pi*(m:ℝ))) := by
 intro r hr
 interval_cases m <;> first
 | exact cos_neg24 r hr
 | exact cos_neg23 r hr
 | exact cos_neg22 r hr
 | exact cos_neg21 r hr
 | exact cos_neg20 r hr
 | exact cos_neg19 r hr
 | exact cos_neg18 r hr
 | exact cos_neg17 r hr
 | exact cos_neg16 r hr
 | exact cos_neg15 r hr
 | exact cos_neg14 r hr
 | exact cos_neg13 r hr
 | exact cos_neg12 r hr
 | exact cos_neg11 r hr
 | exact cos_neg10 r hr
 | exact cos_neg9 r hr
 | exact cos_neg8 r hr
 | exact cos_neg7 r hr
 | exact cos_neg6 r hr
 | exact cos_neg5 r hr
 | exact cos_neg4 r hr
 | exact cos_neg3 r hr
 | exact cos_neg2 r hr
 | exact cos_neg1 r hr
 | exact cos_0 r hr
 | exact cos_1 r hr
 | exact cos_2 r hr
 | exact cos_3 r hr
 | exact cos_4 r hr
 | exact cos_5 r hr
 | exact cos_6 r hr
 | exact cos_7 r hr
 | exact cos_8 r hr
 | exact cos_9 r hr
 | exact cos_10 r hr
 | exact cos_11 r hr
 | exact cos_12 r hr
 | exact cos_13 r hr
 | exact cos_14 r hr
 | exact cos_15 r hr
 | exact cos_16 r hr
 | exact cos_17 r hr
 | exact cos_18 r hr
 | exact cos_19 r hr
 | exact cos_20 r hr
 | exact cos_21 r hr
 | exact cos_22 r hr
 | exact cos_23 r hr
 | exact cos_24 r hr
 | exact cos_25 r hr
 | exact cos_26 r hr
 | exact cos_27 r hr
 | exact cos_28 r hr
 | exact cos_29 r hr
 | exact cos_30 r hr
 | exact cos_31 r hr
 | exact cos_32 r hr
 | exact cos_33 r hr
 | exact cos_34 r hr
 | exact cos_35 r hr
 | exact cos_36 r hr
 | exact cos_37 r hr
 | exact cos_38 r hr
 | exact cos_39 r hr
 | exact cos_40 r hr
 | exact cos_41 r hr
 | exact cos_42 r hr
 | exact cos_43 r hr
 | exact cos_44 r hr
 | exact cos_45 r hr
 | exact cos_46 r hr
 | exact cos_47 r hr
 | exact cos_48 r hr
 | exact cos_49 r hr
 | exact cos_50 r hr
 | exact cos_51 r hr
 | exact cos_52 r hr
 | exact cos_53 r hr
 | exact cos_54 r hr
 | exact cos_55 r hr
 | exact cos_56 r hr

#print axioms base_sound
#print axioms cos_sound
end StructuralGoal20261016.WindowJetTablesAll
end
