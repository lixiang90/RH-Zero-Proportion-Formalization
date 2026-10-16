/- SPDX-License-Identifier: Apache-2.0
Partial replay surface only. No global energy floor is asserted here.
The counting roots retain their explicit Floor premise.
-/
import StructuralGoal20261016.WindowAnchorAll
import StructuralGoal20261016.WindowLinearConvexityPilot
import StructuralGoal20261016.WindowRecordFromFloor
import StructuralGoal20261016.WindowRecordDyadic
import StructuralGoal20261016.WindowPressureRoot
import StructuralGoal20261016.WindowKKTInstance
import StructuralGoal20261016.WindowSecondVariation
import StructuralGoal20261016.WindowQuantizedSupport
import StructuralGoal20261016.DifferenceCell
import StructuralGoal20261016.FlowBasisPilot
set_option Elab.async false
set_option pp.fullNames true
#print axioms StructuralGoal20261016.WindowFixedTablesAll.k_sound
#print axioms StructuralGoal20261016.WindowFixedTablesAll.w_sound
#print axioms StructuralGoal20261016.WindowAnchorAll.valid
#print axioms StructuralGoal20261016.WindowLinearConvexityPilot.cell
#print axioms StructuralGoal20261016.WindowPairCertificate.short_pair_floor
#print axioms StructuralGoal20261016.WindowGapEnergy.exists_ordered_global_min
#print axioms StructuralGoal20261016.WindowPressureRoot.selected_span_upper
#print axioms StructuralGoal20261016.WindowPressureRoot.global_floor_of_checked
#print axioms StructuralGoal20261016.WindowKKTInstance.of_relevantBelow
#print axioms StructuralGoal20261016.WindowSecondVariation.curvature_nonneg_of_relevant
#print axioms StructuralGoal20261016.WindowQuantizedSupport.zero_extension
#print axioms StructuralGoal20261016.DifferenceCell.split_sound
#print axioms StructuralGoal20261016.DifferenceCell.affine_flow_bound
#print axioms StructuralGoal20261016.FlowBasisPilot.bound0
#print axioms StructuralGoal20261016.FlowBasisPilot.bound1
#print axioms StructuralGoal20261016.FlowBasisPilot.bound2
#print axioms StructuralGoal20261016.FlowBasisPilot.bound3
#print axioms StructuralGoal20261016.WindowRecordFromFloor.improvement
#print axioms StructuralGoal20261016.WindowRecordFromFloor.simple_cumulative
#print axioms StructuralGoal20261016.WindowRecordFromFloor.distinct_cumulative
#print axioms StructuralGoal20261016.WindowRecordDyadic.simple_dyadic
#print axioms StructuralGoal20261016.WindowRecordDyadic.distinct_dyadic
