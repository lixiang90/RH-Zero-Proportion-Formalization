/- SPDX-License-Identifier: Apache-2.0
The KKT predicate for the actual new-window gradient follows from genuine
orthant minimality. Cell faces play no role in the complementarity condition.
-/
import StructuralGoal20261016.WindowMinimizerCover
import StructuralGoal20261016.CoverKKTContraction
set_option Elab.async false
noncomputable section

namespace StructuralGoal20261016.WindowKKTInstance
open WindowGapEnergy WindowMinimizerCover

theorem of_relevant {sep : ℝ} {g : Fin 9 → ℝ} (hg : Relevant sep g) :
    CoverKKTContraction.KKT sep g
      (gradient StructuralW10Followup20261016.NewLedger.W g) := by
  constructor
  · intro r
    exact CoverCoerciveKKT.gradient_nonneg hg.1 hg.2.2 r
      (coordinate_hasDerivAt StructuralW10Followup20261016.NewLedger.W g r)
  · intro r hr
    exact CoverCoerciveKKT.gradient_eq_zero hg.1 hg.2.2 r hr
      (coordinate_hasDerivAt StructuralW10Followup20261016.NewLedger.W g r)

theorem of_relevantBelow {sep c : ℝ} {g : Fin 9 → ℝ}
    (hg : RelevantBelow sep c g) :
    CoverKKTContraction.KKT sep g
      (gradient StructuralW10Followup20261016.NewLedger.W g) :=
  of_relevant hg.1

#print axioms of_relevant
#print axioms of_relevantBelow
end StructuralGoal20261016.WindowKKTInstance
end
