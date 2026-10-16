/- SPDX-License-Identifier: Apache-2.0
Actual Fourier kernel and squared-kernel coefficients at integer centre 1.
-/
import StructuralGoal20261016.WindowFixedKernel
import StructuralGoal20261016.WindowFixedKernelPilot
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowFixedKernelCenters
open WindowRationalInterval WindowNormalizedJets WindowJetTableData WindowFixedRational

theorem k_1 : ∀ r ≤ 23, Holds (K 1 r) (kc 24 WindowKernel.d24 r (1:ℝ)) := by
 simpa only [Nat.cast_one] using WindowFixedKernelPilot.k_one
set_option pp.fullNames true
#print axioms k_1

theorem w_1 : ∀ r ≤ 23, Holds (W 1 r) (wc 24 WindowKernel.d24 r (1:ℝ)) := by
 simpa only [Nat.cast_one] using WindowFixedKernelPilot.w_one
set_option pp.fullNames true
#print axioms w_1
end StructuralGoal20261016.WindowFixedKernelCenters
end
