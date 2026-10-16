/- SPDX-License-Identifier: Apache-2.0
Ordinary-kernel pilot of the fraction-free coefficient checker at centre 1.
-/
import StructuralGoal20261016.WindowFixedKernel
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowFixedKernelPilot
open WindowRationalInterval WindowNormalizedJets WindowJetTableData WindowFixedRational

theorem k_one : ∀ r ≤ 23, Holds (K 1 r) (kc 24 WindowKernel.d24 r ((1:ℕ):ℝ)) := by
 have hc : ∀ r : Fin 24, coversQ (WindowFixedKernel.FI.kernel 1 r) (K 1 r) = true := by decide +kernel
 intro r hr
 exact WindowFixedKernel.FI.kernel_of_check (by decide) (by decide) hr (hc ⟨r,by omega⟩)

set_option pp.fullNames true
#print axioms k_one

theorem w_one : ∀ r ≤ 23, Holds (W 1 r) (wc 24 WindowKernel.d24 r ((1:ℕ):ℝ)) := by
 have hc : ∀ r : Fin 24, coversQ (WindowFixedKernel.FI.square 1 r) (W 1 r) = true := by decide +kernel
 intro r hr
 exact WindowFixedKernel.FI.square_of_check (fun j hj => k_one j (by omega)) (hc ⟨r,by omega⟩)

#print axioms w_one
end StructuralGoal20261016.WindowFixedKernelPilot
end
