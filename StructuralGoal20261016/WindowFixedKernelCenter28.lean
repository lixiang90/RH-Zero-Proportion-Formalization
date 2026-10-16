/- SPDX-License-Identifier: Apache-2.0
Actual Fourier kernel and squared-kernel coefficients at integer centre 28.
-/
import StructuralGoal20261016.WindowFixedKernel
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowFixedKernelCenters
open WindowRationalInterval WindowNormalizedJets WindowJetTableData WindowFixedRational

theorem k_28 : ∀ r ≤ 23, Holds (K 28 r) (kc 24 WindowKernel.d24 r (28:ℝ)) := by
 have hc : ∀ r : Fin 24, coversQ (WindowFixedKernel.FI.kernel 28 r) (K 28 r) = true := by decide +kernel
 intro r hr
 have h := WindowFixedKernel.FI.kernel_of_check (n := 28) (by decide) (by decide) hr (hc ⟨r,by omega⟩)
 simpa only [Nat.cast_ofNat] using h
set_option pp.fullNames true
#print axioms k_28

theorem w_28 : ∀ r ≤ 23, Holds (W 28 r) (wc 24 WindowKernel.d24 r (28:ℝ)) := by
 have hc : ∀ r : Fin 24, coversQ (WindowFixedKernel.FI.square 28 r) (W 28 r) = true := by decide +kernel
 intro r hr
 have h := WindowFixedKernel.FI.square_of_check (n := 28)
   (fun j hj => by simpa only [Nat.cast_ofNat] using k_28 j (by omega)) (hc ⟨r,by omega⟩)
 simpa only [Nat.cast_ofNat] using h
set_option pp.fullNames true
#print axioms w_28
end StructuralGoal20261016.WindowFixedKernelCenters
end
