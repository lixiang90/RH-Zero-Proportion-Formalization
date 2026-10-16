/- SPDX-License-Identifier: Apache-2.0
Actual Fourier kernel and squared-kernel coefficients at integer centre 15.
-/
import StructuralGoal20261016.WindowFixedKernel
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowFixedKernelCenters
open WindowRationalInterval WindowNormalizedJets WindowJetTableData WindowFixedRational

theorem k_15 : ∀ r ≤ 23, Holds (K 15 r) (kc 24 WindowKernel.d24 r (15:ℝ)) := by
 have hc : ∀ r : Fin 24, coversQ (WindowFixedKernel.FI.kernel 15 r) (K 15 r) = true := by decide +kernel
 intro r hr
 have h := WindowFixedKernel.FI.kernel_of_check (n := 15) (by decide) (by decide) hr (hc ⟨r,by omega⟩)
 simpa only [Nat.cast_ofNat] using h
set_option pp.fullNames true
#print axioms k_15

theorem w_15 : ∀ r ≤ 23, Holds (W 15 r) (wc 24 WindowKernel.d24 r (15:ℝ)) := by
 have hc : ∀ r : Fin 24, coversQ (WindowFixedKernel.FI.square 15 r) (W 15 r) = true := by decide +kernel
 intro r hr
 have h := WindowFixedKernel.FI.square_of_check (n := 15)
   (fun j hj => by simpa only [Nat.cast_ofNat] using k_15 j (by omega)) (hc ⟨r,by omega⟩)
 simpa only [Nat.cast_ofNat] using h
set_option pp.fullNames true
#print axioms w_15
end StructuralGoal20261016.WindowFixedKernelCenters
end
