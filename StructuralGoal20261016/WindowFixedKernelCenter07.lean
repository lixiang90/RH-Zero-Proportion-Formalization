/- SPDX-License-Identifier: Apache-2.0
Actual Fourier kernel and squared-kernel coefficients at integer centre 7.
-/
import StructuralGoal20261016.WindowFixedKernel
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowFixedKernelCenters
open WindowRationalInterval WindowNormalizedJets WindowJetTableData WindowFixedRational

theorem k_7 : ∀ r ≤ 23, Holds (K 7 r) (kc 24 WindowKernel.d24 r (7:ℝ)) := by
 have hc : ∀ r : Fin 24, coversQ (WindowFixedKernel.FI.kernel 7 r) (K 7 r) = true := by decide +kernel
 intro r hr
 have h := WindowFixedKernel.FI.kernel_of_check (n := 7) (by decide) (by decide) hr (hc ⟨r,by omega⟩)
 simpa only [Nat.cast_ofNat] using h
set_option pp.fullNames true
#print axioms k_7

theorem w_7 : ∀ r ≤ 23, Holds (W 7 r) (wc 24 WindowKernel.d24 r (7:ℝ)) := by
 have hc : ∀ r : Fin 24, coversQ (WindowFixedKernel.FI.square 7 r) (W 7 r) = true := by decide +kernel
 intro r hr
 have h := WindowFixedKernel.FI.square_of_check (n := 7)
   (fun j hj => by simpa only [Nat.cast_ofNat] using k_7 j (by omega)) (hc ⟨r,by omega⟩)
 simpa only [Nat.cast_ofNat] using h
set_option pp.fullNames true
#print axioms w_7
end StructuralGoal20261016.WindowFixedKernelCenters
end
