/- SPDX-License-Identifier: Apache-2.0
Actual Fourier kernel and squared-kernel coefficients at integer centre 30.
-/
import StructuralGoal20261016.WindowFixedKernel
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
namespace StructuralGoal20261016.WindowFixedKernelCenters
open WindowRationalInterval WindowNormalizedJets WindowJetTableData WindowFixedRational

theorem k_30 : ∀ r ≤ 23, Holds (K 30 r) (kc 24 WindowKernel.d24 r (30:ℝ)) := by
 have hc : ∀ r : Fin 24, coversQ (WindowFixedKernel.FI.kernel 30 r) (K 30 r) = true := by decide +kernel
 intro r hr
 have h := WindowFixedKernel.FI.kernel_of_check (n := 30) (by decide) (by decide) hr (hc ⟨r,by omega⟩)
 simpa only [Nat.cast_ofNat] using h
set_option pp.fullNames true
#print axioms k_30

theorem w_30 : ∀ r ≤ 23, Holds (W 30 r) (wc 24 WindowKernel.d24 r (30:ℝ)) := by
 have hc : ∀ r : Fin 24, coversQ (WindowFixedKernel.FI.square 30 r) (W 30 r) = true := by decide +kernel
 intro r hr
 have h := WindowFixedKernel.FI.square_of_check (n := 30)
   (fun j hj => by simpa only [Nat.cast_ofNat] using k_30 j (by omega)) (hc ⟨r,by omega⟩)
 simpa only [Nat.cast_ofNat] using h
set_option pp.fullNames true
#print axioms w_30
end StructuralGoal20261016.WindowFixedKernelCenters
end
