/- SPDX-License-Identifier: Apache-2.0
Actual normalized coefficients at every required integer centre.
-/
import StructuralGoal20261016.WindowFixedKernelCenter01
import StructuralGoal20261016.WindowFixedKernelCenter02
import StructuralGoal20261016.WindowFixedKernelCenter03
import StructuralGoal20261016.WindowFixedKernelCenter04
import StructuralGoal20261016.WindowFixedKernelCenter05
import StructuralGoal20261016.WindowFixedKernelCenter06
import StructuralGoal20261016.WindowFixedKernelCenter07
import StructuralGoal20261016.WindowFixedKernelCenter08
import StructuralGoal20261016.WindowFixedKernelCenter09
import StructuralGoal20261016.WindowFixedKernelCenter10
import StructuralGoal20261016.WindowFixedKernelCenter11
import StructuralGoal20261016.WindowFixedKernelCenter12
import StructuralGoal20261016.WindowFixedKernelCenter13
import StructuralGoal20261016.WindowFixedKernelCenter14
import StructuralGoal20261016.WindowFixedKernelCenter15
import StructuralGoal20261016.WindowFixedKernelCenter16
import StructuralGoal20261016.WindowFixedKernelCenter17
import StructuralGoal20261016.WindowFixedKernelCenter18
import StructuralGoal20261016.WindowFixedKernelCenter19
import StructuralGoal20261016.WindowFixedKernelCenter20
import StructuralGoal20261016.WindowFixedKernelCenter21
import StructuralGoal20261016.WindowFixedKernelCenter22
import StructuralGoal20261016.WindowFixedKernelCenter23
import StructuralGoal20261016.WindowFixedKernelCenter24
import StructuralGoal20261016.WindowFixedKernelCenter25
import StructuralGoal20261016.WindowFixedKernelCenter26
import StructuralGoal20261016.WindowFixedKernelCenter27
import StructuralGoal20261016.WindowFixedKernelCenter28
import StructuralGoal20261016.WindowFixedKernelCenter29
import StructuralGoal20261016.WindowFixedKernelCenter30
import StructuralGoal20261016.WindowFixedKernelCenter31
import StructuralGoal20261016.WindowFixedKernelCenter32
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
namespace StructuralGoal20261016.WindowFixedTablesAll
open WindowRationalInterval WindowNormalizedJets WindowJetTableData WindowFixedKernelCenters

theorem k_sound {n : ℕ} (hn0 : 1 ≤ n) (hn1 : n ≤ 32) (r : ℕ) (hr : r ≤ 23) :
 Holds (K n r) (kc 24 WindowKernel.d24 r (n:ℝ)) := by
 interval_cases n
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_1 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_2 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_3 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_4 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_5 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_6 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_7 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_8 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_9 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_10 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_11 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_12 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_13 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_14 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_15 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_16 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_17 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_18 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_19 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_20 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_21 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_22 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_23 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_24 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_25 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_26 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_27 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_28 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_29 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_30 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_31 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using k_32 r hr
set_option pp.fullNames true
#print axioms k_sound

theorem w_sound {n : ℕ} (hn0 : 1 ≤ n) (hn1 : n ≤ 32) (r : ℕ) (hr : r ≤ 23) :
 Holds (W n r) (wc 24 WindowKernel.d24 r (n:ℝ)) := by
 interval_cases n
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_1 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_2 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_3 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_4 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_5 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_6 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_7 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_8 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_9 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_10 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_11 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_12 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_13 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_14 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_15 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_16 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_17 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_18 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_19 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_20 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_21 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_22 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_23 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_24 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_25 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_26 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_27 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_28 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_29 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_30 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_31 r hr
 · simpa only [Nat.cast_one,Nat.cast_ofNat] using w_32 r hr
set_option pp.fullNames true
#print axioms w_sound
end StructuralGoal20261016.WindowFixedTablesAll
end
