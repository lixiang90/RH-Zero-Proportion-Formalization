/- SPDX-License-Identifier: Apache-2.0
Actual new-window energy floor in coherent integer basin 0.
All 41 scalar inequalities come from the common checked row minorants.
-/
import StructuralGoal20261016.WindowScalarBridge
import StructuralGoal20261016.WindowGramTransferPart00
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set
open Zeta23Ext.Bridge Zeta23Ext.BridgeW
namespace StructuralGoal20261016.WindowActualBasins
open WindowGramTransfer WindowGramBasins WindowScalarBridge WindowAnchorCertificateData

def index0 : Fin 41 → ℕ := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40]
def Region0 (g : Fin 9 → ℝ) : Prop := ∀ t : Fin 41,
 span g t ∈ Icc (((row (index0 t)).center:ℝ)-21/100) (((row (index0 t)).center:ℝ)+21/100)

theorem index0_lt (t : Fin 41) : index0 t < 1567 := by fin_cases t <;> decide

theorem scalar0_eq (g : Fin 9 → ℝ) (t : Fin 41) :
 WindowGramTransfer.scalar0 g t = minorant (row (index0 t)) (span g t) := by
 unfold WindowGramTransfer.scalar0
 suffices ∀ x : ℝ, V0 t+S0 t*(x-span q0 t)+A0 t*(x-span q0 t)^2 =
     minorant (row (index0 t)) x from this (span g t)
 intro x
 fin_cases t <;>
   norm_num [V0,S0,A0,q0,span,pairI,pairJ,ptsN,index0,minorant,radius,
     WindowConvexityAll.lower,WindowAnchorCertificateData.row,WindowAnchorCertificateData.rows00,
     Fin.sum_univ_succ,Fin.succ] <;> ring

theorem actual0 (g : Fin 9 → ℝ) (hregion : Region0 g) :
 (221:ℝ)/25000 ≤ WindowGapEnergy.Fw24 g := by
 apply WindowGramTransfer.actual0 g
 intro t
 rw [scalar0_eq]
 exact WindowScalarBridge.actual (index0 t) (index0_lt t) (hregion t)

set_option pp.fullNames true
#print axioms actual0
end StructuralGoal20261016.WindowActualBasins
end
