/- SPDX-License-Identifier: Apache-2.0
Actual Fw24 transfer from 41 explicit scalar minorants per coherent basin.
The actual-kernel scalar inequalities remain hypotheses. No global floor is
asserted without those analytic hypotheses and a complete chamber cover.
-/
import StructuralGoal20261016.WindowGapEnergy
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
noncomputable section
open Finset
open scoped BigOperators
open Zeta23Ext.Bridge
open Zeta23Ext.BridgeW
namespace StructuralGoal20261016.WindowGramTransfer
def pairI : Fin 41 → Fin 10 := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 5, 5, 5, 6, 6, 6, 7, 8]
def pairJ : Fin 41 → Fin 10 := ![1, 3, 5, 6, 7, 8, 9, 2, 3, 4, 5, 6, 7, 8, 9, 3, 4, 5, 6, 7, 8, 9, 4, 5, 6, 7, 8, 9, 5, 6, 7, 8, 9, 6, 7, 8, 7, 8, 9, 8, 9]
def weight : Fin 41 → ℝ := ![(195195711 : ℝ) / 2000000000, (1008375533 : ℝ) / 10000000000, (1879917691 : ℝ) / 5000000000, (2851965903 : ℝ) / 10000000000, (1310911881 : ℝ) / 2000000000, (1 : ℝ) / 1, (2 : ℝ) / 1, (485225937 : ℝ) / 2500000000, (784443699 : ℝ) / 5000000000, (648608813 : ℝ) / 2000000000, (506909809 : ℝ) / 1250000000, (2227433729 : ℝ) / 5000000000, (446752131 : ℝ) / 625000000, (6890881189 : ℝ) / 10000000000, (1 : ℝ) / 1, (513175917 : ℝ) / 2000000000, (4121909221 : ℝ) / 10000000000, (3824161541 : ℝ) / 10000000000, (5944721527 : ℝ) / 10000000000, (1785297159 : ℝ) / 5000000000, (446752131 : ℝ) / 625000000, (1310911881 : ℝ) / 2000000000, (2928557891 : ℝ) / 10000000000, (215460169 : ℝ) / 500000000, (1924418859 : ℝ) / 5000000000, (5944721527 : ℝ) / 10000000000, (2227433729 : ℝ) / 5000000000, (2851965903 : ℝ) / 10000000000, (79434011 : ℝ) / 250000000, (215460169 : ℝ) / 500000000, (3824161541 : ℝ) / 10000000000, (506909809 : ℝ) / 1250000000, (1879917691 : ℝ) / 5000000000, (2928557891 : ℝ) / 10000000000, (4121909221 : ℝ) / 10000000000, (648608813 : ℝ) / 2000000000, (513175917 : ℝ) / 2000000000, (784443699 : ℝ) / 5000000000, (1008375533 : ℝ) / 10000000000, (485225937 : ℝ) / 2500000000, (195195711 : ℝ) / 2000000000]
def span (g : Fin 9 → ℝ) (t : Fin 41) : ℝ :=
  ptsN 10 g (pairJ t)-ptsN 10 g (pairI t)
def pressure (g : Fin 9 → ℝ) : ℝ :=
  ∑ r, StructuralW10Followup20261016.NewLedger.W.b r*g r

theorem weight_nonneg (t : Fin 41) : 0 ≤ weight t := by
  fin_cases t <;> norm_num [weight]

theorem actual_energy_expansion (g : Fin 9 → ℝ) :
    WindowGapEnergy.Fw24 g = pressure g+∑ t : Fin 41,
      weight t*WindowKernel.w 24 WindowKernel.d24 (span g t) := by
  simp [WindowGapEnergy.Fw24, WindowGapEnergy.Fw, pressure, span,
    pairI, pairJ, weight, StructuralW10Followup20261016.NewLedger.W,
    StructuralW10Followup20261016.NewLedger.a,
    StructuralW10Followup20261016.NewLedger.aN,
    StructuralW10Followup20261016.NewLedger.b,
    StructuralW10Followup20261016.NewLedger.bN,
    Fin.sum_univ_succ, Fin.succ] <;> ring

theorem scalar_sum_le (g : Fin 9 → ℝ) (Q : Fin 41 → ℝ)
    (hQ : ∀ t, Q t ≤ WindowKernel.w 24 WindowKernel.d24 (span g t)) :
    pressure g+∑ t, weight t*Q t ≤ WindowGapEnergy.Fw24 g := by
  rw [actual_energy_expansion]
  exact add_le_add le_rfl (Finset.sum_le_sum fun t _ =>
    mul_le_mul_of_nonneg_left (hQ t) (weight_nonneg t))
end StructuralGoal20261016.WindowGramTransfer
end
