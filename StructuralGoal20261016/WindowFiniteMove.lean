/- SPDX-License-Identifier: Apache-2.0
Finite competitors for actual global minimizers of the new-window energy.
Unlike a differential KKT test, a feasible jump may cross an entire well.
Only a checked strict energy decrease can exclude a relevant minimizer.
-/
import StructuralGoal20261016.WindowMinimizerCover
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Finset
open Zeta23Ext.Bridge
open Zeta23Ext.BridgeW (WCert)
namespace StructuralGoal20261016.WindowFiniteMove
open WindowGapEnergy WindowKernel

def vector (q : Fin 9 → ℤ) : Fin 9 → ℝ := fun r => (q r : ℝ)
def move (g : Fin 9 → ℝ) (q : Fin 9 → ℤ) : Fin 9 → ℝ :=
  WindowGapEnergy.line (n := 10) g (vector q) 1
def span (g : Fin 9 → ℝ) (i j : Fin 10) : ℝ := ptsN 10 g j-ptsN 10 g i
def shift (q : Fin 9 → ℤ) (i j : Fin 10) : ℝ := span (vector q) i j
def term (W : WCert 10) (g : Fin 9 → ℝ) (i j : Fin 10) : ℝ :=
  if (i : ℕ) < (j : ℕ) then W.a i j*WindowKernel.w 24 d24 (span g i j) else 0
def delta (W : WCert 10) (g : Fin 9 → ℝ) (q : Fin 9 → ℤ) (i j : Fin 10) : ℝ :=
  if (i : ℕ) < (j : ℕ) then W.a i j*
    (WindowKernel.w 24 d24 (span g i j+shift q i j)-WindowKernel.w 24 d24 (span g i j)) else 0

theorem move_apply (g : Fin 9 → ℝ) (q : Fin 9 → ℤ) (r : Fin 9) :
    move g q r = g r+(q r : ℝ) := by simp [move,line,vector]

theorem span_move (g : Fin 9 → ℝ) (q : Fin 9 → ℤ) (i j : Fin 10) :
    span (move g q) i j = span g i j+shift q i j := by
  simp only [span,move,ptsN_line,one_mul,shift]
  ring

theorem feasible {sep : ℝ} (g : Fin 9 → ℝ) (q : Fin 9 → ℤ)
    (h : ∀ r, sep ≤ g r+(q r : ℝ)) : CoverCoerciveKKT.Orthant sep (move g q) := by
  intro r
  simpa only [move_apply] using h r

theorem feasible_nonnegative {sep : ℝ} (g : Fin 9 → ℝ) (q : Fin 9 → ℤ)
    (hg : CoverCoerciveKKT.Orthant sep g) (hq : ∀ r, 0 ≤ q r) :
    CoverCoerciveKKT.Orthant sep (move g q) := by
  apply feasible
  intro r
  have hr : (0:ℝ) ≤ (q r : ℝ) := by exact_mod_cast hq r
  linarith [hg r]

theorem term_move (W : WCert 10) (g : Fin 9 → ℝ) (q : Fin 9 → ℤ) (i j : Fin 10) :
    term W (move g q) i j = term W g i j+delta W g q i j := by
  by_cases hij : (i : ℕ) < (j : ℕ)
  · simp only [term,delta,if_pos hij,span_move]
    ring
  · simp only [term,delta,if_neg hij,add_zero]

theorem energy_difference (W : WCert 10) (g : Fin 9 → ℝ) (q : Fin 9 → ℤ) :
    Fw W (move g q)-Fw W g =
      (∑ r, W.b r*(q r : ℝ)) + ∑ i, ∑ j, delta W g q i j := by
  have hp : (∑ r, W.b r*move g q r) = (∑ r, W.b r*g r)+(∑ r, W.b r*(q r : ℝ)) := by
    simp only [move_apply,mul_add,Finset.sum_add_distrib]
  have ht : (∑ i, ∑ j, term W (move g q) i j) =
      (∑ i, ∑ j, term W g i j)+(∑ i, ∑ j, delta W g q i j) := by
    simp only [term_move,Finset.sum_add_distrib]
  change ((∑ r, W.b r*move g q r)+(∑ i, ∑ j, term W (move g q) i j))-
    ((∑ r, W.b r*g r)+(∑ i, ∑ j, term W g i j)) = _
  rw [hp,ht]
  ring

theorem energy_difference_le (W : WCert 10) (g : Fin 9 → ℝ) (q : Fin 9 → ℤ)
    (u : Fin 10 → Fin 10 → ℝ) (ha : ∀ i j : Fin 10, 0 ≤ W.a i j)
    (hu : ∀ i j : Fin 10, (i : ℕ) < (j : ℕ) →
      WindowKernel.w 24 d24 (span g i j+shift q i j)-WindowKernel.w 24 d24 (span g i j) ≤ u i j) :
    Fw W (move g q)-Fw W g ≤ (∑ r, W.b r*(q r : ℝ))+
      ∑ i : Fin 10, ∑ j : Fin 10, if (i : ℕ) < (j : ℕ) then W.a i j*u i j else 0 := by
  rw [energy_difference]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : (i : ℕ) < (j : ℕ)
  · simp only [delta,if_pos hij]
    exact mul_le_mul_of_nonneg_left (hu i j hij) (ha i j)
  · simp only [delta,if_neg hij,le_refl]

theorem exclude_relevant {sep : ℝ} {g : Fin 9 → ℝ}
    (hg : WindowMinimizerCover.Relevant sep g) (q : Fin 9 → ℤ)
    (hq : CoverCoerciveKKT.Orthant sep (move g q))
    (hdecrease : Fw24 (move g q)-Fw24 g < 0) : False := by
  have hmin := hg.2.2 (move g q) hq
  linarith

theorem exclude_by_scalar_bounds {sep : ℝ} {g : Fin 9 → ℝ}
    (hg : WindowMinimizerCover.Relevant sep g) (q : Fin 9 → ℤ)
    (hq : CoverCoerciveKKT.Orthant sep (move g q))
    (u : Fin 10 → Fin 10 → ℝ)
    (hu : ∀ i j : Fin 10, (i : ℕ) < (j : ℕ) →
      WindowKernel.w 24 d24 (span g i j+shift q i j)-WindowKernel.w 24 d24 (span g i j) ≤ u i j)
    (hbudget : (∑ r, StructuralW10Followup20261016.NewLedger.W.b r*(q r : ℝ))+
      (∑ i : Fin 10, ∑ j : Fin 10, if (i : ℕ) < (j : ℕ) then
        StructuralW10Followup20261016.NewLedger.W.a i j*u i j else 0) < 0) : False := by
  apply exclude_relevant hg q hq
  exact (energy_difference_le _ g q u StructuralW10Followup20261016.NewLedger.a_nonneg hu).trans_lt hbudget

/-- A counterexample's unused energy budget can strengthen a global-jump
certificate. The scalar minorant need only be below the actual energy;
nonnegative payment preserves the strict-decrease implication. -/
theorem exclude_with_sublevel {sep c A payment : ℝ} {g : Fin 9 → ℝ}
    (hg : WindowMinimizerCover.RelevantBelow sep c g) (q : Fin 9 → ℤ)
    (hq : CoverCoerciveKKT.Orthant sep (move g q))
    (hA : A ≤ Fw24 g) (hpayment : 0 ≤ payment)
    (hpaid : Fw24 (move g q)-Fw24 g+payment*(c-A) < 0) : False := by
  have hbudget : 0 ≤ c-A := by linarith [hg.2]
  have hnonneg := mul_nonneg hpayment hbudget
  apply exclude_relevant hg.1 q hq
  linarith

set_option pp.fullNames true
#print axioms span_move
#print axioms feasible
#print axioms feasible_nonnegative
#print axioms energy_difference
#print axioms energy_difference_le
#print axioms exclude_relevant
#print axioms exclude_by_scalar_bounds
#print axioms exclude_with_sublevel
end StructuralGoal20261016.WindowFiniteMove
end
