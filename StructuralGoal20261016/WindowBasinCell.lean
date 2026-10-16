/- SPDX-License-Identifier: Apache-2.0
Checked difference-cell containment in one of the 69 actual Gram basins.
Every test is rational; the analytic basin floor is supplied by the
already proved actual scalar and diagonal Gram certificates.
-/
import StructuralGoal20261016.WindowRationalBasinAll
import StructuralGoal20261016.WindowScalarLine
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
namespace StructuralGoal20261016.WindowBasinCell
open WindowGramTransfer WindowGramRational WindowRationalBasinData
open WindowAnchorCertificateData
open WindowScalarLine (lower upper)

def center (i : ℕ) (t : Fin 41) : ℚ :=
  ((row ((basin i).index t)).center:ℚ)

def check (cell : DifferenceCell.Cell 10) (i : ℕ) : Bool := decide (
  i < 69 ∧ ∀ t : Fin 41,
    center i t-21/100 ≤ (lower cell t:ℚ)/32768 ∧
    (upper cell t:ℚ)/32768 ≤ center i t+21/100)

theorem region {cell : DifferenceCell.Cell 10} {i : ℕ}
    (hc : check cell i = true) {g : Fin 9 → ℝ}
    (hg : WindowDifferenceCell.Contains cell g) : Region (basin i) g := by
  have hh : i < 69 ∧ ∀ t : Fin 41,
      center i t-21/100 ≤ (lower cell t:ℚ)/32768 ∧
      (upper cell t:ℚ)/32768 ≤ center i t+21/100 := of_decide_eq_true hc
  intro t
  have hs := WindowScalarLine.span_bounds hg t
  have hL : (((center i t-21/100:ℚ):ℝ)) ≤ (((lower cell t:ℚ)/32768:ℚ):ℝ) :=
    Rat.cast_le.mpr (hh.2 t).1
  have hU : ((((upper cell t:ℚ)/32768:ℚ):ℝ)) ≤ ((center i t+21/100:ℚ):ℝ) :=
    Rat.cast_le.mpr (hh.2 t).2
  unfold center at hL hU
  push_cast at hL hU
  exact ⟨hL.trans hs.1,hs.2.trans hU⟩

theorem floor {cell : DifferenceCell.Cell 10} {i : ℕ}
    (hc : check cell i = true) {g : Fin 9 → ℝ}
    (hg : WindowDifferenceCell.Contains cell g) :
    (221:ℝ)/25000 ≤ WindowGapEnergy.Fw24 g := by
  have hh : i < 69 ∧ ∀ t : Fin 41,
      center i t-21/100 ≤ (lower cell t:ℚ)/32768 ∧
      (upper cell t:ℚ)/32768 ≤ center i t+21/100 := of_decide_eq_true hc
  exact WindowRationalBasinAll.actual i hh.1 g (region hc hg)

theorem lower_floor {cell : DifferenceCell.Cell 10} {i : ℕ}
    (hc : check cell i = true) {g : Fin 9 → ℝ}
    (hg : WindowDifferenceCell.Contains cell g) :
    (11:ℝ)/1250 ≤ WindowGapEnergy.Fw24 g :=
  (show (11:ℝ)/1250 ≤ (221:ℝ)/25000 by norm_num).trans (floor hc hg)

theorem exclude_below {cell : DifferenceCell.Cell 10} {i : ℕ} {sep c : ℝ}
    (hc : check cell i = true) {g : Fin 9 → ℝ}
    (hg : WindowDifferenceCell.Contains cell g)
    (hrel : WindowMinimizerCover.RelevantBelow sep c g)
    (htarget : c ≤ (221:ℝ)/25000) : False := by
  have hf := htarget.trans (floor hc hg)
  exact (not_lt_of_ge hf) hrel.2

set_option pp.fullNames true
#print axioms region
#print axioms floor
#print axioms lower_floor
#print axioms exclude_below
end StructuralGoal20261016.WindowBasinCell
end
