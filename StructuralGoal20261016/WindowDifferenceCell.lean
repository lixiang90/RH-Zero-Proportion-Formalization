/- SPDX-License-Identifier: Apache-2.0
Difference-cell geometry and edge-only flow bounds for actual gap vectors.
The scaling, endpoint convention, and reflection orientation match discovery.
-/
import StructuralGoal20261016.DifferenceCell
import StructuralGoal20261016.WindowGapEnergy
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Finset
open Zeta23Ext.Bridge
namespace StructuralGoal20261016.WindowDifferenceCell

def positions (g : Fin 9 → ℝ) (i : Fin 10) : ℝ := 32768*ptsN 10 g i
def Contains (cell : DifferenceCell.Cell 10) (g : Fin 9 → ℝ) : Prop :=
  DifferenceCell.Contains cell (positions g)

def divergence (q : Fin 9 → ℤ) : Fin 10 → ℤ :=
  ![-q 0, q 0-q 1, q 1-q 2, q 2-q 3, q 3-q 4,
    q 4-q 5, q 5-q 6, q 6-q 7, q 7-q 8, q 8]

theorem adjacent_difference (g : Fin 9 → ℝ) (r : Fin 9) :
    ptsN 10 g r.succ-ptsN 10 g r.castSucc = g r := by
  fin_cases r <;> norm_num [ptsN, Fin.sum_univ_succ, Fin.succ] <;> ring

theorem summation_by_parts (g : Fin 9 → ℝ) (q : Fin 9 → ℤ) :
    (∑ i, (divergence q i : ℝ)*ptsN 10 g i) = ∑ r, (q r : ℝ)*g r := by
  have hsum : (∑ r, (q r : ℝ)*g r) =
      ∑ r, (q r : ℝ)*(ptsN 10 g r.succ-ptsN 10 g r.castSucc) := by
    apply Finset.sum_congr rfl
    intro r _
    rw [adjacent_difference]
  rw [hsum]
  let p : Fin 10 → ℝ := ptsN 10 g
  change (∑ i, (divergence q i : ℝ)*p i) =
    ∑ r, (q r : ℝ)*(p r.succ-p r.castSucc)
  simp only [divergence, Fin.sum_univ_succ, Fin.sum_univ_zero]
  change
    (((-q 0 : ℤ) : ℝ) * p 0) + ((((q 0-q 1 : ℤ) : ℝ) * p 1) + ((((q 1-q 2 : ℤ) : ℝ) * p 2) + ((((q 2-q 3 : ℤ) : ℝ) * p 3) + ((((q 3-q 4 : ℤ) : ℝ) * p 4) + ((((q 4-q 5 : ℤ) : ℝ) * p 5) + ((((q 5-q 6 : ℤ) : ℝ) * p 6) + ((((q 6-q 7 : ℤ) : ℝ) * p 7) + ((((q 7-q 8 : ℤ) : ℝ) * p 8) + (((q 8 : ℝ) * p 9) + (0)))))))))) =
    ((q 0 : ℝ) * (p 1-p 0)) + (((q 1 : ℝ) * (p 2-p 1)) + (((q 2 : ℝ) * (p 3-p 2)) + (((q 3 : ℝ) * (p 4-p 3)) + (((q 4 : ℝ) * (p 5-p 4)) + (((q 5 : ℝ) * (p 6-p 5)) + (((q 6 : ℝ) * (p 7-p 6)) + (((q 7 : ℝ) * (p 8-p 7)) + (((q 8 : ℝ) * (p 9-p 8)) + (0)))))))))
  push_cast
  ring

theorem split_sound {cell : DifferenceCell.Cell 10} {g : Fin 9 → ℝ}
    (hg : Contains cell g) (i j : Fin 10) (q : ℤ) :
    Contains (DifferenceCell.addEdge cell i j q) g ∨
      Contains (DifferenceCell.addEdge cell j i (-q)) g :=
  DifferenceCell.split_sound hg i j q

theorem reflection_exclusion {cell : DifferenceCell.Cell 10} {g : Fin 9 → ℝ}
    (hg : Contains cell g) (horiented : g 0 ≤ g 8)
    (hnegative : cell 8 9 + cell 1 0 < 0) : False := by
  have hlast := hg 8 9
  have hfirst := hg 1 0
  have hneg : (cell 8 9 : ℝ)+(cell 1 0 : ℝ) < 0 := by exact_mod_cast hnegative
  have h8 := adjacent_difference g 8
  have h0 := adjacent_difference g 0
  change ptsN 10 g 9-ptsN 10 g 8 = g 8 at h8
  change ptsN 10 g 1-ptsN 10 g 0 = g 0 at h0
  change 32768*ptsN 10 g 9-32768*ptsN 10 g 8 ≤ (cell 8 9 : ℝ) at hlast
  change 32768*ptsN 10 g 0-32768*ptsN 10 g 1 ≤ (cell 1 0 : ℝ) at hfirst
  nlinarith

theorem flow_gap_bound (cell : DifferenceCell.Cell 10) (g : Fin 9 → ℝ)
    (hg : Contains cell g) (edges : List FlowBasisCodec.Edge)
    (q : Fin 9 → ℤ) (intercept target : ℤ)
    (checked : FlowBasisCodec.checkBasis edges cell (divergence q) intercept target = true) :
    (target : ℝ) ≤ (intercept : ℝ)+32768*(∑ r, (q r : ℝ)*g r) := by
  have h := DifferenceCell.affine_flow_bound cell (positions g) hg edges (divergence q) intercept target checked
  have he : (∑ i, (divergence q i : ℝ)*positions g i) =
      32768*(∑ i, (divergence q i : ℝ)*ptsN 10 g i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold positions
    ring
  rw [he,summation_by_parts] at h
  exact h

set_option pp.fullNames true
#print axioms adjacent_difference
#print axioms summation_by_parts
#print axioms split_sound
#print axioms reflection_exclusion
#print axioms flow_gap_bound
end StructuralGoal20261016.WindowDifferenceCell
end
