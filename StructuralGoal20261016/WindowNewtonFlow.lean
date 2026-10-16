/- SPDX-License-Identifier: Apache-2.0
Integer double-flow Newton retention for the actual new-window energy.
No numerical matrix inverse is trusted. At an actual relevant minimum,
the checked interior-support derivative is zero; the two exact flows and
cross-multiplied integer rounding retain the original scaled coordinate.
-/
import StructuralGoal20261016.WindowDirectionalFlow
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Finset
open scoped BigOperators
namespace StructuralGoal20261016.WindowNewtonFlow
open WindowDirectionalFlow
open StructuralW10Followup20261016.NewLedger (W)

def other (q : Fin 9 → ℤ) (i r : Fin 9) : ℤ := if r = i then 0 else q r

theorem split_sum (q : Fin 9 → ℤ) (g : Fin 9 → ℝ) (i : Fin 9) :
 (SC:ℝ)*(∑ r, (q r:ℝ)*g r) = (q i:ℝ)*((SC:ℝ)*g i)+
   (SC:ℝ)*(∑ r, (other q i r:ℝ)*g r) := by
 have ht (r : Fin 9) : (q r:ℝ)*g r =
     (if r = i then (q i:ℝ)*g i else 0)+(other q i r:ℝ)*g r := by
   by_cases hr : r = i
   · subst r
     simp [other]
   · simp [other,hr]
 have hs : (∑ r, (q r:ℝ)*g r) = (q i:ℝ)*g i+∑ r, (other q i r:ℝ)*g r := by
   calc
     _ = ∑ r, ((if r = i then (q i:ℝ)*g i else 0)+(other q i r:ℝ)*g r) :=
       Finset.sum_congr rfl (fun r _ => ht r)
     _ = _ := by rw [Finset.sum_add_distrib]; simp
 rw [hs]
 ring

def check (cell : DifferenceCell.Cell 10) (minimum maximum : List FlowBasisCodec.Edge)
 (d : Fin 9 → ℤ) (row : Fin 41 → Row) (i : Fin 9) (L U lower upper : ℤ) : Bool :=
 decide (0 < coefficient d row i ∧
   lower*coefficient d row i ≤ -error d row-constant d row-U ∧
   error d row-constant d row-L ≤ upper*coefficient d row i) &&
 (FlowBasisCodec.checkBasis minimum cell (WindowDifferenceCell.divergence (other (coefficient d row) i)) 0 L &&
  FlowBasisCodec.checkBasis maximum cell
    (WindowDifferenceCell.divergence (fun r => -other (coefficient d row) i r)) 0 (-U))

theorem retain {sep : ℝ} {g : Fin 9 → ℝ}
 (hg : WindowMinimizerCover.Relevant sep g)
 (cell : DifferenceCell.Cell 10) (hcell : WindowDifferenceCell.Contains cell g)
 (minimum maximum : List FlowBasisCodec.Edge)
 (d : Fin 9 → ℤ) (row : Fin 41 → Row) (i : Fin 9) (L U lower upper : ℤ)
 (hsupport : ∀ r, d r ≠ 0 → sep < g r) (hscalar : ScalarValid g row)
 (hc : check cell minimum maximum d row i L U lower upper = true) :
 (lower:ℝ) ≤ 32768*g i ∧ 32768*g i ≤ (upper:ℝ) := by
 have hh : (0 < coefficient d row i ∧
     lower*coefficient d row i ≤ -error d row-constant d row-U ∧
     error d row-constant d row-L ≤ upper*coefficient d row i) ∧
     FlowBasisCodec.checkBasis minimum cell
       (WindowDifferenceCell.divergence (other (coefficient d row) i)) 0 L = true ∧
     FlowBasisCodec.checkBasis maximum cell
       (WindowDifferenceCell.divergence (fun r => -other (coefficient d row) i r)) 0 (-U) = true := by
   simpa only [check,Bool.and_eq_true,decide_eq_true_eq] using hc
 have hz := WindowDirectionalAffine.zero_at_relevant hg (direction d) (by
   intro r hr
   apply hsupport r
   intro hn
   apply hr
   change (d r:ℝ) = 0
   simp only [hn,Int.cast_zero])
 have he := enclosure g d row hscalar
 rw [hz,mul_zero,split_sum] at he
 have hL := WindowDifferenceCell.flow_gap_bound cell g hcell minimum
   (other (coefficient d row) i) 0 L hh.2.1
 have hU := WindowDifferenceCell.flow_gap_bound cell g hcell maximum
   (fun r => -other (coefficient d row) i r) 0 (-U) hh.2.2
 simp only [Int.cast_zero,zero_add,Int.cast_neg,neg_mul,Finset.sum_neg_distrib] at hL hU
 have hroundL : (lower:ℝ)*(coefficient d row i:ℝ) ≤
     -(error d row:ℝ)-(constant d row:ℝ)-(U:ℝ) := by
   have ht : ((lower*coefficient d row i:ℤ):ℝ) ≤
       ((-error d row-constant d row-U:ℤ):ℝ) := Int.cast_le.mpr hh.1.2.1
   push_cast at ht
   exact ht
 have hroundU : (error d row:ℝ)-(constant d row:ℝ)-(L:ℝ) ≤
     (upper:ℝ)*(coefficient d row i:ℝ) := by
   have ht : ((error d row-constant d row-L:ℤ):ℝ) ≤
       ((upper*coefficient d row i:ℤ):ℝ) := Int.cast_le.mpr hh.1.2.2
   push_cast at ht
   exact ht
 have hpositive : (0:ℝ) < (coefficient d row i:ℝ) := by exact_mod_cast hh.1.1
 unfold SC at he
 norm_num at he
 obtain ⟨hl,hu⟩ := abs_le.mp he
 constructor <;> nlinarith only [hL,hU,hroundL,hroundU,hpositive,hl,hu]

set_option pp.fullNames true
#print axioms split_sum
#print axioms retain
end StructuralGoal20261016.WindowNewtonFlow
end
