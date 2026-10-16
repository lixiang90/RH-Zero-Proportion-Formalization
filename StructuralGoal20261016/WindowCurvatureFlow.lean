/- SPDX-License-Identifier: Apache-2.0
Integer affine/flow upper certificates for the actual second variation.
The graph weights are a_ij*(span d)^2 and are nonnegative, so scalar
one-sided upper inequalities suffice. All aggregate scaling identities
are proved from the integer midpoint/value/slope/error data.
-/
import StructuralGoal20261016.WindowCurvatureAffine
import StructuralGoal20261016.WindowDirectionalFlow
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Finset
open scoped BigOperators
namespace StructuralGoal20261016.WindowCurvatureFlow
open WindowGramTransfer
open WindowDirectionalFlow (SC DS D denominator denominator_pos direction Row scalarA scalarB scalarError
 weightInt spanInt incidence)
open StructuralW10Followup20261016.NewLedger (W)

def constant (d : Fin 9 → ℤ) (row : Fin 41 → Row) : ℤ :=
 ∑ e, weightInt e*(spanInt d e)^2*(2*SC*(row e).value-(row e).slope*(row e).anchor)
def coefficient (d : Fin 9 → ℤ) (row : Fin 41 → Row) (r : Fin 9) : ℤ :=
 ∑ e, 2*weightInt e*(spanInt d e)^2*(row e).slope*incidence e r
def error (d : Fin 9 → ℤ) (row : Fin 41 → Row) : ℤ :=
 2*SC*∑ e, weightInt e*(spanInt d e)^2*(row e).error

def ScalarValid (g : Fin 9 → ℝ) (row : Fin 41 → Row) : Prop := ∀ e,
 WindowSecondVariation.w2 (span g e) ≤
   ((row e).value:ℝ)/(DS:ℝ)+((row e).slope:ℝ)/(DS:ℝ)*
     (span g e-((row e).anchor:ℝ)/(2*(SC:ℝ)))+((row e).error:ℝ)/(DS:ℝ)

theorem constant_scaling (d : Fin 9 → ℤ) (row : Fin 41 → Row) :
 (denominator:ℝ)*WindowCurvatureAffine.intercept (direction d) (fun e => scalarA (row e)) =
   (constant d row:ℝ) := by
 unfold WindowCurvatureAffine.intercept constant
 rw [Finset.mul_sum]
 push_cast
 apply Finset.sum_congr rfl
 intro e _
 unfold WindowCurvatureAffine.mass
 rw [← WindowDirectionalFlow.weight_cast,← WindowDirectionalFlow.span_cast]
 unfold denominator scalarA SC D DS
 push_cast
 ring

theorem coefficient_scaling (d : Fin 9 → ℤ) (row : Fin 41 → Row) (r : Fin 9) :
 (denominator:ℝ)*WindowCurvatureAffine.coefficient (direction d) (fun e => scalarB (row e)) r =
   (SC:ℝ)*(coefficient d row r:ℝ) := by
 unfold WindowCurvatureAffine.coefficient coefficient
 rw [Finset.mul_sum]
 push_cast
 rw [Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro e _
 unfold WindowCurvatureAffine.mass
 rw [← WindowDirectionalFlow.weight_cast,← WindowDirectionalFlow.span_cast,
   ← WindowDirectionalFlow.incidence_cast]
 unfold denominator scalarB SC D DS
 push_cast
 ring

theorem error_scaling (d : Fin 9 → ℤ) (row : Fin 41 → Row) :
 (denominator:ℝ)*WindowCurvatureAffine.error (direction d) (fun e => scalarError (row e)) =
   (error d row:ℝ) := by
 unfold WindowCurvatureAffine.error error
 rw [Finset.mul_sum]
 push_cast
 rw [Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro e _
 unfold WindowCurvatureAffine.mass
 rw [← WindowDirectionalFlow.weight_cast,← WindowDirectionalFlow.span_cast]
 unfold denominator scalarError SC D DS
 push_cast
 ring

theorem model_scaling (g : Fin 9 → ℝ) (d : Fin 9 → ℤ) (row : Fin 41 → Row) :
 (denominator:ℝ)*(WindowCurvatureAffine.intercept (direction d) (fun e => scalarA (row e))+
   ∑ r, WindowCurvatureAffine.coefficient (direction d) (fun e => scalarB (row e)) r*g r) =
 (constant d row:ℝ)+(SC:ℝ)*∑ r, (coefficient d row r:ℝ)*g r := by
 rw [mul_add,constant_scaling,Finset.mul_sum,Finset.mul_sum]
 congr 1
 apply Finset.sum_congr rfl
 intro r _
 rw [← mul_assoc,coefficient_scaling]
 ring

theorem upper (g : Fin 9 → ℝ) (d : Fin 9 → ℤ) (row : Fin 41 → Row)
 (hscalar : ScalarValid g row) :
 (denominator:ℝ)*WindowSecondVariation.curvature W g (direction d) ≤
   ((constant d row:ℝ)+(SC:ℝ)*∑ r, (coefficient d row r:ℝ)*g r)+(error d row:ℝ) := by
 have hs : ∀ e, WindowSecondVariation.w2 (span g e) ≤
     scalarA (row e)+scalarB (row e)*span g e+scalarError (row e) := by
   intro e
   have hmodel : scalarA (row e)+scalarB (row e)*span g e =
       ((row e).value:ℝ)/(DS:ℝ)+((row e).slope:ℝ)/(DS:ℝ)*
         (span g e-((row e).anchor:ℝ)/(2*(SC:ℝ))) := by
     unfold scalarA scalarB
     ring
   rw [hmodel]
   exact hscalar e
 have h := WindowCurvatureAffine.upper g (direction d)
   (fun e => scalarA (row e)) (fun e => scalarB (row e)) (fun e => scalarError (row e)) hs
 have hm := mul_le_mul_of_nonneg_left h denominator_pos.le
 rw [mul_add,model_scaling,error_scaling] at hm
 exact hm

def check (cell : DifferenceCell.Cell 10) (edges : List FlowBasisCodec.Edge)
 (d : Fin 9 → ℤ) (row : Fin 41 → Row) : Bool :=
 FlowBasisCodec.checkBasis edges cell
   (WindowDifferenceCell.divergence (fun r => -coefficient d row r))
   (-constant d row-error d row) 1

theorem exclude {sep : ℝ} {g : Fin 9 → ℝ}
 (hg : WindowMinimizerCover.Relevant sep g)
 (cell : DifferenceCell.Cell 10) (hcell : WindowDifferenceCell.Contains cell g)
 (edges : List FlowBasisCodec.Edge) (d : Fin 9 → ℤ) (row : Fin 41 → Row)
 (hsupport : ∀ r, d r ≠ 0 → sep < g r)
 (hscalar : ScalarValid g row) (hc : check cell edges d row = true) : False := by
 have hp := WindowSecondVariation.curvature_nonneg_of_relevant hg (direction d) (by
   intro r hr
   apply hsupport r
   intro hz
   apply hr
   change (d r:ℝ) = 0
   simp only [hz,Int.cast_zero])
 have hu := upper g d row hscalar
 have hf := WindowDifferenceCell.flow_gap_bound cell g hcell edges
   (fun r => -coefficient d row r) (-constant d row-error d row) 1 hc
 simp only [Int.cast_neg,Int.cast_sub,neg_mul,Finset.sum_neg_distrib] at hf
 have hpos := mul_nonneg denominator_pos.le hp
 norm_num only [Int.cast_one] at hf
 change (1:ℝ) ≤ -(constant d row:ℝ)-(error d row:ℝ)+
   32768*(-∑ r, (coefficient d row r:ℝ)*g r) at hf
 unfold SC at hu
 norm_num at hu
 linarith

set_option pp.fullNames true
#print axioms constant_scaling
#print axioms coefficient_scaling
#print axioms error_scaling
#print axioms upper
#print axioms exclude
end StructuralGoal20261016.WindowCurvatureFlow
end
