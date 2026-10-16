/- SPDX-License-Identifier: Apache-2.0
Integer aggregates and scaled flow certificates for actual directional
derivatives. The supplied midpoint/affine parameters are integers. Their
aggregate scaling identities are proved here, rather than assumed from
the external decoder. Only actual scalar oracle inequalities remain to
be supplied by the checked point/grid consumers.
-/
import StructuralGoal20261016.WindowDirectionalAffine
import StructuralGoal20261016.WindowValueFlow
import StructuralGoal20261016.WindowDifferenceCell
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Finset
open scoped BigOperators
namespace StructuralGoal20261016.WindowDirectionalFlow
open WindowGramTransfer
open StructuralW10Followup20261016.NewLedger (W aN bN)

def SC : ℤ := 32768
def DS : ℤ := 1000000000000000
def D : ℤ := 10000000000
def denominator : ℤ := 2*SC*D*DS
def direction (d : Fin 9 → ℤ) : Fin 9 → ℝ := fun r => (d r:ℝ)
def incidence (e : Fin 41) (r : Fin 9) : ℤ :=
 (if (r:ℕ) < (pairJ e:ℕ) then 1 else 0)-
   (if (r:ℕ) < (pairI e:ℕ) then 1 else 0)
def spanInt (d : Fin 9 → ℤ) (e : Fin 41) : ℤ := ∑ r, d r*incidence e r
def weightInt (e : Fin 41) : ℤ := (aN (pairI e) (pairJ e):ℤ)
def pressureInt (r : Fin 9) : ℤ := (bN r:ℤ)

structure Row where
 anchor : ℤ
 value : ℤ
 slope : ℤ
 error : ℤ

def scalarA (r : Row) : ℝ := (r.value:ℝ)/(DS:ℝ)-
 (r.slope:ℝ)/(DS:ℝ)*((r.anchor:ℝ)/(2*(SC:ℝ)))
def scalarB (r : Row) : ℝ := (r.slope:ℝ)/(DS:ℝ)
def scalarError (r : Row) : ℝ := (r.error:ℝ)/(DS:ℝ)
def constant (d : Fin 9 → ℤ) (row : Fin 41 → Row) : ℤ :=
 2*SC*DS*(∑ r, pressureInt r*d r)+
   ∑ e, weightInt e*spanInt d e*(2*SC*(row e).value-(row e).slope*(row e).anchor)
def coefficient (d : Fin 9 → ℤ) (row : Fin 41 → Row) (r : Fin 9) : ℤ :=
 ∑ e, 2*weightInt e*spanInt d e*(row e).slope*incidence e r
def error (d : Fin 9 → ℤ) (row : Fin 41 → Row) : ℤ :=
 2*SC*∑ e, weightInt e * |spanInt d e| * (row e).error

def ScalarValid (g : Fin 9 → ℝ) (row : Fin 41 → Row) : Prop := ∀ e,
 |WindowGapEnergy.w1 (span g e)-
   (((row e).value:ℝ)/(DS:ℝ)+((row e).slope:ℝ)/(DS:ℝ)*
     (span g e-((row e).anchor:ℝ)/(2*(SC:ℝ))))| ≤ ((row e).error:ℝ)/(DS:ℝ)

theorem denominator_pos : (0:ℝ) < (denominator:ℝ) := by norm_num [denominator,SC,DS,D]

theorem incidence_cast (e : Fin 41) (r : Fin 9) :
 (incidence e r:ℝ) = WindowDirectionalAffine.incidence e r := by
 unfold incidence WindowDirectionalAffine.incidence
 split_ifs <;> norm_num

theorem span_cast (d : Fin 9 → ℤ) (e : Fin 41) :
 (spanInt d e:ℝ) = span (direction d) e := by
 rw [WindowDirectionalAffine.span_eq_sum]
 simp only [spanInt,Int.cast_sum,Int.cast_mul,incidence_cast,direction]

theorem weight_cast (e : Fin 41) : (weightInt e:ℝ)/(D:ℝ) = weight e := by
 have h := WindowValueFlow.capacity_eq e
 unfold WindowValueFlow.capacity at h
 convert h using 1 <;> first | rfl | (unfold weightInt D; push_cast; ring)

theorem pressure_cast (r : Fin 9) : (pressureInt r:ℝ)/(D:ℝ) = W.b r := by
 norm_num [pressureInt,D,StructuralW10Followup20261016.NewLedger.W,
   StructuralW10Followup20261016.NewLedger.b]

theorem constant_scaling (d : Fin 9 → ℤ) (row : Fin 41 → Row) :
 (denominator:ℝ)*WindowDirectionalAffine.intercept (direction d) (fun e => scalarA (row e)) =
   (constant d row:ℝ) := by
 have hp : (denominator:ℝ)*pressure (direction d) =
     ((2*SC*DS*(∑ r, pressureInt r*d r):ℤ):ℝ) := by
   unfold pressure
   rw [Finset.mul_sum]
   push_cast
   rw [Finset.mul_sum]
   apply Finset.sum_congr rfl
   intro r _
   rw [← pressure_cast]
   unfold denominator direction SC D DS
   push_cast
   ring
 have he (e : Fin 41) : (denominator:ℝ)*(weight e*span (direction d) e*scalarA (row e)) =
     ((weightInt e*spanInt d e*(2*SC*(row e).value-(row e).slope*(row e).anchor):ℤ):ℝ) := by
   rw [← weight_cast,← span_cast]
   unfold denominator scalarA SC D DS
   push_cast
   ring
 unfold WindowDirectionalAffine.intercept constant
 rw [mul_add,hp,Finset.mul_sum]
 push_cast
 congr 1
 rw [Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro e _
 have hh := he e
 push_cast at hh
 exact hh

theorem coefficient_scaling (d : Fin 9 → ℤ) (row : Fin 41 → Row) (r : Fin 9) :
 (denominator:ℝ)*WindowDirectionalAffine.coefficient (direction d) (fun e => scalarB (row e)) r =
   (SC:ℝ)*(coefficient d row r:ℝ) := by
 unfold WindowDirectionalAffine.coefficient coefficient
 rw [Finset.mul_sum]
 push_cast
 rw [Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro e _
 rw [← weight_cast,← span_cast,← incidence_cast]
 unfold denominator scalarB SC D DS
 push_cast
 ring

theorem error_scaling (d : Fin 9 → ℤ) (row : Fin 41 → Row) :
 (denominator:ℝ)*WindowDirectionalAffine.error (direction d) (fun e => scalarError (row e)) =
   (error d row:ℝ) := by
 have he (e : Fin 41) :
     (denominator:ℝ)*(|weight e*span (direction d) e| * scalarError (row e)) =
     ((2*SC*weightInt e*|spanInt d e| * (row e).error:ℤ):ℝ) := by
   rw [abs_mul,abs_of_nonneg (weight_nonneg e),← span_cast]
   rw [← weight_cast]
   unfold denominator scalarError SC D DS
   push_cast
   ring
 unfold WindowDirectionalAffine.error
 rw [Finset.mul_sum]
 calc
   _ = ∑ e : Fin 41, ((2*SC*weightInt e*|spanInt d e| * (row e).error:ℤ):ℝ) :=
     Finset.sum_congr rfl (fun e _ => he e)
   _ = (error d row:ℝ) := by
     unfold error
     push_cast
     rw [Finset.mul_sum]
     apply Finset.sum_congr rfl
     intro e _
     ring

theorem model_scaling (g : Fin 9 → ℝ) (d : Fin 9 → ℤ) (row : Fin 41 → Row) :
 (denominator:ℝ)*(WindowDirectionalAffine.intercept (direction d) (fun e => scalarA (row e))+
   ∑ r, WindowDirectionalAffine.coefficient (direction d) (fun e => scalarB (row e)) r*g r) =
 (constant d row:ℝ)+(SC:ℝ)*∑ r, (coefficient d row r:ℝ)*g r := by
 rw [mul_add,constant_scaling,Finset.mul_sum,Finset.mul_sum]
 congr 1
 apply Finset.sum_congr rfl
 intro r _
 rw [← mul_assoc,coefficient_scaling]
 ring

theorem enclosure (g : Fin 9 → ℝ) (d : Fin 9 → ℤ) (row : Fin 41 → Row)
 (hscalar : ScalarValid g row) :
 |(denominator:ℝ)*WindowGapEnergy.directional W g (direction d)-
   ((constant d row:ℝ)+(SC:ℝ)*∑ r, (coefficient d row r:ℝ)*g r)| ≤ (error d row:ℝ) := by
 have hs : ∀ e, |WindowGapEnergy.w1 (span g e)-
     (scalarA (row e)+scalarB (row e)*span g e)| ≤ scalarError (row e) := by
   intro e
   have hmodel : scalarA (row e)+scalarB (row e)*span g e =
       ((row e).value:ℝ)/(DS:ℝ)+((row e).slope:ℝ)/(DS:ℝ)*
         (span g e-((row e).anchor:ℝ)/(2*(SC:ℝ))) := by
     unfold scalarA scalarB
     ring
   rw [hmodel]
   exact hscalar e
 have h := WindowDirectionalAffine.enclosure g (direction d)
   (fun e => scalarA (row e)) (fun e => scalarB (row e)) (fun e => scalarError (row e)) hs
 have hm := mul_le_mul_of_nonneg_left h denominator_pos.le
 rw [← abs_of_pos denominator_pos,← abs_mul,mul_sub,model_scaling] at hm
 rw [abs_of_pos denominator_pos,error_scaling] at hm
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
 (hscalar : ScalarValid g row) (hc : check cell edges d row = true)
 (hfeasible : ∀ r, g r = sep → 0 ≤ d r) : False := by
 have hp := WindowMinimizerCover.directional_nonneg hg (direction d) (by
   intro r hr
   change (0:ℝ) ≤ (d r:ℝ)
   exact_mod_cast hfeasible r hr)
 have he := (abs_le.mp (enclosure g d row hscalar)).2
 have hf := WindowDifferenceCell.flow_gap_bound cell g hcell edges
   (fun r => -coefficient d row r) (-constant d row-error d row) 1 hc
 simp only [Int.cast_neg,Int.cast_sub,neg_mul,Finset.sum_neg_distrib] at hf
 have hpos := mul_nonneg denominator_pos.le hp
 norm_num only [Int.cast_one] at hf
 change (1:ℝ) ≤ -(constant d row:ℝ)-(error d row:ℝ)+
   32768*(-∑ r, (coefficient d row r:ℝ)*g r) at hf
 unfold SC at he
 norm_num at he
 linarith

set_option pp.fullNames true
#print axioms constant_scaling
#print axioms coefficient_scaling
#print axioms error_scaling
#print axioms enclosure
#print axioms exclude
end StructuralGoal20261016.WindowDirectionalFlow
end
