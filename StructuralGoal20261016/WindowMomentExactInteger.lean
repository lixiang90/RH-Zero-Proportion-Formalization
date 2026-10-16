/- SPDX-License-Identifier: Apache-2.0
Exact common-denominator certificates for rational moment aggregates.
The checker verifies every coefficient and the bound before multiplying
an actual inequality by a positive integer. No rounding error is introduced.
-/
import StructuralGoal20261016.WindowMomentRounding
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators
namespace StructuralGoal20261016.WindowMomentExactInteger
open WindowBoundedMomentFarkas (Row eval)
open WindowMomentRounding (rationalEval)

def check {m : ℕ} (den : ℤ) (a : Fin m → ℚ) (B : ℚ) (row : Row m) : Bool := decide (
 0 < den ∧ (∀ j, (row.coeff j:ℚ) = (den:ℚ)*a j) ∧ (row.bound:ℚ) = (den:ℚ)*B)

theorem eval_eq {m : ℕ} {den : ℤ} {a : Fin m → ℚ} {B : ℚ} {row : Row m}
 (hc : check den a B row = true) (x : Fin m → ℝ) :
 eval row x = (den:ℝ)*rationalEval a x := by
 have hh : 0 < den ∧ (∀ j, (row.coeff j:ℚ) = (den:ℚ)*a j) ∧
     (row.bound:ℚ) = (den:ℚ)*B := of_decide_eq_true hc
 unfold eval rationalEval
 rw [Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro j _
 have he : ((row.coeff j:ℚ):ℝ) = (((den:ℚ)*a j:ℚ):ℝ) :=
   congrArg (fun z : ℚ => (z:ℝ)) (hh.2.1 j)
 push_cast at he
 rw [he]
 ring

theorem valid {m : ℕ} {den : ℤ} {a : Fin m → ℚ} {B : ℚ} {row : Row m}
 (hc : check den a B row = true) (x : Fin m → ℝ)
 (ha : rationalEval a x ≤ (B:ℝ)) : eval row x ≤ (row.bound:ℝ) := by
 have hh : 0 < den ∧ (∀ j, (row.coeff j:ℚ) = (den:ℚ)*a j) ∧
     (row.bound:ℚ) = (den:ℚ)*B := of_decide_eq_true hc
 have hd : (0:ℝ) < (den:ℝ) := by exact_mod_cast hh.1
 have hb : ((row.bound:ℚ):ℝ) = (((den:ℚ)*B:ℚ):ℝ) :=
   congrArg (fun z : ℚ => (z:ℝ)) hh.2.2
 push_cast at hb
 rw [eval_eq hc,hb]
 exact mul_le_mul_of_nonneg_left ha hd.le

def strictCheck {m : ℕ} (boxScale : ℤ) (row : Row m) (L U : Fin m → ℤ) : Bool :=
 decide (0 < boxScale ∧ boxScale*row.bound < WindowBoundedMomentFarkas.supportLower row.coeff L U)

theorem exclude {m : ℕ} {den boxScale : ℤ} {a : Fin m → ℚ} {B : ℚ} {row : Row m}
 (L U : Fin m → ℤ) (hc : check den a B row = true)
 (hs : strictCheck boxScale row L U = true) (x : Fin m → ℝ)
 (hx : ∀ j, (L j:ℝ)/(boxScale:ℝ) ≤ x j ∧ x j ≤ (U j:ℝ)/(boxScale:ℝ))
 (ha : rationalEval a x ≤ (B:ℝ)) : False := by
 have hh : 0 < boxScale ∧ boxScale*row.bound <
     WindowBoundedMomentFarkas.supportLower row.coeff L U := of_decide_eq_true hs
 have hb : (0:ℝ) < (boxScale:ℝ) := by exact_mod_cast hh.1
 have hstrict : (boxScale:ℝ)*(row.bound:ℝ) <
     (WindowBoundedMomentFarkas.supportLower row.coeff L U:ℝ) := by exact_mod_cast hh.2
 have hu := valid hc x ha
 have hl := WindowBoundedMomentFarkas.scaled_support_lower boxScale row.coeff L U hh.1 x hx
 have hup := mul_le_mul_of_nonneg_left hu hb.le
 change (WindowBoundedMomentFarkas.supportLower row.coeff L U:ℝ) ≤
   (boxScale:ℝ)*eval row x at hl
 linarith

set_option pp.fullNames true
#print axioms eval_eq
#print axioms valid
#print axioms exclude
end StructuralGoal20261016.WindowMomentExactInteger
end
