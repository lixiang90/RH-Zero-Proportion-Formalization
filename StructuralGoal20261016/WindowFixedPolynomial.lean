/- SPDX-License-Identifier: Apache-2.0
Linear-cost Horner interval evaluation with a rational scalar. Its sign
selects one input endpoint for each output endpoint, avoiding four-corner
interval multiplication at every nested polynomial evaluation.
-/
import StructuralGoal20261016.WindowFixedRational
import StructuralGoal20261016.WindowPointTableArithmetic
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real
open scoped BigOperators
namespace StructuralGoal20261016.WindowFixedPolynomial
open WindowRationalInterval (QI Holds)
open WindowFixedInterval WindowFixedRational
open WindowScalarMinorant WindowConvexityCertificate

def scale (I : FI) (q : ℚ) : FI :=
 if 0 ≤ q.num then
   (floorDiv (I.1*q.num) q.den,ceilDiv (I.2*q.num) q.den)
 else (floorDiv (I.2*q.num) q.den,ceilDiv (I.1*q.num) q.den)

theorem scale_lower (a : ℤ) (q : ℚ) :
 (floorDiv (a*q.num) q.den:ℚ)/(S:ℚ) ≤ ((a:ℚ)/(S:ℚ))*q := by
 have h := floorDiv_le (a*q.num) q.den
 simp only [Int.cast_mul,Int.cast_natCast,mul_div_assoc,q.num_div_den] at h
 have hh := div_le_div_of_nonneg_right h SQ_pos.le
 convert hh using 1 <;> first | rfl | ring

theorem scale_upper (a : ℤ) (q : ℚ) :
 ((a:ℚ)/(S:ℚ))*q ≤ (ceilDiv (a*q.num) q.den:ℚ)/(S:ℚ) := by
 have h := le_ceilDiv (a*q.num) q.den
 simp only [Int.cast_mul,Int.cast_natCast,mul_div_assoc,q.num_div_den] at h
 have hh := div_le_div_of_nonneg_right h SQ_pos.le
 convert hh using 1 <;> first | rfl | ring

theorem scale_sound {I : FI} {x : ℝ} (hx : Holds (decode I) x) (q : ℚ) :
 Holds (decode (scale I q)) (x*(q:ℝ)) := by
 by_cases hq : 0 ≤ q.num
 · have hqQ : (0:ℚ) ≤ q := by
     rw [← q.num_div_den]
     exact div_nonneg (by exact_mod_cast hq) (by positivity)
   have hqR : (0:ℝ) ≤ (q:ℝ) := by exact_mod_cast hqQ
   rw [scale,if_pos hq]
   unfold Holds decode at hx ⊢
   push_cast at hx ⊢
   have hl : (floorDiv (I.1*q.num) q.den:ℝ)/(S:ℝ) ≤ ((I.1:ℝ)/(S:ℝ))*(q:ℝ) := by
     exact_mod_cast scale_lower I.1 q
   have hu : ((I.2:ℝ)/(S:ℝ))*(q:ℝ) ≤ (ceilDiv (I.2*q.num) q.den:ℝ)/(S:ℝ) := by
     exact_mod_cast scale_upper I.2 q
   exact ⟨hl.trans
     (mul_le_mul_of_nonneg_right hx.1 hqR),
     (mul_le_mul_of_nonneg_right hx.2 hqR).trans hu⟩
 · have hqQ : q ≤ (0:ℚ) := by
     rw [← q.num_div_den]
     exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast (le_of_not_ge hq)) (by positivity)
   have hqR : (q:ℝ) ≤ (0:ℝ) := by exact_mod_cast hqQ
   rw [scale,if_neg hq]
   unfold Holds decode at hx ⊢
   push_cast at hx ⊢
   have hl : (floorDiv (I.2*q.num) q.den:ℝ)/(S:ℝ) ≤ ((I.2:ℝ)/(S:ℝ))*(q:ℝ) := by
     exact_mod_cast scale_lower I.2 q
   have hu : ((I.1:ℝ)/(S:ℝ))*(q:ℝ) ≤ (ceilDiv (I.1*q.num) q.den:ℝ)/(S:ℝ) := by
     exact_mod_cast scale_upper I.1 q
   exact ⟨hl.trans
     (mul_le_mul_of_nonpos_right hx.2 hqR),
     (mul_le_mul_of_nonpos_right hx.1 hqR).trans hu⟩

def poly (C : ℕ → FI) (δ : ℚ) : ℕ → FI
 | 0 => C 0
 | n+1 => add (C 0) (scale (poly (fun j => C (j+1)) δ n) δ)

theorem horner_sound (C : ℕ → FI) (a : ℕ → ℝ) (δ : ℚ) (n : ℕ)
 (hC : ∀ j ≤ n, Holds (decode (C j)) (a j)) :
 Holds (decode (poly C δ n)) (∑ j ∈ Finset.range (n+1), a j*(δ:ℝ)^j) := by
 induction n generalizing C a with
 | zero => simpa only [poly,Nat.zero_add,Finset.sum_range_one,pow_zero,mul_one] using hC 0 (by omega)
 | succ n ih =>
   have h := add_sound (hC 0 (by omega)) (scale_sound
     (ih (fun j => C (j+1)) (fun j => a (j+1)) (fun j hj => hC (j+1) (by omega))) δ)
   convert h using 1
   · rfl
   · rw [Finset.sum_range_succ']
     simp only [pow_zero,mul_one]
     rw [Finset.sum_mul]
     rw [add_comm]
     congr 1
     apply Finset.sum_congr rfl
     intro j _
     rw [pow_succ]
     ring

theorem poly_sound (f : ℝ → ℝ) (p : ℝ) (C : ℕ → FI) (δ : ℚ) (n : ℕ)
 (hC : ∀ j ≤ n, Holds (decode (C j)) (iteratedDeriv j f p/(j.factorial:ℝ))) :
 Holds (decode (poly C δ n)) (taylorPoly f n p (p+δ)) := by
 unfold taylorPoly
 have he : p+(δ:ℝ)-p = δ := by ring
 rw [he]
 exact horner_sound C (fun j => iteratedDeriv j f p/(j.factorial:ℝ)) δ n hC

def lowerCheck (I : FI) (L : ℚ) : Bool := decide (L*(S:ℚ) ≤ (I.1:ℚ))
def upperCheck (I : FI) (U : ℚ) : Bool := decide ((I.2:ℚ) ≤ U*(S:ℚ))

theorem lowerCheck_sound {I : FI} {L : ℚ} {x : ℝ}
 (hc : lowerCheck I L = true) (hx : Holds (decode I) x) : (L:ℝ) ≤ x := by
 have h : L*(S:ℚ) ≤ (I.1:ℚ) := of_decide_eq_true hc
 exact (Rat.cast_le.mpr ((le_div_iff₀ SQ_pos).mpr h)).trans hx.1

theorem upperCheck_sound {I : FI} {U : ℚ} {x : ℝ}
 (hc : upperCheck I U = true) (hx : Holds (decode I) x) : x ≤ (U:ℝ) := by
 have h : (I.2:ℚ) ≤ U*(S:ℚ) := of_decide_eq_true hc
 exact hx.2.trans (Rat.cast_le.mpr ((div_le_iff₀ SQ_pos).mpr h))

set_option pp.fullNames true
#print axioms scale_sound
#print axioms horner_sound
#print axioms poly_sound
#print axioms lowerCheck_sound
end StructuralGoal20261016.WindowFixedPolynomial
end
