/- SPDX-License-Identifier: Apache-2.0
Fixed 10^-30 integer-endpoint interval arithmetic. The checked computation
uses only integers; soundness is transferred to the already proved rational
interval arithmetic. This module changes no existing certificate source.
-/
import StructuralGoal20261016.WindowRationalInterval
import Mathlib.Data.Rat.Floor
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real
namespace StructuralGoal20261016.WindowFixedInterval
open WindowRationalInterval

abbrev FI := ℤ × ℤ
def S : ℤ := 10^30
def decode (I : FI) : QI := ((I.1:ℚ)/(S:ℚ),(I.2:ℚ)/(S:ℚ))
def floorDiv (a b : ℤ) : ℤ := if 0 ≤ b then a/b else (-a)/(-b)
def ceilDiv (a b : ℤ) : ℤ := -floorDiv (-a) b
def point (m : ℤ) : FI := (m*S,m*S)
def add (I J : FI) : FI := (I.1+J.1,I.2+J.2)
def neg (I : FI) : FI := (-I.2,-I.1)
def sub (I J : FI) : FI := add I (neg J)
def mul (I J : FI) : FI :=
 (min (min (floorDiv (I.1*J.1) S) (floorDiv (I.1*J.2) S))
      (min (floorDiv (I.2*J.1) S) (floorDiv (I.2*J.2) S)),
  max (max (ceilDiv (I.1*J.1) S) (ceilDiv (I.1*J.2) S))
      (max (ceilDiv (I.2*J.1) S) (ceilDiv (I.2*J.2) S)))
def inv (I : FI) : FI := (floorDiv (S*S) I.2,ceilDiv (S*S) I.1)
def div (I J : FI) : FI := mul I (inv J)
def covers (I J : FI) : Bool := decide (J.1 ≤ I.1 ∧ I.2 ≤ J.2)

theorem S_pos : (0:ℤ) < S := by norm_num [S]
theorem SQ_pos : (0:ℚ) < (S:ℚ) := by exact_mod_cast S_pos

theorem floorDiv_eq (a b : ℤ) : floorDiv a b = ⌊((a:ℚ)/(b:ℚ))⌋ := by
 unfold floorDiv
 split_ifs with hb
 · have he : (b.toNat:ℤ) = b := Int.toNat_of_nonneg hb
   have heq : (b.toNat:ℚ) = (b:ℚ) := by exact_mod_cast he
   have h := Rat.floor_intCast_div_natCast a b.toNat
   simpa only [heq,he] using h.symm
 · have hn : 0 ≤ -b := by omega
   have he : ((-b).toNat:ℤ) = -b := Int.toNat_of_nonneg hn
   have heq : ((-b).toNat:ℚ) = (-b:ℚ) := by exact_mod_cast he
   have h := Rat.floor_intCast_div_natCast (-a) (-b).toNat
   have hq : ((-a:ℤ):ℚ)/(((-b).toNat:ℕ):ℚ) = (a:ℚ)/(b:ℚ) := by
     rw [heq]
     push_cast
     ring
   rw [hq] at h
   simpa only [he] using h.symm

theorem floorDiv_le (a b : ℤ) : (floorDiv a b:ℚ) ≤ (a:ℚ)/(b:ℚ) := by
 rw [floorDiv_eq]
 exact Int.floor_le _

theorem le_ceilDiv (a b : ℤ) : (a:ℚ)/(b:ℚ) ≤ (ceilDiv a b:ℚ) := by
 have h := neg_le_neg (floorDiv_le (-a) b)
 simpa only [ceilDiv,Int.cast_neg,neg_div,neg_neg] using h

theorem covers_sound {I J : FI} {x : ℝ} (h : covers I J = true)
 (hx : Holds (decode I) x) : Holds (decode J) x := by
 have he : J.1 ≤ I.1 ∧ I.2 ≤ J.2 := of_decide_eq_true h
 apply WindowRationalInterval.widen hx
 · exact div_le_div_of_nonneg_right (by exact_mod_cast he.1) SQ_pos.le
 · exact div_le_div_of_nonneg_right (by exact_mod_cast he.2) SQ_pos.le

theorem point_sound (m : ℤ) : Holds (decode (point m)) (m:ℝ) := by
 unfold Holds decode point
 have hS : (S:ℝ) ≠ 0 := by exact_mod_cast S_pos.ne'
 push_cast
 constructor <;> simp [hS]

theorem add_sound {I J : FI} {x y : ℝ}
 (hx : Holds (decode I) x) (hy : Holds (decode J) y) :
 Holds (decode (add I J)) (x+y) := by
 have h := WindowRationalInterval.add_sound hx hy
 simpa only [decode,add,WindowRationalInterval.add,Int.cast_add,add_div] using h

theorem neg_sound {I : FI} {x : ℝ} (hx : Holds (decode I) x) :
 Holds (decode (neg I)) (-x) := by
 have h := WindowRationalInterval.neg_sound hx
 simpa only [decode,neg,WindowRationalInterval.neg,Int.cast_neg,neg_div] using h

theorem sub_sound {I J : FI} {x y : ℝ}
 (hx : Holds (decode I) x) (hy : Holds (decode J) y) :
 Holds (decode (sub I J)) (x-y) := by
 simpa only [sub,sub_eq_add_neg] using add_sound hx (neg_sound hy)

theorem product_lower (a b : ℤ) : (floorDiv (a*b) S:ℚ)/(S:ℚ) ≤
 ((a:ℚ)/(S:ℚ))*((b:ℚ)/(S:ℚ)) := by
 have h := div_le_div_of_nonneg_right (floorDiv_le (a*b) S) SQ_pos.le
 convert h using 1 <;> first | rfl | (push_cast; ring)

theorem product_upper (a b : ℤ) : ((a:ℚ)/(S:ℚ))*((b:ℚ)/(S:ℚ)) ≤
 (ceilDiv (a*b) S:ℚ)/(S:ℚ) := by
 have h := div_le_div_of_nonneg_right (le_ceilDiv (a*b) S) SQ_pos.le
 convert h using 1 <;> first | rfl | (push_cast; ring)

theorem mul_sound {I J : FI} {x y : ℝ}
 (hx : Holds (decode I) x) (hy : Holds (decode J) y) :
 Holds (decode (mul I J)) (x*y) := by
 apply WindowRationalInterval.widen (WindowRationalInterval.mul_sound hx hy)
 · unfold decode mul WindowRationalInterval.mul
   push_cast
   simp only [← min_div_div_right SQ_pos.le]
   exact min_le_min (min_le_min (product_lower I.1 J.1) (product_lower I.1 J.2))
     (min_le_min (product_lower I.2 J.1) (product_lower I.2 J.2))
 · unfold decode mul WindowRationalInterval.mul
   push_cast
   simp only [← max_div_div_right SQ_pos.le]
   exact max_le_max (max_le_max (product_upper I.1 J.1) (product_upper I.1 J.2))
     (max_le_max (product_upper I.2 J.1) (product_upper I.2 J.2))

theorem inverse_lower (a : ℤ) : (floorDiv (S*S) a:ℚ)/(S:ℚ) ≤
 1/((a:ℚ)/(S:ℚ)) := by
 have h := div_le_div_of_nonneg_right (floorDiv_le (S*S) a) SQ_pos.le
 have hS : (S:ℚ) ≠ 0 := SQ_pos.ne'
 convert h using 1 <;> first | rfl | (push_cast; field_simp <;> ring)

theorem inverse_upper (a : ℤ) : 1/((a:ℚ)/(S:ℚ)) ≤
 (ceilDiv (S*S) a:ℚ)/(S:ℚ) := by
 have h := div_le_div_of_nonneg_right (le_ceilDiv (S*S) a) SQ_pos.le
 have hS : (S:ℚ) ≠ 0 := SQ_pos.ne'
 convert h using 1 <;> first | rfl | (push_cast; field_simp <;> ring)

theorem inv_sound {I : FI} {x : ℝ} (hx : Holds (decode I) x)
 (hnz : 0 < I.1 ∨ I.2 < 0) : Holds (decode (inv I)) (1/x) := by
 have hg : 0 < (decode I).1 ∨ (decode I).2 < 0 := by
   rcases hnz with hp | hn
   · left
     exact div_pos (by exact_mod_cast hp) SQ_pos
   · right
     exact div_neg_of_neg_of_pos (by exact_mod_cast hn) SQ_pos
 exact WindowRationalInterval.widen (WindowRationalInterval.inv_sound hx hg)
   (inverse_lower I.2) (inverse_upper I.1)

theorem div_sound {I J : FI} {x y : ℝ}
 (hx : Holds (decode I) x) (hy : Holds (decode J) y)
 (hnz : 0 < J.1 ∨ J.2 < 0) : Holds (decode (div I J)) (x/y) := by
 simpa only [div,div_eq_mul_inv,one_div,one_mul] using mul_sound hx (inv_sound hy hnz)

set_option pp.fullNames true
#print axioms floorDiv_eq
#print axioms mul_sound
#print axioms div_sound
end StructuralGoal20261016.WindowFixedInterval
end
