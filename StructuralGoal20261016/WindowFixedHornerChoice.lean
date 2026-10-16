/- SPDX-License-Identifier: Apache-2.0
Compact corner-choice certificates for interval Horner evaluation. A four-bit
digit selects the two output corners at each layer. The checker verifies
that the selected interval covers the ordinary four-corner product; no sign
choice or claimed extremality of the supplied digits is trusted.
-/
import StructuralGoal20261016.WindowFixedPolynomial
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open scoped BigOperators
namespace StructuralGoal20261016.WindowFixedHornerChoice
open WindowRationalInterval (Holds)
open WindowFixedInterval

def corner (I J : FI) (b : ℕ) : ℤ := match b%4 with
 | 0 => I.1*J.1
 | 1 => I.1*J.2
 | 2 => I.2*J.1
 | _ => I.2*J.2
def choice (I J : FI) (b : ℕ) : FI :=
 (floorDiv (corner I J b) S,ceilDiv (corner I J (b/4)) S)

theorem choice_sound {I J : FI} {x y : ℝ} {b : ℕ}
 (hx : Holds (decode I) x) (hy : Holds (decode J) y)
 (hc : covers (mul I J) (choice I J b) = true) :
 Holds (decode (choice I J b)) (x*y) := covers_sound hc (mul_sound hx hy)

def poly (C : ℕ → FI) (X : FI) (b : ℕ) : ℕ → FI
 | 0 => C 0
 | n+1 => add (C 0) (choice (poly (fun j => C (j+1)) X (b/16) n) X b)
def check (C : ℕ → FI) (X : FI) (b : ℕ) : ℕ → Bool
 | 0 => true
 | n+1 => check (fun j => C (j+1)) X (b/16) n &&
   covers (mul (poly (fun j => C (j+1)) X (b/16) n) X)
     (choice (poly (fun j => C (j+1)) X (b/16) n) X b)

theorem sound (C : ℕ → FI) (a : ℕ → ℝ) (X : FI) (y : ℝ) (b n : ℕ)
 (hC : ∀ j ≤ n, Holds (decode (C j)) (a j))
 (hX : Holds (decode X) y) (hc : check C X b n = true) :
 Holds (decode (poly C X b n)) (∑ j ∈ Finset.range (n+1), a j*y^j) := by
 induction n generalizing C a b with
 | zero => simpa only [poly,Nat.zero_add,Finset.sum_range_one,pow_zero,mul_one] using hC 0 (by omega)
 | succ n ih =>
   have hh : check (fun j => C (j+1)) X (b/16) n = true ∧
       covers (mul (poly (fun j => C (j+1)) X (b/16) n) X)
         (choice (poly (fun j => C (j+1)) X (b/16) n) X b) = true := by
     simpa only [check,Bool.and_eq_true] using hc
   have hp := ih (fun j => C (j+1)) (fun j => a (j+1)) (b/16)
     (fun j hj => hC (j+1) (by omega)) hh.1
   have h := add_sound (hC 0 (by omega)) (choice_sound hp hX hh.2)
   convert h using 1
   · rfl
   · rw [Finset.sum_range_succ']
     simp only [pow_zero,mul_one]
     rw [Finset.sum_mul,add_comm]
     congr 1
     apply Finset.sum_congr rfl
     intro j _
     rw [pow_succ]
     ring

set_option pp.fullNames true
#print axioms choice_sound
#print axioms sound
end StructuralGoal20261016.WindowFixedHornerChoice
end
