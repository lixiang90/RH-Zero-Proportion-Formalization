/- SPDX-License-Identifier: Apache-2.0
Bernstein weights on the fixed relative cells as one integer numerator
over one common denominator. The LCM 25740 clears all binomial denominators;
the proof is generic in the integer cell offset and both coefficient indices.
-/
import StructuralGoal20261016.WindowBernsteinLinear
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators
namespace StructuralGoal20261016.WindowBernsteinIntegerWeights
open WindowBernsteinLinear

def D : ℤ := 25740
def chooseDiv (j : ℕ) : ℤ := D/((13:ℕ).choose j:ℤ)
theorem chooseDiv_mul : ∀ j : Fin 14, chooseDiv j*((13:ℕ).choose j:ℤ) = D := by decide +kernel

theorem reciprocal (j : ℕ) (hj : j < 14) :
 (1:ℚ)/((13:ℕ).choose j:ℚ) = (chooseDiv j:ℚ)/(D:ℚ) := by
 have hz : ((13:ℕ).choose j:ℚ) ≠ 0 := by
   exact_mod_cast (Nat.choose_pos (by omega : j ≤ 13)).ne'
 have hD : (D:ℚ) ≠ 0 := by norm_num [D]
 apply (div_eq_div_iff hz hD).mpr
 have hm : (chooseDiv j:ℚ)*((13:ℕ).choose j:ℚ) = (D:ℚ) := by
   exact_mod_cast chooseDiv_mul ⟨j,hj⟩
 simpa only [one_mul] using hm.symm

def numerator (A : ℤ) (k i : ℕ) : ℤ :=
 ∑ j ∈ Finset.range 14, if j ≤ i then
   (i.choose j:ℤ)*A^(i-j)*21^j*(k.choose j:ℤ)*chooseDiv j else 0
def weights (A : ℤ) (k i : ℕ) : ℚ := (numerator A k i:ℚ)/((D:ℚ)*400^i)

theorem term (A : ℤ) (k i j : ℕ) (hj : j < 14) (hji : j ≤ i) :
 (i.choose j:ℚ)*((A:ℚ)/400)^(i-j)*(21/400:ℚ)^j*(k.choose j:ℚ)/((13:ℕ).choose j:ℚ) =
 (((i.choose j:ℤ)*A^(i-j)*21^j*(k.choose j:ℤ)*chooseDiv j:ℤ):ℚ)/((D:ℚ)*400^i) := by
 have hp : (400:ℚ)^(i-j)*(400:ℚ)^j = 400^i := by
   rw [← pow_add,Nat.sub_add_cancel hji]
 have hs : ((A:ℚ)/400)^(i-j)*(21/400:ℚ)^j =
     ((A:ℚ)^(i-j)*21^j)/(400:ℚ)^i := by
   rw [div_pow,div_pow,div_mul_div_comm,hp]
 calc
   _ = (i.choose j:ℚ)*(k.choose j:ℚ)*
       (((A:ℚ)/400)^(i-j)*(21/400:ℚ)^j)*(1/((13:ℕ).choose j:ℚ)) := by ring
   _ = (i.choose j:ℚ)*(k.choose j:ℚ)*
       (((A:ℚ)^(i-j)*21^j)/(400:ℚ)^i)*((chooseDiv j:ℚ)/(D:ℚ)) := by
     rw [hs,reciprocal j hj]
   _ = _ := by push_cast; ring

theorem weights_eq (A : ℤ) (k i : ℕ) :
 weights A k i = weightQ ((A:ℚ)/400) (21/400) k i := by
 unfold weights numerator weightQ
 rw [Int.cast_sum,Finset.sum_div]
 apply Finset.sum_congr rfl
 intro j hj
 split_ifs with hji
 · exact (term A k i j (Finset.mem_range.mp hj) hji).symm
 · norm_num

set_option pp.fullNames true
#print axioms chooseDiv_mul
#print axioms weights_eq
end StructuralGoal20261016.WindowBernsteinIntegerWeights
end
