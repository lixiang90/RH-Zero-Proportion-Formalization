/- SPDX-License-Identifier: Apache-2.0
Actual value and slope enclosures at rational points from the checked
integer-centred normalized coefficient tables and a global Taylor remainder.
-/
import StructuralGoal20261016.WindowConvexityArithmetic
import StructuralGoal20261016.WindowScalarMinorant
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real
open scoped BigOperators
namespace StructuralGoal20261016.WindowPointTableArithmetic
open WindowRationalInterval WindowIntegerKernelRecipe WindowNormalizedJets
open WindowConvexityCertificate WindowScalarMinorant WindowConvexityArithmetic

def polyI (C : ℕ → QI) (δ : ℚ) : ℕ → QI
 | 0 => C 0
 | n+1 => radd (C 0) (rmul (point δ) (polyI (fun j => C (j+1)) δ n))

theorem horner_sound (C : ℕ → QI) (a : ℕ → ℝ) (δ : ℚ) (n : ℕ)
 (hC : ∀ j ≤ n, Holds (C j) (a j)) :
 Holds (polyI C δ n) (∑ j ∈ Finset.range (n+1), a j*(δ:ℝ)^j) := by
 induction n generalizing C a with
 | zero => simpa only [polyI,Nat.zero_add,Finset.sum_range_one,pow_zero,mul_one] using hC 0 (by omega)
 | succ n ih =>
   have h := radd_sound (hC 0 (by omega)) (rmul_sound (point_sound δ)
     (ih (fun j => C (j+1)) (fun j => a (j+1)) (fun j hj => hC (j+1) (by omega))))
   convert h using 1
   · rfl
   · rw [Finset.sum_range_succ']
     simp only [pow_zero,mul_one]
     rw [Finset.mul_sum]
     rw [add_comm]
     congr 1
     apply Finset.sum_congr rfl
     intro j _
     rw [pow_succ]
     ring

theorem polyI_sound (f : ℝ → ℝ) (p : ℝ) (C : ℕ → QI) (δ : ℚ) (n : ℕ)
 (hC : ∀ j ≤ n, Holds (C j) (iteratedDeriv j f p/(j.factorial:ℝ))) :
 Holds (polyI C δ n) (taylorPoly f n p (p+δ)) := by
 unfold taylorPoly
 have he : p+(δ:ℝ)-p = δ := by ring
 rw [he]
 exact horner_sound C (fun j => iteratedDeriv j f p/(j.factorial:ℝ)) δ n hC

def slopeCoeffs (C : ℕ → QI) (j : ℕ) : QI := rmul (point (j+1)) (C (j+1))

theorem slopeCoeffs_sound (C : ℕ → QI) (p : ℝ)
 (hC : ∀ j ≤ 23, Holds (C j) (wc 24 WindowKernel.d24 j p)) :
 ∀ j ≤ 22, Holds (slopeCoeffs C j) (iteratedDeriv j (iteratedDeriv 1 f) p/(j.factorial:ℝ)) := by
 intro j hj
 rw [first_coeff]
 exact rmul_sound
   (by simpa only [Rat.cast_add,Rat.cast_natCast,Rat.cast_one,
     Nat.cast_add,Nat.cast_one] using point_sound (j+1:ℚ)) (hC (j+1) (by omega))

def valueError (δ : ℚ) : ℚ := (44/7)^24*|δ|^24/(24:ℕ).factorial
def slopeError (δ : ℚ) : ℚ := (44/7)^24*|δ|^23/(23:ℕ).factorial

theorem actual_value_lower (C : ℕ → QI) (p q V : ℚ)
 (hC : ∀ j ≤ 23, Holds (C j) (wc 24 WindowKernel.d24 j p))
 (hc : V+valueError (q-p) ≤ (polyI C (q-p) 23).1) : (V:ℝ) ≤ f q := by
 have hp := (polyI_sound f p C (q-p) 23 hC).1
 have he : (p:ℝ)+((q-p:ℚ):ℝ) = q := by push_cast; ring
 rw [he] at hp
 apply value_lower_from_taylor (p := (p:ℝ)) (x := (q:ℝ))
   (R := (valueError (q-p):ℝ))
 · unfold valueError
   push_cast
   exact le_rfl
 · have hh : ((V+valueError (q-p):ℚ):ℝ) ≤ ((polyI C (q-p) 23).1:ℝ) := by exact_mod_cast hc
   push_cast at hh
   exact hh.trans hp

theorem actual_slope_interval (C : ℕ → QI) (p q L U : ℚ)
 (hC : ∀ j ≤ 23, Holds (C j) (wc 24 WindowKernel.d24 j p))
 (hl : L+slopeError (q-p) ≤ (polyI (slopeCoeffs C) (q-p) 22).1)
 (hu : (polyI (slopeCoeffs C) (q-p) 22).2 ≤ U-slopeError (q-p)) :
 (L:ℝ) ≤ iteratedDeriv 1 f q ∧ iteratedDeriv 1 f q ≤ U := by
 have hp := polyI_sound (iteratedDeriv 1 f) p (slopeCoeffs C) (q-p) 22
   (slopeCoeffs_sound C p hC)
 have he : (p:ℝ)+((q-p:ℚ):ℝ) = q := by push_cast; ring
 rw [he] at hp
 apply slope_interval_from_taylor (p := (p:ℝ)) (x := (q:ℝ))
   (R := (slopeError (q-p):ℝ))
 · unfold slopeError
   push_cast
   exact le_rfl
 · have hh : ((L+slopeError (q-p):ℚ):ℝ) ≤
       ((polyI (slopeCoeffs C) (q-p) 22).1:ℝ) := by exact_mod_cast hl
   push_cast at hh
   exact hh.trans hp.1
 · have hh : ((polyI (slopeCoeffs C) (q-p) 22).2:ℝ) ≤
       ((U-slopeError (q-p):ℚ):ℝ) := by exact_mod_cast hu
   push_cast at hh
   exact hp.2.trans hh

theorem actual_slope_error (C : ℕ → QI) (p q S ε : ℚ)
 (hC : ∀ j ≤ 23, Holds (C j) (wc 24 WindowKernel.d24 j p))
 (hl : S-ε+slopeError (q-p) ≤ (polyI (slopeCoeffs C) (q-p) 22).1)
 (hu : (polyI (slopeCoeffs C) (q-p) 22).2 ≤ S+ε-slopeError (q-p)) :
 |iteratedDeriv 1 f q-S| ≤ ε := by
 have h := actual_slope_interval C p q (S-ε) (S+ε) hC hl hu
 push_cast at h
 rw [abs_le]
 constructor <;> linarith [h.1,h.2]

set_option pp.fullNames true
#print axioms actual_value_lower
#print axioms actual_slope_error
end StructuralGoal20261016.WindowPointTableArithmetic
end
