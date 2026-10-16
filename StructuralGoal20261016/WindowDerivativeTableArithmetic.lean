/- SPDX-License-Identifier: Apache-2.0
Actual arbitrary derivative point intervals from the checked normalized
integer tables. In particular q=1,n=22 and q=3,n=20 supply the derivative
and third-derivative data used by the global minimizer cover.
-/
import StructuralGoal20261016.WindowPointTableArithmetic
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real
namespace StructuralGoal20261016.WindowDerivativeTableArithmetic
open WindowRationalInterval WindowNormalizedJets WindowConvexityCertificate
open WindowScalarMinorant WindowPointTableArithmetic WindowTaylorBridge

def shiftedCoeffs (C : ℕ → QI) (q j : ℕ) : QI :=
 rmul (point (((j+q).factorial:ℚ)/(j.factorial:ℚ))) (C (j+q))

theorem shifted_coeff (q j : ℕ) (p : ℝ) :
 iteratedDeriv j (iteratedDeriv q f) p/(j.factorial:ℝ) =
   ((j+q).factorial:ℝ)/(j.factorial:ℝ)*wc 24 WindowKernel.d24 (j+q) p := by
 rw [iterated_iterated]
 unfold wc
 have h0 : ((j+q).factorial:ℝ) ≠ 0 := by exact_mod_cast (j+q).factorial_ne_zero
 have h1 : (j.factorial:ℝ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
 field_simp [h0,h1]
 <;> ring

theorem shiftedCoeffs_sound (C : ℕ → QI) (p : ℝ) (q n : ℕ)
 (hqn : q+n ≤ 23) (hC : ∀ j ≤ 23, Holds (C j) (wc 24 WindowKernel.d24 j p)) :
 ∀ j ≤ n, Holds (shiftedCoeffs C q j)
   (iteratedDeriv j (iteratedDeriv q f) p/(j.factorial:ℝ)) := by
 intro j hj
 rw [shifted_coeff]
 exact rmul_sound (by
   simpa only [Rat.cast_div,Rat.cast_natCast] using
     point_sound (((j+q).factorial:ℚ)/(j.factorial:ℚ))) (hC (j+q) (by omega))

theorem derivative_remainder (q n : ℕ) (hqn : q+n+1 = 24) (p x : ℝ) :
 |iteratedDeriv q f x-taylorPoly (iteratedDeriv q f) n p x| ≤
   (44/7:ℝ)^24*|x-p|^(n+1)/((n+1).factorial:ℝ) := by
 apply taylor_remainder (iteratedDeriv q f)
   (fun m => w_iterated_contDiff 24 WindowKernel.d24 q m) n
 intro y
 rw [iterated_iterated,show n+1+q = 24 by omega]
 exact w24_twentyfour_abs_le y

def error (δ : ℚ) (n : ℕ) : ℚ := (44/7)^24*|δ|^(n+1)/(n+1).factorial

theorem actual_derivative_interval (C : ℕ → QI) (p x L U : ℚ) (q n : ℕ)
 (hqn : q+n+1 = 24)
 (hC : ∀ j ≤ 23, Holds (C j) (wc 24 WindowKernel.d24 j p))
 (hl : L+error (x-p) n ≤ (polyI (shiftedCoeffs C q) (x-p) n).1)
 (hu : (polyI (shiftedCoeffs C q) (x-p) n).2 ≤ U-error (x-p) n) :
 (L:ℝ) ≤ iteratedDeriv q f x ∧ iteratedDeriv q f x ≤ U := by
 have hp := polyI_sound (iteratedDeriv q f) p (shiftedCoeffs C q) (x-p) n
   (shiftedCoeffs_sound C p q n (by omega) hC)
 have he : (p:ℝ)+((x-p:ℚ):ℝ) = x := by push_cast; ring
 rw [he] at hp
 have hr := derivative_remainder q n hqn p x
 have herr : (44/7:ℝ)^24*|((x:ℝ)-p)|^(n+1)/((n+1).factorial:ℝ) =
     (error (x-p) n:ℝ) := by
   unfold error
   push_cast
   rfl
 rw [herr] at hr
 have hl' : ((L+error (x-p) n:ℚ):ℝ) ≤
     ((polyI (shiftedCoeffs C q) (x-p) n).1:ℝ) := Rat.cast_le.mpr hl
 have hu' : ((polyI (shiftedCoeffs C q) (x-p) n).2:ℝ) ≤
     ((U-error (x-p) n:ℚ):ℝ) := Rat.cast_le.mpr hu
 push_cast at hl' hu'
 exact ⟨by linarith [hp.1,(abs_le.mp hr).1],by linarith [hp.2,(abs_le.mp hr).2]⟩

set_option pp.fullNames true
#print axioms derivative_remainder
#print axioms actual_derivative_interval
end StructuralGoal20261016.WindowDerivativeTableArithmetic
end
