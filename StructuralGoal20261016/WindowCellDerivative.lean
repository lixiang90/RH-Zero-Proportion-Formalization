/- SPDX-License-Identifier: Apache-2.0
Actual derivative enclosures on a rational cell, using compact certified
corner choices for Horner evaluation. The same frozen coefficient table
and uniform half-unit Taylor remainder are used as in the numerical oracle.
-/
import StructuralGoal20261016.WindowFixedDerivative
import StructuralGoal20261016.WindowFixedHornerChoice
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowCellDerivative
open WindowRationalInterval (Holds)
open WindowFixedInterval WindowFixedRational
open WindowFixedPolynomial (lowerCheck upperCheck lowerCheck_sound upperCheck_sound)
open WindowScalarMinorant WindowConvexityCertificate
open WindowFixedDerivative (coeff coeff_sound)
open WindowDerivativeTableArithmetic (error derivative_remainder)

def box (n : ℕ) (a b : ℚ) : FI := ofQI (a-n,b-n)
def poly (n q d : ℕ) (a b : ℚ) (mask : ℕ) : FI :=
 WindowFixedHornerChoice.poly (coeff n q) (box n a b) mask d
def check (n q d : ℕ) (a b : ℚ) (mask : ℕ) (L U : ℚ) : Bool := decide (
 1 ≤ n ∧ n ≤ 32 ∧ q+d+1 = 24 ∧ a ≤ b ∧ -(1/2:ℚ) ≤ a-n ∧ b-n ≤ 1/2 ∧
 WindowFixedHornerChoice.check (coeff n q) (box n a b) mask d = true ∧
 lowerCheck (poly n q d a b mask) (L+error (1/2) d) = true ∧
 upperCheck (poly n q d a b mask) (U-error (1/2) d) = true)

theorem interval {n q d mask : ℕ} {a b L U : ℚ}
 (hc : check n q d a b mask L U = true) {x : ℝ} (hx : x ∈ Icc (a:ℝ) b) :
 (L:ℝ) ≤ iteratedDeriv q f x ∧ iteratedDeriv q f x ≤ (U:ℝ) := by
 have hh : 1 ≤ n ∧ n ≤ 32 ∧ q+d+1 = 24 ∧ a ≤ b ∧ -(1/2:ℚ) ≤ a-n ∧ b-n ≤ 1/2 ∧
     WindowFixedHornerChoice.check (coeff n q) (box n a b) mask d = true ∧
     lowerCheck (poly n q d a b mask) (L+error (1/2) d) = true ∧
     upperCheck (poly n q d a b mask) (U-error (1/2) d) = true := of_decide_eq_true hc
 have hn0 := hh.1
 have hn1 := hh.2.1
 have hqd := hh.2.2.1
 have hleft := hh.2.2.2.2.1
 have hright := hh.2.2.2.2.2.1
 have hchoice := hh.2.2.2.2.2.2.1
 have hlower := hh.2.2.2.2.2.2.2.1
 have hupper := hh.2.2.2.2.2.2.2.2
 have hX : Holds (decode (box n a b)) (x-(n:ℝ)) := by
   apply ofQI_sound
   unfold Holds
   push_cast
   exact ⟨sub_le_sub_right hx.1 _,sub_le_sub_right hx.2 _⟩
 have hp := WindowFixedHornerChoice.sound (coeff n q)
   (fun j => iteratedDeriv j (iteratedDeriv q f) (n:ℝ)/(j.factorial:ℝ))
   (box n a b) (x-(n:ℝ)) mask d (coeff_sound hn0 hn1 (by omega)) hX hchoice
 change Holds (decode (poly n q d a b mask)) (taylorPoly (iteratedDeriv q f) d (n:ℝ) x) at hp
 have ha : -(1/2:ℝ) ≤ (a:ℝ)-(n:ℝ) := by
   have hh : ((-(1/2:ℚ):ℚ):ℝ) ≤ ((a-n:ℚ):ℝ) := Rat.cast_le.mpr hleft
   push_cast at hh
   exact hh
 have hb : (b:ℝ)-(n:ℝ) ≤ 1/2 := by
   have hh : ((b-n:ℚ):ℝ) ≤ ((1/2:ℚ):ℝ) := Rat.cast_le.mpr hright
   push_cast at hh
   exact hh
 have hrad : |x-(n:ℝ)| ≤ 1/2 := by
   rw [abs_le]
   constructor <;> linarith [hx.1,hx.2]
 have he : (error (1/2) d:ℝ) = (44/7:ℝ)^24*(1/2)^(d+1)/((d+1).factorial:ℝ) := by
   unfold error
   push_cast
   rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
 have hr := derivative_remainder q d hqd (n:ℝ) x
 have hrem : |iteratedDeriv q f x-taylorPoly (iteratedDeriv q f) d (n:ℝ) x| ≤ (error (1/2) d:ℝ) := by
   rw [he]
   apply hr.trans
   apply div_le_div_of_nonneg_right _ (by positivity)
   exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hrad (d+1)) (by positivity)
 have hl := lowerCheck_sound hlower hp
 have hu := upperCheck_sound hupper hp
 push_cast at hl hu
 exact ⟨by linarith [(abs_le.mp hrem).1],by linarith [(abs_le.mp hrem).2]⟩

set_option pp.fullNames true
#print axioms interval
end StructuralGoal20261016.WindowCellDerivative
end
