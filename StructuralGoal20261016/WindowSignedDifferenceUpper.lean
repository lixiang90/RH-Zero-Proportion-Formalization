/- SPDX-License-Identifier: Apache-2.0
Signed derivative upper bounds for an integer translation difference. Both
Taylor polynomials use the same x-n coordinate, so coefficient subtraction
precedes interval Horner evaluation. The certificate supplies only corner
choices; all selected product corners are checked. No new transcendental
table, or independence between the two translated values, is assumed.
-/
import StructuralGoal20261016.WindowCellDerivative
import StructuralGoal20261016.WindowFiniteMoveScalar
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real Set
open scoped BigOperators
namespace StructuralGoal20261016.WindowSignedDifferenceUpper
open WindowRationalInterval (Holds)
open WindowFixedInterval WindowFixedRational
open WindowFixedPolynomial (upperCheck upperCheck_sound)
open WindowScalarMinorant WindowConvexityCertificate
open WindowDerivativeTableArithmetic (error derivative_remainder)

def coeff (n m q j : ℕ) : FI :=
 WindowFixedInterval.sub (WindowFixedDerivative.coeff m q j)
   (WindowFixedDerivative.coeff n q j)

theorem coeff_sound {n m q d : ℕ}
 (hn0 : 1 ≤ n) (hn1 : n ≤ 32) (hm0 : 1 ≤ m) (hm1 : m ≤ 32)
 (hqd : q+d ≤ 23) : ∀ j ≤ d, Holds (decode (coeff n m q j))
   (iteratedDeriv j (iteratedDeriv q f) (m:ℝ)/(j.factorial:ℝ)-
    iteratedDeriv j (iteratedDeriv q f) (n:ℝ)/(j.factorial:ℝ)) := by
 intro j hj
 exact WindowFixedInterval.sub_sound
   (WindowFixedDerivative.coeff_sound hm0 hm1 hqd j hj)
   (WindowFixedDerivative.coeff_sound hn0 hn1 hqd j hj)

def poly (n m q d : ℕ) (a b : ℚ) (mask : ℕ) : FI :=
 WindowFixedHornerChoice.poly (coeff n m q)
   (WindowCellDerivative.box n a b) mask d

def check (n m q d : ℕ) (a b : ℚ) (mask : ℕ) (U : ℚ) : Bool := decide (
 1 ≤ n ∧ n ≤ 32 ∧ 1 ≤ m ∧ m ≤ 32 ∧ q+d+1 = 24 ∧ a ≤ b ∧
 -(1/2:ℚ) ≤ a-n ∧ b-n ≤ 1/2 ∧
 WindowFixedHornerChoice.check (coeff n m q)
   (WindowCellDerivative.box n a b) mask d = true ∧
 upperCheck (poly n m q d a b mask) (U-2*error (1/2) d) = true)

theorem polynomial_eq (n m q d : ℕ) (x : ℝ) :
 (∑ j ∈ Finset.range (d+1),
   (iteratedDeriv j (iteratedDeriv q f) (m:ℝ)/(j.factorial:ℝ)-
    iteratedDeriv j (iteratedDeriv q f) (n:ℝ)/(j.factorial:ℝ))*(x-(n:ℝ))^j) =
 taylorPoly (iteratedDeriv q f) d (m:ℝ) (x+((m:ℝ)-n))-
 taylorPoly (iteratedDeriv q f) d (n:ℝ) x := by
 unfold taylorPoly
 rw [← Finset.sum_sub_distrib]
 apply Finset.sum_congr rfl
 intro j _
 have he : x+((m:ℝ)-n)-(m:ℝ) = x-(n:ℝ) := by ring
 rw [he]
 ring

theorem half_remainder {q d : ℕ} (hqd : q+d+1 = 24) (p x : ℝ)
 (hrad : |x-p| ≤ 1/2) :
 |iteratedDeriv q f x-taylorPoly (iteratedDeriv q f) d p x| ≤
   (error (1/2) d:ℝ) := by
 have he : (error (1/2) d:ℝ) =
     (44/7:ℝ)^24*(1/2)^(d+1)/((d+1).factorial:ℝ) := by
   unfold error
   push_cast
   rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
 rw [he]
 apply (derivative_remainder q d hqd p x).trans
 apply div_le_div_of_nonneg_right _ (by positivity)
 exact mul_le_mul_of_nonneg_left
   (pow_le_pow_left₀ (abs_nonneg _) hrad (d+1)) (by positivity)

/-- A single signed upper certificate for any derivative of a translated
difference. The special case q=2, d=21 supplies the curvature upper bounds
needed for concave finite-move tangents. -/
theorem upper {n m q d mask : ℕ} {a b U : ℚ}
 (hc : check n m q d a b mask U = true)
 {x : ℝ} (hx : x ∈ Icc (a:ℝ) b) :
 iteratedDeriv q (WindowFiniteMoveScalar.h ((m:ℝ)-n)) x ≤ (U:ℝ) := by
 have hh : 1 ≤ n ∧ n ≤ 32 ∧ 1 ≤ m ∧ m ≤ 32 ∧ q+d+1 = 24 ∧ a ≤ b ∧
     -(1/2:ℚ) ≤ a-n ∧ b-n ≤ 1/2 ∧
     WindowFixedHornerChoice.check (coeff n m q)
       (WindowCellDerivative.box n a b) mask d = true ∧
     upperCheck (poly n m q d a b mask) (U-2*error (1/2) d) = true :=
   of_decide_eq_true hc
 have hn0 := hh.1
 have hn1 := hh.2.1
 have hm0 := hh.2.2.1
 have hm1 := hh.2.2.2.1
 have hqd := hh.2.2.2.2.1
 have hleft := hh.2.2.2.2.2.2.1
 have hright := hh.2.2.2.2.2.2.2.1
 have hchoice := hh.2.2.2.2.2.2.2.2.1
 have hupper := hh.2.2.2.2.2.2.2.2.2
 have hX : Holds (decode (WindowCellDerivative.box n a b)) (x-(n:ℝ)) := by
   apply ofQI_sound
   unfold Holds
   push_cast
   exact ⟨sub_le_sub_right hx.1 _,sub_le_sub_right hx.2 _⟩
 have hp := WindowFixedHornerChoice.sound (coeff n m q)
   (fun j => iteratedDeriv j (iteratedDeriv q f) (m:ℝ)/(j.factorial:ℝ)-
     iteratedDeriv j (iteratedDeriv q f) (n:ℝ)/(j.factorial:ℝ))
   (WindowCellDerivative.box n a b) (x-(n:ℝ)) mask d
   (coeff_sound hn0 hn1 hm0 hm1 (by omega)) hX hchoice
 change Holds (decode (poly n m q d a b mask))
   (∑ j ∈ Finset.range (d+1),
     (iteratedDeriv j (iteratedDeriv q f) (m:ℝ)/(j.factorial:ℝ)-
      iteratedDeriv j (iteratedDeriv q f) (n:ℝ)/(j.factorial:ℝ))*(x-(n:ℝ))^j) at hp
 rw [polynomial_eq] at hp
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
 have he : x+((m:ℝ)-n)-(m:ℝ) = x-(n:ℝ) := by ring
 have hnrem := half_remainder hqd (n:ℝ) x hrad
 have hmrem := half_remainder hqd (m:ℝ) (x+((m:ℝ)-n)) (by rwa [he])
 have hu := upperCheck_sound hupper hp
 push_cast at hu
 rw [WindowFiniteMoveScalar.iterated_h]
 change iteratedDeriv q f (x+((m:ℝ)-n))-iteratedDeriv q f x ≤ (U:ℝ)
 linarith [(abs_le.mp hmrem).2,(abs_le.mp hnrem).1]

theorem second_upper {n m mask : ℕ} {a b U : ℚ}
 (hc : check n m 2 21 a b mask U = true)
 {x : ℝ} (hx : x ∈ Icc (a:ℝ) b) :
 iteratedDeriv 2 (WindowFiniteMoveScalar.h ((m:ℝ)-n)) x ≤ (U:ℝ) :=
 upper hc hx

theorem concave {n m mask : ℕ} {a b U : ℚ}
 (hc : check n m 2 21 a b mask U = true) (hU : U ≤ 0)
 {x : ℝ} (hx : x ∈ Icc (a:ℝ) b) :
 iteratedDeriv 2 (WindowFiniteMoveScalar.h ((m:ℝ)-n)) x ≤ 0 := by
 exact (second_upper hc hx).trans (by exact_mod_cast hU)

set_option pp.fullNames true
#print axioms coeff_sound
#print axioms polynomial_eq
#print axioms half_remainder
#print axioms upper
#print axioms second_upper
#print axioms concave
end StructuralGoal20261016.WindowSignedDifferenceUpper
end
