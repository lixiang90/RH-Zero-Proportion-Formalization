/- SPDX-License-Identifier: Apache-2.0
Soundness of a compact certificate row for the frozen separated-cell oracle.
The checker consumes four-bit Horner corner choices and keeps the original
10^-15 outward-rounded endpoints and third-derivative payment unchanged.
-/
import StructuralGoal20261016.WindowCellDerivative
import StructuralGoal20261016.WindowGapEnergy
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowGridCertificate
open WindowScalarMinorant

structure Row where
 mask1 : ℕ
 mask3 : ℕ
 lower : ℤ
 upper : ℤ
 third : ℤ
def defaultRow : Row := ⟨0,0,0,0,0⟩
def left (k : ℕ) : ℚ := (k:ℚ)/64
def right (k : ℕ) : ℚ := ((k+1:ℕ):ℚ)/64
def center (k : ℕ) : ℕ := (k+32)/64
def check (k : ℕ) (r : Row) : Bool := decide (61 ≤ k ∧ k < 2048 ∧
 WindowCellDerivative.check (center k) 1 22 (left k) (right k) r.mask1
   ((r.lower:ℚ)/10^15) ((r.upper:ℚ)/10^15) = true ∧
 WindowCellDerivative.check (center k) 3 20 (left k) (right k) r.mask3
   (-(r.third:ℚ)/10^15) ((r.third:ℚ)/10^15) = true)

def Valid (k : ℕ) (r : Row) : Prop := ∀ x ∈ Icc (left k:ℝ) (right k:ℝ),
 (r.lower:ℝ)/10^15 ≤ WindowGapEnergy.w1 x ∧ WindowGapEnergy.w1 x ≤ (r.upper:ℝ)/10^15 ∧
 |iteratedDeriv 3 f x| ≤ (r.third:ℝ)/10^15

theorem sound {k : ℕ} {r : Row} (hc : check k r = true) : Valid k r := by
 have hh : 61 ≤ k ∧ k < 2048 ∧
     WindowCellDerivative.check (center k) 1 22 (left k) (right k) r.mask1
       ((r.lower:ℚ)/10^15) ((r.upper:ℚ)/10^15) = true ∧
     WindowCellDerivative.check (center k) 3 20 (left k) (right k) r.mask3
       (-(r.third:ℚ)/10^15) ((r.third:ℚ)/10^15) = true := of_decide_eq_true hc
 intro x hx
 have h1 := WindowCellDerivative.interval hh.2.2.1 hx
 have h3 := WindowCellDerivative.interval hh.2.2.2 hx
 have he : iteratedDeriv 1 f x = WindowGapEnergy.w1 x := by
   rw [iteratedDeriv_one]
   exact (WindowGapEnergy.w_hasDerivAt x).deriv
 rw [he] at h1
 push_cast at h1 h3
 exact ⟨h1.1,h1.2,abs_le.mpr (by simpa only [neg_div] using h3)⟩

set_option pp.fullNames true
#print axioms sound
end StructuralGoal20261016.WindowGridCertificate
end
