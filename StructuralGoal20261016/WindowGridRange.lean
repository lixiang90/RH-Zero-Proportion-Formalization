/- SPDX-License-Identifier: Apache-2.0
Finite adjacent-cell coverage and exact range-query consumers. The range
checker examines only its selected consecutive cells. Endpoint membership
is inclusive, so a query ending exactly at a grid boundary is covered by
the cell on its left, as in the original outward-rounded oracle.
-/
import StructuralGoal20261016.WindowGridCertificateData
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowGridRange
open WindowGridCertificate WindowGridCertificateData

theorem covered (k0 k1 : ℕ) (h : k0 ≤ k1) (x : ℝ)
 (hx : x ∈ Icc (left k0:ℝ) (right k1:ℝ)) :
 ∃ k, k0 ≤ k ∧ k ≤ k1 ∧ x ∈ Icc (left k:ℝ) (right k:ℝ) := by
 induction k1 generalizing k0 x with
 | zero =>
   have hz : k0 = 0 := by omega
   subst k0
   exact ⟨0,le_rfl,le_rfl,hx⟩
 | succ k ih =>
   by_cases hk : k0 ≤ k
   · by_cases hright : x ≤ (right k:ℝ)
     · obtain ⟨j,hj0,hj1,hjx⟩ := ih (k0 := k0) (x := x) hk ⟨hx.1,hright⟩
       exact ⟨j,hj0,by omega,hjx⟩
     · refine ⟨k+1,by omega,le_rfl,?_,hx.2⟩
       have he : (left (k+1):ℝ) = (right k:ℝ) := rfl
       rw [he]
       exact le_of_not_ge hright
   · have he : k0 = k+1 := by omega
     subst k0
     exact ⟨k+1,le_rfl,le_rfl,hx⟩

def GridSound : Prop := ∀ k : ℕ, 61 ≤ k → k < 2048 → Valid k (row (k-61))

def check (k0 k1 : ℕ) (a b L U M : ℚ) : Bool := decide (
 61 ≤ k0 ∧ k0 ≤ k1 ∧ k1 < 2048 ∧ left k0 ≤ a ∧ b ≤ right k1 ∧
 ∀ j : Fin (k1+1-k0),
   L ≤ ((row (k0+(j:ℕ)-61)).lower:ℚ)/10^15 ∧
   ((row (k0+(j:ℕ)-61)).upper:ℚ)/10^15 ≤ U ∧
   ((row (k0+(j:ℕ)-61)).third:ℚ)/10^15 ≤ M)

theorem sound (hgrid : GridSound) {k0 k1 : ℕ} {a b L U M : ℚ}
 (hc : check k0 k1 a b L U M = true) {x : ℝ} (hx : x ∈ Icc (a:ℝ) b) :
 (L:ℝ) ≤ WindowGapEnergy.w1 x ∧ WindowGapEnergy.w1 x ≤ (U:ℝ) ∧
   |iteratedDeriv 3 WindowScalarMinorant.f x| ≤ (M:ℝ) := by
 have hh : 61 ≤ k0 ∧ k0 ≤ k1 ∧ k1 < 2048 ∧ left k0 ≤ a ∧ b ≤ right k1 ∧
     ∀ j : Fin (k1+1-k0),
       L ≤ ((row (k0+(j:ℕ)-61)).lower:ℚ)/10^15 ∧
       ((row (k0+(j:ℕ)-61)).upper:ℚ)/10^15 ≤ U ∧
       ((row (k0+(j:ℕ)-61)).third:ℚ)/10^15 ≤ M := of_decide_eq_true hc
 have ha : (left k0:ℝ) ≤ (a:ℝ) := Rat.cast_le.mpr hh.2.2.2.1
 have hb : (b:ℝ) ≤ (right k1:ℝ) := Rat.cast_le.mpr hh.2.2.2.2.1
 obtain ⟨k,hk0,hk1,hxk⟩ := covered k0 k1 hh.2.1 x ⟨ha.trans hx.1,hx.2.trans hb⟩
 have hj : k-k0 < k1+1-k0 := by omega
 have he : k0+(k-k0) = k := by omega
 have hv := hh.2.2.2.2.2 ⟨k-k0,hj⟩
 change L ≤ ((row (k0+(k-k0)-61)).lower:ℚ)/10^15 ∧
   ((row (k0+(k-k0)-61)).upper:ℚ)/10^15 ≤ U ∧
   ((row (k0+(k-k0)-61)).third:ℚ)/10^15 ≤ M at hv
 rw [he] at hv
 have hlo : (L:ℝ) ≤ ((((row (k-61)).lower:ℚ)/10^15:ℚ):ℝ) := Rat.cast_le.mpr hv.1
 have hup : (((((row (k-61)).upper:ℚ)/10^15:ℚ):ℝ)) ≤ (U:ℝ) := Rat.cast_le.mpr hv.2.1
 have hM : (((((row (k-61)).third:ℚ)/10^15:ℚ):ℝ)) ≤ (M:ℝ) := Rat.cast_le.mpr hv.2.2
 push_cast at hlo hup hM
 have hs := hgrid k (by omega) (by omega) x hxk
 exact ⟨hlo.trans hs.1,hs.2.1.trans hup,hs.2.2.trans hM⟩

/-- The original oracle uses these global payments beyond its finite grid. -/
theorem fallback (x : ℝ) : |WindowGapEnergy.w1 x| ≤ 7 ∧
 |iteratedDeriv 3 WindowScalarMinorant.f x| ≤ (44/7:ℝ)^3 := by
 have h1 := WindowTaylorBridge.w24_iterated_abs_le 1 x
 change |iteratedDeriv 1 WindowScalarMinorant.f x| ≤ (44/7:ℝ)^1 at h1
 rw [iteratedDeriv_one,(WindowGapEnergy.w_hasDerivAt x).deriv] at h1
 exact ⟨h1.trans (by norm_num),WindowTaylorBridge.w24_iterated_abs_le 3 x⟩

theorem interval_affine {x m E : ℝ}
 (hlo : m-E ≤ -7) (hup : 7 ≤ m+E) : |WindowGapEnergy.w1 x-m| ≤ E := by
 obtain ⟨hl,hu⟩ := abs_le.mp (fallback x).1
 rw [abs_le]
 constructor <;> linarith

set_option pp.fullNames true
#print axioms covered
#print axioms sound
#print axioms fallback
#print axioms interval_affine
end StructuralGoal20261016.WindowGridRange
end
