/- SPDX-License-Identifier: Apache-2.0
Fraction-free finite summation of the actual Fourier kernel coefficients.
Elementary sinc moments are read from their already checked table. Only
the new finite kernel sums and convolutions remain to be checked here.
-/
import StructuralGoal20261016.WindowFixedRational
import StructuralGoal20261016.WindowJetTablesAll
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real
open scoped BigOperators
namespace StructuralGoal20261016.WindowFixedKernel
open WindowRationalInterval (Holds)
open WindowNormalizedJets WindowIntegerJetRecipe
open WindowIntegerKernelRecipe WindowJetTableData WindowJetTablesAll WindowFixedRational
namespace FI
open WindowFixedInterval

def sum (F : ℕ → FI) : ℕ → FI
 | 0 => point 0
 | m+1 => add (sum F m) (F m)

theorem sum_sound (F : ℕ → FI) (f : ℕ → ℝ) (m : ℕ)
 (h : ∀ j < m, Holds (decode (F j)) (f j)) :
 Holds (decode (sum F m)) (∑ j ∈ Finset.range m, f j) := by
 induction m with
 | zero => simpa only [sum,Finset.sum_range_zero,Int.cast_zero] using point_sound 0
 | succ m ih =>
   rw [Finset.sum_range_succ]
   exact add_sound (ih (fun j hj => h j (by omega))) (h m (by omega))

def mode (n r j : ℕ) : FI := add
 (mul (ofQI (WindowRationalInterval.point (coeffQ j))) (ofQI (Cos ((n:ℤ)-((j:ℤ)+1)) r)))
 (mul (ofQI (WindowRationalInterval.point (coeffQ j))) (ofQI (Cos ((n:ℤ)+((j:ℤ)+1)) r)))

theorem mode_sound {n r j : ℕ} (hn0 : 1 ≤ n) (hn1 : n ≤ 32) (hr : r ≤ 23) (hj : j < 24) :
 Holds (decode (mode n r j)) (WindowKernel.d24 j*
   (b r (π*n-π*((j:ℝ)+1))+b r (π*n+π*((j:ℝ)+1)))) := by
 have hd : Holds (decode (ofQI (WindowRationalInterval.point (coeffQ j)))) (WindowKernel.d24 j) := by
   apply ofQI_sound
   convert WindowRationalInterval.point_sound (coeffQ j) using 1 <;> norm_num [coeffQ,WindowKernel.d24]
 have h := add_sound
   (mul_sound hd (ofQI_sound (cos_sound (m := (n:ℤ)-((j:ℤ)+1)) (by omega) (by omega) r hr)))
   (mul_sound hd (ofQI_sound (cos_sound (m := (n:ℤ)+((j:ℤ)+1)) (by omega) (by omega) r hr)))
 unfold mode
 convert h using 1 <;> push_cast <;> ring

def denom : FI := mul (point 2) (ofQI normI)
def kernel (n r : ℕ) : FI := div
 (add (add (ofQI (Base n false r)) (ofQI (Base n true r))) (sum (mode n r) 24)) denom
def square (n r : ℕ) : FI := sum
 (fun j => mul (ofQI (K n j)) (ofQI (K n (r-j)))) (r+1)

theorem denom_guard : 0 < denom.1 ∨ denom.2 < 0 := by decide +kernel

theorem kernel_sound {n r : ℕ} (hn0 : 1 ≤ n) (hn1 : n ≤ 32) (hr : r ≤ 23) :
 Holds (decode (kernel n r)) (kc 24 WindowKernel.d24 r (n:ℝ)) := by
 rw [kc_eq_finite_b]
 apply div_sound
 · apply add_sound
   · have h := add_sound (ofQI_sound (base_sound hn0 hn1 false r hr))
       (ofQI_sound (base_sound hn0 hn1 true r hr))
     simpa [baseZ,sub_eq_add_neg] using h
   · exact sum_sound _ _ _ (fun j hj => mode_sound hn0 hn1 hr hj)
 · exact mul_sound (point_sound 2) (ofQI_sound normI_sound)
 · exact denom_guard

theorem kernel_of_check {n r : ℕ} (hn0 : 1 ≤ n) (hn1 : n ≤ 32) (hr : r ≤ 23)
 (hc : coversQ (kernel n r) (K n r) = true) :
 Holds (K n r) (kc 24 WindowKernel.d24 r (n:ℝ)) :=
 coversQ_sound hc (kernel_sound hn0 hn1 hr)

theorem square_sound {n r : ℕ}
 (hK : ∀ j ≤ r, Holds (K n j) (kc 24 WindowKernel.d24 j (n:ℝ))) :
 Holds (decode (square n r)) (wc 24 WindowKernel.d24 r (n:ℝ)) := by
 rw [wc_convolution]
 exact sum_sound _ _ _ (fun j hj => mul_sound
   (ofQI_sound (hK j (by omega))) (ofQI_sound (hK (r-j) (by omega))))

theorem square_of_check {n r : ℕ}
 (hK : ∀ j ≤ r, Holds (K n j) (kc 24 WindowKernel.d24 j (n:ℝ)))
 (hc : coversQ (square n r) (W n r) = true) :
 Holds (W n r) (wc 24 WindowKernel.d24 r (n:ℝ)) := coversQ_sound hc (square_sound hK)

set_option pp.fullNames true
#print axioms kernel_of_check
#print axioms square_of_check
end FI
end StructuralGoal20261016.WindowFixedKernel
end
