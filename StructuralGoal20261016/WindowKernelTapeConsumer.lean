/- SPDX-License-Identifier: Apache-2.0
Linear partial-sum tapes for the actual normalized kernel coefficients.
Each finite check consumes two stored rational intervals; it never expands
the nested rounded sum of all 24 Fourier modes.
-/
import StructuralGoal20261016.WindowJetTablesAll
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real
open scoped BigOperators
namespace StructuralGoal20261016.WindowKernelTapeConsumer
open WindowRationalInterval WindowNormalizedJets WindowIntegerJetRecipe
open WindowIntegerKernelRecipe WindowJetTableConsumer WindowJetTableData WindowJetTablesAll

theorem sumTape_sound (T I : ℕ → QI) (f : ℕ → ℝ) (z : ℝ) (m : ℕ)
 (h0 : Holds (T 0) z)
 (hs : ∀ j < m, covers (radd (T j) (I j)) (T (j+1)) = true)
 (hI : ∀ j < m, Holds (I j) (f j)) :
 Holds (T m) (z+∑ j ∈ Finset.range m, f j) := by
 suffices ∀ k ≤ m, Holds (T k) (z+∑ j ∈ Finset.range k, f j) from this m le_rfl
 intro k hk
 induction k with
 | zero => simpa only [Finset.sum_range_zero,add_zero] using h0
 | succ k ih =>
   have h := covers_sound (hs k (by omega))
     (radd_sound (ih (by omega)) (hI k (by omega)))
   simpa only [Finset.sum_range_succ,add_assoc] using h

def modeI (n r j : ℕ) : QI := radd
 (rmul (point (coeffQ j)) (Cos ((n:ℤ)-((j:ℤ)+1)) r))
 (rmul (point (coeffQ j)) (Cos ((n:ℤ)+((j:ℤ)+1)) r))
def mode (n r j : ℕ) : ℝ := WindowKernel.d24 j*
 (b r (π*n-π*((j:ℝ)+1))+b r (π*n+π*((j:ℝ)+1)))

theorem modeI_sound {n r j : ℕ} (hn0 : 1 ≤ n) (hn1 : n ≤ 32) (hr : r ≤ 23) (hj : j < 24) :
 Holds (modeI n r j) (mode n r j) := by
 have hd : Holds (point (coeffQ j)) (WindowKernel.d24 j) := by
   convert point_sound (coeffQ j) using 1 <;> norm_num [coeffQ,WindowKernel.d24]
 have h := radd_sound
   (rmul_sound hd (cos_sound (m := (n:ℤ)-((j:ℤ)+1)) (by omega) (by omega) r hr))
   (rmul_sound hd (cos_sound (m := (n:ℤ)+((j:ℤ)+1)) (by omega) (by omega) r hr))
 unfold modeI mode
 convert h using 1 <;> push_cast <;> ring

theorem kTape_sound (n r : ℕ) (hn0 : 1 ≤ n) (hn1 : n ≤ 32) (hr : r ≤ 23)
 (T : ℕ → QI)
 (h0 : covers (radd (Base n false r) (Base n true r)) (T 0) = true)
 (hs : ∀ j < 24, covers (radd (T j) (modeI n r j)) (T (j+1)) = true)
 (hlast : covers (rdiv (T 24) (rmul (point 2) normI)) (K n r) = true) :
 Holds (K n r) (kc 24 WindowKernel.d24 r (n:ℝ)) := by
 have hb := covers_sound h0
   (radd_sound (base_sound hn0 hn1 false r hr) (base_sound hn0 hn1 true r hr))
 have ht := sumTape_sound T (modeI n r) (mode n r)
   (b r (baseZ n false)+b r (baseZ n true)) 24 hb hs
   (fun j hj => modeI_sound hn0 hn1 hr hj)
 have hd := rdiv_sound ht
   (rmul_sound (show Holds (point 2) (2:ℝ) by norm_num [Holds,point]) normI_sound)
   normalization_guard
 have h := covers_sound hlast hd
 rw [kc_eq_finite_b]
 simpa [mode,baseZ,sub_eq_add_neg] using h

theorem wTape_sound (n r : ℕ) (T : ℕ → QI)
 (hK : ∀ j ≤ r, Holds (K n j) (kc 24 WindowKernel.d24 j (n:ℝ)))
 (h0 : covers (point 0) (T 0) = true)
 (hs : ∀ j < r+1, covers (radd (T j) (rmul (K n j) (K n (r-j)))) (T (j+1)) = true)
 (hlast : covers (T (r+1)) (W n r) = true) :
 Holds (W n r) (wc 24 WindowKernel.d24 r (n:ℝ)) := by
 have ht := sumTape_sound T (fun j => rmul (K n j) (K n (r-j)))
   (fun j => kc 24 WindowKernel.d24 j (n:ℝ)*kc 24 WindowKernel.d24 (r-j) (n:ℝ))
   0 (r+1) (covers_sound h0 (by norm_num [Holds,point])) hs
   (fun j hj => rmul_sound (hK j (by omega)) (hK (r-j) (by omega)))
 have h := covers_sound hlast ht
 rw [wc_convolution]
 simpa only [zero_add] using h

set_option pp.fullNames true
#print axioms sumTape_sound
#print axioms kTape_sound
#print axioms wTape_sound
end StructuralGoal20261016.WindowKernelTapeConsumer
end
