/- SPDX-License-Identifier: Apache-2.0
Actual normalized integer-centre kernel coefficients obtained by exact
rounded interval arithmetic. This module contains no numerical jet table.
-/
import StructuralGoal20261016.WindowIntegerJetRecipe
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
noncomputable section
open Real
open scoped BigOperators
namespace StructuralGoal20261016.WindowIntegerKernelRecipe
open WindowRationalInterval WindowNormalizedJets WindowIntegerJetRecipe

def sumI (F : ℕ → QI) : ℕ → QI
 | 0 => point 0
 | n+1 => radd (sumI F n) (F n)

theorem sumI_sound (F : ℕ → QI) (f : ℕ → ℝ) (n : ℕ)
 (h : ∀ j < n, Holds (F j) (f j)) :
 Holds (sumI F n) (∑ j ∈ Finset.range n, f j) := by
 induction n with
 | zero => simp only [sumI, Finset.sum_range_zero]; norm_num [point,Holds]
 | succ n ih =>
   rw [Finset.sum_range_succ]
   exact radd_sound (ih (fun j hj => h j (by omega))) (h n (by omega))

def signI (m : ℤ) : QI := point ((-1:ℚ)^m)
theorem signI_sound (m : ℤ) : Holds (signI m) ((-1:ℝ)^m) := by
 simpa only [signI, Rat.cast_zpow, Rat.cast_neg, Rat.cast_one] using point_sound ((-1:ℚ)^m)

def baseZ (n : ℕ) (s : Bool) : ℝ := π*n+(if s then Real.sqrt 2/2 else -(Real.sqrt 2/2))
def baseZI (n : ℕ) (s : Bool) : QI :=
 radd (rmul piI (point n)) (if s then thetaI else rneg thetaI)
def baseSI (n : ℕ) (s : Bool) : QI :=
 rmul (signI n) (if s then sinI else rneg sinI)
def baseCI (n : ℕ) : QI := rmul (signI n) cosI

theorem baseZI_sound (n : ℕ) (s : Bool) : Holds (baseZI n s) (baseZ n s) := by
 apply radd_sound (rmul_sound piI_sound (by simpa only [Rat.cast_natCast] using point_sound (n:ℚ)))
 cases s
 · exact rneg_sound thetaI_sound
 · exact thetaI_sound

theorem base_trig_sound (n : ℕ) (s : Bool) :
 Holds (baseSI n s) (Real.sin (baseZ n s)) ∧
 Holds (baseCI n) (Real.cos (baseZ n s)) := by
 have hi := integer_sin_cos (n:ℤ) (if s then Real.sqrt 2/2 else -(Real.sqrt 2/2))
 simp only [Int.cast_natCast] at hi
 unfold baseZ
 rw [hi.1,hi.2]
 cases s
 · simp only [Bool.false_eq_true,if_false,Real.sin_neg,Real.cos_neg]
   exact ⟨rmul_sound (signI_sound n) (rneg_sound sinI_sound),rmul_sound (signI_sound n) cosI_sound⟩
 · simp only [if_true]
   exact ⟨rmul_sound (signI_sound n) sinI_sound,rmul_sound (signI_sound n) cosI_sound⟩

def baseBI (n : ℕ) (s : Bool) (r : ℕ) : QI := bI (baseZI n s) (baseSI n s) (baseCI n) r
def cosZI (m : ℤ) : QI := rmul piI (point m)
def cosBI (m : ℤ) (r : ℕ) : QI :=
 if m = 0 then poleI r else bI (cosZI m) (point 0) (signI m) r

theorem base_guard : ∀ n : Fin 33, ∀ s : Bool,
 0 < (baseZI n s).1 ∨ (baseZI n s).2 < 0 := by decide +kernel

theorem cos_guard : ∀ j : Fin 81, ((j:ℤ)-24) ≠ 0 →
 0 < (cosZI ((j:ℤ)-24)).1 ∨ (cosZI ((j:ℤ)-24)).2 < 0 := by decide +kernel

theorem baseBI_sound {n : ℕ} (hn : n < 33) (s : Bool) (r : ℕ) :
 Holds (baseBI n s r) (b r (baseZ n s)) :=
 bI_sound (baseZI_sound n s) (base_trig_sound n s).1 (base_trig_sound n s).2
   (base_guard ⟨n,hn⟩ s) r

theorem cosBI_sound {m : ℤ} (hm0 : -24 ≤ m) (hm1 : m ≤ 56) (r : ℕ) :
 Holds (cosBI m r) (b r (π*(m:ℝ))) := by
 by_cases hm : m = 0
 · subst m
   simpa only [cosBI,if_pos rfl,ite_true,Int.cast_zero,mul_zero] using poleI_sound r
 · rw [cosBI,if_neg hm]
   have hj : (m+24).toNat < 81 := by omega
   have he : (((m+24).toNat:ℕ):ℤ)-24 = m := by omega
   have hg := cos_guard ⟨(m+24).toNat,hj⟩ (by simpa only [he] using hm)
   simp only [he] at hg
   apply bI_sound
   · exact rmul_sound piI_sound (by simpa only [Rat.cast_intCast] using point_sound (m:ℚ))
   · have hs := Real.sin_int_mul_pi m
     rw [mul_comm] at hs
     simpa only [hs] using (show Holds (point 0) (0:ℝ) by norm_num [Holds,point])
   · have hc := Real.cos_int_mul_pi m
     rw [mul_comm] at hc
     rw [hc]
     exact signI_sound m
   · exact hg

def coeffQ (j : ℕ) : ℚ := (StructuralW10Followup20261016.NewWindows.nums24 j:ℚ)/10^9
def totalI (n r : ℕ) : QI :=
 radd (radd (baseBI n false r) (baseBI n true r))
   (sumI (fun j => radd
     (rmul (point (coeffQ j)) (cosBI ((n:ℤ)-((j:ℤ)+1)) r))
     (rmul (point (coeffQ j)) (cosBI ((n:ℤ)+((j:ℤ)+1)) r))) 24)
def kI (n r : ℕ) : QI := rdiv (totalI n r) (rmul (point 2) normI)
def wI (n r : ℕ) : QI := sumI (fun j => rmul (kI n j) (kI n (r-j))) (r+1)

theorem normalization_guard : 0 < (rmul (point 2) normI).1 ∨
 (rmul (point 2) normI).2 < 0 := by decide +kernel

theorem kI_sound {n : ℕ} (hn : n < 33) (r : ℕ) :
 Holds (kI n r) (kc 24 WindowKernel.d24 r (n:ℝ)) := by
 rw [kc_eq_finite_b]
 apply rdiv_sound
 · apply radd_sound
   · have h := radd_sound (baseBI_sound hn false r) (baseBI_sound hn true r)
     simpa [baseZ,sub_eq_add_neg] using h
   · apply sumI_sound
     intro j hj
     have hd : Holds (point (coeffQ j)) (WindowKernel.d24 j) := by
       convert point_sound (coeffQ j) using 1 <;> norm_num [coeffQ,WindowKernel.d24]
     have h := radd_sound
       (rmul_sound hd (cosBI_sound (m := (n:ℤ)-((j:ℤ)+1)) (by omega) (by omega) r))
       (rmul_sound hd (cosBI_sound (m := (n:ℤ)+((j:ℤ)+1)) (by omega) (by omega) r))
     convert h using 1 <;> push_cast <;> ring
 · exact rmul_sound (by norm_num [Holds,point]) normI_sound
 · exact normalization_guard

theorem wI_sound {n : ℕ} (hn : n < 33) (r : ℕ) :
 Holds (wI n r) (wc 24 WindowKernel.d24 r (n:ℝ)) := by
 rw [wc_convolution]
 exact sumI_sound _ _ _ (fun j _ => rmul_sound (kI_sound hn j) (kI_sound hn (r-j)))

#print axioms kI_sound
#print axioms wI_sound
end StructuralGoal20261016.WindowIntegerKernelRecipe
end
