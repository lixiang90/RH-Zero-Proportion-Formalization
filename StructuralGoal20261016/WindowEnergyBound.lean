/- SPDX-License-Identifier: Apache-2.0
Conservative rational lower bound on the actual 24-mode analytic energy.
Adapted from the attributed AMW.PAM_le/HW_ge proof, using the same proven
sine/cosine enclosures. No global gap floor or zero-counting bound is assumed.
-/
import StructuralGoal20261016.WindowKernel
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory
open scoped BigOperators
open AMW
namespace StructuralGoal20261016.WindowEnergyBound

def penaltyHi : ℝ :=
 ∑ n ∈ Finset.range 24, WindowKernel.d24 n ^ 2 * (1 / 2 - 1 / (4 * (314159265358979323847 / 10 ^ 20) ^ 2 * ((n : ℝ) + 1) ^ 2))
theorem penalty_le : WindowEnergy.penalty 24 WindowKernel.d24 ≤ penaltyHi := by
 unfold WindowEnergy.penalty penaltyHi
 apply Finset.sum_le_sum
 intro n _
 apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
 apply sub_le_sub_left
 have hπ := Real.pi_lt_d20
 have hπ0 := Real.pi_pos
 have hk : (0:ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
 apply one_div_le_one_div_of_le (by positivity)
 have : π ^ 2 ≤ (314159265358979323847 / 10 ^ 20 : ℝ) ^ 2 := by
   apply pow_le_pow_left₀ hπ0.le; linarith
 have := mul_le_mul_of_nonneg_right this hk.le
 nlinarith
theorem penaltyHi_nonneg : 0 ≤ penaltyHi := by
 unfold penaltyHi
 apply Finset.sum_nonneg
 intro n _
 apply mul_nonneg (sq_nonneg _)
 have hk : (1:ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
   have : (1:ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
   nlinarith
 have : 1 / (4 * (314159265358979323847 / 10 ^ 20 : ℝ) ^ 2 * ((n : ℝ) + 1) ^ 2) ≤ 1 / 2 := by
   rw [div_le_div_iff₀ (by positivity) (by norm_num)]
   nlinarith
 linarith
theorem floor_numeric :
   (6720963398090236473924 / 10 ^ 22 : ℝ) ≤ 3 / 2 - (760244597075630151253567702555 / 10 ^ 30) / (2 * (707106781186547524400844362104/10^30) * (649636939080062444129454621098 / 10 ^ 30))
     - penaltyHi / (2 * (649636939080062444129454621098 / 10 ^ 30) ^ 2) := by
 unfold penaltyHi WindowKernel.d24
 simp only [Finset.sum_range_succ, Finset.sum_range_zero, StructuralW10Followup20261016.NewWindows.nums24]
 norm_num
theorem H24_ge : (6720963398090236473924 / 10 ^ 22 : ℝ) ≤ WindowEnergy.H 24 WindowKernel.d24 := by
 rw [WindowEnergy.H_eq]
 have hc := cos_theta0_le
 have hs := sin_theta0_ge
 have hb := sqrt2_half_bounds
 have hP := penalty_le
 have hP0 := penaltyHi_nonneg
 have hs0 : (0:ℝ) < 649636939080062444129454621098 / 10 ^ 30 := by norm_num
 have hr0 : (0:ℝ) < 707106781186547524400844362104/10^30 := by norm_num
 have hcos0 : 0 ≤ Real.cos (Real.sqrt 2 / 2) :=
   Real.cos_nonneg_of_mem_Icc ⟨by linarith [hb.1, Real.pi_gt_three], by linarith [hb.2, Real.pi_gt_three]⟩
 have hden : 2 * (707106781186547524400844362104/10^30 : ℝ) * (649636939080062444129454621098 / 10 ^ 30)
     ≤ Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) := by
   have h2 : 2 * (707106781186547524400844362104/10^30 : ℝ) ≤ Real.sqrt 2 := by linarith [hb.1]
   exact mul_le_mul h2 hs hs0.le (Real.sqrt_nonneg 2)
 have h1 : Real.cos (Real.sqrt 2 / 2) / (Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2))
     ≤ (760244597075630151253567702555 / 10 ^ 30) / (2 * (707106781186547524400844362104/10^30) * (649636939080062444129454621098 / 10 ^ 30)) :=
   div_le_div₀ (by norm_num) hc (by positivity) hden
 have hsq : (649636939080062444129454621098 / 10 ^ 30 : ℝ) ^ 2 ≤ Real.sin (Real.sqrt 2 / 2) ^ 2 :=
   pow_le_pow_left₀ hs0.le hs 2
 have h2 : WindowEnergy.penalty 24 WindowKernel.d24 / (2 * Real.sin (Real.sqrt 2 / 2) ^ 2) ≤ penaltyHi / (2 * (649636939080062444129454621098 / 10 ^ 30) ^ 2) :=
   div_le_div₀ hP0 hP (by positivity) (by linarith)
 have := floor_numeric
 linarith

#print axioms penalty_le
#print axioms floor_numeric
#print axioms H24_ge
end StructuralGoal20261016.WindowEnergyBound
end
