/-
Exact rational refinement of the accepted master-of-puppets4 window floor.
Based on source copyright (c) 2026 R. Arun Chandru and Yuhang Shi.
Source commit: 65c71d512f51df92bec4a3d1edb6a795fc1cac63.
SPDX-License-Identifier: Apache-2.0

New contribution: thirty-digit root and trigonometric enclosures, propagated
through the existing order-20 Taylor and circle inequalities. No window
coefficient or weighted zero-counting certificate is changed here.
-/
import GramDefectRecord.Core

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option linter.all false
noncomputable section
open Real Set MeasureTheory Filter Topology AMW
namespace ProportionSharpWindow

theorem taylor20_F (θ : ℝ) (hθ : |θ| ≤ 1) :
   |Real.cos θ - (1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 + θ^12/479001600 - θ^14/87178291200 + θ^16/20922789888000 - θ^18/6402373705728000)|
       ≤ |θ|^20 * (1/2317049531596800000) ∧
   |Real.sin θ - (θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 + θ^13/6227020800 - θ^15/1307674368000 + θ^17/355687428096000 - θ^19/121645100408832000)|
       ≤ |θ|^20 * (1/2317049531596800000) := by
 have hx : ‖(θ : ℂ) * Complex.I‖ ≤ 1 := by
   simpa using hθ
 have hb := Complex.exp_bound hx (n := 20) (by norm_num)
 have hnx : ‖(θ : ℂ) * Complex.I‖ = |θ| := by simp
 have hsum : ∑ m ∈ Finset.range 20, ((θ : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)
     = ((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 + θ^12/479001600 - θ^14/87178291200 + θ^16/20922789888000 - θ^18/6402373705728000 : ℝ) : ℂ)
       + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 + θ^13/6227020800 - θ^15/1307674368000 + θ^17/355687428096000 - θ^19/121645100408832000 : ℝ) : ℂ)
         * Complex.I := by
   simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
   apply Complex.ext <;> · simp [pow_succ]; ring
 rw [hsum, hnx] at hb
 have hE : ‖Complex.exp ((θ : ℂ) * Complex.I)
     - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 + θ^12/479001600 - θ^14/87178291200 + θ^16/20922789888000 - θ^18/6402373705728000 : ℝ) : ℂ)
       + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 + θ^13/6227020800 - θ^15/1307674368000 + θ^17/355687428096000 - θ^19/121645100408832000 : ℝ) : ℂ)
         * Complex.I)‖ ≤ |θ|^20 * (1/2317049531596800000) := by
   refine hb.trans (le_of_eq ?_)
   norm_num
 constructor
 · have := Complex.abs_re_le_norm (Complex.exp ((θ : ℂ) * Complex.I)
     - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 + θ^12/479001600 - θ^14/87178291200 + θ^16/20922789888000 - θ^18/6402373705728000 : ℝ) : ℂ)
       + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 + θ^13/6227020800 - θ^15/1307674368000 + θ^17/355687428096000 - θ^19/121645100408832000 : ℝ) : ℂ)
         * Complex.I))
   refine le_trans (le_of_eq ?_) (this.trans hE)
   simp [Complex.exp_ofReal_mul_I_re, - Complex.ofReal_pow]
 · have := Complex.abs_im_le_norm (Complex.exp ((θ : ℂ) * Complex.I)
     - (((1 - θ^2/2 + θ^4/24 - θ^6/720 + θ^8/40320 - θ^10/3628800 + θ^12/479001600 - θ^14/87178291200 + θ^16/20922789888000 - θ^18/6402373705728000 : ℝ) : ℂ)
       + ((θ - θ^3/6 + θ^5/120 - θ^7/5040 + θ^9/362880 - θ^11/39916800 + θ^13/6227020800 - θ^15/1307674368000 + θ^17/355687428096000 - θ^19/121645100408832000 : ℝ) : ℂ)
         * Complex.I))
   refine le_trans (le_of_eq ?_) (this.trans hE)
   simp [Complex.exp_ofReal_mul_I_im, - Complex.ofReal_pow]
theorem sqrt2_half_bounds :
   (707106781186547524400844362104/10^30 : ℝ) ≤ Real.sqrt 2 / 2 ∧
     Real.sqrt 2 / 2 ≤ 707106781186547524400844362105/10^30 := by
 have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
 have hnn : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
 constructor <;> nlinarith [h2, hnn]
theorem cos_theta0_le : Real.cos (Real.sqrt 2 / 2) ≤ 760244597075630151253567702555 / 10 ^ 30 := by
 have hb := sqrt2_half_bounds
 set r : ℝ := 707106781186547524400844362104/10^30 with hr
 have hr0 : 0 ≤ r := by rw [hr]; norm_num
 have hr1 : |r| ≤ 1 := by rw [abs_of_nonneg hr0, hr]; norm_num
 have hmono : Real.cos (Real.sqrt 2 / 2) ≤ Real.cos r :=
   Real.cos_le_cos_of_nonneg_of_le_pi hr0 (by linarith [hb.2, Real.pi_gt_three]) hb.1
 have ht := (abs_le.mp (taylor20_F r hr1).1).2
 rw [abs_of_nonneg hr0] at ht
 have hv : (1 - r^2/2 + r^4/24 - r^6/720 + r^8/40320 - r^10/3628800 + r^12/479001600 - r^14/87178291200 + r^16/20922789888000 - r^18/6402373705728000) + r ^ 20 * (1/2317049531596800000)
     ≤ 760244597075630151253567702555 / 10 ^ 30 := by
   rw [hr]; norm_num
 linarith
theorem sin_theta0_ge : 649636939080062444129454621098 / 10 ^ 30 ≤ Real.sin (Real.sqrt 2 / 2) := by
 have hb := sqrt2_half_bounds
 have hc := cos_theta0_le
 have hc0 : 0 ≤ Real.cos (Real.sqrt 2 / 2) :=
   Real.cos_nonneg_of_mem_Icc ⟨by linarith [hb.1, Real.pi_gt_three], by linarith [hb.2, Real.pi_gt_three]⟩
 have hcsq : Real.cos (Real.sqrt 2 / 2) ^ 2 ≤ (760244597075630151253567702555 / 10 ^ 30 : ℝ) ^ 2 :=
   pow_le_pow_left₀ hc0 hc 2
 have hcircle := Real.sin_sq_add_cos_sq (Real.sqrt 2 / 2)
 have hs0 := sin_theta0_pos
 have hsq : (649636939080062444129454621098 / 10 ^ 30 : ℝ) ^ 2 ≤ Real.sin (Real.sqrt 2 / 2) ^ 2 := by
   nlinarith only [hcsq, hcircle]
 nlinarith only [hsq, hs0]
def PAMhi : ℝ :=
 ∑ n ∈ Finset.range 12, dAM n ^ 2 * (1 / 2 - 1 / (4 * (314159265358979323847 / 10 ^ 20) ^ 2 * ((n : ℝ) + 1) ^ 2))
theorem PAM_le : PAM ≤ PAMhi := by
 unfold PAM PAMhi
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
theorem PAMhi_nonneg : 0 ≤ PAMhi := by
 unfold PAMhi
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
   (672168410564118874775945444401 / 10 ^ 30 : ℝ) ≤ 3 / 2 - (760244597075630151253567702555 / 10 ^ 30) / (2 * (707106781186547524400844362104/10^30) * (649636939080062444129454621098 / 10 ^ 30))
     - PAMhi / (2 * (649636939080062444129454621098 / 10 ^ 30) ^ 2) := by
 unfold PAMhi dAM
 simp only [Finset.sum_range_succ, Finset.sum_range_zero, cAM, cAMn]
 norm_num
theorem HW_ge : (672168410564118874775945444401 / 10 ^ 30 : ℝ) ≤ HW := by
 rw [HW_eq]
 have hc := cos_theta0_le
 have hs := sin_theta0_ge
 have hb := sqrt2_half_bounds
 have hP := PAM_le
 have hP0 := PAMhi_nonneg
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
 have h2 : PAM / (2 * Real.sin (Real.sqrt 2 / 2) ^ 2) ≤ PAMhi / (2 * (649636939080062444129454621098 / 10 ^ 30) ^ 2) :=
   div_le_div₀ hP0 hP (by positivity) (by linarith)
 have := floor_numeric
 linarith

#print axioms ProportionSharpWindow.HW_ge
end ProportionSharpWindow
end

