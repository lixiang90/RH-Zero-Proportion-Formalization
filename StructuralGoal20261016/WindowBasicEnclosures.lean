/- SPDX-License-Identifier: Apache-2.0
Elementary rational enclosures for the new integer-centred sinc-jet oracle.
The inputs use the already proved order-20 window enclosure and pi bounds;
no unproved high-precision Machin identity is imported as an assumption.
-/
import GramDefect20261015.Core
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real
namespace StructuralGoal20261016.WindowBasicEnclosures

theorem cos_theta_lower :
    (760244597075630151252 / 10^21 : ℝ) ≤
      Real.cos (Real.sqrt 2 / 2) := by
  have hb := AMW.sqrt2_half_bounds
  let r : ℝ := 707106781186547524400844362105 / 10^30
  have hr0 : 0 ≤ r := by dsimp [r]; norm_num
  have hr1 : |r| ≤ 1 := by rw [abs_of_nonneg hr0]; dsimp [r]; norm_num
  have htheta0 : 0 ≤ Real.sqrt 2 / 2 := by positivity
  have hmono : Real.cos r ≤ Real.cos (Real.sqrt 2 / 2) :=
    Real.cos_le_cos_of_nonneg_of_le_pi htheta0
      (by dsimp [r]; linarith [Real.pi_gt_three]) hb.2
  have ht := (abs_le.mp (AMW.taylor20_F r hr1).1).1
  rw [abs_of_nonneg hr0] at ht
  have hv : (760244597075630151252 / 10^21 : ℝ) ≤
      (1-r^2/2+r^4/24-r^6/720+r^8/40320-r^10/3628800+
        r^12/479001600-r^14/87178291200+r^16/20922789888000-
        r^18/6402373705728000) - r^20*(1/2317049531596800000) := by
    dsimp [r]
    norm_num
  linarith

theorem sin_theta_upper : Real.sin (Real.sqrt 2 / 2) ≤
    (649636939080062444132 / 10^21 : ℝ) := by
  have hc := cos_theta_lower
  have hc0 : 0 ≤ (760244597075630151252 / 10^21 : ℝ) := by norm_num
  have hcsq := mul_self_le_mul_self hc0 hc
  have hcircle := Real.sin_sq_add_cos_sq (Real.sqrt 2 / 2)
  have hs0 := AMW.sin_theta0_pos
  nlinarith

theorem pi_interval :
    (314159265358979323846 / 10^20 : ℝ) ≤ Real.pi ∧
      Real.pi ≤ 314159265358979323847 / 10^20 := by
  constructor
  · have h := Real.pi_gt_d20
    norm_num at h ⊢
    linarith
  · have h := Real.pi_lt_d20
    norm_num at h ⊢
    linarith

theorem theta_interval :
    (707106781186547524400844362104 / 10^30 : ℝ) ≤ Real.sqrt 2 / 2 ∧
      Real.sqrt 2 / 2 ≤ 707106781186547524400844362105 / 10^30 :=
  AMW.sqrt2_half_bounds
theorem sin_theta_lower : (649636939080062444129454621098 / 10^30 : ℝ) ≤
    Real.sin (Real.sqrt 2 / 2) := AMW.sin_theta0_ge
theorem cos_theta_upper : Real.cos (Real.sqrt 2 / 2) ≤
    (760244597075630151253567702555 / 10^30 : ℝ) := AMW.cos_theta0_le

#print axioms cos_theta_lower
#print axioms sin_theta_upper
#print axioms pi_interval
end StructuralGoal20261016.WindowBasicEnclosures
end
