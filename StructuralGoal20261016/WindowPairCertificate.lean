/- SPDX-License-Identifier: Apache-2.0
Actual redesigned-window short-pair payment at separation 123/128.
The endpoint w value is checked from the proved integer-centred jet table;
positivity on [0,1] follows analytically from its first cosine coefficient.
-/
import StructuralGoal20261016.WindowFixedKernelCenter01
import StructuralGoal20261016.WindowFixedPoint
import StructuralGoal20261016.WindowClosePair
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory
namespace StructuralGoal20261016.WindowPairCertificate
open WindowEnergy WindowKernel WindowDerivative WindowClosePair
open WindowJetTableData (W)
open WindowFixedKernelCenters WindowPointTableArithmetic

theorem K_one : K 24 d24 1 = AMW.Xk 0+d24 0/2 := by
 unfold K
 have he : ∀ t : ℝ, Real.cos (2*π*1*t) = AMW.ek 0 t := by
   intro t
   norm_num [AMW.ek]
 simp_rw [he]
 exact WindowEnergy.integral_v_ek 24 d24 (m := 0) (by decide)

theorem k_one_nonneg : 0 ≤ k 24 d24 1 := by
 unfold k
 rw [K_one]
 apply div_nonneg _ (K_zero_pos 24 d24).le
 have hx : 0 ≤ AMW.Xk 0 := by
   unfold AMW.Xk
   norm_num only [Nat.cast_zero,zero_add,pow_one,neg_one_mul,one_pow,mul_one]
   apply div_nonneg_iff.mpr
   right
   constructor
   · have h := mul_nonneg AMW.sin_theta0_pos.le (show 0 ≤ 2*Real.sqrt 2 by positivity)
     nlinarith only [h]
   · nlinarith [Real.pi_gt_three,sq_nonneg (π-3)]
 have hd : 0 ≤ d24 0 := by
   norm_num [d24,StructuralW10Followup20261016.NewWindows.nums24]
 exact add_nonneg hx (div_nonneg hd (by norm_num))

theorem k_nonneg {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : 0 ≤ k 24 d24 x :=
 k_one_nonneg.trans (k24_antitoneOn hx (by norm_num) hx.2)

theorem endpoint_floor : (221:ℝ)/25000 ≤ w 24 d24 (123/128) := by
 have hw : ∀ j ≤ 23, WindowRationalInterval.Holds (W 1 j)
     (WindowNormalizedJets.wc 24 d24 j ((1:ℕ):ℝ)) := by
   intro j hj
   simpa only [Nat.cast_one] using w_1 j hj
 have hv := WindowFixedPoint.value_sound (n := 1) (q := 123/128) (V := 221/25000) hw
   (show WindowFixedPoint.valueCheck 1 (123/128) (221/25000) = true by decide +kernel)
 norm_num only [Rat.cast_div,Rat.cast_ofNat] at hv
 exact hv

theorem short_pair_floor {x : ℝ} (hx : |x| ≤ (123:ℝ)/128) :
 (221:ℝ)/25000 ≤ w 24 d24 x := by
 have hd : (123/128:ℝ) ∈ Icc (0:ℝ) 1 := by norm_num
 exact endpoint_floor.trans (short_pair_of_endpoint hd (k_nonneg hd) hx)

set_option pp.fullNames true
#print axioms k_nonneg
#print axioms endpoint_floor
#print axioms short_pair_floor
end StructuralGoal20261016.WindowPairCertificate
end
