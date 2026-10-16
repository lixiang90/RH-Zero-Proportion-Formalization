/- SPDX-License-Identifier: Apache-2.0
Actual new-window monotonicity and short-pair reduction.
The sign of the actual Fourier moment integral proves monotonicity on [0,1].
Only the final scalar endpoint inequality remains a numeric certificate input.
This does not assume a zero-counting or a global local-floor conclusion.
-/
import StructuralGoal20261016.WindowDerivative
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory
namespace StructuralGoal20261016.WindowClosePair
open WindowEnergy WindowKernel WindowDerivative

theorem t_mul_sin_nonneg {x t : ℝ} (hx : x ∈ Icc (0:ℝ) 1)
 (ht : t ∈ Icc (-(1:ℝ)/2) (1/2)) : 0 ≤ t * Real.sin (2*π*x*t) := by
 by_cases ht0 : 0 ≤ t
 · have hxt : 0 ≤ 2*π*x*t :=
     mul_nonneg (mul_nonneg (by positivity) hx.1) ht0
   have hxt' : 2*π*x*t ≤ π := by
     have hprod : x*t ≤ 1/2 :=
       (mul_le_mul_of_nonneg_right hx.2 ht0).trans (by simpa using ht.2)
     calc
       _ = (2*π)*(x*t) := by ring
       _ ≤ (2*π)*(1/2) := mul_le_mul_of_nonneg_left hprod (by positivity)
       _ = _ := by ring
   exact mul_nonneg ht0 (Real.sin_nonneg_of_nonneg_of_le_pi hxt hxt')
 · have ht0' : t ≤ 0 := le_of_not_ge ht0
   have hxt : 0 ≤ 2*π*x*(-t) :=
     mul_nonneg (mul_nonneg (by positivity) hx.1) (neg_nonneg.mpr ht0')
   have hxt' : 2*π*x*(-t) ≤ π := by
     have hprod : x*(-t) ≤ 1/2 :=
       (mul_le_mul_of_nonneg_right hx.2 (neg_nonneg.mpr ht0')).trans (by linarith [ht.1])
     calc
       _ = (2*π)*(x*(-t)) := by ring
       _ ≤ (2*π)*(1/2) := mul_le_mul_of_nonneg_left hprod (by positivity)
       _ = _ := by ring
   have hs := Real.sin_nonneg_of_nonneg_of_le_pi hxt hxt'
   rw [show 2*π*x*t = -(2*π*x*(-t)) by ring, Real.sin_neg]
   exact mul_nonneg_of_nonpos_of_nonpos ht0' (neg_nonpos.mpr hs)

theorem jet24_one_nonpos {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) :
 jet 24 d24 1 x ≤ 0 := by
 apply div_nonpos_of_nonpos_of_nonneg _ AMW.K0AM_pos.le
 unfold moment
 change (∫ t in (-(1:ℝ)/2)..(1/2), atom 24 d24 1 x t) ≤ 0
 suffices (∫ t in (-(1:ℝ)/2)..(1/2), atom 24 d24 1 x t) ≤
     (∫ t in (-(1:ℝ)/2)..(1/2), (0:ℝ)) by simpa using this
 apply intervalIntegral.integral_mono_on (by norm_num : (-(1:ℝ)/2) ≤ 1/2)
   ((atom_continuous 24 d24 1 x).intervalIntegrable _ _)
   (continuous_const.intervalIntegrable _ _)
 intro t ht
 have hts := t_mul_sin_nonneg hx ht
 have hv := v24_nonneg t ht
 have hprod := mul_nonneg (mul_nonneg (show 0 ≤ 2*π by positivity) hv) hts
 unfold atom
 norm_num only [Nat.cast_one, pow_one, one_mul] at *
 rw [Real.cos_add_pi_div_two]
 nlinarith only [hprod]

theorem k24_antitoneOn : AntitoneOn (k 24 d24) (Icc (0:ℝ) 1) := by
 intro x hx y hy hxy
 have hi : IntervalIntegrable (jet 24 d24 1) volume x y :=
   (continuous_iff_continuousAt.mpr fun s =>
     (jet_hasDerivAt 24 d24 1 s).continuousAt).intervalIntegrable _ _
 have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
   (a := x) (b := y) (f := k 24 d24) (f' := jet 24 d24 1)
   (fun s _ => k24_hasDerivAt s) hi
 have hnonpos : (∫ s in x..y, jet 24 d24 1 s) ≤ 0 := by
   suffices (∫ s in x..y, jet 24 d24 1 s) ≤ (∫ s in x..y, (0:ℝ)) by simpa using this
   apply intervalIntegral.integral_mono_on hxy hi (continuous_const.intervalIntegrable _ _)
   intro s hs
   exact jet24_one_nonpos ⟨hx.1.trans hs.1, hs.2.trans hy.2⟩
 linarith

theorem k24_neg (x : ℝ) : k 24 d24 (-x) = k 24 d24 x := by
 unfold k
 rw [K_neg]

theorem k24_abs (x : ℝ) : k 24 d24 |x| = k 24 d24 x := by
 by_cases hx : 0 ≤ x
 · rw [abs_of_nonneg hx]
 · rw [abs_of_neg (lt_of_not_ge hx), k24_neg]

theorem short_pair_of_endpoint {δ x : ℝ} (hδ : δ ∈ Icc (0:ℝ) 1)
 (hK : 0 ≤ k 24 d24 δ) (hx : |x| ≤ δ) :
 k 24 d24 δ ^ 2 ≤ w 24 d24 x := by
 have habs : |x| ∈ Icc (0:ℝ) 1 := ⟨abs_nonneg x, hx.trans hδ.2⟩
 have hle := k24_antitoneOn habs hδ hx
 rw [k24_abs] at hle
 exact pow_le_pow_left₀ hK hle 2

#print axioms k24_antitoneOn
#print axioms short_pair_of_endpoint
end StructuralGoal20261016.WindowClosePair
end
