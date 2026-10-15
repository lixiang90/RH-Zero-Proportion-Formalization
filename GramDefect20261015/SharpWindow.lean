/-
Copyright (c) 2026 Li Xiang (lixiang90), modifications. Apache-2.0.
Based on the accepted AMW window and Meshuggah alternating-polynomial
inequalities, whose original notices are retained in Core.lean.

The new enclosure evaluates cosPoly of order 17 and sincPoly of order 18
exactly at theta^2 = 1/2.  This avoids the previous exponential remainder
and rational square-root enclosure.  It keeps all window coefficients and
the accepted pi upper bound unchanged.
SPDX-License-Identifier: Apache-2.0
-/
import GramDefect20261015.Core

set_option Elab.async false
set_option maxHeartbeats 4000000
set_option linter.all false

noncomputable section
open Real AMW
namespace GramDefect20261015.Window

private def evenSeries (offset : ℕ) (q : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => evenSeries offset q n +
      (-1) ^ n * q ^ n / ((2 * n + offset).factorial : ℝ)

private theorem cosPoly_as_evenSeries (x : ℝ) (n : ℕ) :
    Meshuggah.Majorant.cosPoly x n = evenSeries 0 (x ^ 2) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Meshuggah.Majorant.cosPoly, evenSeries, ih, Nat.add_zero, pow_mul]

private theorem sincPoly_as_evenSeries (x : ℝ) (n : ℕ) :
    Meshuggah.Majorant.sincPoly x n = evenSeries 1 (x ^ 2) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Meshuggah.Majorant.sincPoly, evenSeries, ih, pow_mul]

private theorem theta_sq : (Real.sqrt 2 / 2) ^ 2 = (1 / 2 : ℝ) := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

def cosUpper : ℝ :=
  132424952393242556021461169421128332043 /
    174187298275621608010492925706240000000

def sincLower : ℝ :=
  14302403666080084620954960913502913904936237 /
    15567659428162813657715716369101619200000000

theorem cos_theta0_le : Real.cos (Real.sqrt 2 / 2) ≤ cosUpper := by
  calc
    Real.cos (Real.sqrt 2 / 2) ≤
        Meshuggah.Majorant.cosPoly (Real.sqrt 2 / 2) 17 :=
      Meshuggah.Majorant.cos_le_cosPoly (Real.sqrt 2 / 2) 8
    _ = cosUpper := by
      rw [cosPoly_as_evenSeries, theta_sq]
      norm_num [evenSeries, cosUpper]

theorem sinc_theta0_ge : sincLower ≤ Real.sinc (Real.sqrt 2 / 2) := by
  calc
    sincLower = Meshuggah.Majorant.sincPoly (Real.sqrt 2 / 2) 18 := by
      rw [sincPoly_as_evenSeries, theta_sq]
      norm_num [evenSeries, sincLower]
    _ ≤ Real.sinc (Real.sqrt 2 / 2) :=
      Meshuggah.Majorant.sincPoly_le_sinc (Real.sqrt 2 / 2) 8

theorem sincLower_pos : 0 < sincLower := by norm_num [sincLower]

theorem denominator_ge : sincLower ≤ Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) := by
  have hθ : Real.sqrt 2 / 2 ≠ 0 := by positivity
  have hid : Real.sin (Real.sqrt 2 / 2) / (Real.sqrt 2 / 2) =
      Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) := by
    rw [div_eq_iff hθ]
    calc
      Real.sin (Real.sqrt 2 / 2) =
          (Real.sqrt 2 ^ 2 / 2) * Real.sin (Real.sqrt 2 / 2) := by
        rw [Real.sq_sqrt (by norm_num)]
        ring
      _ = Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) := by ring
  have hs := sinc_theta0_ge
  rwa [Real.sinc_of_ne_zero hθ, hid] at hs

theorem square_denominator_ge : sincLower ^ 2 ≤ 2 * Real.sin (Real.sqrt 2 / 2) ^ 2 := by
  have hsq := pow_le_pow_left₀ sincLower_pos.le denominator_ge 2
  simpa only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using hsq

theorem floor_numeric :
    (6721684105641188747759983512104999330646 / 10 ^ 40 : ℝ) ≤
      3 / 2 - cosUpper / sincLower - AMW.PAMhi / sincLower ^ 2 := by
  unfold cosUpper sincLower AMW.PAMhi AMW.dAM
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, AMW.cAM, AMW.cAMn]
  norm_num

theorem HW_ge : (6721684105641188747759983512104999330646 / 10 ^ 40 : ℝ) ≤ AMW.HW := by
  rw [AMW.HW_eq]
  have h1 : Real.cos (Real.sqrt 2 / 2) /
      (Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2)) ≤ cosUpper / sincLower :=
    div_le_div₀ (by norm_num [cosUpper]) cos_theta0_le sincLower_pos denominator_ge
  have h2 : AMW.PAM / (2 * Real.sin (Real.sqrt 2 / 2) ^ 2) ≤
      AMW.PAMhi / sincLower ^ 2 :=
    div_le_div₀ AMW.PAMhi_nonneg AMW.PAM_le (pow_pos sincLower_pos 2)
      square_denominator_ge
  linarith [floor_numeric]

theorem strict_improvement :
    (6721684105641188747759454444013516755656 / 10 ^ 40 : ℝ) <
      6721684105641188747759983512104999330646 / 10 ^ 40 := by norm_num

#print axioms GramDefect20261015.Window.HW_ge
end GramDefect20261015.Window
end
