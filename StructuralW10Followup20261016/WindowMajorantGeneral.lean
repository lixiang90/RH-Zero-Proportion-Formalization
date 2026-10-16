/- SPDX-License-Identifier: Apache-2.0
General domination for positive Fourier profiles with l1 perturbation ≤2/25.
The sinc-polynomial argument adapts Opeth.AMMajorant in the attributed Core.
The degree-six Bernstein identity is exact rational arithmetic.
This establishes a profile input, not a new zero-counting bound.
-/
import StructuralW10Followup20261016.WindowProfileGeneral
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real
open scoped BigOperators
open Opeth.AMMajorant
open StructuralW10Followup20261016.WindowProfileGeneral
namespace StructuralW10Followup20261016.WindowMajorantGeneral

def cubic (x : ℝ) : ℝ :=
  (2 - 119 / 200 + 7921 / 150000 - 13 / 5760) +
  (-119 / 50 + 7921 / 6250 - 13 / 96) * x +
  (31684 / 37500 - 13 / 24) * x ^ 2 - (13 / 90) * x ^ 3

lemma frequency_powers :
    (π * (17 / 20) : ℝ) ^ 2 ≤ 357 / 50 ∧
    31684 / 625 ≤ (π * (17 / 20) : ℝ) ^ 4 ∧
    (π * (17 / 20) : ℝ) ^ 6 ≤ 364 := by
  set d : ℝ := π * (17 / 20)
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hlo : (2669 / 1000 : ℝ) ≤ d := by
    dsimp [d]; linarith [pi_coarse.1]
  have hhi : d ≤ (187 / 70 : ℝ) := by
    dsimp [d]; linarith [pi_coarse.2]
  have h2lo : (178 / 25 : ℝ) ≤ d ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hlo)
      (show 0 ≤ d + 2669 / 1000 by positivity)
    nlinarith only [h]
  have h2hi : d ^ 2 ≤ (357 / 50 : ℝ) := by
    have h := mul_nonneg (sub_nonneg.mpr hhi)
      (show 0 ≤ 187 / 70 + d by positivity)
    nlinarith only [h]
  have h4lo : (31684 / 625 : ℝ) ≤ d ^ 4 := by
    have h := mul_nonneg (sub_nonneg.mpr h2lo)
      (show 0 ≤ d ^ 2 + 178 / 25 by positivity)
    nlinarith only [h]
  have h6hi : d ^ 6 ≤ (364 : ℝ) := by
    have h := mul_nonneg (sub_nonneg.mpr h2hi)
      (show 0 ≤ (357 / 50 : ℝ) ^ 2 + (357 / 50) * d ^ 2 + (d ^ 2) ^ 2 by
        positivity)
    nlinarith only [h]
  exact ⟨h2hi, h4lo, h6hi⟩
lemma cubic_sinc_lower {s : ℝ} (hs : |s| ≤ 1 / 2) :
    cubic (s ^ 2) ≤
      sinc (π * (17 / 20) * (s - 1 / 2)) +
        sinc (π * (17 / 20) * (s + 1 / 2)) := by
  set d : ℝ := π * (17 / 20)
  set x : ℝ := s ^ 2
  have hx0 : 0 ≤ x := sq_nonneg s
  have hx1 : x ≤ 1 / 4 := by
    have h := abs_le.mp hs
    dsimp [x]
    nlinarith [h.1, h.2]
  have hd := frequency_powers
  change d ^ 2 ≤ 357 / 50 ∧ 31684 / 625 ≤ d ^ 4 ∧ d ^ 6 ≤ 364 at hd
  have hT :
      2 - d ^ 2 / 6 * (1 / 2 + 2 * x) +
          d ^ 4 / 120 * (1 / 8 + 3 * x + 2 * x ^ 2) -
          d ^ 6 / 5040 * (1 / 32 + (15 / 8) * x + (15 / 2) * x ^ 2 + 2 * x ^ 3)
        ≤ sinc (d * (s - 1 / 2)) + sinc (d * (s + 1 / 2)) := by
    calc
      _ = (1 - (d * (s - 1 / 2)) ^ 2 / 6 + (d * (s - 1 / 2)) ^ 4 / 120 -
              (d * (s - 1 / 2)) ^ 6 / 5040) +
          (1 - (d * (s + 1 / 2)) ^ 2 / 6 + (d * (s + 1 / 2)) ^ 4 / 120 -
              (d * (s + 1 / 2)) ^ 6 / 5040) := by dsimp [x]; ring
      _ ≤ _ := add_le_add (sinc_lower _) (sinc_lower _)
  have hm2 := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hd.1 (show (0 : ℝ) ≤ 6 by norm_num))
    (show 0 ≤ 1 / 2 + 2 * x by positivity)
  have hm4 := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hd.2.1 (show (0 : ℝ) ≤ 120 by norm_num))
    (show 0 ≤ 1 / 8 + 3 * x + 2 * x ^ 2 by positivity)
  have hm6 := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hd.2.2 (show (0 : ℝ) ≤ 5040 by norm_num))
    (show 0 ≤ 1 / 32 + (15 / 8) * x + (15 / 2) * x ^ 2 + 2 * x ^ 3 by positivity)
  have hC :
      (2 - 119 / 200 + 7921 / 150000 - 13 / 5760) +
          (-119 / 50 + 7921 / 6250 - 13 / 96) * x +
          (31684 / 37500 - 13 / 24) * x ^ 2 - (13 / 90) * x ^ 3
        ≤ sinc (d * (s - 1 / 2)) + sinc (d * (s + 1 / 2)) := by
    nlinarith only [hT, hm2, hm4, hm6]
  simpa only [cubic, x, d] using hC

theorem cubic_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 4) :
    0 ≤ cubic x := by
  have hlast : 0 ≤ (31684 / 37500 - 13 / 24 : ℝ) - (13 / 90) * x := by
    linarith only [hx1]
  have hprod := mul_nonneg (sq_nonneg x) hlast
  unfold cubic
  nlinarith only [hprod, hx0, hx1]

theorem polynomial_gap {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 4) :
    0 ≤ (7 / 10) * cubic x ^ 2 - (109 / 100) * (27 / 25 - x + x ^ 2 / 6) := by
  have hux : 0 ≤ 1 - 4 * x := by linarith only [hx1]
  have hid : (7 / 10) * cubic x ^ 2 - (109 / 100) * (27 / 25 - x + x ^ 2 / 6) =
      (39636539443087 / 129600000000000 : ℝ) * (4 * x) ^ 0 * (1 - 4 * x) ^ 6 +
      (588684794859 / 400000000000 : ℝ) * (4 * x) ^ 1 * (1 - 4 * x) ^ 5 +
      (30957240422413 / 10800000000000 : ℝ) * (4 * x) ^ 2 * (1 - 4 * x) ^ 4 +
      (722012910329 / 253125000000 : ℝ) * (4 * x) ^ 3 * (1 - 4 * x) ^ 3 +
      (3351415273 / 2250000000 : ℝ) * (4 * x) ^ 4 * (1 - 4 * x) ^ 2 +
      (15351841601 / 42187500000 : ℝ) * (4 * x) ^ 5 * (1 - 4 * x) ^ 1 +
      (13284605053 / 506250000000 : ℝ) * (4 * x) ^ 6 * (1 - 4 * x) ^ 0 := by
    unfold cubic
    ring
  rw [hid]
  positivity

theorem normalized_profile_le_scaled_majorant {m : ℕ} (c : Fin m → ℝ)
    (hc : ∑ j, |c j| ≤ 2 / 25) {s : ℝ} (hs : |s| ≤ 1 / 2) :
    AMW.rhoAM * profile c s ≤ scaledMajorant s := by
  let x : ℝ := s ^ 2
  let S : ℝ := sinc (π * (17 / 20) * (s - 1 / 2)) +
    sinc (π * (17 / 20) * (s + 1 / 2))
  have hx0 : 0 ≤ x := sq_nonneg s
  have hx1 : x ≤ 1 / 4 := by
    have h := abs_le.mp hs
    dsimp [x]
    nlinarith only [h.1, h.2]
  have hC : cubic x ≤ S := cubic_sinc_lower hs
  have hC0 := cubic_nonneg hx0 hx1
  have hS0 : 0 ≤ S := hC0.trans hC
  have hsquare := mul_nonneg (sub_nonneg.mpr hC) (add_nonneg hS0 hC0)
  have hgap := polynomial_gap hx0 hx1
  have hv0 : 0 ≤ profile c s := (by norm_num : (0 : ℝ) ≤ 67 / 100).trans
    (profile_ge_core c hc hs)
  have hv : profile c s ≤ 27 / 25 - x + x ^ 2 / 6 := by
    have hcos := cos_core_upper s
    have hp := (abs_le.mp (abs_perturb_le c hc s)).2
    have h4 : s ^ 4 = x ^ 2 := by dsimp [x]; ring
    rw [h4] at hcos
    unfold profile
    dsimp only [x] at *
    linarith only [hcos, hp]
  have hr := (mul_le_mul_of_nonneg_right rho_le hv0).trans
    (mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 109 / 100))
  rw [scaledMajorant_eq]
  change AMW.rhoAM * profile c s ≤ (7 / 10) * S ^ 2
  nlinarith only [hr, hsquare, hgap]

#print axioms cubic_sinc_lower
#print axioms polynomial_gap
#print axioms normalized_profile_le_scaled_majorant
end StructuralW10Followup20261016.WindowMajorantGeneral
end
