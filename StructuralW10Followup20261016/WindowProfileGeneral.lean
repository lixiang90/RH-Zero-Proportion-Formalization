/- SPDX-License-Identifier: Apache-2.0
Positive Fourier-window profiles under a finite l1 perturbation bound.
These analytic profile facts assert no counting theorem for the new windows.
-/
import GramDefect20261015.Core

noncomputable section
open scoped BigOperators
namespace StructuralW10Followup20261016.WindowProfileGeneral

def perturb {m : ℕ} (c : Fin m → ℝ) (s : ℝ) : ℝ :=
  ∑ j, c j * Real.cos (2 * Real.pi * ((j : ℕ) + 1) * s)

def profile {m : ℕ} (c : Fin m → ℝ) (s : ℝ) : ℝ :=
  Real.cos (Real.sqrt 2 * s) + perturb c s

theorem abs_perturb_le {m : ℕ} (c : Fin m → ℝ) {b : ℝ}
    (hb : ∑ j, |c j| ≤ b) (s : ℝ) : |perturb c s| ≤ b := by
  unfold perturb
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply le_trans (Finset.sum_le_sum (fun j _ => ?_)) hb
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

theorem profile_le {m : ℕ} (c : Fin m → ℝ)
    (hc : ∑ j, |c j| ≤ 2 / 25) (s : ℝ) : profile c s ≤ 42 / 25 := by
  have hp := (abs_le.mp (abs_perturb_le c hc s)).2
  have hcos := Real.cos_le_one (Real.sqrt 2 * s)
  unfold profile
  linarith only [hp, hcos]

theorem profile_ge_core {m : ℕ} (c : Fin m → ℝ)
    (hc : ∑ j, |c j| ≤ 2 / 25) {s : ℝ} (hs : |s| ≤ 1 / 2) :
    67 / 100 ≤ profile c s := by
  have hp := (abs_le.mp (abs_perturb_le c hc s)).1
  have hcos := AMW.cos_sqrt2_ge (s := s)
  have hs2 : s ^ 2 ≤ 1 / 4 := by
    have hh := abs_le.mp hs
    nlinarith only [hh.1, hh.2]
  unfold profile
  linarith only [hp, hcos, hs2]

theorem profile_ge_wide {m : ℕ} (c : Fin m → ℝ)
    (hc : ∑ j, |c j| ≤ 2 / 25) {s : ℝ} (hs : |s| ≤ 3 / 5) :
    14 / 25 ≤ profile c s := by
  have hp := (abs_le.mp (abs_perturb_le c hc s)).1
  have hcos := AMW.cos_sqrt2_ge (s := s)
  have hs2 : s ^ 2 ≤ 9 / 25 := by
    have hh := abs_le.mp hs
    nlinarith only [hh.1, hh.2]
  unfold profile
  linarith only [hp, hcos, hs2]

theorem profile_even {m : ℕ} (c : Fin m → ℝ) (s : ℝ) :
    profile c (-s) = profile c s := by
  simp only [profile, perturb, mul_neg, Real.cos_neg]

theorem profile_continuous {m : ℕ} (c : Fin m → ℝ) : Continuous (profile c) := by
  unfold profile perturb
  fun_prop

#print axioms profile_ge_core
#print axioms profile_ge_wide
#print axioms profile_even
#print axioms profile_continuous
end StructuralW10Followup20261016.WindowProfileGeneral
end
