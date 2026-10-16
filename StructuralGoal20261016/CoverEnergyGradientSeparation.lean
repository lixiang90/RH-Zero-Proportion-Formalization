/- SPDX-License-Identifier: Apache-2.0
Joint energy-gradient separation on a sublevel. The scalar actual-energy
minorant and directional upper inequality remain explicit certificate inputs.
-/
import StructuralGoal20261016.CoverKKTContraction
set_option Elab.async false
set_option pp.fullNames true
noncomputable section
open Finset
namespace StructuralGoal20261016.CoverEnergyGradientSeparation
open CoverKKTContraction

theorem dot_nonneg {n : ℕ} {sep : ℝ} {g p d : Fin n → ℝ}
    (hkkt : KKT sep g p) (hsupport : ∀ i, d i < 0 → sep < g i) :
    0 ≤ dot d p := by
  unfold dot
  apply Finset.sum_nonneg
  intro i _
  by_cases hd : 0 ≤ d i
  · exact mul_nonneg hd (hkkt.1 i)
  · rw [hkkt.2 i (hsupport i (lt_of_not_ge hd)), mul_zero]

/-- A nonnegative sublevel multiplier combines the energy information and
KKT gradients before taking a single cell-wide affine/flow upper bound. -/
theorem joint_impossible {n : ℕ} {sep energy c A lam : ℝ}
    {g p d : Fin n → ℝ} (hkkt : KKT sep g p)
    (hsupport : ∀ i, d i < 0 → sep < g i)
    (hminorant : A ≤ energy) (hbelow : energy ≤ c) (hlam : 0 ≤ lam)
    (hnegative : dot d p + lam * (c - A) < 0) : False := by
  have hD := dot_nonneg hkkt hsupport
  have hA : 0 ≤ c - A := sub_nonneg.mpr (hminorant.trans hbelow)
  have hsum := add_nonneg hD (mul_nonneg hlam hA)
  exact (not_lt_of_ge hsum) hnegative

#print axioms dot_nonneg
#print axioms joint_impossible
end StructuralGoal20261016.CoverEnergyGradientSeparation
end
