/- SPDX-License-Identifier: Apache-2.0
Exact Lagrange-flow contraction on an energy sublevel. Every discarded part
lies outside F<c. This is not an unconditional pointwise cell contraction.
-/
import StructuralGoal20261016.CoverCoerciveKKT
set_option Elab.async false

noncomputable section
namespace StructuralGoal20261016.CoverSublevelContraction

/-- Any certified affine energy minorant can be added with a nonnegative
multiplier before applying a linear-flow lower bound. -/
theorem lower {energy c A z lam m : ℝ}
    (hminorant : A ≤ energy) (hbelow : energy < c) (hlam : 0 ≤ lam)
    (hflow : m ≤ z + lam * A) : m - lam * c ≤ z := by
  have hAc : A ≤ c := hminorant.trans hbelow.le
  have hmul := mul_le_mul_of_nonneg_left hAc hlam
  linarith

/-- Applying the same construction to -z gives an upper bound. -/
theorem upper {energy c A z lam m : ℝ}
    (hminorant : A ≤ energy) (hbelow : energy < c) (hlam : 0 ≤ lam)
    (hflow : m ≤ -z + lam * A) : z ≤ lam * c - m := by
  have h := lower hminorant hbelow hlam hflow
  linarith

theorem rounded_lower {energy c A z lam m l : ℝ}
    (hminorant : A ≤ energy) (hbelow : energy < c) (hlam : 0 ≤ lam)
    (hflow : m ≤ z + lam * A) (hround : l ≤ m - lam * c) : l ≤ z :=
  hround.trans (lower hminorant hbelow hlam hflow)

theorem rounded_upper {energy c A z lam m u : ℝ}
    (hminorant : A ≤ energy) (hbelow : energy < c) (hlam : 0 ≤ lam)
    (hflow : m ≤ -z + lam * A) (hround : lam * c - m ≤ u) : z ≤ u :=
  (upper hminorant hbelow hlam hflow).trans hround

#print axioms lower
#print axioms upper
#print axioms rounded_lower
#print axioms rounded_upper
end StructuralGoal20261016.CoverSublevelContraction
end
