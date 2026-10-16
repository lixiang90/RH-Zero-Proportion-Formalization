/- SPDX-License-Identifier: Apache-2.0
An exact positive diagonal alone suffices for the current basin polynomials.
This theorem is algebraic; it does not assert coverage by those basins.
-/
import StructuralW10Unconditional20261016.QuadraticEnvelope

noncomputable section
open Finset
open scoped BigOperators
namespace StructuralW10Unconditional20261016.DiagonalPolynomial

theorem single_lower (d b x : ℝ) (hd : 0 < d) :
    -(b^2)/(4*d) ≤ b*x+d*x^2 := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<4*d)).mpr
  nlinarith only [sq_nonneg (2*d*x+b)]

theorem lower {ι : Type*} [Fintype ι] (C target : ℝ) (b d : ι → ℝ)
    (hd : ∀ i, 0 < d i)
    (hnumeric : target ≤ C-∑ i, (b i)^2/(4*d i)) :
    ∀ x : ι → ℝ, target ≤ C+∑ i, (b i*x i+d i*(x i)^2) := by
  intro x
  have hs : -(∑ i, (b i)^2/(4*d i)) ≤ ∑ i, (b i*x i+d i*(x i)^2) := by
    rw [← Finset.sum_neg_distrib]
    exact sum_le_sum fun i _ => by
      simpa only [neg_div] using single_lower (d i) (b i) (x i) (hd i)
  linarith only [hnumeric,hs]

#print axioms single_lower
#print axioms lower
end StructuralW10Unconditional20261016.DiagonalPolynomial
end
