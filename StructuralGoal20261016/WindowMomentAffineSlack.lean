/- SPDX-License-Identifier: Apache-2.0
RLT multipliers from a valid joint affine gap bound. This retains coupled
span geometry instead of requiring nonnegativity on the larger coordinate
box. The existing 464-variable lift already contains every product used.
No actual numerical exclusion or global floor is asserted here.
-/
import StructuralGoal20261016.WindowMomentPolynomial
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators
namespace StructuralGoal20261016.WindowMomentAffineSlack
open WindowMomentPolynomial WindowMomentLayout

def factorA (d : Fin 9 → ℚ) (B : ℚ) (center : Fin 9 → ℚ) : ℚ :=
  B-∑ r, d r*center r

def factorB (d radius : Fin 9 → ℚ) (r : Fin 9) : ℚ :=
  -d r*radius r

theorem multiplier_eq (d : Fin 9 → ℚ) (B : ℚ)
    (center radius : Fin 9 → ℚ) (g : Fin 9 → ℝ)
    (hr : ∀ r, radius r ≠ 0) :
    WindowMomentRLT.multiplier (factorA d B center : ℝ)
      (realVector (factorB d radius))
      (normalized (realVector center) (realVector radius) g) =
      (B:ℝ)-dotQ d g := by
  have ht (r : Fin 9) :
      (-(d r:ℝ)*(radius r:ℝ))*((g r-(center r:ℝ))/(radius r:ℝ)) =
        -(d r:ℝ)*g r+(d r:ℝ)*(center r:ℝ) := by
    have hn : (radius r:ℝ) ≠ 0 := by exact_mod_cast hr r
    field_simp [hn]
    <;> ring
  simp only [WindowMomentRLT.multiplier,factorA,factorB,realVector,
    normalized,dotQ,Rat.cast_sub,Rat.cast_sum,Rat.cast_mul,Rat.cast_neg]
  simp_rw [ht,neg_mul,Finset.sum_add_distrib,Finset.sum_neg_distrib]
  ring

theorem grouped_nonpos (a : WindowLiftedFarkas.Form)
    (d : Fin 9 → ℚ) (B : ℚ) (center radius : Fin 9 → ℚ)
    (g : Fin 9 → ℝ) (hr : ∀ r, radius r ≠ 0)
    (hgeometry : dotQ d g ≤ (B:ℝ))
    (hrow : WindowLiftedFarkas.eval a g ≤ (a.bound:ℝ)) :
    eval (grouped a center radius (factorA d B center) (factorB d radius))
      (realVector center) (realVector radius) g ≤
      ((grouped a center radius (factorA d B center) (factorB d radius)).bound:ℝ) := by
  apply sub_nonpos.mp
  rw [grouped_identity a center radius _ _ g hr]
  rw [multiplier_eq d B center radius g hr]
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hrow)
    (sub_nonneg.mpr hgeometry)

set_option pp.fullNames true
#print axioms multiplier_eq
#print axioms grouped_nonpos
end StructuralGoal20261016.WindowMomentAffineSlack
end
