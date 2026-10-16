/- SPDX-License-Identifier: Apache-2.0
Objective bounds from actual feasible competitors and a shared sublevel budget.
No assertion about arbitrary KKT points or numerical optimizer correctness.
-/
import StructuralGoal20261016.WindowFiniteMoveFamily
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators
namespace StructuralGoal20261016.WindowFiniteMoveSublevelBounds
open WindowGapEnergy (Fw24)
open WindowFiniteMove (move)
open WindowFiniteMoveFamily (changeEnergy weighted_upper_nonneg)
open WindowMinimizerCover (RelevantBelow)
variable {ι : Type*} [Fintype ι]

/-- A nonnegative energy-budget multiplier and nonnegative competitor cuts
can only decrease an objective at a genuine sublevel global minimizer. -/
theorem objective_lower {sep c A payment target objective : ℝ} {g : Fin 9 → ℝ}
    (hg : RelevantBelow sep c g) (q : ι → Fin 9 → ℤ)
    (hq : ∀ v, CoverCoerciveKKT.Orthant sep (move g (q v)))
    (U : ι → ℝ) (hU : ∀ v, changeEnergy g (q v) ≤ U v)
    (lam : ι → ℝ) (hlam : ∀ v, 0 ≤ lam v)
    (hA : A ≤ Fw24 g) (hpayment : 0 ≤ payment)
    (hcert : target ≤ objective+payment*(A-c)-(∑ v, lam v*U v)) :
    target ≤ objective := by
  have hb : A-c ≤ 0 := sub_nonpos.mpr (hA.trans hg.2.le)
  have hp := mul_nonpos_of_nonneg_of_nonpos hpayment hb
  have hs := weighted_upper_nonneg hg.1 q hq U hU lam hlam
  linarith

/-- The same certificate for the negative objective gives an upper bound. -/
theorem objective_upper {sep c A payment target objective : ℝ} {g : Fin 9 → ℝ}
    (hg : RelevantBelow sep c g) (q : ι → Fin 9 → ℤ)
    (hq : ∀ v, CoverCoerciveKKT.Orthant sep (move g (q v)))
    (U : ι → ℝ) (hU : ∀ v, changeEnergy g (q v) ≤ U v)
    (lam : ι → ℝ) (hlam : ∀ v, 0 ≤ lam v)
    (hA : A ≤ Fw24 g) (hpayment : 0 ≤ payment)
    (hcert : target ≤ -objective+payment*(A-c)-(∑ v, lam v*U v)) :
    objective ≤ -target := by
  have h := objective_lower hg q hq U hU lam hlam hA hpayment hcert
  linarith

/-- Integer outward rounding can be supplied as the explicit target comparison;
the multiplier scale must be positive. -/
theorem scaled_lower {sep c A payment target objective scale lo : ℝ} {g : Fin 9 → ℝ}
    (hg : RelevantBelow sep c g) (q : ι → Fin 9 → ℤ)
    (hq : ∀ v, CoverCoerciveKKT.Orthant sep (move g (q v)))
    (U : ι → ℝ) (hU : ∀ v, changeEnergy g (q v) ≤ U v)
    (lam : ι → ℝ) (hlam : ∀ v, 0 ≤ lam v)
    (hA : A ≤ Fw24 g) (hpayment : 0 ≤ payment) (hscale : 0 < scale)
    (hround : scale*lo ≤ target)
    (hcert : target ≤ scale*objective+payment*(A-c)-(∑ v, lam v*U v)) :
    lo ≤ objective := by
  have h := objective_lower hg q hq U hU lam hlam hA hpayment hcert
  nlinarith [hround.trans h]

theorem scaled_upper {sep c A payment target objective scale hi : ℝ} {g : Fin 9 → ℝ}
    (hg : RelevantBelow sep c g) (q : ι → Fin 9 → ℤ)
    (hq : ∀ v, CoverCoerciveKKT.Orthant sep (move g (q v)))
    (U : ι → ℝ) (hU : ∀ v, changeEnergy g (q v) ≤ U v)
    (lam : ι → ℝ) (hlam : ∀ v, 0 ≤ lam v)
    (hA : A ≤ Fw24 g) (hpayment : 0 ≤ payment) (hscale : 0 < scale)
    (hround : -scale*hi ≤ target)
    (hcert : target ≤ -scale*objective+payment*(A-c)-(∑ v, lam v*U v)) :
    objective ≤ hi := by
  have h := objective_lower hg q hq U hU lam hlam hA hpayment hcert
  nlinarith

set_option pp.fullNames true
#print axioms objective_lower
#print axioms objective_upper
#print axioms scaled_lower
#print axioms scaled_upper
end StructuralGoal20261016.WindowFiniteMoveSublevelBounds
end
