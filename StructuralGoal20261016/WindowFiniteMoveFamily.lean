/- SPDX-License-Identifier: Apache-2.0
Finite families of actual global competitors and their linear upper cuts.
A cut need hold only at genuine global minima. Nonnegative combinations
and an unused sublevel budget give exact Farkas certificates; no optimizer
optimality or feasibility of a numerical search is a proof premise.
-/
import StructuralGoal20261016.WindowFiniteMove
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators
namespace StructuralGoal20261016.WindowFiniteMoveFamily
open WindowGapEnergy (Fw24)
open WindowFiniteMove (move)
open WindowMinimizerCover (Relevant RelevantBelow)

def changeEnergy (g : Fin 9 → ℝ) (q : Fin 9 → ℤ) : ℝ :=
  Fw24 (move g q)-Fw24 g

theorem change_nonneg {sep : ℝ} {g : Fin 9 → ℝ}
    (hg : Relevant sep g) (q : Fin 9 → ℤ)
    (hq : CoverCoerciveKKT.Orthant sep (move g q)) :
    0 ≤ changeEnergy g q :=
  sub_nonneg.mpr (hg.2.2 (move g q) hq)

theorem upper_cut_nonneg {sep : ℝ} {g : Fin 9 → ℝ}
    (hg : Relevant sep g) (q : Fin 9 → ℤ)
    (hq : CoverCoerciveKKT.Orthant sep (move g q)) {U : ℝ}
    (hU : changeEnergy g q ≤ U) : 0 ≤ U :=
  (change_nonneg hg q hq).trans hU

variable {ι : Type*} [Fintype ι]

theorem weighted_changes_nonneg {sep : ℝ} {g : Fin 9 → ℝ}
    (hg : Relevant sep g) (q : ι → Fin 9 → ℤ)
    (hq : ∀ v, CoverCoerciveKKT.Orthant sep (move g (q v)))
    (theta : ι → ℝ) (htheta : ∀ v, 0 ≤ theta v) :
    0 ≤ ∑ v, theta v*changeEnergy g (q v) := by
  apply Finset.sum_nonneg
  intro v _
  exact mul_nonneg (htheta v) (change_nonneg hg (q v) (hq v))

theorem weighted_upper_nonneg {sep : ℝ} {g : Fin 9 → ℝ}
    (hg : Relevant sep g) (q : ι → Fin 9 → ℤ)
    (hq : ∀ v, CoverCoerciveKKT.Orthant sep (move g (q v)))
    (U : ι → ℝ) (hU : ∀ v, changeEnergy g (q v) ≤ U v)
    (theta : ι → ℝ) (htheta : ∀ v, 0 ≤ theta v) :
    0 ≤ ∑ v, theta v*U v := by
  apply Finset.sum_nonneg
  intro v _
  exact mul_nonneg (htheta v) (upper_cut_nonneg hg (q v) (hq v) (hU v))

theorem exclude_with_sublevel {sep c A payment : ℝ} {g : Fin 9 → ℝ}
    (hg : RelevantBelow sep c g) (q : ι → Fin 9 → ℤ)
    (hq : ∀ v, CoverCoerciveKKT.Orthant sep (move g (q v)))
    (theta : ι → ℝ) (htheta : ∀ v, 0 ≤ theta v)
    (hA : A ≤ Fw24 g) (hpayment : 0 ≤ payment)
    (hpaid : (∑ v, theta v*changeEnergy g (q v))+payment*(c-A) < 0) : False := by
  have hb : 0 ≤ c-A := sub_nonneg.mpr (hA.trans hg.2.le)
  have hs := weighted_changes_nonneg hg.1 q hq theta htheta
  exact (not_lt_of_ge (add_nonneg hs (mul_nonneg hpayment hb))) hpaid

theorem exclude_by_upper_cuts {sep c A payment : ℝ} {g : Fin 9 → ℝ}
    (hg : RelevantBelow sep c g) (q : ι → Fin 9 → ℤ)
    (hq : ∀ v, CoverCoerciveKKT.Orthant sep (move g (q v)))
    (U : ι → ℝ) (hU : ∀ v, changeEnergy g (q v) ≤ U v)
    (theta : ι → ℝ) (htheta : ∀ v, 0 ≤ theta v)
    (hA : A ≤ Fw24 g) (hpayment : 0 ≤ payment)
    (hpaid : (∑ v, theta v*U v)+payment*(c-A) < 0) : False := by
  have hb : 0 ≤ c-A := sub_nonneg.mpr (hA.trans hg.2.le)
  have hs := weighted_upper_nonneg hg.1 q hq U hU theta htheta
  exact (not_lt_of_ge (add_nonneg hs (mul_nonneg hpayment hb))) hpaid

/-- Subtracting valid nonnegative competitor cuts preserves an actual
energy minorant at a genuine global minimum. -/
theorem minorant_with_cuts {sep A : ℝ} {g : Fin 9 → ℝ}
    (hg : Relevant sep g) (q : ι → Fin 9 → ℤ)
    (hq : ∀ v, CoverCoerciveKKT.Orthant sep (move g (q v)))
    (U : ι → ℝ) (hU : ∀ v, changeEnergy g (q v) ≤ U v)
    (lam : ι → ℝ) (hlam : ∀ v, 0 ≤ lam v) (hA : A ≤ Fw24 g) :
    A-(∑ v, lam v*U v) ≤ Fw24 g := by
  exact (sub_le_self A (weighted_upper_nonneg hg q hq U hU lam hlam)).trans hA

/-- A flow lower bound on a dual-adjusted objective yields a lower bound
on the objective at a minimizer, including objectives used by OBBT. -/
theorem lower_of_cut_certificate {sep target objective : ℝ} {g : Fin 9 → ℝ}
    (hg : Relevant sep g) (q : ι → Fin 9 → ℤ)
    (hq : ∀ v, CoverCoerciveKKT.Orthant sep (move g (q v)))
    (U : ι → ℝ) (hU : ∀ v, changeEnergy g (q v) ≤ U v)
    (lam : ι → ℝ) (hlam : ∀ v, 0 ≤ lam v)
    (hcert : target ≤ objective-(∑ v, lam v*U v)) : target ≤ objective :=
  hcert.trans (sub_le_self objective (weighted_upper_nonneg hg q hq U hU lam hlam))

theorem floor_of_cut_certificate {sep A c : ℝ} {g : Fin 9 → ℝ}
    (hg : Relevant sep g) (q : ι → Fin 9 → ℤ)
    (hq : ∀ v, CoverCoerciveKKT.Orthant sep (move g (q v)))
    (U : ι → ℝ) (hU : ∀ v, changeEnergy g (q v) ≤ U v)
    (lam : ι → ℝ) (hlam : ∀ v, 0 ≤ lam v) (hA : A ≤ Fw24 g)
    (hcert : c ≤ A-(∑ v, lam v*U v)) : c ≤ Fw24 g :=
  hcert.trans (minorant_with_cuts hg q hq U hU lam hlam hA)

set_option pp.fullNames true
#print axioms change_nonneg
#print axioms upper_cut_nonneg
#print axioms weighted_changes_nonneg
#print axioms exclude_with_sublevel
#print axioms exclude_by_upper_cuts
#print axioms minorant_with_cuts
#print axioms lower_of_cut_certificate
#print axioms floor_of_cut_certificate
end StructuralGoal20261016.WindowFiniteMoveFamily
end
