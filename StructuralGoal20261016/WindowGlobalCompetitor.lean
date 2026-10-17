/- SPDX-License-Identifier: Apache-2.0
Actual gap permutations as global competitors for the 24-mode energy.
The competitor need only remain in the separated orthant: its orientation
is irrelevant because Relevant minimizes over the whole orthant. Numerical
energy envelopes remain explicit premises. No table, global floor, improved
zero proportion, or particular numerical exclusion is asserted here.
-/
import StructuralGoal20261016.WindowMinimizerCover
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open scoped BigOperators

namespace StructuralGoal20261016.WindowGlobalCompetitor
open WindowGapEnergy (Fw24)
open WindowMinimizerCover (Relevant)

/-- Exchange two actual gap coordinates, with no change in their values. -/
def swapGap (g : Fin 9 → ℝ) (i j : Fin 9) : Fin 9 → ℝ :=
  g ∘ Equiv.swap i j

theorem swapGap_apply (g : Fin 9 → ℝ) (i j r : Fin 9) :
    swapGap g i j r = g (Equiv.swap i j r) := rfl

theorem swapGap_feasible {sep : ℝ} {g : Fin 9 → ℝ}
    (hg : CoverCoerciveKKT.Orthant sep g) (i j : Fin 9) :
    CoverCoerciveKKT.Orthant sep (swapGap g i j) := by
  intro r
  exact hg (Equiv.swap i j r)

/-- This uses the actual global-minimum clause, not a local KKT condition. -/
theorem swap_energy_le {sep : ℝ} {g : Fin 9 → ℝ}
    (hg : Relevant sep g) (i j : Fin 9) :
    Fw24 g ≤ Fw24 (swapGap g i j) :=
  hg.2.2 (swapGap g i j) (swapGap_feasible hg.1 i j)

theorem swap_change_nonneg {sep : ℝ} {g : Fin 9 → ℝ}
    (hg : Relevant sep g) (i j : Fin 9) :
    0 ≤ Fw24 (swapGap g i j) - Fw24 g :=
  sub_nonneg.mpr (swap_energy_le hg i j)

/-- A lower bound at the minimizer and an upper bound at the competitor
give a nonnegative cut. Both actual energy bounds are explicit premises. -/
theorem envelope_difference_nonneg {sep L U : ℝ} {g : Fin 9 → ℝ}
    (hg : Relevant sep g) (i j : Fin 9)
    (hL : L ≤ Fw24 g) (hU : Fw24 (swapGap g i j) ≤ U) :
    0 ≤ U - L :=
  sub_nonneg.mpr (hL.trans ((swap_energy_le hg i j).trans hU))

theorem upper_change_nonneg {sep D : ℝ} {g : Fin 9 → ℝ}
    (hg : Relevant sep g) (i j : Fin 9)
    (hD : Fw24 (swapGap g i j) - Fw24 g ≤ D) : 0 ≤ D :=
  (swap_change_nonneg hg i j).trans hD

variable {ι : Type*} [Fintype ι]

theorem weighted_changes_nonneg {sep : ℝ} {g : Fin 9 → ℝ}
    (hg : Relevant sep g) (i j : ι → Fin 9)
    (theta : ι → ℝ) (htheta : ∀ v, 0 ≤ theta v) :
    0 ≤ ∑ v, theta v * (Fw24 (swapGap g (i v) (j v)) - Fw24 g) := by
  apply Finset.sum_nonneg
  intro v _
  exact mul_nonneg (htheta v) (swap_change_nonneg hg (i v) (j v))

theorem weighted_envelopes_nonneg {sep : ℝ} {g : Fin 9 → ℝ}
    (hg : Relevant sep g) (i j : ι → Fin 9) (L U : ι → ℝ)
    (hL : ∀ v, L v ≤ Fw24 g)
    (hU : ∀ v, Fw24 (swapGap g (i v) (j v)) ≤ U v)
    (theta : ι → ℝ) (htheta : ∀ v, 0 ≤ theta v) :
    0 ≤ ∑ v, theta v * (U v - L v) := by
  apply Finset.sum_nonneg
  intro v _
  exact mul_nonneg (htheta v)
    (envelope_difference_nonneg hg (i v) (j v) (hL v) (hU v))

theorem exclude_by_upper_change {sep D : ℝ} {g : Fin 9 → ℝ}
    (hg : Relevant sep g) (i j : Fin 9)
    (hD : Fw24 (swapGap g i j) - Fw24 g ≤ D) (hstrict : D < 0) : False :=
  (not_lt_of_ge (upper_change_nonneg hg i j hD)) hstrict

theorem exclude_by_weighted_envelopes {sep : ℝ} {g : Fin 9 → ℝ}
    (hg : Relevant sep g) (i j : ι → Fin 9) (L U : ι → ℝ)
    (hL : ∀ v, L v ≤ Fw24 g)
    (hU : ∀ v, Fw24 (swapGap g (i v) (j v)) ≤ U v)
    (theta : ι → ℝ) (htheta : ∀ v, 0 ≤ theta v)
    (hstrict : (∑ v, theta v * (U v - L v)) < 0) : False :=
  (not_lt_of_ge (weighted_envelopes_nonneg hg i j L U hL hU theta htheta)) hstrict

/-- Uniform checked envelopes with a strict negative difference exclude an
actual relevant minimizer throughout a cell. No such envelope is supplied
by this module. The containment predicate can be a concrete certified cell. -/
theorem exclude_cell_of_envelopes {Cell : Type*}
    (contains : Cell → (Fin 9 → ℝ) → Prop) (cell : Cell) {sep : ℝ}
    (i j : Fin 9) (L U : (Fin 9 → ℝ) → ℝ)
    (hL : ∀ g, contains cell g → L g ≤ Fw24 g)
    (hU : ∀ g, contains cell g → Fw24 (swapGap g i j) ≤ U g)
    (hstrict : ∀ g, contains cell g → U g - L g < 0) :
    ∀ g, contains cell g → ¬ Relevant sep g := by
  intro g hc hg
  exact (not_lt_of_ge (envelope_difference_nonneg hg i j (hL g hc) (hU g hc)))
    (hstrict g hc)

set_option pp.fullNames true
#print axioms swapGap_apply
#print axioms swapGap_feasible
#print axioms swap_energy_le
#print axioms swap_change_nonneg
#print axioms envelope_difference_nonneg
#print axioms upper_change_nonneg
#print axioms weighted_changes_nonneg
#print axioms weighted_envelopes_nonneg
#print axioms exclude_by_upper_change
#print axioms exclude_by_weighted_envelopes
#print axioms exclude_cell_of_envelopes
end StructuralGoal20261016.WindowGlobalCompetitor
end
