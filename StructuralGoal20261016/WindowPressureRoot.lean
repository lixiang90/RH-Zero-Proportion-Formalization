/- SPDX-License-Identifier: Apache-2.0
Coupled pressure root for the actual minimizer cover.
Coordinate bounds alone do not imply the sharper shared-budget span bounds.
The root region here retains the full pressure inequality from F<c.
-/
import StructuralGoal20261016.WindowMinimizerCover
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Finset
namespace StructuralGoal20261016.WindowPressureRoot
open WindowGapEnergy WindowMinimizerCover
open StructuralW10Followup20261016.NewLedger

def Region (sep c : ℝ) (g : Fin 9 → ℝ) : Prop :=
  CoverCoerciveKKT.Orthant sep g ∧ (∑ i, W.b i*g i) < c

theorem region_of_relevantBelow {sep c : ℝ} {g : Fin 9 → ℝ}
    (hg : RelevantBelow sep c g) : Region sep c g := by
  exact ⟨hg.1.1, (pressure_le W a_nonneg g).trans_lt hg.2⟩

theorem selected_excess_le {ι : Type*} [Fintype ι] (S : Finset ι)
    (b g : ι → ℝ) (sep m : ℝ)
    (hb : ∀ i, 0 ≤ b i) (hg : ∀ i, sep ≤ g i)
    (hm : ∀ i ∈ S, m ≤ b i) :
    m*(∑ i ∈ S, (g i-sep)) ≤ ∑ i, b i*(g i-sep) := by
  classical
  calc
    m*(∑ i ∈ S, (g i-sep)) = ∑ i ∈ S, m*(g i-sep) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ S, b i*(g i-sep) := by
      exact Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_right (hm i hi) (sub_nonneg.mpr (hg i)))
    _ ≤ ∑ i, b i*(g i-sep) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      intro i _ _
      exact mul_nonneg (hb i) (sub_nonneg.mpr (hg i))

theorem selected_span_upper {ι : Type*} [Fintype ι] (S : Finset ι)
    (b g : ι → ℝ) (sep c m : ℝ)
    (hb : ∀ i, 0 ≤ b i) (hg : ∀ i, sep ≤ g i)
    (hm : 0 < m) (hmb : ∀ i ∈ S, m ≤ b i)
    (hpressure : (∑ i, b i*g i) < c) :
    (∑ i ∈ S, g i) < (S.card:ℝ)*sep + (c-sep*(∑ i, b i))/m := by
  classical
  have h := selected_excess_le S b g sep m hb hg hmb
  have hleft : (∑ i ∈ S, (g i-sep)) = (∑ i ∈ S, g i)-(S.card:ℝ)*sep := by
    simp [Finset.sum_sub_distrib]
  have hright : (∑ i, b i*(g i-sep)) = (∑ i, b i*g i)-sep*(∑ i, b i) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hleft,hright] at h
  have hmul : m*((∑ i ∈ S, g i)-(S.card:ℝ)*sep) < c-sep*(∑ i, b i) := by linarith
  have hdiv : (∑ i ∈ S, g i)-(S.card:ℝ)*sep < (c-sep*(∑ i, b i))/m := by
    apply (lt_div_iff₀ hm).mpr
    nlinarith
  linarith

/-- The actual numerical root may use every coupled pressure bound, not
merely the weaker independent coordinate box. -/
theorem global_floor_of_checked {Cell : Type}
    (ops : MinimizerCover.Operations Cell (Fin 9 → ℝ)) {sep c : ℝ}
    (sound : MinimizerCover.Sound ops (RelevantBelow sep c) Fw24 c)
    (tree : MinimizerCover.Tree) (root : Cell)
    (checked : tree.check ops root = true)
    (root_contains : ∀ g, Region sep c g → ops.contains root g)
    (g : Fin 9 → ℝ) (hg : CoverCoerciveKKT.Orthant sep g) : c ≤ Fw24 g := by
  by_contra h
  obtain ⟨m, hm, ho, hmin, hmc⟩ :=
    exists_ordered_min_below (sep := sep) (c := c) ⟨g,hg,lt_of_not_ge h⟩
  have hrel : RelevantBelow sep c m := ⟨⟨hm,ho,hmin⟩,hmc⟩
  have hroot := root_contains m (region_of_relevantBelow hrel)
  exact (not_lt_of_ge (tree.check_sound sound root checked m hrel hroot)) hmc

set_option pp.fullNames true
#print axioms region_of_relevantBelow
#print axioms selected_excess_le
#print axioms selected_span_upper
#print axioms global_floor_of_checked
end StructuralGoal20261016.WindowPressureRoot
end
