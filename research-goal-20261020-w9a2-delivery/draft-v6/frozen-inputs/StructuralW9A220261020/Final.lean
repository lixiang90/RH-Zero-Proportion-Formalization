/-
SPDX-License-Identifier: Apache-2.0

Preparation only. Actual W9A2 quantitative-localization / finite-state
composition. No graph, local-energy, matrix, or counting premise remains in
the two conclusions. The source is not yet compiled or independently checked.
The literal baseline records the frozen official 2026-10-19 W9A2 result;
the official challenge wrapper must use a freshly generated trusted spec.
-/
import StructuralW9A220261020.Localization
import StructuralW9A220261020.Counting

set_option Elab.async false
set_option maxHeartbeats 0

noncomputable section
open Zeta23 Zeta23Ext.BridgeW

namespace StructuralW9A220261020.Final

def base : ℝ := 893029029923108825 / 100000000000000000000
def increment : ℝ := 622387738726 / (5 * 100000000000000000000)
def c : ℝ := base + increment
def boundary : ℝ := 2504722000690 / (5 * 100000000000000000000)
def pressure : ℝ := 454741897490 / 100000000000000

def weightedKappa : ℝ :=
  3337881639516708570682858853672166187793 /
    4955348542279967171490000000000000000000

def baselineKappa : ℝ :=
  3337881639516708570682858853672166187793 /
    4955348548503844558750000000000000000000

theorem strict_improvement : baselineKappa < weightedKappa := by
  norm_num [baselineKappa, weightedKappa]

private theorem hc : (0 : ℝ) < c := by norm_num [c, base, increment]
private theorem hboundary : (0 : ℝ) ≤ boundary := by norm_num [boundary]
private theorem hboundaryc : boundary ≤ c := by norm_num [boundary, c, base, increment]
private theorem hc64 : c ≤ (1 : ℝ) / 64 := by norm_num [c, base, increment]

private theorem hB : RiemannFail.W9.B = pressure := by
  simpa only [pressure] using RiemannFail.W9_B

/-- Every real separated window is located by the new quantitative walk.
The transition theorem is the complete shared-span exclusion proof, and the
integer potential is converted to physical energy units before telescoping.
The maximum potential oscillation is charged once to the separated remainder. -/
theorem actual_summed :
    StructuralW9A220261020.Counting.SeparatedSummedCertificate
      RiemannFail.W9 c boundary (17 / 20) := by
  change StructuralW9A220261020.Counting.SeparatedSummedCertificate
    RiemannFail.W9 (base + increment) boundary (17 / 20)
  apply StructuralW9A220261020.Counting.summed_of_state RiemannFail.W9
    base increment boundary (17 / 20)
    (fun s => (StructuralW9A220261020.Graph.cost s : ℝ) / 100000000000000000000)
    (fun s => (StructuralW9A220261020.Graph.potential s : ℝ) /
      (5 * 100000000000000000000))
    StructuralW9A220261020.Graph.StateAt StructuralW9A220261020.Graph.Edge
    StructuralW9A220261020.Graph.good
  · intro g hg
    obtain ⟨s, hs, hf⟩ := StructuralW9A220261020.Localization.located_state g hg
    refine ⟨s, hs, ?_⟩
    simpa only [base, StructuralW9A220261020.Localization.base,
      AMW.Cert.PC9QB6M.cN, AMW.Cert.PC9QB6M.SA, Nat.cast_ofNat] using hf
  · intro g _ s t hs ht
    apply StructuralW9A220261020.Graph.edge_from_locations g s t
    · change StructuralW9A220261020.Graph.StateAt
        (StructuralW9A220261020.Counting.leftGaps g) s
      exact hs
    · change StructuralW9A220261020.Graph.StateAt
        (StructuralW9A220261020.Counting.rightGaps g) t
      exact ht
  · exact StructuralW9A220261020.Graph.all_to_good
  · intro s t he
    have hi : (622387738726 : ℝ) +
        (StructuralW9A220261020.Graph.potential t : ℝ) -
        (StructuralW9A220261020.Graph.potential s : ℝ) ≤
        5 * (StructuralW9A220261020.Graph.cost s : ℝ) := by
      exact_mod_cast StructuralW9A220261020.Graph.edge_potential s t he
    dsimp [increment]
    linarith only [hi]
  · intro s
    have hi : (0 : ℝ) ≤ (StructuralW9A220261020.Graph.potential s : ℝ) := by
      exact_mod_cast StructuralW9A220261020.Graph.potential_nonneg s
    exact div_nonneg hi (by norm_num)
  · intro s
    have hi : (StructuralW9A220261020.Graph.potential s : ℝ) ≤ 2504722000690 := by
      exact_mod_cast StructuralW9A220261020.Graph.potential_le s
    exact div_le_div_of_nonneg_right hi (by norm_num)

private theorem ratio_exact :
    StructuralW9A220261020.Counting.ratio c pressure = weightedKappa := by
  norm_num [StructuralW9A220261020.Counting.ratio, c, base, increment,
    pressure, weightedKappa]

theorem actual_dyadic :
    ∀ epsilon > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0,
      (weightedKappa - epsilon) * (_root_.Ncount T (2*T) : ℝ) ≤
        _root_.N0star T (2*T) := by
  have h := StructuralW9A220261020.Counting.actual_dyadic_of_summed
    RiemannFail.W9 RiemannFail.W9_adm hc hboundary hboundaryc hc64 hB actual_summed
  rw [← ratio_exact]
  exact h

theorem actual_cumulative :
    ∀ epsilon > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0,
      (weightedKappa - epsilon) * (_root_.Ncount 0 T : ℝ) ≤ _root_.N0star 0 T := by
  have h := StructuralW9A220261020.Counting.actual_cumulative_of_summed
    RiemannFail.W9 RiemannFail.W9_adm hc hboundary hboundaryc hc64 hB actual_summed
  rw [← ratio_exact]
  exact h

end StructuralW9A220261020.Final

set_option pp.fullNames true
#print axioms StructuralW9A220261020.Localization.located_state
#print axioms StructuralW9A220261020.Graph.edge_from_locations
#print axioms StructuralW9A220261020.Graph.edge_potential
#print axioms StructuralW9A220261020.Final.actual_summed
#print axioms StructuralW9A220261020.Final.strict_improvement
#print axioms StructuralW9A220261020.Final.actual_dyadic
#print axioms StructuralW9A220261020.Final.actual_cumulative
end
