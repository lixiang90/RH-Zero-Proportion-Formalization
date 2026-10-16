/- SPDX-License-Identifier: Apache-2.0
The full W10 conclusion depends on Certificate.initial_covered, which checks
the complete finite tree. Full compilation of that concrete instance remains
pending; this source is not evidence of a kernel-verified new bound.
No analytic floor is assumed in these intended final statements. -/
import StructuralW10Cert20261016.Certificate
import StructuralW10Cert20261016.FloorTransfer

noncomputable section
namespace StructuralW10Cert20261016.Final

abbrev ratio := FinalConditional.candidateRatio

theorem separated_floor : FinalConditional.SeparatedFloor :=
  FloorTransfer.separated_floor Certificate.initial_covered

theorem strict_improvement : FinalConditional.currentSiteRatio < ratio :=
  FinalConditional.strict_improvement

theorem simple_dyadic : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (ratio - ε) * (Zeta23.Ncount T (2*T) : ℝ) ≤ Zeta23.N0simple T (2*T) :=
  FinalConditional.simple_dyadic separated_floor

theorem simple_cumulative : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (ratio - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0simple 0 T :=
  FinalConditional.simple_cumulative separated_floor

theorem distinct_dyadic : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (ratio - ε) * (Zeta23.Ncount T (2*T) : ℝ) ≤ Zeta23.N0star T (2*T) :=
  FinalConditional.distinct_dyadic separated_floor

theorem distinct_cumulative : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
    (ratio - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  FinalConditional.distinct_cumulative separated_floor

#print axioms separated_floor
#print axioms simple_dyadic
#print axioms simple_cumulative
#print axioms distinct_dyadic
#print axioms distinct_cumulative
end StructuralW10Cert20261016.Final
end
