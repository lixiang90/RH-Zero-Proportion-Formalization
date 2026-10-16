/- SPDX-License-Identifier: Apache-2.0
The analytic premise has been reduced to one finite executable check.
This module proves the transfer conditionally; it does not assert that
the concrete complete finite data have passed the Lean kernel. -/
import StructuralW10Cert20261016.AdaptiveCoverage
import StructuralW10Cert20261016.FastPruefer
import StructuralW10Cert20261016.FloorTransfer

noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016.LocalChecker
namespace StructuralW10Cert20261016.FiniteConditional

def FiniteCheck (SL : List ℕ) (read payload : ℕ → ℕ) : Prop :=
  SLok 9 PR SL ∧
    AdaptiveCoverage.walk SL read (FastPruefer.dispatch payload)
      128 1 RootBounds.initialCell ≠ 0

theorem local_floor {SL : List ℕ} {read payload : ℕ → ℕ}
    (checked : FiniteCheck SL read payload) : FinalConditional.SeparatedFloor := by
  apply FloorTransfer.separated_floor
  exact AdaptiveCoverage.walk_sound checked.1 read (FastPruefer.dispatch payload)
    (FastPruefer.dispatch_sound payload) 128 1 RootBounds.initialCell checked.2

theorem strict_improvement :
    FinalConditional.currentSiteRatio < FinalConditional.candidateRatio :=
  FinalConditional.strict_improvement

theorem simple_dyadic {SL : List ℕ} {read payload : ℕ → ℕ}
    (checked : FiniteCheck SL read payload) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (FinalConditional.candidateRatio - ε) * (Zeta23.Ncount T (2*T) : ℝ) ≤
        Zeta23.N0simple T (2*T) :=
  FinalConditional.simple_dyadic (local_floor checked)

theorem simple_cumulative {SL : List ℕ} {read payload : ℕ → ℕ}
    (checked : FiniteCheck SL read payload) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (FinalConditional.candidateRatio - ε) * (Zeta23.Ncount 0 T : ℝ) ≤
        Zeta23.N0simple 0 T :=
  FinalConditional.simple_cumulative (local_floor checked)

theorem distinct_dyadic {SL : List ℕ} {read payload : ℕ → ℕ}
    (checked : FiniteCheck SL read payload) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (FinalConditional.candidateRatio - ε) * (Zeta23.Ncount T (2*T) : ℝ) ≤
        Zeta23.N0star T (2*T) :=
  FinalConditional.distinct_dyadic (local_floor checked)

theorem distinct_cumulative {SL : List ℕ} {read payload : ℕ → ℕ}
    (checked : FiniteCheck SL read payload) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (FinalConditional.candidateRatio - ε) * (Zeta23.Ncount 0 T : ℝ) ≤
        Zeta23.N0star 0 T :=
  FinalConditional.distinct_cumulative (local_floor checked)

#print axioms local_floor
#print axioms strict_improvement
#print axioms simple_dyadic
#print axioms simple_cumulative
#print axioms distinct_dyadic
#print axioms distinct_cumulative
end StructuralW10Cert20261016.FiniteConditional
end
