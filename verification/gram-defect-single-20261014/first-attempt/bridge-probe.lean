import GramDefectRecord.Final
import ChallengeDeps.CandidateSpec

/- Local website wrapper probe. Li Xiang, 2026-10-14, Apache-2.0.
The trusted and Zeta23 definitions are compared explicitly by reflexivity.
No score or trusted counting function is redefined. -/
noncomputable section

namespace GramDefectSubmissionCounts

theorem count_eq (T₁ T₂ : ℝ) :
    _root_.Ncount T₁ T₂ = Zeta23.Ncount T₁ T₂ := by rfl

theorem distinct_eq (T₁ T₂ : ℝ) :
    _root_.N0star T₁ T₂ = Zeta23.N0star T₁ T₂ := by rfl

end GramDefectSubmissionCounts

theorem candidate_strict_improvement :
    currentRecordKappa < candidateKappa := by
  norm_num [currentRecordKappa, candidateKappa]

theorem candidate_critical_line_bound :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T) := by
  simpa only [candidateKappa, GramDefectRecord.recordRatio,
    GramDefectSubmissionCounts.count_eq, GramDefectSubmissionCounts.distinct_eq] using
    GramDefectRecord.distinct_dyadic

theorem candidate_critical_line_bound_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (candidateKappa - ε) * (Ncount 0 T : ℝ) ≤ N0star 0 T := by
  simpa only [candidateKappa, GramDefectRecord.recordRatio,
    GramDefectSubmissionCounts.count_eq, GramDefectSubmissionCounts.distinct_eq] using
    GramDefectRecord.distinct_cumulative

#print axioms GramDefectSubmissionCounts.count_eq
#print axioms GramDefectSubmissionCounts.distinct_eq
#print axioms candidate_strict_improvement
#print axioms candidate_critical_line_bound
#print axioms candidate_critical_line_bound_cumulative

end
