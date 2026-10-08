import ChallengeDeps
import Zeta23.Statement

/- The website's trusted counting definitions are independent copies of the
same definitions in Zeta23. These identities preserve the exact zero sets,
ordinate windows, multiplicities and critical-line counts. -/
namespace RHWeilRecord.TrustedCounts

theorem count_eq (T₁ T₂ : ℝ) :
    _root_.Ncount T₁ T₂ = Zeta23.Ncount T₁ T₂ := by rfl

theorem distinct_eq (T₁ T₂ : ℝ) :
    _root_.N0star T₁ T₂ = Zeta23.N0star T₁ T₂ := by rfl

theorem simple_eq (T₁ T₂ : ℝ) :
    _root_.N0simple T₁ T₂ = Zeta23.N0simple T₁ T₂ := by rfl

end RHWeilRecord.TrustedCounts
