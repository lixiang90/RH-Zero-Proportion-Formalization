import ChallengeDeps
import Zeta23.Statement.SeamClosed

/-!
Count inclusion for the site's fixed zeta-zero definitions.

No counting definition is copied or replaced here.  The root-namespace
definitions are imported from the trusted comparator layer.  Their
definitional equality with Zeta23's statement layer lets us reuse its proved
local finiteness.  All proportion hypotheses remain explicit: these lemmas
transport a genuine simple critical-line bound; they do not prove that bound.
-/

noncomputable section

namespace RHWeilRecord

/-- The trusted positive-ordinate zero window is finite, without RH. -/
theorem trusted_zerosIn_finite (T₁ T₂ : ℝ) :
    (zerosIn T₁ T₂).Finite := by
  change (Zeta23.zerosIn T₁ T₂).Finite
  exact Zeta23.zerosIn_finite T₁ T₂

/-- Every simple critical-line zero is a distinct critical-line zero. -/
theorem n0simple_le_n0star (T₁ T₂ : ℝ) :
    N0simple T₁ T₂ ≤ N0star T₁ T₂ := by
  unfold N0simple N0star
  exact Set.ncard_le_ncard Set.inter_subset_left
    ((trusted_zerosIn_finite T₁ T₂).subset Set.inter_subset_left)

/-- The same actual count inclusion after the cast used by the challenge. -/
theorem n0simple_le_n0star_real (T₁ T₂ : ℝ) :
    (N0simple T₁ T₂ : ℝ) ≤ (N0star T₁ T₂ : ℝ) := by
  exact_mod_cast n0simple_le_n0star T₁ T₂

/-- Preserve epsilon and threshold quantifiers on any fixed window functions. -/
theorem asymptotic_simple_to_distinct {κ : ℝ} (a b : ℝ → ℝ)
    (h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Ncount (a T) (b T) : ℝ) ≤ (N0simple (a T) (b T) : ℝ)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Ncount (a T) (b T) : ℝ) ≤ (N0star (a T) (b T) : ℝ) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := h ε hε
  refine ⟨T₀, ?_⟩
  intro T hT
  exact (hT₀ T hT).trans (n0simple_le_n0star_real (a T) (b T))

/-- A proved simple bound yields exactly the site's dyadic counting statement. -/
theorem dyadic_simple_to_distinct {κ : ℝ}
    (h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Ncount T (2 * T) : ℝ) ≤ (N0simple T (2 * T) : ℝ)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Ncount T (2 * T) : ℝ) ≤ (N0star T (2 * T) : ℝ) := by
  exact asymptotic_simple_to_distinct (fun T => T) (fun T => 2 * T) h

/-- A proved simple bound yields exactly the site's cumulative statement. -/
theorem cumulative_simple_to_distinct {κ : ℝ}
    (h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Ncount 0 T : ℝ) ≤ (N0simple 0 T : ℝ)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (κ - ε) * (Ncount 0 T : ℝ) ≤ (N0star 0 T : ℝ) := by
  exact asymptotic_simple_to_distinct (fun _ => 0) (fun T => T) h

end RHWeilRecord

#print axioms RHWeilRecord.trusted_zerosIn_finite
#print axioms RHWeilRecord.n0simple_le_n0star
#print axioms RHWeilRecord.n0simple_le_n0star_real
#print axioms RHWeilRecord.asymptotic_simple_to_distinct
#print axioms RHWeilRecord.dyadic_simple_to_distinct
#print axioms RHWeilRecord.cumulative_simple_to_distinct
