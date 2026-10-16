/- SPDX-License-Identifier: Apache-2.0
KKT-only interval contraction. These algebraic lemmas retain every original
orthant KKT point; they do not assert a pointwise cover of the discarded part
of a cell. Actual gradient/Taylor and flow enclosures remain explicit inputs.
-/
import StructuralGoal20261016.CoverCoerciveKKT
set_option Elab.async false

noncomputable section
open Finset
namespace StructuralGoal20261016.CoverKKTContraction

def KKT {n : ℕ} (sep : ℝ) (g p : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ (∀ i, sep < g i → p i = 0)

def dot {n : ℕ} (d p : Fin n → ℝ) : ℝ := ∑ i, d i * p i

/-- A combination supported strictly inside the original orthant vanishes
at every KKT point. A cell boundary is irrelevant to this statement. -/
theorem dot_eq_zero {n : ℕ} {sep : ℝ} {g p d : Fin n → ℝ}
    (hkkt : KKT sep g p) (hsupport : ∀ i, d i ≠ 0 → sep < g i) :
    dot d p = 0 := by
  unfold dot
  apply Finset.sum_eq_zero
  intro i _
  by_cases hd : d i = 0
  · simp [hd]
  · rw [hkkt.2 i (hsupport i hd), mul_zero]

/-- Strict negative derivative on a support consisting of interior
coordinates and one uncertain boundary coordinate forces that coordinate
onto the original sep face. This is complementarity, not boundary descent. -/
theorem boundary_face {n : ℕ} {sep : ℝ} {g p d : Fin n → ℝ}
    (hg : CoverCoerciveKKT.Orthant sep g) (hkkt : KKT sep g p)
    (i : Fin n) (hsupport : ∀ j, d j ≠ 0 → j ≠ i → sep < g j)
    (hnegative : dot d p < 0) : g i = sep := by
  by_contra hne
  have hi : sep < g i := lt_of_le_of_ne (hg i) (Ne.symm hne)
  have hz : dot d p = 0 := dot_eq_zero hkkt (by
    intro j hd
    by_cases hji : j = i
    · simpa [hji] using hi
    · exact hsupport j hd hji)
  linarith

/-- Exact Newton coordinate bounds from an affine enclosure of an interior
gradient combination. No floating inverse or matrix property is trusted. -/
theorem interval_of_affine_enclosure {n : ℕ} {sep : ℝ} {g p d : Fin n → ℝ}
    (hkkt : KKT sep g p) (hsupport : ∀ j, d j ≠ 0 → sep < g j)
    (i : Fin n) (C τ R E L U : ℝ) (hτ : 0 < τ)
    (henclose : -E ≤ dot d p - (C + τ * g i + R) ∧
      dot d p - (C + τ * g i + R) ≤ E)
    (hR : L ≤ R ∧ R ≤ U) :
    (-E - C - U) / τ ≤ g i ∧ g i ≤ (E - C - L) / τ := by
  have hz := dot_eq_zero hkkt hsupport
  rw [hz] at henclose
  constructor
  · apply (div_le_iff₀ hτ).mpr
    nlinarith [henclose.2, hR.2]
  · apply (le_div_iff₀ hτ).mpr
    nlinarith [henclose.1, hR.1]

/-- Outward rounding need only be checked by rational inequalities. The
retained coordinates stay inside every certified, rounded interval. -/
theorem rounded_interval_of_affine_enclosure
    {n : ℕ} {sep : ℝ} {g p d : Fin n → ℝ}
    (hkkt : KKT sep g p) (hsupport : ∀ j, d j ≠ 0 → sep < g j)
    (i : Fin n) (C τ R E L U l u : ℝ) (hτ : 0 < τ)
    (henclose : -E ≤ dot d p - (C + τ * g i + R) ∧
      dot d p - (C + τ * g i + R) ≤ E)
    (hR : L ≤ R ∧ R ≤ U)
    (hl : l ≤ (-E - C - U) / τ) (hu : (E - C - L) / τ ≤ u) :
    l ≤ g i ∧ g i ≤ u := by
  obtain ⟨hlo, hhi⟩ := interval_of_affine_enclosure hkkt hsupport i C τ R E L U hτ henclose hR
  exact ⟨hl.trans hlo, hhi.trans hu⟩

#print axioms dot_eq_zero
#print axioms boundary_face
#print axioms interval_of_affine_enclosure
#print axioms rounded_interval_of_affine_enclosure
end StructuralGoal20261016.CoverKKTContraction
end
