import GramDefect20261015.Core

/-! Weighted overlapping principal compressions for the existing spectral defect.
This module proves a structural tool; it states no improved zeta proportion.
-/

noncomputable section
open Matrix Finset RHLinalg
open scoped BigOperators ComplexOrder
open Zeta23Ext.Bridge Zeta23Ext.StableRankTrace

namespace StructuralResearch20261016

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]

theorem compression_weighted_cover
    {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (B : β → Finset ι) (w : β → ℝ)
    (hcover : ∀ k, ∑ b, (if k ∈ B b then w b else 0) ≤ 1) (i : ι) :
    ∑ b, w b * compressWeight hM (Subtype.val : B b → ι) i ≤ 1 := by
  classical
  let u : ι → ℝ := fun k => ‖(hM.eigenvectorUnitary : Matrix ι ι ℂ) k i‖ ^ 2
  have hsub (b : β) : compressWeight hM (Subtype.val : B b → ι) i =
      ∑ k ∈ B b, u k := by
    exact Finset.sum_coe_sort (B b) u
  calc
    (∑ b, w b * compressWeight hM (Subtype.val : B b → ι) i)
        = ∑ b, ∑ k, (if k ∈ B b then w b else 0) * u k := by
          simp [hsub, Finset.mul_sum, ite_mul]
    _ = ∑ k, (∑ b, if k ∈ B b then w b else 0) * u k := by
          rw [Finset.sum_comm]
          simp only [Finset.sum_mul]
    _ ≤ ∑ k, 1 * u k := by
          exact Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_right (hcover k) (sq_nonneg _)
    _ = 1 := by
          simp only [one_mul]
          exact sum_normSq_col_eigenvectorUnitary hM i

theorem fractional_pinching
    {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (B : β → Finset ι) (w : β → ℝ)
    (hw : ∀ b, 0 ≤ w b)
    (hcover : ∀ k, ∑ b, (if k ∈ B b then w b else 0) ≤ 1) :
    ∑ b, w b * blockDefect hM (B b) ≤ defect hM := by
  classical
  have hlocal (b : β) : blockDefect hM (B b) ≤
      ∑ i, compressWeight hM (Subtype.val : B b → ι) i * Psi (hM.eigenvalues i) := by
    unfold blockDefect defect
    rw [rtrace_specMap]
    exact sum_eigenvalues_submatrix_le hM Subtype.val_injective Psi_convexOn
  calc
    (∑ b, w b * blockDefect hM (B b)) ≤
        ∑ b, w b * ∑ i, compressWeight hM (Subtype.val : B b → ι) i *
          Psi (hM.eigenvalues i) :=
            Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hlocal b) (hw b)
    _ = ∑ i, (∑ b, w b * compressWeight hM (Subtype.val : B b → ι) i) *
          Psi (hM.eigenvalues i) := by
            simp_rw [Finset.mul_sum, ← mul_assoc]
            rw [Finset.sum_comm]
            simp only [Finset.sum_mul]
    _ ≤ ∑ i, Psi (hM.eigenvalues i) := by
            apply Finset.sum_le_sum
            intro i _
            simpa only [one_mul] using mul_le_mul_of_nonneg_right
              (compression_weighted_cover hM B w hcover i) (Psi_nonneg _)
    _ = defect hM := by rw [defect, rtrace_specMap]

end StructuralResearch20261016
