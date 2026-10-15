/-
Copyright (c) 2026 OpenAI. Released under Apache-2.0.

Uses the attributed RHLinalg spectral trace development and the existing
piecewise quadratic defect Psi. This independent research module adds a
matrix-valued Fenchel lower certificate; it does not change a published bound.
-/
import GramDefect20261015.Core

noncomputable section

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23Ext.StableRankTrace Zeta23Ext.Bridge

namespace StructuralResearch20261016.Fenchel

/-- The conjugate of the capped quadratic is `s^2/4+s` on `s <= 2`.
There is no lower bound on the dual variable. -/
theorem scalar_lower (t s : ℝ) (hs : s ≤ 2) :
    s * (t - 1) - s ^ 2 / 4 ≤ Psi t := by
  unfold Psi
  split_ifs with ht
  · nlinarith [sq_nonneg (t - 1 - s / 2)]
  · have hprod : 0 ≤ (2 - s) * (t - 2) :=
      mul_nonneg (sub_nonneg.mpr hs) (by linarith)
    nlinarith [sq_nonneg (s - 2)]

section Matrix

variable {𝕜 : Type*} [RCLike 𝕜]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A positive semidefinite slack `2I-S` supplies the dual spectral cap. -/
theorem eigenvalues_le_two {S : Matrix ι ι 𝕜} (hS : S.IsHermitian)
    (hcap : ((2 : 𝕜) • (1 : Matrix ι ι 𝕜) - S).PosSemidef) :
    ∀ i, hS.eigenvalues i ≤ 2 := by
  intro i
  have hnorm : RCLike.re
      (star ⇑(hS.eigenvectorBasis i) ⬝ᵥ ⇑(hS.eigenvectorBasis i)) = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K,
      hS.eigenvectorBasis.orthonormal.1 i]
    simp
  have hpos := hcap.re_dotProduct_nonneg ⇑(hS.eigenvectorBasis i)
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, map_sub, smul_eq_mul, RCLike.mul_re,
    RCLike.ofNat_re, RCLike.ofNat_im, zero_mul, sub_zero] at hpos
  rw [hnorm, ← hS.eigenvalues_eq i] at hpos
  linarith

/-- An entrywise row-sum certificate is sufficient. This is particularly useful
for rational supporting matrices: only finite arithmetic remains to check. -/
theorem eigenvalues_le_two_of_row_sum {S : Matrix ι ι 𝕜} (hS : S.IsHermitian)
    (hrow : ∀ k, RCLike.re (S k k) +
      (∑ j ∈ univ.erase k, ‖S k j‖) ≤ 2) :
    ∀ i, hS.eigenvalues i ≤ 2 := by
  intro i
  have hvec : Module.End.HasEigenvector (Matrix.toLin' S)
      (hS.eigenvalues i : 𝕜) ⇑(hS.eigenvectorBasis i) := by
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, ?_⟩
    · simpa only [Matrix.toLin'_apply, RCLike.real_smul_eq_coe_smul (K := 𝕜)]
        using hS.mulVec_eigenvectorBasis i
    · exact (WithLp.ofLp_eq_zero 2).ne.2 (hS.eigenvectorBasis.orthonormal.ne_zero i)
  obtain ⟨k, hk⟩ := eigenvalue_mem_ball
    (Module.End.hasEigenvalue_of_hasEigenvector hvec)
  have hnorm : ‖(hS.eigenvalues i : 𝕜) - S k k‖ ≤
      ∑ j ∈ univ.erase k, ‖S k j‖ := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hk
  have hre := RCLike.re_le_norm ((hS.eigenvalues i : 𝕜) - S k k)
  simp only [map_sub, RCLike.ofReal_re] at hre
  linarith [hrow k]

/-- A Hermitian dual certificate need only have spectrum bounded above by two.
The proof uses von Neumann's trace inequality, then scalar Fenchel inequalities
for the sorted eigenvalues. In particular, no commutation assumption is made. -/
theorem trace_lower {A S : Matrix ι ι 𝕜}
    (hA : A.IsHermitian) (hS : S.IsHermitian)
    (hcap : ∀ i, hS.eigenvalues i ≤ 2) :
    rtrace (S * (A - 1)) - rtrace (S * S) / 4 ≤
      rtrace (specMap hA Psi) := by
  have hprod : rtrace (S * A) ≤
      ∑ i, hS.eigenvalues₀ i * hA.eigenvalues₀ i :=
    vonNeumann_trace_ineq hS hA
  have htr : rtrace S = ∑ i, hS.eigenvalues₀ i := by
    rw [rtrace_eq_sum_eigenvalues hS]
    exact sum_eigenvalues_reindex hS id
  have hsq : rtrace (S * S) = ∑ i, (hS.eigenvalues₀ i) ^ 2 := by
    rw [← sum_eigenvalues_reindex hS (fun x => x ^ 2),
      ← frobSq_hermitian_eq_sum_sq_eigenvalues hS]
    simp only [frobSq, hS.eq, rtrace]
  have hscalar :
      ∑ i, (hS.eigenvalues₀ i * (hA.eigenvalues₀ i - 1)
        - (hS.eigenvalues₀ i) ^ 2 / 4) ≤ ∑ i, Psi (hA.eigenvalues₀ i) := by
    refine sum_le_sum fun i _ => scalar_lower _ _ ?_
    simpa only [eigenvalues_eigEquiv] using hcap (eigEquiv (n := ι) i)
  rw [Matrix.mul_sub, Matrix.mul_one, rtrace_sub, htr, hsq,
    rtrace_specMap, sum_eigenvalues_reindex hA Psi]
  calc rtrace (S * A) - ∑ i, hS.eigenvalues₀ i
      - (∑ i, (hS.eigenvalues₀ i) ^ 2) / 4
      ≤ (∑ i, hS.eigenvalues₀ i * hA.eigenvalues₀ i)
        - ∑ i, hS.eigenvalues₀ i - (∑ i, (hS.eigenvalues₀ i) ^ 2) / 4 := by
          linarith
    _ = ∑ i, (hS.eigenvalues₀ i * (hA.eigenvalues₀ i - 1)
        - (hS.eigenvalues₀ i) ^ 2 / 4) := by
          simp only [mul_sub, mul_one, sum_sub_distrib, sum_div]
    _ ≤ ∑ i, Psi (hA.eigenvalues₀ i) := hscalar

/-- Matrix Fenchel bound with a positive semidefinite slack certificate. -/
theorem trace_lower_of_posSemidef {A S : Matrix ι ι 𝕜}
    (hA : A.IsHermitian) (hS : S.IsHermitian)
    (hcap : ((2 : 𝕜) • (1 : Matrix ι ι 𝕜) - S).PosSemidef) :
    rtrace (S * (A - 1)) - rtrace (S * S) / 4 ≤
      rtrace (specMap hA Psi) :=
  trace_lower hA hS (eigenvalues_le_two hS hcap)

theorem trace_lower_of_row_sum {A S : Matrix ι ι 𝕜}
    (hA : A.IsHermitian) (hS : S.IsHermitian)
    (hrow : ∀ k, RCLike.re (S k k) +
      (∑ j ∈ univ.erase k, ‖S k j‖) ≤ 2) :
    rtrace (S * (A - 1)) - rtrace (S * S) / 4 ≤
      rtrace (specMap hA Psi) :=
  trace_lower hA hS (eigenvalues_le_two_of_row_sum hS hrow)

end Matrix

/-- Direct interface to the defect used by the published zero-counting bridge. -/
theorem defect_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A S : Matrix ι ι ℂ} (hA : A.IsHermitian) (hS : S.IsHermitian)
    (hcap : ∀ i, hS.eigenvalues i ≤ 2) :
    rtrace (S * (A - 1)) - rtrace (S * S) / 4 ≤ defect hA :=
  trace_lower hA hS hcap

theorem defect_lower_of_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A S : Matrix ι ι ℂ} (hA : A.IsHermitian) (hS : S.IsHermitian)
    (hcap : ((2 : ℂ) • (1 : Matrix ι ι ℂ) - S).PosSemidef) :
    rtrace (S * (A - 1)) - rtrace (S * S) / 4 ≤ defect hA :=
  trace_lower_of_posSemidef hA hS hcap

end StructuralResearch20261016.Fenchel
