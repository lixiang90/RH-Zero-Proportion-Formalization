/-
SPDX-License-Identifier: Apache-2.0

The matching composition below adapts the attributed OpethN matching proof:
R. Arun Chandru's combination of Samuel Lavery's defect bridge and Kristian
Muri Knausgard's matching development. Its only new charge is one bounded
endpoint potential on the separated remainder. The zeta counting argument
is reused through the already proved generic ActualDefectEstimate interface.
All numerical local certificate premises remain explicit.
-/
import StructuralResearch20261016.Coboundary
import GramDefect20261015.RefinedCounting

noncomputable section

open Matrix Finset RHLinalg Filter Topology
open scoped ComplexOrder BigOperators
open Zeta23Ext.StableRankTrace Zeta23Ext.Bridge Zeta23Ext.BridgeW
open StructuralResearch20261016.Coboundary

namespace StructuralResearch20261016.CoboundaryCounting

section Matching

open Meshuggah.Gram
variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem block_remainder_bound_separated {n : ℕ} (hn : 2 ≤ n)
    {x : ι → ℝ} (hx : Function.Injective x) {G : Matrix ι ι ℂ}
    (hG : G.IsHermitian) {c C sep : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (W : WCert n) (hW : W.Adm)
    (hCert : SeparatedSummedCertificate W c C sep)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i j, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ)
    (B : Finset ι)
    (hsep : ∀ i j : B, i ≠ j → sep ≤ |x i - x j|)
    (hcap : ∀ i, (hG.submatrix (Subtype.val : B → ι)).eigenvalues i ≤ 2)
    {R : ℝ} (hR : 0 ≤ R) (hspan : ∀ i j, x i - x j ≤ R) :
    (c - 4 * ((n - 1 : ℕ) : ℝ) * δ) * (B.card : ℝ) - W.B * R
      - ((n - 1 : ℕ) : ℝ) * c - C ≤ blockDefect hG B := by
  classical
  have hxB : Function.Injective (fun i : B => x i) := fun i j h =>
    Subtype.ext (hx h)
  have hcloseB : ∀ i j : B, i ≠ j →
      ‖G.submatrix (Subtype.val : B → ι) (Subtype.val : B → ι) i j -
        (kfun (x i - x j) : ℂ)‖ ≤ δ := fun i j hij =>
    hclose i j (fun h => hij (Subtype.ext h))
  have h := remainder_bound_separated_summed hn hxB
    (hG.submatrix (Subtype.val : B → ι)) hc hC W hW hCert hsep
    hδ hcloseB hcap hR (fun i j => hspan i j)
  simpa only [Fintype.card_coe, blockDefect] using h

/-- Close pairs use their existing payment; only the separated remainder pays
the potential oscillation, exactly once in the matching partition. -/
theorem matching_defect_bound_summed {n : ℕ} (hn : 2 ≤ n)
    {x : ι → ℝ} (hx : Function.Injective x)
    {G : Matrix ι ι ℂ} (hG : G.IsHermitian) {c C : ℝ}
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hcPair : c ≤ 1 / 64)
    (W : WCert n) (hW : W.Adm)
    (hCert : SeparatedSummedCertificate W c C (17 / 20))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i j, i ≠ j →
      ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ)
    (hcap : ∀ S : Finset ι,
      (∀ i j : S, i ≠ j → 17 / 20 ≤ |x i - x j|) →
      ∀ k : S, (hG.submatrix (Subtype.val : S → ι)).eigenvalues k ≤ 2)
    {R : ℝ} (hR : 0 ≤ R) (hspan : ∀ i j, x i - x j ≤ R) :
    (c - 4 * ((n - 1 : ℕ) : ℝ) * δ) * (Fintype.card ι : ℝ) - W.B * R
      - ((n - 1 : ℕ) : ℝ) * c - C ≤ defect hG := by
  classical
  set k : ℝ := ((n - 1 : ℕ) : ℝ) with hkdef
  have hk1 : (1 : ℝ) ≤ k := by
    rw [hkdef]; exact_mod_cast (by omega : 1 ≤ n - 1)
  obtain ⟨σ, hσ, hσsep⟩ := exists_maximal_matching x (17 / 20)
  let S : Option (Sym2 ι) → Finset ι :=
    fun z => univ.filter (fun i => matchLabel σ i = z)
  have hpinch : (∑ z, blockDefect hG (S z)) ≤ defect hG :=
    pinching_partition hG (Option (Sym2 ι)) (matchLabel σ)
  have hblock (z : Option (Sym2 ι)) :
      (c - 4 * k * δ) * ((S z).card : ℝ) -
        (if z = none then W.B * R + k * c + C else 0) ≤ blockDefect hG (S z) := by
    cases z with
    | none =>
      rw [if_pos rfl]
      have hfixed (i : S none) : σ i = i :=
        matchLabel_eq_none.mp ((mem_filter.mp i.property).2)
      have hsep : ∀ i j : S none, i ≠ j → 17 / 20 ≤ |x i - x j| := by
        intro i j hij
        exact hσsep i j (hfixed i) (hfixed j)
          (fun h => hij (Subtype.ext h))
      have hb := block_remainder_bound_separated hn hx hG hc hC W hW hCert
        hδ hclose (S none) hsep (hcap (S none) hsep) hR hspan
      linarith only [hb]
    | some z =>
      rw [if_neg (Option.some_ne_none z), sub_zero]
      by_cases hne : (S (some z)).Nonempty
      · obtain ⟨i, hi⟩ := hne
        have hiLabel : matchLabel σ i = some z := (mem_filter.mp hi).2
        obtain ⟨hiMove, hiPair⟩ := matchLabel_eq_some.mp hiLabel
        subst z
        have hpair : S (some s(i, σ i)) = {i, σ i} := by
          ext l
          change l ∈ univ.filter (fun j => matchLabel σ j = some s(i, σ i)) ↔
            l ∈ ({i, σ i} : Finset ι)
          simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
          constructor
          · exact eq_or_eq_of_matchLabel
          · intro hl
            rcases hl with rfl | rfl
            · exact matchLabel_eq_some.mpr ⟨hiMove, rfl⟩
            · exact matchLabel_partner hσ.invol hiMove
        have hij : i ≠ σ i := fun h => hiMove h.symm
        have hb := Opeth.AMMatching.close_pair_block_bound hG hcPair hδ hclose hij
          (hσ.close i hiMove).le
        rw [hpair]
        have hcard : ({i, σ i} : Finset ι).card = 2 := by simp [hij]
        rw [hcard]
        have hkδ : δ ≤ k * δ := le_mul_of_one_le_left hδ hk1
        norm_num only [Nat.cast_ofNat]
        linarith only [hb, hδ, hkδ]
      · have hempty : S (some z) = ∅ := not_nonempty_iff_eq_empty.mp hne
        rw [hempty, card_empty, Nat.cast_zero, mul_zero]
        exact blockDefect_nonneg hG ∅
  have hcardsNat : (∑ z : Option (Sym2 ι), (S z).card) = Fintype.card ι := by
    simpa only [S, mem_univ, filter_true, card_univ] using
      (sum_card_fiberwise_eq_card_filter (univ : Finset ι)
        (univ : Finset (Option (Sym2 ι))) (matchLabel σ))
  have hcards : (∑ z : Option (Sym2 ι), ((S z).card : ℝ)) =
      (Fintype.card ι : ℝ) := by exact_mod_cast hcardsNat
  have hcharge : (∑ z : Option (Sym2 ι),
      if z = none then W.B * R + k * c + C else 0) = W.B * R + k * c + C := by simp
  calc
    (c - 4 * k * δ) * (Fintype.card ι : ℝ) - W.B * R - k * c - C =
        ∑ z : Option (Sym2 ι), ((c - 4 * k * δ) * ((S z).card : ℝ) -
          (if z = none then W.B * R + k * c + C else 0)) := by
      rw [sum_sub_distrib, ← mul_sum, hcards, hcharge]
      ring
    _ ≤ ∑ z, blockDefect hG (S z) := sum_le_sum (fun z _ => hblock z)
    _ ≤ defect hG := hpinch

/-- `C <= c` fits the existing counting interface after increasing its harmless
boundary parameter from `n` to `n+1`. -/
theorem matching_defect_bound_effective {n : ℕ} (hn : 2 ≤ n)
    {x : ι → ℝ} (hx : Function.Injective x)
    {G : Matrix ι ι ℂ} (hG : G.IsHermitian) {c C : ℝ}
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hCc : C ≤ c) (hcPair : c ≤ 1 / 64)
    (W : WCert n) (hW : W.Adm)
    (hCert : SeparatedSummedCertificate W c C (17 / 20))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i j, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ)
    (hcap : ∀ S : Finset ι,
      (∀ i j : S, i ≠ j → 17 / 20 ≤ |x i - x j|) →
      ∀ k : S, (hG.submatrix (Subtype.val : S → ι)).eigenvalues k ≤ 2)
    {R : ℝ} (hR : 0 ≤ R) (hspan : ∀ i j, x i - x j ≤ R) :
    (c - 4 * (((n + 1) - 1 : ℕ) : ℝ) * δ) * (Fintype.card ι : ℝ) - W.B * R
      - (((n + 1) - 1 : ℕ) : ℝ) * c ≤ defect hG := by
  have h := matching_defect_bound_summed hn hx hG hc hC hcPair W hW hCert
    hδ hclose hcap hR hspan
  have hncast : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ n)).symm
  have hdm : 0 ≤ δ * (Fintype.card ι : ℝ) := mul_nonneg hδ (Nat.cast_nonneg _)
  simp only [Nat.add_sub_cancel] at ⊢
  rw [hncast]
  nlinarith only [h, hCc, hdm]

end Matching

open Zeta23

theorem actual_defect_estimate_effective (Z : ZeroConfig) {n : ℕ} (hn : 2 ≤ n)
    (W : WCert n) (hW : W.Adm) {c C B : ℝ}
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hCc : C ≤ c) (hc64 : c ≤ 1 / 64)
    (hB : W.B = B) (hCert : SeparatedSummedCertificate W c C (17 / 20)) :
    OpethN.Counting.ActualDefectEstimate Z (n + 1) c B := by
  classical
  intro δ hδ
  filter_upwards [Opeth.AMUniformKernel.kernel_limit_uniform Z δ hδ,
    Opeth.AMSeparatedSpectrum.eventually_principal_eigenvalues_le_two Z,
    eventually_L_pos] with T hclose hcap hL
  have hx := xret_injective Z (mtParams T) T hL
  have hspan : ∀ i j : retained Z (mtParams T) T,
      xret Z (mtParams T) T i - xret Z (mtParams T) T j ≤
        spanOf (xret Z (mtParams T) T) Finset.univ := by
    intro i j
    exact (le_abs_self _).trans
      (abs_sub_le_spanOf (xret Z (mtParams T) T) (mem_univ i) (mem_univ j))
  have h := matching_defect_bound_effective hn hx
    (gram_isHermitian Z (mtParams T) T) hc hC hCc hc64 W hW hCert
    hδ.le (fun i j _ => hclose i j) hcap
    (spanOf_nonneg (xret Z (mtParams T) T) Finset.univ) hspan
  simpa only [Fintype.card_coe, hB, Dcirc] using h

/-- Conditional counting conclusion from the separated summed certificate.
All analytic counting steps are the existing proved generic steps. -/
theorem simple_dyadic {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
    {c C B hw : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hCc : C ≤ c)
    (hc64 : c ≤ 1 / 64) (hB : W.B = B) (hfloor : hw ≤ AMW.HW)
    (hCert : SeparatedSummedCertificate W c C (17 / 20)) :
    ∀ ε > (0 : ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((hw - B) / (1 - c) - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤
        Zeta23.N0simple T (2 * T) := by
  have hB0 : 0 ≤ B := hB ▸ WCert.B_nonneg hW
  have hdef := actual_defect_estimate_effective zetaZeroConfig hn W hW
    hc.le hC hCc hc64 hB hCert
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
    (GramDefect20261015.Counting.defect_to_dyadic zetaZeroConfig paperInputs_zeta
      (by omega : 2 ≤ n + 1) hc (by linarith) hB0 hfloor hdef ε hε)
  refine ⟨T₀, fun T hT => ?_⟩
  simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using hT₀ T hT

theorem simple_cumulative {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
    {c C B hw : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hCc : C ≤ c)
    (hc64 : c ≤ 1 / 64) (hB : W.B = B) (hfloor : hw ≤ AMW.HW)
    (hCert : SeparatedSummedCertificate W c C (17 / 20)) :
    ∀ ε > (0 : ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((hw - B) / (1 - c) - ε) * (Zeta23.Ncount 0 T : ℝ) ≤
        Zeta23.N0simple 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0simple_add' Zeta23.zetaSeam)
    (simple_dyadic hn W hW hc hC hCc hc64 hB hfloor hCert)

theorem distinct_cumulative {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
    {c C B hw : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hCc : C ≤ c)
    (hc64 : c ≤ 1 / 64) (hB : W.B = B) (hfloor : hw ≤ AMW.HW)
    (hCert : SeparatedSummedCertificate W c C (17 / 20)) :
    ∀ ε > (0 : ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((hw - B) / (1 - c) - ε) * (Zeta23.Ncount 0 T : ℝ) ≤
        Zeta23.N0star 0 T := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := simple_cumulative hn W hW hc hC hCc hc64 hB hfloor hCert ε hε
  refine ⟨T₀, fun T hT => (hT₀ T hT).trans ?_⟩
  exact_mod_cast AMW.N0simple_le_N0star' 0 T

end StructuralResearch20261016.CoboundaryCounting
