/- SPDX-License-Identifier: Apache-2.0
Actual new-window maximal-matching defect payment at arbitrary separation.
Adapted from the attributed Opeth/CoboundaryCounting proofs. The short-pair
scalar input is explicit and refers to the actual new kernel, and the
separated energy input uses shared WindowGapEnergy.Fw. No record is asserted.
-/
import StructuralGoal20261016.WindowDiscreteEnergy
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23Ext.StableRankTrace Zeta23Ext.Bridge Zeta23Ext.BridgeW
open Meshuggah.Gram
namespace StructuralGoal20261016.WindowMatching
open WindowDiscreteEnergy
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem close_pair_block_bound {x : ι → ℝ} {G : Matrix ι ι ℂ}
    (hG : G.IsHermitian) {c δ sep : ℝ} (hc : c ≤ 1 / 64) (hPair : ∀ t : ℝ, |t| ≤ sep → c ≤ WindowDiscreteEnergy.wfun t) (hδ : 0 ≤ δ)
    (hclose : ∀ i j, i ≠ j →
      ‖G i j - (WindowDiscreteEnergy.kfun (x i - x j) : ℂ)‖ ≤ δ)
    {i j : ι} (hij : i ≠ j) (hnear : |x i - x j| ≤ sep) :
    2 * c - 4 * δ ≤ blockDefect hG {i, j} := by
  classical
  have hkij : c ≤ WindowDiscreteEnergy.wfun (x i - x j) := hPair _ hnear
  have hkji : c ≤ WindowDiscreteEnergy.wfun (x j - x i) := hPair _ (by simpa only [abs_sub_comm] using hnear)
  have heij := WindowDiscreteEnergy.wfun_sub_le_norm_sq (hclose i j hij)
  have heji := WindowDiscreteEnergy.wfun_sub_le_norm_sq (hclose j i hij.symm)
  have hoff : offDiagSqOn G {i, j} = ‖G i j‖ ^ 2 + ‖G j i‖ ^ 2 := by
    simp [offDiagSqOn, hij, hij.symm]
  have hmin : 2 * c - 4 * δ ≤ min 1 (offDiagSqOn G {i, j}) := by
    apply le_min
    · linarith
    · rw [hoff]
      linarith
  have hd := block_defect_of_isHermitian
    (hG.submatrix (Subtype.val : ({i, j} : Finset ι) → ι))
  rw [offDiagSqOn_submatrix] at hd
  exact hmin.trans hd
theorem matching_defect_bound_summed {n : ℕ} (hn : 2 ≤ n)
    {x : ι → ℝ} (hx : Function.Injective x)
    {G : Matrix ι ι ℂ} (hG : G.IsHermitian) {c C sep : ℝ}
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hcPair : c ≤ 1 / 64)
    (hPair : ∀ t : ℝ, |t| ≤ sep → c ≤ WindowDiscreteEnergy.wfun t)
    (W : WCert n) (hW : W.Adm)
    (hCert : SeparatedSummedCertificate W c C (sep))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i j, i ≠ j →
      ‖G i j - (WindowDiscreteEnergy.kfun (x i - x j) : ℂ)‖ ≤ δ)
    (hcap : ∀ S : Finset ι,
      (∀ i j : S, i ≠ j → sep ≤ |x i - x j|) →
      ∀ k : S, (hG.submatrix (Subtype.val : S → ι)).eigenvalues k ≤ 2)
    {R : ℝ} (hR : 0 ≤ R) (hspan : ∀ i j, x i - x j ≤ R) :
    (c - 4 * ((n - 1 : ℕ) : ℝ) * δ) * (Fintype.card ι : ℝ) - W.B * R
      - ((n - 1 : ℕ) : ℝ) * c - C ≤ defect hG := by
  classical
  set k : ℝ := ((n - 1 : ℕ) : ℝ) with hkdef
  have hk1 : (1 : ℝ) ≤ k := by
    rw [hkdef]; exact_mod_cast (by omega : 1 ≤ n - 1)
  obtain ⟨σ, hσ, hσsep⟩ := exists_maximal_matching x (sep)
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
      have hsep : ∀ i j : S none, i ≠ j → sep ≤ |x i - x j| := by
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
        have hb := close_pair_block_bound hG hcPair hPair hδ hclose hij
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
    {G : Matrix ι ι ℂ} (hG : G.IsHermitian) {c C sep : ℝ}
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hCc : C ≤ c) (hcPair : c ≤ 1 / 64)
    (hPair : ∀ t : ℝ, |t| ≤ sep → c ≤ WindowDiscreteEnergy.wfun t)
    (W : WCert n) (hW : W.Adm)
    (hCert : SeparatedSummedCertificate W c C (sep))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i j, i ≠ j → ‖G i j - (WindowDiscreteEnergy.kfun (x i - x j) : ℂ)‖ ≤ δ)
    (hcap : ∀ S : Finset ι,
      (∀ i j : S, i ≠ j → sep ≤ |x i - x j|) →
      ∀ k : S, (hG.submatrix (Subtype.val : S → ι)).eigenvalues k ≤ 2)
    {R : ℝ} (hR : 0 ≤ R) (hspan : ∀ i j, x i - x j ≤ R) :
    (c - 4 * (((n + 1) - 1 : ℕ) : ℝ) * δ) * (Fintype.card ι : ℝ) - W.B * R
      - (((n + 1) - 1 : ℕ) : ℝ) * c ≤ defect hG := by
  have h := matching_defect_bound_summed hn hx hG hc hC hcPair hPair W hW hCert
    hδ hclose hcap hR hspan
  have hncast : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel (by omega : 1 ≤ n)).symm
  have hdm : 0 ≤ δ * (Fintype.card ι : ℝ) := mul_nonneg hδ (Nat.cast_nonneg _)
  simp only [Nat.add_sub_cancel] at ⊢
  rw [hncast]
  nlinarith only [h, hCc, hdm]

#print axioms close_pair_block_bound
#print axioms matching_defect_bound_effective
end StructuralGoal20261016.WindowMatching
end
