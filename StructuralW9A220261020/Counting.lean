/-
SPDX-License-Identifier: Apache-2.0

W9A2 finite-state summed-floor transfer. Preparation only: this source has not
been compiled. The final theorem is instantiated by the actual quantitative
walk/localization and exact graph in the companion Final module.

The band/matching proof bodies below are adapted from the accepted v3
StructuralS1RTiny20261018.Production.Counting development, itself adapted from
the attributed StructuralResearch20261016.Coboundary / CoboundaryCounting:
R. Arun Chandru's combination of Samuel Lavery's AM defect bridge and Kristian
Muri Knausgard's matching development. Their original notices and the current
W9A2 Core notices remain applicable. No old kernel data are imported.
-/
import StructuralW9A220261020.Core

set_option Elab.async false
set_option maxHeartbeats 0

noncomputable section
open Matrix Finset RHLinalg Filter Topology
open scoped ComplexOrder BigOperators
open Zeta23Ext.StableRankTrace Zeta23Ext.Bridge Zeta23Ext.BridgeW

namespace StructuralW9A220261020.Counting

/-- A pointwise coboundary payment telescopes over every finite prefix.
The potential has the same physical energy units as E and c. -/
theorem sum_range_coboundary_lower (E P : ℕ → ℝ) (c : ℝ) (N : ℕ)
    (hstep : ∀ i, i < N → c + P (i + 1) - P i ≤ E i) :
    c * (N : ℝ) + P N - P 0 ≤ ∑ i ∈ range N, E i := by
  revert hstep
  induction N with
  | zero => intro hstep; simp
  | succ n ih =>
    intro hstep
    have hs := ih (fun i hi => hstep i (by omega))
    have hp := hstep n (by omega)
    rw [sum_range_succ]
    have hn : (n.succ : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hn]
    linarith only [hs, hp]

theorem sum_range_coboundary_bounded (E P : ℕ → ℝ) (c C : ℝ) (N : ℕ)
    (hstep : ∀ i, i < N → c + P (i + 1) - P i ≤ E i)
    (hstart : P 0 ≤ C) (hfinish : 0 ≤ P N) :
    c * (N : ℝ) - C ≤ ∑ i ∈ range N, E i := by
  have h := sum_range_coboundary_lower E P c N hstep
  linarith only [h, hstart, hfinish]

def leftGaps (g : Fin 9 → ℝ) : Fin 8 → ℝ :=
  fun r => g ⟨r.val, by omega⟩

def rightGaps (g : Fin 9 → ℝ) : Fin 8 → ℝ :=
  fun r => g ⟨r.val + 1, by omega⟩

theorem left_window (Y : ℕ → ℝ) (i : ℕ) :
    leftGaps (windowGaps 10 Y i) = windowGaps 9 Y i := rfl

theorem right_window (Y : ℕ → ℝ) (i : ℕ) :
    rightGaps (windowGaps 10 Y i) = windowGaps 9 Y (i + 1) := by
  funext r
  simp only [rightGaps, windowGaps]
  congr 1 <;> congr 1 <;> omega

def SeparatedSummedCertificate {n : ℕ} (W : WCert n) (c C sep : ℝ) : Prop :=
  ∀ {m : ℕ}, n ≤ m → ∀ y : Fin m → ℝ, StrictMono y →
    (∀ i j, i ≠ j → sep ≤ |y i - y j|) →
    c * ((m : ℝ) - ((n - 1 : ℕ) : ℝ)) - C ≤
      ∑ i ∈ range (m - (n - 1)), Fw W (windowGaps n (sortedExt y) i)

/-- The actual localization and actual transition premises concern every
separated configuration. No sampled leaf, minimizer, or state word is assumed.
An artificial terminal good state pays the last window's outgoing edge. -/
theorem summed_of_state {α : Type*} (W : WCert 9)
    (base increment C sep : ℝ) (cost potential : α → ℝ)
    (At : (Fin 8 → ℝ) → α → Prop) (Edge : α → α → Prop) (good : α)
    (hloc : ∀ g : Fin 8 → ℝ, (∀ r, sep ≤ g r) →
      ∃ s, At g s ∧ base + cost s ≤ Fw W g)
    (hnext : ∀ g : Fin 9 → ℝ, (∀ r, sep ≤ g r) → ∀ s t,
      At (leftGaps g) s → At (rightGaps g) t → Edge s t)
    (hgood : ∀ s, Edge s good)
    (hpayment : ∀ s t, Edge s t →
      increment + potential t - potential s ≤ cost s)
    (hpotential0 : ∀ s, 0 ≤ potential s)
    (hpotentialC : ∀ s, potential s ≤ C) :
    SeparatedSummedCertificate W (base + increment) C sep := by
  classical
  intro m hm y hy hsep
  let N := m - 8
  let Y := sortedExt y
  have hgap (a b : ℕ) (hab : a < b) (hb : b < m) :
      sep ≤ Y b - Y a := by
    have ha : a < m := lt_trans hab hb
    have hne : (⟨b, hb⟩ : Fin m) ≠ ⟨a, ha⟩ := by
      intro h
      have := congrArg Fin.val h
      dsimp at this
      omega
    have hs := hsep ⟨b, hb⟩ ⟨a, ha⟩ hne
    rw [abs_of_nonneg (sub_nonneg.mpr (hy.monotone (by exact_mod_cast hab.le)))] at hs
    simpa only [Y, sortedExt_of_lt y hb, sortedExt_of_lt y ha] using hs
  have hg8 (i : ℕ) (hi : i < N) : ∀ r, sep ≤ windowGaps 9 Y i r := by
    intro r
    have hr := r.isLt
    have hlast : i + ((r : ℕ) + 1) < m := by dsimp [N] at hi; omega
    exact hgap _ _ (by omega) hlast
  let S : ℕ → α := fun i =>
    if hi : i < N then Classical.choose (hloc (windowGaps 9 Y i) (hg8 i hi)) else good
  have hS (i : ℕ) (hi : i < N) :
      At (windowGaps 9 Y i) (S i) ∧
      base + cost (S i) ≤ Fw W (windowGaps 9 Y i) := by
    simpa only [S, dif_pos hi] using
      Classical.choose_spec (hloc (windowGaps 9 Y i) (hg8 i hi))
  have hedge (i : ℕ) (hi : i < N) : Edge (S i) (S (i + 1)) := by
    by_cases hi1 : i + 1 < N
    · have hg : ∀ r, sep ≤ windowGaps 10 Y i r := by
        intro r
        have hr := r.isLt
        have hlast : i + ((r : ℕ) + 1) < m := by dsimp [N] at hi1; omega
        exact hgap _ _ (by omega) hlast
      apply hnext (windowGaps 10 Y i) hg (S i) (S (i + 1))
      · simpa only [left_window] using (hS i hi).1
      · simpa only [right_window] using (hS (i + 1) hi1).1
    · have hterminal : S (i + 1) = good := by simp only [S, dif_neg hi1]
      rw [hterminal]
      exact hgood (S i)
  have hstep (i : ℕ) (hi : i < N) :
      base + increment + potential (S (i + 1)) - potential (S i) ≤
        Fw W (windowGaps 9 Y i) := by
    have hp := hpayment (S i) (S (i + 1)) (hedge i hi)
    have hf := (hS i hi).2
    linarith only [hp, hf]
  have hs := sum_range_coboundary_bounded
    (fun i => Fw W (windowGaps 9 Y i)) (fun i => potential (S i))
    (base + increment) C N hstep (hpotentialC (S 0)) (hpotential0 (S N))
  have hcast : (N : ℝ) = (m : ℝ) - 8 := by
    dsimp [N]
    rw [Nat.cast_sub (by omega : 8 ≤ m)]
    norm_num
  rw [hcast] at hs
  simpa only [N, Y, Nat.reduceSub, Nat.cast_ofNat] using hs

section Payment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem block_energy_band_of_sum {c C : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (W : WCert n) (hW : W.Adm)
    {m : ℕ} (hm : n ≤ m) (x : ι → ℝ) (hx : Function.Injective x)
    (hS : (univ.image x).card = m)
    (hSum : c * ((m : ℝ) - ((n - 1 : ℕ) : ℝ)) - C ≤
      ∑ i ∈ range (m - (n - 1)), Fw W
        (windowGaps n (sortedExt ((univ.image x).orderEmbOfFin hS)) i)) :
    c * ((m : ℝ) - ((n - 1 : ℕ) : ℝ)) - C ≤
      (∑ r : Fin m × Fin m,
        if r.1 ≠ r.2 ∧ (r.1 : ℕ) ≤ (r.2 : ℕ) + (n - 1) ∧
          (r.2 : ℕ) ≤ (r.1 : ℕ) + (n - 1) then
          wfun ((univ.image x).orderEmbOfFin hS r.1 -
            (univ.image x).orderEmbOfFin hS r.2) else 0)
        + blkPress W.b x univ := by
  classical
  let y : Fin m → ℝ := ⇑((univ.image x).orderEmbOfFin hS)
  have hsum := hSum
  simp_rw [Fw_windowGaps] at hsum
  rw [sum_add_distrib] at hsum
  have hlin :
      (∑ i ∈ range (m - (n - 1)), ∑ r : Fin (n - 1),
        W.b r * (sortedExt y (i + ((r : ℕ) + 1)) - sortedExt y (i + r))) =
        blkPress W.b x univ := by
    rw [sum_comm]
    unfold blkPress
    rw [hS]
    refine sum_congr rfl fun r _ => ?_
    rw [← mul_sum, sum_gap_shift, sortedOn_eq hS, sortedOn_eq hS]
  have hquad := window_pairs_le_band hn hm W hW x hx hS
  change (∑ i ∈ range (m - (n - 1)), ∑ a : Fin n, ∑ b : Fin n,
      if (a : ℕ) < (b : ℕ) then
        W.a a b * wfun (sortedExt y (i + b) - sortedExt y (i + a)) else 0) ≤ _ at hquad
  linarith

theorem sorted_separated {x : ι → ℝ} {m : ℕ} (hS : (univ.image x).card = m)
    {sep : ℝ} (hsep : ∀ i j, i ≠ j → sep ≤ |x i - x j|) :
    ∀ i j : Fin m, i ≠ j → sep ≤
      |(univ.image x).orderEmbOfFin hS i - (univ.image x).orderEmbOfFin hS j| := by
  intro i j hij
  obtain ⟨a, _, ha⟩ := mem_image.mp (orderEmbOfFin_mem _ hS i)
  obtain ⟨b, _, hb⟩ := mem_image.mp (orderEmbOfFin_mem _ hS j)
  have hab : a ≠ b := by
    intro h
    apply hij
    apply ((univ.image x).orderEmbOfFin hS).injective
    rw [← ha, ← hb, h]
  rw [← ha, ← hb]
  exact hsep a b hab

theorem block_energy_band_separated {c C sep : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (W : WCert n) (hW : W.Adm) (hCert : SeparatedSummedCertificate W c C sep)
    {m : ℕ} (hm : n ≤ m) (x : ι → ℝ) (hx : Function.Injective x)
    (hS : (univ.image x).card = m)
    (hsep : ∀ i j, i ≠ j → sep ≤ |x i - x j|) :
    c * ((m : ℝ) - ((n - 1 : ℕ) : ℝ)) - C ≤
      (∑ r : Fin m × Fin m,
        if r.1 ≠ r.2 ∧ (r.1 : ℕ) ≤ (r.2 : ℕ) + (n - 1) ∧
          (r.2 : ℕ) ≤ (r.1 : ℕ) + (n - 1) then
          wfun ((univ.image x).orderEmbOfFin hS r.1 -
            (univ.image x).orderEmbOfFin hS r.2) else 0)
        + blkPress W.b x univ :=
  block_energy_band_of_sum hn W hW hm x hx hS
    (hCert hm _ ((univ.image x).orderEmbOfFin hS).strictMono (sorted_separated hS hsep))

theorem remainder_bound_separated_summed {n : ℕ} (hn : 2 ≤ n)
    {x : ι → ℝ} (hx : Function.Injective x) {G : Matrix ι ι ℂ}
    (hG : G.IsHermitian) {c C sep : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (W : WCert n) (hW : W.Adm)
    (hCert : SeparatedSummedCertificate W c C sep)
    (hsep : ∀ i j, i ≠ j → sep ≤ |x i - x j|)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i j, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ)
    (hcap : ∀ i, hG.eigenvalues i ≤ 2)
    {R : ℝ} (hR : 0 ≤ R) (hspan : ∀ i j, x i - x j ≤ R) :
    (c - 4 * ((n - 1 : ℕ) : ℝ) * δ) * (Fintype.card ι : ℝ) - W.B * R
      - ((n - 1 : ℕ) : ℝ) * c - C ≤ defect hG := by
  classical
  let m := Fintype.card ι
  have hcard : Fintype.card ι = m := rfl
  have hS : (univ.image x).card = m := by
    rw [card_image_of_injective _ hx, card_univ, hcard]
  by_cases hm : n ≤ m
  · have he := block_energy_band_separated hn W hW hCert hm x hx hS hsep
    have hb := OpethN.band_close_n n hx hS hcard G hδ hclose
    have hp := OpethN.pressure_le_n hm hS W hW.b_nonneg hspan
    have hd := Opeth.AMSparseDefect.offdiag_le_defect_of_spectrum_le_two hG hcap
    change (c - 4 * ((n - 1 : ℕ) : ℝ) * δ) * (m : ℝ) - W.B * R
      - ((n - 1 : ℕ) : ℝ) * c - C ≤ defect hG
    nlinarith only [he, hb, hp, hd]
  · have hmk : (m : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : m ≤ n - 1)
    have hcm := mul_le_mul_of_nonneg_left hmk hc
    have hbr : 0 ≤ W.B * R := mul_nonneg (WCert.B_nonneg hW) hR
    have hdm : 0 ≤ 4 * ((n - 1 : ℕ) : ℝ) * δ * (m : ℝ) := by positivity
    have hd := Opeth.AMSparseDefect.defect_nonneg hG
    change (c - 4 * ((n - 1 : ℕ) : ℝ) * δ) * (m : ℝ) - W.B * R
      - ((n - 1 : ℕ) : ℝ) * c - C ≤ defect hG
    nlinarith only [hcm, hbr, hdm, hd, hC]

end Payment

section Matching
open Meshuggah.Gram
variable {ι : Type} [Fintype ι] [DecidableEq ι]

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

/-- W9A2's current H, pinned to the official source of 2026-10-19. -/
def ratio (c B : ℝ) : ℝ :=
  (6721237468782417141365717707344332375586 /
    10000000000000000000000000000000000000000 - B) / (1 - c)

theorem actual_dyadic_of_summed (W : WCert 9) (hW : W.Adm)
    {c C B : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hCc : C ≤ c)
    (hc64 : c ≤ 1 / 64) (hB : W.B = B)
    (hCert : SeparatedSummedCertificate W c C (17 / 20)) :
    ∀ epsilon > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0,
      (ratio c B - epsilon) * (Zeta23.Ncount T (2*T) : ℝ) ≤ Zeta23.N0star T (2*T) := by
  have hB0 : 0 ≤ B := hB ▸ WCert.B_nonneg hW
  have hdef := actual_defect_estimate_effective zetaZeroConfig
    (by norm_num : 2 ≤ 9) W hW hc.le hC hCc hc64 hB hCert
  intro epsilon hepsilon
  obtain ⟨T0, hT0⟩ := eventually_atTop.mp
    (OpethN.Counting.defect_to_dyadic zetaZeroConfig paperInputs_zeta
      (by norm_num : 2 ≤ 10) hc (by linarith) hB0 hdef epsilon hepsilon)
  refine ⟨T0, fun T hT => ?_⟩
  have hs : (ratio c B - epsilon) * (Zeta23.Ncount T (2*T) : ℝ) ≤
      (Zeta23.N0simple T (2*T) : ℝ) := by
    simpa only [ratio, zetaZeroConfig_N, zetaZeroConfig_N0s] using hT0 T hT
  exact hs.trans (by exact_mod_cast AMW.N0simple_le_N0star' T (2*T))

theorem actual_cumulative_of_summed (W : WCert 9) (hW : W.Adm)
    {c C B : ℝ} (hc : 0 < c) (hC : 0 ≤ C) (hCc : C ≤ c)
    (hc64 : c ≤ 1 / 64) (hB : W.B = B)
    (hCert : SeparatedSummedCertificate W c C (17 / 20)) :
    ∀ epsilon > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0,
      (ratio c B - epsilon) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0star_add' Zeta23.zetaSeam)
    (actual_dyadic_of_summed W hW hc hC hCc hc64 hB hCert)

end StructuralW9A220261020.Counting

set_option pp.fullNames true
#print axioms StructuralW9A220261020.Counting.sum_range_coboundary_lower
#print axioms StructuralW9A220261020.Counting.summed_of_state
#print axioms StructuralW9A220261020.Counting.actual_defect_estimate_effective
#print axioms StructuralW9A220261020.Counting.actual_dyadic_of_summed
#print axioms StructuralW9A220261020.Counting.actual_cumulative_of_summed
end
