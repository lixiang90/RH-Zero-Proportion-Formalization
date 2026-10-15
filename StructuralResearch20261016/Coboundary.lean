/-
SPDX-License-Identifier: Apache-2.0

Independent structural extension of the attributed window-energy payment
interface. No new numerical certificate or zeta proportion is asserted.
-/
import GramDefect20261015.Core

noncomputable section

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23Ext.StableRankTrace Zeta23Ext.Bridge Zeta23Ext.BridgeW

namespace StructuralResearch20261016.Coboundary

/-- Local coboundaries cancel at every interior state. -/
theorem sum_lower_of_local (f v : ℕ → ℝ) (c : ℝ) (N : ℕ)
    (hlocal : ∀ i ∈ range N, c + v (i + 1) - v i ≤ f i) :
    c * (N : ℝ) + v N - v 0 ≤ ∑ i ∈ range N, f i := by
  have h := sum_le_sum hlocal
  have htel := sum_range_sub v N
  have heq : (∑ i ∈ range N, (c + v (i + 1) - v i)) =
      c * (N : ℝ) + (v N - v 0) := by
    simp_rw [show ∀ i, c + v (i + 1) - v i = c + (v (i + 1) - v i) by
      intro i; ring]
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, htel]
    ring
  rw [heq] at h
  linarith

/-- Only the endpoint oscillation of the potential is paid. -/
theorem sum_lower_of_bounded_local (f v : ℕ → ℝ) (c : ℝ) (N : ℕ)
    {lower upper : ℝ} (hstart : v 0 ≤ upper) (hfinish : lower ≤ v N)
    (hlocal : ∀ i ∈ range N, c + v (i + 1) - v i ≤ f i) :
    c * (N : ℝ) - (upper - lower) ≤ ∑ i ∈ range N, f i := by
  linarith [sum_lower_of_local f v c N hlocal]

/-- A periodic string pays no boundary charge at all. -/
theorem sum_lower_of_periodic_local (f v : ℕ → ℝ) (c : ℝ) (N : ℕ)
    (hperiod : v N = v 0)
    (hlocal : ∀ i ∈ range N, c + v (i + 1) - v i ≤ f i) :
    c * (N : ℝ) ≤ ∑ i ∈ range N, f i := by
  have h := sum_lower_of_local f v c N hlocal
  rw [hperiod] at h
  linarith

/-- A constant boundary charge is absorbed by any available linear budget. -/
theorem absorb_boundary {c a eps N D C E : ℝ}
    (h : (c - a) * N - D - C ≤ E) (hbudget : C ≤ eps * N) :
    (c - a - eps) * N - D ≤ E := by
  nlinarith

theorem boundary_budget_of_threshold {C eps N : ℝ}
    (heps : 0 < eps) (hN : C / eps ≤ N) : C ≤ eps * N := by
  have h := (div_le_iff₀ heps).mp hN
  nlinarith

theorem absorb_boundary_of_threshold {c a eps N D C E : ℝ}
    (h : (c - a) * N - D - C ≤ E) (heps : 0 < eps)
    (hN : C / eps ≤ N) : (c - a - eps) * N - D ≤ E :=
  absorb_boundary h (boundary_budget_of_threshold heps hN)

def headState {n : ℕ} (hn : 2 ≤ n) (g : Fin (n - 1) → ℝ) :
    Fin (n - 2) → ℝ := fun r => g ⟨r, by have := r.isLt; omega⟩

def tailState {n : ℕ} (hn : 2 ≤ n) (g : Fin (n - 1) → ℝ) :
    Fin (n - 2) → ℝ := fun r => g ⟨r + 1, by have := r.isLt; omega⟩

def shortGaps (n : ℕ) (Y : ℕ → ℝ) (i : ℕ) : Fin (n - 2) → ℝ :=
  fun r => Y (i + ((r : ℕ) + 1)) - Y (i + r)

theorem head_window {n : ℕ} (hn : 2 ≤ n) (Y : ℕ → ℝ) (i : ℕ) :
    headState hn (windowGaps n Y i) = shortGaps n Y i := rfl

theorem tail_window {n : ℕ} (hn : 2 ≤ n) (Y : ℕ → ℝ) (i : ℕ) :
    tailState hn (windowGaps n Y i) = shortGaps n Y (i + 1) := by
  ext r
  simp only [tailState, windowGaps, shortGaps]
  congr 1 <;> congr 1 <;> omega

/-- Replacement for a pointwise local floor: a finite string of overlapping
windows may have a stronger average floor with one fixed boundary charge. -/
def SummedCertificate {n : ℕ} (W : WCert n) (c C : ℝ) : Prop :=
  ∀ {m : ℕ}, n ≤ m → ∀ y : Fin m → ℝ, StrictMono y →
    c * ((m : ℝ) - ((n - 1 : ℕ) : ℝ)) - C ≤
      ∑ i ∈ range (m - (n - 1)), Fw W (windowGaps n (sortedExt y) i)

/-- The separated version does not assert a certificate for small gaps. -/
def SeparatedSummedCertificate {n : ℕ} (W : WCert n) (c C sep : ℝ) : Prop :=
  ∀ {m : ℕ}, n ≤ m → ∀ y : Fin m → ℝ, StrictMono y →
    (∀ i j, i ≠ j → sep ≤ |y i - y j|) →
    c * ((m : ℝ) - ((n - 1 : ℕ) : ℝ)) - C ≤
      ∑ i ∈ range (m - (n - 1)), Fw W (windowGaps n (sortedExt y) i)

/-- A bounded `(n-2)`-gap state potential turns a local affine certificate into
the summed interface. For nine points the state has exactly seven gaps. -/
theorem summed_of_coboundary {n : ℕ} (hn : 2 ≤ n) (W : WCert n)
    (V : (Fin (n - 2) → ℝ) → ℝ) (c lower upper : ℝ)
    (hV : ∀ g, (∀ r, 0 ≤ g r) → lower ≤ V g ∧ V g ≤ upper)
    (hlocal : ∀ g : Fin (n - 1) → ℝ, (∀ r, 0 ≤ g r) →
      c + V (tailState hn g) - V (headState hn g) ≤ Fw W g) :
    SummedCertificate W c (upper - lower) := by
  intro m hm y hy
  let N := m - (n - 1)
  let Y := sortedExt y
  have hstate (i : ℕ) (hi : i ≤ N) : ∀ r, 0 ≤ shortGaps n Y i r := by
    intro r
    have hr := r.isLt
    have hlast : i + ((r : ℕ) + 1) < m := by dsimp [N] at hi; omega
    exact sub_nonneg.mpr (sortedExt_mono hy (by omega) hlast)
  have hfirst := (hV (shortGaps n Y 0) (hstate 0 (Nat.zero_le N))).2
  have hlast := (hV (shortGaps n Y N) (hstate N le_rfl)).1
  have hwin (i : ℕ) (hi : i ∈ range N) :
      c + V (shortGaps n Y (i + 1)) - V (shortGaps n Y i) ≤
        Fw W (windowGaps n Y i) := by
    have hi' : i < N := mem_range.mp hi
    have hg : ∀ r, 0 ≤ windowGaps n Y i r := by
      intro r
      have hr := r.isLt
      have hlast : i + ((r : ℕ) + 1) < m := by dsimp [N] at hi'; omega
      exact sub_nonneg.mpr (sortedExt_mono hy (by omega) hlast)
    simpa only [head_window, tail_window] using hlocal (windowGaps n Y i) hg
  have hsum := sum_lower_of_bounded_local (fun i => Fw W (windowGaps n Y i))
    (fun i => V (shortGaps n Y i)) c N hfirst hlast hwin
  have hcast : (N : ℝ) = (m : ℝ) - ((n - 1 : ℕ) : ℝ) := by
    dsimp [N]
    rw [Nat.cast_sub (by omega : n - 1 ≤ m)]
  simpa only [hcast] using hsum

/-- The old pointwise certificate is the zero-potential special case. -/
theorem summed_of_pointwise {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (c : ℝ)
    (hlocal : ∀ g : Fin (n - 1) → ℝ, (∀ r, 0 ≤ g r) → c ≤ Fw W g) :
    SummedCertificate W c 0 := by
  have hs : SummedCertificate W c (0 - 0) :=
    summed_of_coboundary hn W (fun _ => 0) c 0 0
      (fun _ _ => ⟨le_rfl, le_rfl⟩)
      (fun g hg => by simpa only [add_zero, sub_zero] using hlocal g hg)
  intro m hm y hy
  simpa only [sub_self] using hs hm y hy

/-- A local potential certificate on `g_r >= sep` applies precisely to
separated strings; it is not extended to all nonnegative gaps. -/
theorem summed_of_separated_coboundary {n : ℕ} (hn : 2 ≤ n) (W : WCert n)
    (V : (Fin (n - 2) → ℝ) → ℝ) (c lower upper sep : ℝ)
    (hV : ∀ g, (∀ r, sep ≤ g r) → lower ≤ V g ∧ V g ≤ upper)
    (hlocal : ∀ g : Fin (n - 1) → ℝ, (∀ r, sep ≤ g r) →
      c + V (tailState hn g) - V (headState hn g) ≤ Fw W g) :
    SeparatedSummedCertificate W c (upper - lower) sep := by
  intro m hm y hy hsep
  let N := m - (n - 1)
  let Y := sortedExt y
  have hgap (a b : ℕ) (hab : a < b) (hb : b < m) :
      sep ≤ Y b - Y a := by
    have ha : a < m := lt_trans hab hb
    have hne : (⟨b, hb⟩ : Fin m) ≠ ⟨a, ha⟩ := by
      intro h; have := congrArg Fin.val h; dsimp at this; omega
    have hs := hsep ⟨b, hb⟩ ⟨a, ha⟩ hne
    rw [abs_of_nonneg (sub_nonneg.mpr (hy.monotone (by exact_mod_cast hab.le)))] at hs
    simpa only [Y, sortedExt_of_lt y hb, sortedExt_of_lt y ha] using hs
  have hstate (i : ℕ) (hi : i ≤ N) : ∀ r, sep ≤ shortGaps n Y i r := by
    intro r
    have hr := r.isLt
    have hlast : i + ((r : ℕ) + 1) < m := by dsimp [N] at hi; omega
    exact hgap _ _ (by omega) hlast
  have hfirst := (hV (shortGaps n Y 0) (hstate 0 (Nat.zero_le N))).2
  have hlast := (hV (shortGaps n Y N) (hstate N le_rfl)).1
  have hwin (i : ℕ) (hi : i ∈ range N) :
      c + V (shortGaps n Y (i + 1)) - V (shortGaps n Y i) ≤
        Fw W (windowGaps n Y i) := by
    have hi' : i < N := mem_range.mp hi
    have hg : ∀ r, sep ≤ windowGaps n Y i r := by
      intro r
      have hr := r.isLt
      have hlast : i + ((r : ℕ) + 1) < m := by dsimp [N] at hi'; omega
      exact hgap _ _ (by omega) hlast
    simpa only [head_window, tail_window] using hlocal (windowGaps n Y i) hg
  have hsum := sum_lower_of_bounded_local (fun i => Fw W (windowGaps n Y i))
    (fun i => V (shortGaps n Y i)) c N hfirst hlast hwin
  have hcast : (N : ℝ) = (m : ℝ) - ((n - 1 : ℕ) : ℝ) := by
    dsimp [N]
    rw [Nat.cast_sub (by omega : n - 1 ≤ m)]
  simpa only [hcast] using hsum

section Payment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original band payment needs only a summed certificate. The pair
capacity and pressure calculations are reused without any modification. -/
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

theorem block_energy_band_summed {c C : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (W : WCert n) (hW : W.Adm) (hCert : SummedCertificate W c C)
    {m : ℕ} (hm : n ≤ m) (x : ι → ℝ) (hx : Function.Injective x)
    (hS : (univ.image x).card = m) :
    c * ((m : ℝ) - ((n - 1 : ℕ) : ℝ)) - C ≤
      (∑ r : Fin m × Fin m,
        if r.1 ≠ r.2 ∧ (r.1 : ℕ) ≤ (r.2 : ℕ) + (n - 1) ∧
          (r.2 : ℕ) ≤ (r.1 : ℕ) + (n - 1) then
          wfun ((univ.image x).orderEmbOfFin hS r.1 -
            (univ.image x).orderEmbOfFin hS r.2) else 0)
        + blkPress W.b x univ :=
  block_energy_band_of_sum hn W hW hm x hx hS
    (hCert hm _ ((univ.image x).orderEmbOfFin hS).strictMono)

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

/-- Existing sparse Gram payment with one extra endpoint oscillation `C`.
The approximation cost, band width and pressure coefficient are unchanged. -/
theorem remainder_bound_summed {n : ℕ} (hn : 2 ≤ n)
    {x : ι → ℝ} (hx : Function.Injective x) {G : Matrix ι ι ℂ}
    (hG : G.IsHermitian) {c C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (W : WCert n) (hW : W.Adm) (hCert : SummedCertificate W c C)
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
  · have he := block_energy_band_summed hn W hW hCert hm x hx hS
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

/-- Direct replacement interface for a bounded local state potential. -/
theorem remainder_bound_coboundary {n : ℕ} (hn : 2 ≤ n)
    {x : ι → ℝ} (hx : Function.Injective x) {G : Matrix ι ι ℂ}
    (hG : G.IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (W : WCert n) (hW : W.Adm)
    (V : (Fin (n - 2) → ℝ) → ℝ) (lower upper : ℝ)
    (hV : ∀ g, (∀ r, 0 ≤ g r) → lower ≤ V g ∧ V g ≤ upper)
    (hlocal : ∀ g : Fin (n - 1) → ℝ, (∀ r, 0 ≤ g r) →
      c + V (tailState hn g) - V (headState hn g) ≤ Fw W g)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i j, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ)
    (hcap : ∀ i, hG.eigenvalues i ≤ 2)
    {R : ℝ} (hR : 0 ≤ R) (hspan : ∀ i j, x i - x j ≤ R) :
    (c - 4 * ((n - 1 : ℕ) : ℝ) * δ) * (Fintype.card ι : ℝ) - W.B * R
      - ((n - 1 : ℕ) : ℝ) * c - (upper - lower) ≤ defect hG := by
  have hC : 0 ≤ upper - lower := by
    obtain ⟨hlo, hup⟩ := hV (fun _ => 0) (fun _ => le_rfl)
    linarith
  exact remainder_bound_summed hn hx hG hc hC W hW
    (summed_of_coboundary hn W V c lower upper hV hlocal)
    hδ hclose hcap hR hspan

/-- Payment for the actual separated remainder, with no assertion on smaller
gaps. The separation parameter stays visible in both certificate and geometry. -/
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

theorem remainder_bound_separated_coboundary {n : ℕ} (hn : 2 ≤ n)
    {x : ι → ℝ} (hx : Function.Injective x) {G : Matrix ι ι ℂ}
    (hG : G.IsHermitian) {c sep : ℝ} (hc : 0 ≤ c)
    (W : WCert n) (hW : W.Adm)
    (V : (Fin (n - 2) → ℝ) → ℝ) (lower upper : ℝ)
    (hV : ∀ g, (∀ r, sep ≤ g r) → lower ≤ V g ∧ V g ≤ upper)
    (hlocal : ∀ g : Fin (n - 1) → ℝ, (∀ r, sep ≤ g r) →
      c + V (tailState hn g) - V (headState hn g) ≤ Fw W g)
    (hsep : ∀ i j, i ≠ j → sep ≤ |x i - x j|)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i j, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ)
    (hcap : ∀ i, hG.eigenvalues i ≤ 2)
    {R : ℝ} (hR : 0 ≤ R) (hspan : ∀ i j, x i - x j ≤ R) :
    (c - 4 * ((n - 1 : ℕ) : ℝ) * δ) * (Fintype.card ι : ℝ) - W.B * R
      - ((n - 1 : ℕ) : ℝ) * c - (upper - lower) ≤ defect hG := by
  have hC : 0 ≤ upper - lower := by
    obtain ⟨hlo, hup⟩ := hV (fun _ => sep) (fun _ => le_rfl)
    linarith
  exact remainder_bound_separated_summed hn hx hG hc hC W hW
    (summed_of_separated_coboundary hn W V c lower upper sep hV hlocal)
    hsep hδ hclose hcap hR hspan

omit [Fintype ι] in
/-- The summed payment also transfers to an arbitrary principal block. -/
theorem block_remainder_bound_summed {n : ℕ} (hn : 2 ≤ n)
    {x : ι → ℝ} (hx : Function.Injective x) {G : Matrix ι ι ℂ}
    (hG : G.IsHermitian) {c C : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (W : WCert n) (hW : W.Adm) (hCert : SummedCertificate W c C)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hclose : ∀ i j, i ≠ j → ‖G i j - (kfun (x i - x j) : ℂ)‖ ≤ δ)
    (B : Finset ι)
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
  have h := remainder_bound_summed hn hxB (hG.submatrix (Subtype.val : B → ι))
    hc hC W hW hCert hδ hcloseB hcap hR (fun i j => hspan i j)
  simpa only [Fintype.card_coe, blockDefect] using h

end Payment

end StructuralResearch20261016.Coboundary
