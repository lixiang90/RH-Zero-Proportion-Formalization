import GramDefect20261015.Core

/-
Copyright (c) 2026 Li Xiang (lixiang90). Apache-2.0.
Reused 2026-10-15 with the accepted ajp88 nine-point certificate.
The generic counting argument is unchanged from the 2026-10-14 module,
based on R. Arun Chandru's master-of-puppets4 counting bridge.
This version makes the proved window floor explicit and retains the
stronger simple-zero conclusion before passing to distinct zeros.
All upstream attribution and license notices are preserved in Core.lean.
-/
noncomputable section
open Filter Topology Zeta23
open Zeta23Ext.Bridge Zeta23Ext.BridgeW
open scoped BigOperators

namespace GramDefect20261015.Counting
open Classical
theorem defect_to_dyadic (Z : ZeroConfig) (H : PaperInputs Z) {n : ℕ} (hn : 2 ≤ n)
    {c B hw : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hB : 0 ≤ B) (hfloor : hw ≤ AMW.HW)
    (hdef : OpethN.Counting.ActualDefectEstimate Z n c B) :
    ∀ ε > (0 : ℝ), ∀ᶠ T in atTop,
      ((hw - B) / (1 - c) - ε) * (Z.N T (2 * T) : ℝ)
        ≤ (Z.N0s T (2 * T) : ℝ) := by
  intro ε hε
  set k : ℝ := ((n - 1 : ℕ) : ℝ) with hkdef
  have hk1 : (1 : ℝ) ≤ k := by
    rw [hkdef]; exact_mod_cast (by omega : 1 ≤ n - 1)
  have hk0 : 0 < k := by linarith
  have hmu : 0 < 1 - c := sub_pos.mpr hc1
  set C : ℝ := 4 * k + 2 + c + B with hCdef
  have hC : 0 < C := by
    dsimp [C]
    linarith
  set δ : ℝ := min (c / (8 * k)) ((1 - c) * ε / C) with hδdef
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (div_pos hc0 (by positivity)) (div_pos (mul_pos hmu hε) hC)
  have hδcap : δ ≤ c / (8 * k) := min_le_left _ _
  have hδeps : δ ≤ (1 - c) * ε / C := min_le_right _ _
  have hbudget : C * δ ≤ (1 - c) * ε := by
    have h := (le_div_iff₀ hC).mp hδeps
    linarith only [h]
  have hcoef : 0 ≤ c - 4 * k * δ := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * k)).mp hδcap
    nlinarith only [h, hc0]
  filter_upwards [hdef δ hδ, deleted_strips Z H δ hδ,
    span_retained_le Z H δ hδ, tail_passage Z H (eventually_h7 Z) δ hδ,
    (Zeta23.Assembly.tendsto_N_atTop Z H.RvM).eventually_ge_atTop (k * c / δ)]
    with T hd hstrip hspan htail hNlarge
  set N : ℝ := (Z.N T (2 * T) : ℝ)
  set n0 : ℝ := (Z.N0s T (2 * T) : ℝ)
  set m : ℝ := ((retained Z (mtParams T) T).card : ℝ)
  set R : ℝ := spanOf (xret Z (mtParams T) T) Finset.univ
  set D : ℝ := Dcirc Z (mtParams T) T
  change (c - 4 * k * δ) * m - B * R - k * c ≤ D at hd
  change n0 - δ * N ≤ m at hstrip
  change R ≤ (1 + δ) * N at hspan
  change (AMW.HW - δ) * N + D ≤ n0 at htail
  change k * c / δ ≤ N at hNlarge
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hn0N : n0 ≤ N := by
    have h := (Z.trivial_chain T (2 * T)).1.trans
      ((Z.trivial_chain T (2 * T)).2.1.trans (Z.trivial_chain T (2 * T)).2.2.1)
    change (Z.N0s T (2 * T) : ℝ) ≤ (Z.N T (2 * T) : ℝ)
    exact_mod_cast h
  have hn := mul_le_mul_of_nonneg_left hstrip hcoef
  have hR := mul_le_mul_of_nonneg_left hspan hB
  have herr := mul_le_mul_of_nonneg_left hn0N
    (show 0 ≤ 4 * k * δ by positivity)
  have hδ2N : 0 ≤ 4 * k * δ * δ * N := by positivity
  have hD : c * n0 - B * N - (4 * k + c + B) * δ * N - k * c ≤ D := by
    nlinarith only [hd, hn, hR, herr, hδ2N]
  have hend : k * c ≤ δ * N := by
    have h := (div_le_iff₀ hδ).mp hNlarge
    nlinarith only [h]
  have hHW : hw * N ≤ AMW.HW * N :=
    mul_le_mul_of_nonneg_right hfloor hN0
  have hmain : ((hw : ℝ) - B - C * δ) * N ≤ (1 - c) * n0 := by
    dsimp [C]
    nlinarith only [hD, htail, hend, hHW]
  have hid : (1 - c) * ((hw - B) / (1 - c)) = hw - B := by
    field_simp
  have hcoeff : (1 - c) * ((hw - B) / (1 - c) - ε) ≤
      (hw : ℝ) - B - C * δ := by
    rw [mul_sub, hid]
    linarith only [hbudget]
  have hscaled : (1 - c) * (((hw - B) / (1 - c) - ε) * N) ≤ (1 - c) * n0 := by
    calc
      _ = ((1 - c) * ((hw - B) / (1 - c) - ε)) * N := by ring
      _ ≤ ((hw : ℝ) - B - C * δ) * N :=
        mul_le_mul_of_nonneg_right hcoeff hN0
      _ ≤ _ := hmain
  exact le_of_mul_le_mul_left hscaled hmu

theorem simple_dyadic {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
    {c B hw : ℝ} (hc0 : 0 < c) (hc64 : c ≤ 1 / 64) (hB : W.B = B)
    (hfloor : hw ≤ AMW.HW)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g) :
    ∀ ε > (0 : ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((hw - B) / (1 - c) - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤
        Zeta23.N0simple T (2 * T) := by
  have hB0 : 0 ≤ B := hB ▸ WCert.B_nonneg hW
  have hdef := OpethN.ActualDefect.actual_defect_estimate
    zetaZeroConfig hn W hW hc0.le hc64 hB hCert
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
    (defect_to_dyadic zetaZeroConfig paperInputs_zeta hn hc0
      (by linarith) hB0 hfloor hdef ε hε)
  refine ⟨T₀, fun T hT => ?_⟩
  simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using hT₀ T hT

theorem simple_cumulative {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
    {c B hw : ℝ} (hc0 : 0 < c) (hc64 : c ≤ 1 / 64) (hB : W.B = B)
    (hfloor : hw ≤ AMW.HW)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g) :
    ∀ ε > (0 : ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((hw - B) / (1 - c) - ε) * (Zeta23.Ncount 0 T : ℝ) ≤
        Zeta23.N0simple 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0simple_add' Zeta23.zetaSeam)
    (simple_dyadic hn W hW hc0 hc64 hB hfloor hCert)

theorem distinct_dyadic {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
    {c B hw : ℝ} (hc0 : 0 < c) (hc64 : c ≤ 1 / 64) (hB : W.B = B)
    (hfloor : hw ≤ AMW.HW)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g) :
    ∀ ε > (0 : ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((hw - B) / (1 - c) - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤
        Zeta23.N0star T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := simple_dyadic hn W hW hc0 hc64 hB hfloor hCert ε hε
  refine ⟨T₀, fun T hT => (hT₀ T hT).trans ?_⟩
  exact_mod_cast AMW.N0simple_le_N0star' T (2 * T)

theorem distinct_cumulative {n : ℕ} (hn : 2 ≤ n) (W : WCert n) (hW : W.Adm)
    {c B hw : ℝ} (hc0 : 0 < c) (hc64 : c ≤ 1 / 64) (hB : W.B = B)
    (hfloor : hw ≤ AMW.HW)
    (hCert : ∀ g : Fin (n - 1) → ℝ, (∀ i, 0 ≤ g i) → c ≤ Fw W g) :
    ∀ ε > (0 : ℝ), ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((hw - B) / (1 - c) - ε) * (Zeta23.Ncount 0 T : ℝ) ≤
        Zeta23.N0star 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0star_add' Zeta23.zetaSeam)
    (distinct_dyadic hn W hW hc0 hc64 hB hfloor hCert)

end GramDefect20261015.Counting
