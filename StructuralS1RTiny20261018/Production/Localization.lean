/-
SPDX-License-Identifier: Apache-2.0

Preparation only: current s1R original-COV localization, unique exception,
and the actual adjacent-window pair floor. No Lean run has checked this file.
The root construction follows AMW.Cert.PCell.root_cover in the attributed
accepted source; only the separated pressure payments and target predicate
are changed. All original COV/state/FS/kernel data are imported unchanged.
-/
import StructuralS1RTiny20261018.Production.Core

set_option Elab.async false
set_option maxHeartbeats 0

noncomputable section
open Finset
open AMW.Cert AMW.Cert.PCell
open AMW.Cert.PC9Tiny AMW.Cert.PC9TinyData
open Zeta23Ext.BridgeW

namespace StructuralS1RTiny20261018.Dev.Localization

def sep : ℝ := 17 / 20
def base : ℝ := (cN : ℝ) / SA
def delta : ℝ := (tinyDeltaN : ℝ) / SA
def c : ℝ := base + delta
def tau : ℝ := (tinyTauN : ℝ) / SA

def pressure (g : ℕ → ℝ) : ℝ :=
  ∑ r ∈ range 8, (BS.getD r 0 : ℝ) * g r

theorem Fg_ge_full_pressure (g : ℕ → ℝ) :
    pressure g ≤ Fg 8 BS TS g := by
  have hn : 0 ≤ ∑ n ∈ range TS.length,
      (tA TS n : ℝ) * AMW.Cert.wfun (gsum g (tI TS n) (tJ TS n)) := by
    exact Finset.sum_nonneg fun n _ => mul_nonneg (Nat.cast_nonneg _) (AMW.Cert.wfun_nonneg _)
  exact le_add_of_nonneg_right hn

theorem Fg_ge_term_add_pressure (g : ℕ → ℝ) {n : ℕ} (hn : n < TS.length) :
    pressure g + (tA TS n : ℝ) * AMW.Cert.wfun (gsum g (tI TS n) (tJ TS n))
      ≤ Fg 8 BS TS g := by
  have hs := Finset.single_le_sum
    (f := fun n => (tA TS n : ℝ) * AMW.Cert.wfun (gsum g (tI TS n) (tJ TS n)))
    (fun n _ => mul_nonneg (Nat.cast_nonneg _) (AMW.Cert.wfun_nonneg _))
    (Finset.mem_range.mpr hn)
  simpa only [Fg, pressure, add_comm] using (add_le_add_left hs (pressure g))

theorem pressure_of_sep {g : ℕ → ℝ} (hg : ∀ r < 8, sep ≤ g r) :
    sep * (∑ r ∈ range 8, (BS.getD r 0 : ℝ)) ≤ pressure g := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  simpa only [mul_comm] using
    (mul_le_mul_of_nonneg_left (hg r (Finset.mem_range.mp hr)) (Nat.cast_nonneg (BS.getD r 0) : (0 : ℝ) ≤ _))

theorem pressure_rest_of_sep {g : ℕ → ℝ} (hg : ∀ k < 8, sep ≤ g k)
    {r : ℕ} (hr : r < 8) :
    (BS.getD r 0 : ℝ) * g r + sep * (∑ k ∈ (range 8).erase r, (BS.getD k 0 : ℝ))
      ≤ pressure g := by
  have hs : sep * (∑ k ∈ (range 8).erase r, (BS.getD k 0 : ℝ)) ≤
      ∑ k ∈ (range 8).erase r, (BS.getD k 0 : ℝ) * g k := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hk8 := Finset.mem_range.mp (Finset.mem_of_mem_erase hk)
    simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_left (hg k hk8) (Nat.cast_nonneg (BS.getD k 0) : (0 : ℝ) ≤ _))
  rw [pressure, ← Finset.add_sum_erase (range 8)
    (fun k => (BS.getD k 0 : ℝ) * g k) (Finset.mem_range.mpr hr)]
  simpa only [add_comm] using
    (add_le_add_left hs ((BS.getD r 0 : ℝ) * g r))

/-- These are the exact same old-c9 finite checks appearing as anonymous
arguments of the accepted Data.cert. There is no raised coverChk/WZ query.
They may later be shared with that theorem to avoid duplicate proof work. -/
theorem original_hS : ∀ r < 8, cN * SC ≤ BS.getD r 0 * SMAX r := by
  decide

theorem original_hcov : ∀ r < 8,
    coverChk cN (tA TS (ADJ.getD r 0)) (SC / 2) (SMAX r) (COV.getD r []) = true := by
  decide +kernel

theorem flagged_pressure_budget :
    (tinyTauN : ℝ) ≤ (cN : ℝ) + sep * (∑ r ∈ range 8, (BS.getD r 0 : ℝ)) := by
  norm_num [tinyTauN, tinyDeltaN, cN, sep, BS, Finset.sum_range_succ]

theorem tail_pressure_budget (r : ℕ) (hr : r < 8) :
    (tinyTauN : ℝ) ≤ (cN : ℝ) + sep * (∑ k ∈ (range 8).erase r, (BS.getD k 0 : ℝ)) := by
  interval_cases r <;>
    norm_num [tinyTauN, tinyDeltaN, cN, sep, BS, Finset.sum_range_succ]

/-- Separated root localization keeps the old root geometry and COV. The
additional pressure pays the new target outside the roots. -/
theorem root_TinyGoal (g : ℕ → ℝ) (hsep : ∀ r < 8, sep ≤ g r) : TinyGoal g := by
  classical
  have hg : ∀ r < 8, 0 ≤ g r := fun r hr => le_trans (by norm_num [sep]) (hsep r hr)
  have hSC : (0 : ℝ) < SC := by norm_num [SC]
  by_cases hgood : (tinyTauN : ℝ) ≤ Fg 8 BS TS g
  · exact Or.inl (Or.inl hgood)
  have hbad : ∀ r < 8, ∃ i, i < (badOf (COV.getD r [])).length ∧
      (((badOf (COV.getD r [])).getD i (0, 0)).1 : ℝ) / SC ≤ g r ∧
      g r ≤ (((badOf (COV.getD r [])).getD i (0, 0)).2 : ℝ) / SC ∧
      ((badOf (COV.getD r [])).getD i (0, 0)).2 < KB := by
    intro r hr
    obtain ⟨hn, hi, hj⟩ := hADJ r hr
    have hsr : gsum g (tI TS (ADJ.getD r 0)) (tJ TS (ADJ.getD r 0)) = g r := by
      rw [hi, hj, gsum]; simp
    by_cases hcut : (SMAX r : ℝ) / SC ≤ g r
    · exfalso
      have hq := (Nat.cast_le (α := ℝ)).mpr (original_hS r hr)
      push_cast at hq
      have hbase : (cN : ℝ) ≤ (BS.getD r 0 : ℝ) * g r := by
        have hl : (cN : ℝ) ≤ (BS.getD r 0 : ℝ) * ((SMAX r : ℝ) / SC) := by
          rw [mul_div_assoc', le_div_iff₀ hSC]; linarith
        exact hl.trans (mul_le_mul_of_nonneg_left hcut (Nat.cast_nonneg _))
      have hp := (pressure_rest_of_sep hsep hr).trans (Fg_ge_full_pressure g)
      have hb := tail_pressure_budget r hr
      exact hgood (by linarith)
    push_neg at hcut
    rcases le_total (g r) (((SC / 2 : ℕ) : ℝ) / SC) with hw | hw
    · exfalso
      have hh : ((SC / 2 : ℕ) : ℝ) / SC = 1 / 2 := by norm_num [SC]
      rw [hh] at hw
      have hs := hsep r hr
      norm_num [sep] at hs
      linarith
    rcases coverChk_sound cN (tA TS (ADJ.getD r 0)) (COV.getD r [])
        (SC / 2) (SMAX r) (original_hcov r hr) (g r) hw hcut with
      hclear | ⟨s, hs, he, h1, h2, h3⟩
    · exfalso
      have ht := Fg_ge_term_add_pressure g hn
      rw [hsr] at ht
      have hp := pressure_of_sep hsep
      have hb := flagged_pressure_budget
      exact hgood (by linarith)
    obtain ⟨i, hi', hsi⟩ := List.mem_iff_getElem.mp (badOf_mem hs he)
    refine ⟨i, hi', ?_, ?_, ?_⟩
    · rw [List.getD_eq_getElem _ _ hi', hsi]; exact h1
    · rw [List.getD_eq_getElem _ _ hi', hsi]; exact h2
    · rw [List.getD_eq_getElem _ _ hi', hsi]; exact h3
  choose! idx hidx using hbad
  apply AMW.Cert.PC9TinyData.run idx (fun r hr => (hidx r hr).1) g
  refine incell_root hPR (W := 1099511627776)
    (fun k hk => by
      have hkn : k < 28 := by simpa [PR] using hk
      interval_cases k <;> rfl)
    (fun k hk => by
      have hkn : k < 28 := by simpa [PR] using hk
      interval_cases k <;> rfl) ?_ (fun r hr => ?_)
  · have h1 : ((sumR (rootCl 8 PR.length 1099511627776 COV idx).U 0 8 : ℕ) : ℝ) ≤
        ((8 * KB : ℕ) : ℝ) := by
      rw [sumR_eq, Nat.zero_add]; push_cast
      calc
        ∑ r ∈ Finset.Ico 0 8,
            (((rootCl 8 PR.length 1099511627776 COV idx).U.getD r 0 : ℕ) : ℝ)
            ≤ ∑ r ∈ Finset.Ico 0 8, (KB : ℝ) := by
              apply Finset.sum_le_sum
              intro r hr
              have hr' : r < 8 := (Finset.mem_Ico.mp hr).2
              simp only [rootCl]
              rw [getD_map_range _ hr']
              exact_mod_cast (hidx r hr').2.2.2.le
        _ = (8 : ℝ) * KB := by simp
    exact (by exact_mod_cast h1 : sumR _ 0 8 ≤ 8 * KB).trans (by decide)
  · simp only [rootCl]
    rw [getD_map_range _ hr, getD_map_range _ hr]
    exact ⟨(hidx r hr).2.1, (hidx r hr).2.2.1⟩

theorem ordered_exception (g : ℕ → ℝ) (hsep : ∀ r < 8, sep ≤ g r)
    (horder : g 0 ≤ g 7) (hlow : Fg 8 BS TS g < (tinyTauN : ℝ)) :
    InCell 8 PR tinyExceptionCell g := by
  rcases root_TinyGoal g hsep with h | h
  · rcases h with h | h
    · exact False.elim ((not_le_of_gt hlow) h)
    · change g 7 < g 0 at h
      exact False.elim ((not_lt_of_ge horder) h)
  · exact h.1

def natGaps (g : Fin 8 → ℝ) : ℕ → ℝ :=
  fun r => [g 0, g 1, g 2, g 3, g 4, g 5, g 6, g 7].getD r 0

def reverse8 (g : Fin 8 → ℝ) : Fin 8 → ℝ :=
  fun r => g ⟨7 - r.val, by omega⟩

theorem natGaps_apply (g : Fin 8 → ℝ) {r : ℕ} (hr : r < 8) :
    natGaps g r = g ⟨r, hr⟩ := by
  interval_cases r <;> rfl

theorem scaled_energy (g : Fin 8 → ℝ) :
    Fg 8 BS TS (natGaps g) = (SA : ℝ) * Fw RiemannFail.W9 g := by
  rw [RiemannFail.Fw_W9]
  exact Fg_G (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7)

theorem reverse_energy (g : Fin 8 → ℝ) :
    Fw RiemannFail.W9 (reverse8 g) = Fw RiemannFail.W9 g := by
  rw [RiemannFail.Fw_W9, RiemannFail.Fw_W9]
  simpa [reverse8] using AMW.Cert.PC9Tiny_G_rev (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7)

theorem finite_ordered_exception (g : Fin 8 → ℝ) (hsep : ∀ r, sep ≤ g r)
    (horder : g 0 ≤ g 7) (hlow : Fw RiemannFail.W9 g < tau) :
    InCell 8 PR tinyExceptionCell (natGaps g) := by
  apply ordered_exception
  · intro r hr
    rw [natGaps_apply g hr]
    exact hsep _
  · simpa [natGaps] using horder
  · rw [scaled_energy]
    have hSA : (0 : ℝ) < SA := by norm_num [SA]
    change Fw RiemannFail.W9 g < (tinyTauN : ℝ) / SA at hlow
    simpa only [mul_comm] using (lt_div_iff₀ hSA).mp hlow

theorem exception_or_reverse (g : Fin 8 → ℝ) (hsep : ∀ r, sep ≤ g r)
    (hlow : Fw RiemannFail.W9 g < tau) :
    InCell 8 PR tinyExceptionCell (natGaps g) ∨
      InCell 8 PR tinyExceptionCell (natGaps (reverse8 g)) := by
  by_cases ho : g 0 ≤ g 7
  · exact Or.inl (finite_ordered_exception g hsep ho hlow)
  · right
    apply finite_ordered_exception (reverse8 g)
    · intro r; exact hsep _
    · simpa [reverse8] using (le_of_lt (lt_of_not_ge ho))
    · simpa only [reverse_energy] using hlow

theorem second_gap_small (g : Fin 8 → ℝ) (hsep : ∀ r, sep ≤ g r)
    (hlow : Fw RiemannFail.W9 g < tau) : g 1 ≤ (34980 : ℝ) / 32768 := by
  rcases exception_or_reverse g hsep hlow with h | h
  · simpa [natGaps, tinyExceptionCell, tinyExceptionState, toCl, SC] using (h.1 1 (by norm_num)).2
  · have hb : g 1 ≤ (34464 : ℝ) / 32768 := by
      simpa [natGaps, reverse8, tinyExceptionCell, tinyExceptionState, toCl, SC] using (h.1 6 (by norm_num)).2
    linarith

theorem first_gap_large (g : Fin 8 → ℝ) (hsep : ∀ r, sep ≤ g r)
    (hlow : Fw RiemannFail.W9 g < tau) : (64168 : ℝ) / 32768 ≤ g 0 := by
  rcases exception_or_reverse g hsep hlow with h | h
  · simpa [natGaps, tinyExceptionCell, tinyExceptionState, toCl, SC] using (h.1 0 (by norm_num)).1
  · have hb : (64461 : ℝ) / 32768 ≤ g 0 := by
      simpa [natGaps, reverse8, tinyExceptionCell, tinyExceptionState, toCl, SC] using (h.1 7 (by norm_num)).1
    linarith

def leftGaps (g : Fin 9 → ℝ) : Fin 8 → ℝ := fun r => g ⟨r.val, by omega⟩
def rightGaps (g : Fin 9 → ℝ) : Fin 8 → ℝ := fun r => g ⟨r.val + 1, by omega⟩

theorem base_floor (g : Fin 8 → ℝ) (hg : ∀ r, 0 ≤ g r) : base ≤ Fw RiemannFail.W9 g := by
  simpa [base, cN, SA] using RiemannFail.cert_AM g hg

theorem two_c_eq : 2 * c = base + tau := by
  norm_num [c, base, delta, tau, tinyTauN, tinyDeltaN, cN, SA]

/-- Actual current-kernel pair floor on all separated nine-gap inputs.
No scalar-model, numerical or minimizer premise is used. -/
theorem pair_floor (g : Fin 9 → ℝ) (hg : ∀ r, (17 : ℝ) / 20 ≤ g r) :
    2 * c ≤ Fw RiemannFail.W9 (leftGaps g) + Fw RiemannFail.W9 (rightGaps g) := by
  have hlsep : ∀ r, sep ≤ leftGaps g r := fun r => hg _
  have hrsep : ∀ r, sep ≤ rightGaps g r := fun r => hg _
  have hlbase := base_floor (leftGaps g) (fun r => le_trans (by norm_num [sep]) (hlsep r))
  have hrbase := base_floor (rightGaps g) (fun r => le_trans (by norm_num [sep]) (hrsep r))
  by_contra h
  have hsum : Fw RiemannFail.W9 (leftGaps g) + Fw RiemannFail.W9 (rightGaps g) < 2 * c := lt_of_not_ge h
  have hleft : Fw RiemannFail.W9 (leftGaps g) < tau := by linarith [two_c_eq]
  have hright : Fw RiemannFail.W9 (rightGaps g) < tau := by linarith [two_c_eq]
  have hlu := second_gap_small (leftGaps g) hlsep hleft
  have hrl := first_gap_large (rightGaps g) hrsep hright
  change g 1 ≤ (34980 : ℝ) / 32768 at hlu
  change (64168 : ℝ) / 32768 ≤ g 1 at hrl
  have hc : (64168 : ℝ) / 32768 ≤ (34980 : ℝ) / 32768 := hrl.trans hlu
  norm_num at hc

end StructuralS1RTiny20261018.Dev.Localization
end
