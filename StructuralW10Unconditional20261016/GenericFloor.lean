/- SPDX-License-Identifier: Apache-2.0
The fixed ten-point weights with a variable exact local floor. This module
does not assert a successful concrete cover. Its purpose is to support
smaller complete certificates without changing the frozen W10 candidate.
-/
import StructuralW10Cert20261016.FastPruefer
import StructuralW10Cert20261016.AdaptiveCoverage

noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
open StructuralW10Cert20261016
open LocalChecker
open StructuralResearch20261016.W10RefinedCandidate
open StructuralResearch20261016.Coboundary
open Zeta23Ext.BridgeW Zeta23Ext.Bridge
namespace StructuralW10Unconditional20261016.GenericFloor

def floor (n : ℕ) : ℝ := n / 10000000000
def ratio (n : ℕ) : ℝ :=
  (FinalConditional.windowFloor - FinalConditional.pressure) / (1 - floor n)

def checkLeaf (n : ℕ) (c : Cl) (FS : List Term) (moves : List DualMove) : Bool :=
  let s := runDual c moves initialDual
  mcheckGX (mokI PC9QB6MData.PT) PC9QB6MData.TOP PC9QB6MData.BK
    (tf PC9QB6MData.PT) 9 BS TS n c FS s.P s.S s.Cp s.Cm

theorem checkLeaf_sound {n : ℕ} {c : Cl} {FS : List Term} {moves : List DualMove}
    (h : checkLeaf n c FS moves = true) : CovBy 9 PR (Pg n 9 BS TS) c := by
  exact mcheckGX_sound (mtermTI PC9QB6MData.lbS PC9QB6MData.ptS) hPR hTS
    (runDual_good c moves initialDual (initial_good c)).2.2 h

def checkPacked (n : ℕ) (c : Cl) (word : ℕ) : Bool :=
  FastPruefer.forceTerms (RelCompactLeaf.decodeTerms c (word / 100000000)) fun FS =>
    checkLeaf n c FS (FastPruefer.moves FS (word % 100000000))

theorem checkPacked_sound {n : ℕ} {c : Cl} {word : ℕ}
    (h : checkPacked n c word = true) : CovBy 9 PR (Pg n 9 BS TS) c := by
  simp only [checkPacked, FastPruefer.forceTerms_eq] at h
  exact checkLeaf_sound h

theorem reflection_leaf {n : ℕ} {c : Cl}
    (h : c.U.getD 8 0 < c.L.getD 0 0) : CovBy 9 PR (Pg n 9 BS TS) c := by
  intro g hg
  right
  have h0 := (hg.1 0 (by decide)).1
  have h8 := (hg.1 8 (by decide)).2
  have hh : (c.U.getD 8 0 : ℝ) / SC < (c.L.getD 0 0 : ℝ) / SC :=
    (div_lt_div_iff_of_pos_right SC_pos).mpr (by exact_mod_cast h)
  exact lt_of_le_of_lt h8 (lt_of_lt_of_le hh h0)

def dispatch (n : ℕ) (payload : ℕ → ℕ) (c : Cl) (id : ℕ) : Bool :=
  if id = 0 then decide (c.U.getD 8 0 < c.L.getD 0 0)
  else if id ≤ 9 then decide (c.U.getD (id-1) 0 < c.L.getD (id-1) 0)
  else if id ≤ 45 then decide (c.B.getD (id-10) 0 < c.A.getD (id-10) 0)
  else checkPacked n c (payload (id-46))

theorem dispatch_sound (n : ℕ) (payload : ℕ → ℕ) (c : Cl) (id : ℕ)
    (h : dispatch n payload c id = true) : CovBy 9 PR (Pg n 9 BS TS) c := by
  unfold dispatch at h
  split_ifs at h with h0 h9 h45
  · exact reflection_leaf (of_decide_eq_true h)
  · exact TreeCoverage.cov_of_coordinate_empty (by omega) (of_decide_eq_true h)
  · have hk : id - 10 < PR.length := by
      norm_num only [PR, List.length_cons, List.length_nil] at ⊢
      omega
    exact TreeCoverage.cov_of_span_empty hk (of_decide_eq_true h)
  · exact checkPacked_sound h

theorem floor_le_original {n : ℕ} (hn : n ≤ 86600000) :
    floor n ≤ (433 : ℝ) / 50000 := by
  have hh : (n : ℝ) ≤ 86600000 := by exact_mod_cast hn
  unfold floor
  linarith only [hh]

theorem ordered_floor {n : ℕ} (hn : n ≤ 86600000)
    (hcov : CovBy 9 PR (Pg n 9 BS TS) RootBounds.initialCell)
    (g : Fin 9 → ℝ) (hg : ∀ i, (17 / 20 : ℝ) ≤ g i)
    (ho : g 0 ≤ g 8) : floor n ≤ Fw W g := by
  by_contra h
  have hcounter : Fw W g < floor n := lt_of_not_ge h
  have hnsep : ∀ r < 9, (17 / 20 : ℝ) ≤ FloorTransfer.extend g r := by
    intro r hr
    simpa only [FloorTransfer.extend, dif_pos hr] using hg ⟨r,hr⟩
  have hc : Fw W (fun r : Fin 9 => FloorTransfer.extend g r) < (433 : ℝ) / 50000 := by
    rw [FloorTransfer.extend_fin]
    exact hcounter.trans_le (floor_le_original hn)
  rcases hcov (FloorTransfer.extend g) (RootBounds.counterexample_in_root hnsep hc) with hf | hr
  · rw [fg_eq_scaled_Fw, FloorTransfer.extend_fin] at hf
    unfold floor at hcounter
    nlinarith only [hf, hcounter]
  · have hh : FloorTransfer.extend g 0 ≤ FloorTransfer.extend g 8 := by
      simpa [FloorTransfer.extend] using ho
    exact (not_lt_of_ge hh) hr

theorem separated_floor {n : ℕ} (hn : n ≤ 86600000)
    (hcov : CovBy 9 PR (Pg n 9 BS TS) RootBounds.initialCell) :
    ∀ g : Fin 9 → ℝ, (∀ i, (17 / 20 : ℝ) ≤ g i) → floor n ≤ Fw W g := by
  intro g hg
  by_cases ho : g 0 ≤ g 8
  · exact ordered_floor hn hcov g hg ho
  · have hr : Reflection.reverse g 0 ≤ Reflection.reverse g 8 := by
      simpa [Reflection.reverse, Fin.rev] using (le_of_lt (lt_of_not_ge ho))
    have hf := ordered_floor hn hcov (Reflection.reverse g)
      (Reflection.reverse_lower g (17 / 20) hg) hr
    simpa only [Reflection.Fw_reverse] using hf

theorem summed {n : ℕ} (hn : n ≤ 86600000)
    (hcov : CovBy 9 PR (Pg n 9 BS TS) RootBounds.initialCell) :
    SeparatedSummedCertificate W (floor n) 0 (17 / 20) := by
  have h : SeparatedSummedCertificate W (floor n) ((0 : ℝ) - 0) (17 / 20) :=
    summed_of_separated_coboundary (by norm_num : 2 ≤ 10) W
      (fun _ => (0 : ℝ)) (floor n) 0 0 (17 / 20)
      (by intro g hg; exact ⟨le_rfl, le_rfl⟩)
      (by
        intro g hg
        simpa only [add_zero, sub_zero] using separated_floor hn hcov g hg)
  intro m hm y hy hsep
  simpa only [sub_self] using h (m := m) hm y hy hsep

theorem floor_pos {n : ℕ} (hn : 0 < n) : 0 < floor n := by
  exact div_pos (by exact_mod_cast hn) (by norm_num)

theorem floor_le_64 {n : ℕ} (hn : n ≤ 86600000) : floor n ≤ (1 : ℝ) / 64 :=
  (floor_le_original hn).trans (by norm_num)

theorem simple_dyadic {n : ℕ} (hn0 : 0 < n) (hn : n ≤ 86600000)
    (hcov : CovBy 9 PR (Pg n 9 BS TS) RootBounds.initialCell) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ratio n - ε) * (Zeta23.Ncount T (2*T) : ℝ) ≤ Zeta23.N0simple T (2*T) := by
  exact StructuralResearch20261016.CoboundaryCounting.simple_dyadic
    (hw := FinalConditional.windowFloor) (c := floor n) (C := 0)
    (B := FinalConditional.pressure) (by norm_num : 2 ≤ 10) W
    StructuralResearch20261016.W10RefinedCandidate.adm
    (floor_pos hn0) (by norm_num) (floor_pos hn0).le (floor_le_64 hn)
    (by simpa only [FinalConditional.pressure] using
      StructuralResearch20261016.W10RefinedCandidate.pressure_eq)
    (by simpa only [FinalConditional.windowFloor] using GramDefect20261015.Window.HW_ge)
    (summed hn hcov)

theorem simple_cumulative {n : ℕ} (hn0 : 0 < n) (hn : n ≤ 86600000)
    (hcov : CovBy 9 PR (Pg n 9 BS TS) RootBounds.initialCell) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ratio n - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0simple 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0simple_add' Zeta23.zetaSeam) (simple_dyadic hn0 hn hcov)

theorem distinct_dyadic {n : ℕ} (hn0 : 0 < n) (hn : n ≤ 86600000)
    (hcov : CovBy 9 PR (Pg n 9 BS TS) RootBounds.initialCell) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ratio n - ε) * (Zeta23.Ncount T (2*T) : ℝ) ≤ Zeta23.N0star T (2*T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := simple_dyadic hn0 hn hcov ε hε
  exact ⟨T₀, fun T hT => (hT₀ T hT).trans (by
    exact_mod_cast AMW.N0simple_le_N0star' T (2*T))⟩

theorem distinct_cumulative {n : ℕ} (hn0 : 0 < n) (hn : n ≤ 86600000)
    (hcov : CovBy 9 PR (Pg n 9 BS TS) RootBounds.initialCell) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (ratio n - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0star_add' Zeta23.zetaSeam) (distinct_dyadic hn0 hn hcov)

#print axioms checkLeaf_sound
#print axioms dispatch_sound
#print axioms separated_floor
#print axioms simple_dyadic
#print axioms distinct_cumulative
end StructuralW10Unconditional20261016.GenericFloor
end
