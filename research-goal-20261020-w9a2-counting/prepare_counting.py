"""Prepare same-kernel W9A2 finite-state counting source; never invoke Lean.

The generic band/matching bridge is copied verbatim from the accepted v3
development's Production/Counting.lean, after namespace/import replacement.
The current W9A2 H is substituted only in the ratio-to-counting interface.
"""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent
OLD = ROOT / 'StructuralS1RTiny20261018/Production/Counting.lean'
old = OLD.read_text(encoding='utf-8')
header = '''/-
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

'''
finite = '''/-- A pointwise coboundary payment telescopes over every finite prefix.
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

'''
common = old[old.index('section Payment'):old.index('/-- No new ten-point ledger')]
tail = '''/-- W9A2's current H, pinned to the official source of 2026-10-19. -/
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
'''
source = header + finite + common + tail
assert 'StructuralS1RTiny20261018.Counting' not in source
assert '6721290091768038344368273523390880473594' not in source
assert 'sorry' not in source and 'admit' not in source
for target in [HERE / 'Counting.lean', ROOT / 'StructuralW9A220261020/Counting.lean']:
    target.write_text(source, encoding='utf-8', newline='\n')
summary = {
    'status': 'PREPARATION_ONLY_NOT_COMPILED',
    'scope': 'Generic coboundary telescoping and same-kernel actual dyadic/cumulative bridge; actual localization and transitions are supplied by companion Final.',
    'copied_common_section': 'section Payment through actual_defect_estimate_effective, unchanged proof bodies',
    'old_counting_path': str(OLD.relative_to(ROOT)).replace('\\', '/'),
    'old_counting_sha256': hashlib.sha256(OLD.read_bytes()).hexdigest(),
    'common_section_sha256': hashlib.sha256(common.encode()).hexdigest(),
    'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
    'source_bytes': len(source.encode()),
    'compiler_runs': 0,
    'independent_kernel_runs': 0,
}
(HERE / 'counting-preparation.json').write_text(json.dumps(summary, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')
print(json.dumps(summary, ensure_ascii=False))
