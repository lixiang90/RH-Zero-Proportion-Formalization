"""Prepare current-s1R summed counting source; text/bytes/AST only, no Lean."""
import ast
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent


def item(p):
    b = p.read_bytes()
    return {'path': p.relative_to(ROOT).as_posix(), 'bytes': len(b),
            'sha256': hashlib.sha256(b).hexdigest()}


def cut(text, start, end):
    return text[text.index(start):text.index(end, text.index(start))].rstrip() + '\n\n'


HEADER = r'''/-
SPDX-License-Identifier: Apache-2.0

Current s1R separated summed-floor transfer. The finite pair-floor premise is
explicit. This source has not been compiled and its future Core import has
not yet been supplied.

The band/matching proof bodies below are adapted from the attributed
StructuralResearch20261016.Coboundary / CoboundaryCounting development:
R. Arun Chandru's combination of Samuel Lavery's AM defect bridge and Kristian
Muri Knausgard's matching development. Their original licenses and notices,
and the current accepted s1R Core notices, remain applicable. No old kernel
or old Core is imported. Current 17/20 separation and 1/64 pair payment are
used through the current Core's actual AM theorems.
-/
import StructuralS1RTiny20261018.Core

set_option Elab.async false
set_option maxHeartbeats 0

noncomputable section
open Matrix Finset RHLinalg Filter Topology
open scoped ComplexOrder BigOperators
open Zeta23Ext.StableRankTrace Zeta23Ext.Bridge Zeta23Ext.BridgeW

namespace StructuralS1RTiny20261018.Counting

/-- Two consecutive pair payments and a single old-floor payment cover a
finite string, with at most one boundary deficit. -/
theorem sum_range_pair_lower (E : ℕ → ℝ) (c delta : ℝ)
    (hdelta : 0 ≤ delta) (N : ℕ) :
    (∀ i, i < N → c - delta ≤ E i) →
    (∀ i, i + 1 < N → 2 * c ≤ E i + E (i + 1)) →
    c * (N : ℝ) - delta ≤ ∑ i ∈ range N, E i := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro hbase hpair
    cases N with
    | zero => simpa using (neg_nonpos.mpr hdelta)
    | succ k =>
      cases k with
      | zero => simpa using (hbase 0 (by omega))
      | succ n =>
        have hs := ih n (by omega)
          (fun i hi => hbase i (by omega))
          (fun i hi => hpair i (by omega))
        have hp := hpair n (by omega)
        rw [sum_range_succ, sum_range_succ]
        have hn : (n.succ.succ : ℝ) = (n : ℝ) + 2 := by push_cast; ring
        rw [hn]
        linarith only [hs, hp]

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

'''

PAIR_TO_SUM = r'''/-- The old floor is only used on one possible leftover nine-point
window. The pair premise is a real current-kernel statement on all separated
ten-point configurations, not a hypothesis about minimizers or sampled cells. -/
theorem summed_of_pair (W : WCert 9) (c delta sep : ℝ) (hdelta : 0 ≤ delta)
    (hbase : ∀ g : Fin 8 → ℝ, (∀ r, 0 ≤ g r) → c - delta ≤ Fw W g)
    (hpair : ∀ g : Fin 9 → ℝ, (∀ r, sep ≤ g r) →
      2 * c ≤ Fw W (leftGaps g) + Fw W (rightGaps g)) :
    SeparatedSummedCertificate W c delta sep := by
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
  have hb (i : ℕ) (hi : i < N) : c - delta ≤ Fw W (windowGaps 9 Y i) := by
    apply hbase
    intro r
    have hr := r.isLt
    have hlast : i + ((r : ℕ) + 1) < m := by dsimp [N] at hi; omega
    change 0 ≤ Y (i + ((r : ℕ) + 1)) - Y (i + r)
    exact sub_nonneg.mpr (sortedExt_mono hy (by omega) hlast)
  have hp (i : ℕ) (hi : i + 1 < N) :
      2 * c ≤ Fw W (windowGaps 9 Y i) + Fw W (windowGaps 9 Y (i + 1)) := by
    have hg : ∀ r, sep ≤ windowGaps 10 Y i r := by
      intro r
      have hr := r.isLt
      have hlast : i + ((r : ℕ) + 1) < m := by dsimp [N] at hi; omega
      exact hgap _ _ (by omega) hlast
    simpa only [left_window, right_window] using hpair (windowGaps 10 Y i) hg
  have hs := sum_range_pair_lower (fun i => Fw W (windowGaps 9 Y i))
    c delta hdelta N hb hp
  have hcast : (N : ℝ) = (m : ℝ) - 8 := by
    dsimp [N]
    rw [Nat.cast_sub (by omega : 8 ≤ m)]
    norm_num
  simpa only [hcast] using hs

section Payment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

'''

WRAPPERS = r'''/-- No new ten-point ledger is required. The boundary charge delta is
absorbed once by the existing harmless increase 9 -> 10 in the defect index. -/
theorem actual_defect_estimate_of_pair (Z : ZeroConfig) (W : WCert 9) (hW : W.Adm)
    {c delta B : ℝ} (hc : 0 ≤ c) (hdelta : 0 ≤ delta) (hdeltac : delta ≤ c)
    (hc64 : c ≤ 1 / 64) (hB : W.B = B)
    (hbase : ∀ g : Fin 8 → ℝ, (∀ r, 0 ≤ g r) → c - delta ≤ Fw W g)
    (hpair : ∀ g : Fin 9 → ℝ, (∀ r, (17 / 20 : ℝ) ≤ g r) →
      2 * c ≤ Fw W (leftGaps g) + Fw W (rightGaps g)) :
    OpethN.Counting.ActualDefectEstimate Z 10 c B :=
  actual_defect_estimate_effective Z (by norm_num : 2 ≤ 9) W hW
    hc hdelta hdeltac hc64 hB (summed_of_pair W c delta (17/20) hdelta hbase hpair)

/-- This is the current source's H, not an old-window constant. -/
def ratio (c B : ℝ) : ℝ :=
  (6721290091768038344368273523390880473594 /
    10000000000000000000000000000000000000000 - B) / (1 - c)

theorem actual_dyadic_of_pair (W : WCert 9) (hW : W.Adm)
    {c delta B : ℝ} (hc : 0 < c) (hdelta : 0 ≤ delta) (hdeltac : delta ≤ c)
    (hc64 : c ≤ 1 / 64) (hB : W.B = B)
    (hbase : ∀ g : Fin 8 → ℝ, (∀ r, 0 ≤ g r) → c - delta ≤ Fw W g)
    (hpair : ∀ g : Fin 9 → ℝ, (∀ r, (17 / 20 : ℝ) ≤ g r) →
      2 * c ≤ Fw W (leftGaps g) + Fw W (rightGaps g)) :
    ∀ epsilon > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0,
      (ratio c B - epsilon) * (Zeta23.Ncount T (2*T) : ℝ) ≤ Zeta23.N0star T (2*T) := by
  have hB0 : 0 ≤ B := hB ▸ WCert.B_nonneg hW
  have hdef := actual_defect_estimate_of_pair zetaZeroConfig W hW
    hc.le hdelta hdeltac hc64 hB hbase hpair
  intro epsilon hepsilon
  obtain ⟨T0, hT0⟩ := eventually_atTop.mp
    (OpethN.Counting.defect_to_dyadic zetaZeroConfig paperInputs_zeta
      (by norm_num : 2 ≤ 10) hc (by linarith) hB0 hdef epsilon hepsilon)
  refine ⟨T0, fun T hT => ?_⟩
  have hs : (ratio c B - epsilon) * (Zeta23.Ncount T (2*T) : ℝ) ≤
      (Zeta23.N0simple T (2*T) : ℝ) := by
    simpa only [ratio, zetaZeroConfig_N, zetaZeroConfig_N0s] using hT0 T hT
  exact hs.trans (by exact_mod_cast AMW.N0simple_le_N0star' T (2*T))

theorem actual_cumulative_of_pair (W : WCert 9) (hW : W.Adm)
    {c delta B : ℝ} (hc : 0 < c) (hdelta : 0 ≤ delta) (hdeltac : delta ≤ c)
    (hc64 : c ≤ 1 / 64) (hB : W.B = B)
    (hbase : ∀ g : Fin 8 → ℝ, (∀ r, 0 ≤ g r) → c - delta ≤ Fw W g)
    (hpair : ∀ g : Fin 9 → ℝ, (∀ r, (17 / 20 : ℝ) ≤ g r) →
      2 * c ≤ Fw W (leftGaps g) + Fw W (rightGaps g)) :
    ∀ epsilon > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0,
      (ratio c B - epsilon) * (Zeta23.Ncount 0 T : ℝ) ≤ Zeta23.N0star 0 T :=
  Zeta23.cumulative_of_dyadic Zeta23.zetaSeam Zeta23.paperInputs_zeta.RvM
    (fun _ _ _ => Zeta23.N0star_add' Zeta23.zetaSeam)
    (actual_dyadic_of_pair W hW hc hdelta hdeltac hc64 hB hbase hpair)

end StructuralS1RTiny20261018.Counting

set_option pp.fullNames true
#print axioms StructuralS1RTiny20261018.Counting.sum_range_pair_lower
#print axioms StructuralS1RTiny20261018.Counting.summed_of_pair
#print axioms StructuralS1RTiny20261018.Counting.actual_defect_estimate_of_pair
#print axioms StructuralS1RTiny20261018.Counting.actual_dyadic_of_pair
#print axioms StructuralS1RTiny20261018.Counting.actual_cumulative_of_pair
end
'''


def main():
    old1 = ROOT / 'StructuralResearch20261016/Coboundary.lean'
    old2 = ROOT / 'StructuralResearch20261016/CoboundaryCounting.lean'
    a = old1.read_text(encoding='utf-8')
    b = old2.read_text(encoding='utf-8')
    definition = cut(a, 'def SeparatedSummedCertificate', '/-- A bounded')
    band = cut(a, 'theorem block_energy_band_of_sum', 'theorem block_energy_band_summed')
    sorted_band = cut(a, 'theorem sorted_separated', '/-- Existing sparse Gram payment')
    remainder = cut(a, 'theorem remainder_bound_separated_summed', 'theorem remainder_bound_separated_coboundary')
    matching = cut(b, 'theorem block_remainder_bound_separated', '\nend Matching')
    actual = cut(b, 'theorem actual_defect_estimate_effective', '/-- Conditional counting conclusion')
    text = (HEADER + definition + PAIR_TO_SUM + band + sorted_band + remainder +
        'end Payment\n\nsection Matching\nopen Meshuggah.Gram\n'
        'variable {ι : Type} [Fintype ι] [DecidableEq ι]\n\n' +
        matching + 'end Matching\n\nopen Zeta23\n\n' + actual + WRAPPERS)
    out = ROOT / 'StructuralS1RTiny20261018/Counting.lean'
    out.parent.mkdir(exist_ok=True)
    assert not out.exists()
    out.write_text(text, encoding='utf-8', newline='\n')
    assert 'import GramDefect' not in text and 'import StructuralResearch' not in text
    assert 'sorry' not in text and 'axiom ' not in text and 'native_decide' not in text
    ast.parse(Path(__file__).read_text(encoding='utf-8'))
    manifest = {
        'schema': 'current-s1R-tiny-counting-preparation-v1',
        'files': [item(out), item(Path(__file__)), item(HERE/'INTERFACE.zh.md')],
        'read_dependencies': [item(p) for p in [old1, old2,
            ROOT/'research-goal-20261018-record-source-audit/snapshot/Solution.lean']],
        'future_import': {'module': 'StructuralS1RTiny20261018.Core',
            'present': (ROOT/'StructuralS1RTiny20261018/Core.lean').exists(),
            'required_identity': 'Current accepted s1R source f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf; same actual wfun/WCert/matching/current H/counting declarations, no old profile.'},
        'Lean_runs': 0, 'solver_or_FS_or_kernel_runs': 0,
        'generated_finite_payloads': False, 'ordinary_compile_passed': False,
        'conditional_pair_input_discharged': False,
        'new_unconditional_proportion_proved': False,
        'current_s1R_kernel_explicit': True, 'separation': '17/20',
        'short_pair_payment': '1/64', 'boundary_charge': 'delta=c-c9',
        'new_W10_ledger_required': False,
        'unchanged_old_proof_bodies_adapted_by_namespace_only': True,
        'source_bytes': len(text.encode('utf-8')),
        'baseline_bytes': 1818411,
        'baseline_plus_prepared_counting_bytes': 1818411 + len(text.encode('utf-8')),
        'remaining_before_2MB_excludes_future_finite_pair_root_and_wrapper':
            2000000 - 1818411 - len(text.encode('utf-8')),
        'no_compile_gate_yet': True}
    target = HERE/'prepared-files.json'
    with target.open('x', encoding='utf-8', newline='\n') as f:
        json.dump(manifest, f, indent=2)
        f.write('\n')
    print(json.dumps(item(target)))
    print(json.dumps(item(out)))


if __name__ == '__main__':
    main()
