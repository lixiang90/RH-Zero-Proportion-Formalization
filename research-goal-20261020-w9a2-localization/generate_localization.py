"""Prepare actual W9A2 separated localization by source-text conversion only."""
from pathlib import Path
from hashlib import sha256
import json
import os

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
OLD=ROOT/'StructuralS1RTiny20261018/Production/Localization.lean'
OUT=ROOT/'StructuralW9A220261020/Localization.lean'
def write(path,data):
    with path.open('xb') as h: h.write(data);h.flush();os.fsync(h.fileno())
def main():
    assert not OUT.exists()
    old=OLD.read_text(encoding='utf-8')
    # Only the already-proved symbolic root/pressure argument is reused.
    # Every old numerical exception lemma and every old numeric constant is omitted.
    body=old[old.index('def pressure '):old.index('theorem ordered_exception ')]
    body=body.replace('tinyTauN','qGoodTarget').replace('tinyDeltaN','qGoodIncrement')
    body=body.replace('TinyGoal','QuantGoal').replace('PC9Tiny','PC9QB6M')
    body=body.replace('[qGoodTarget, qGoodIncrement, cN, sep, BS,','[qGoodTarget, qGoodIncrement, cN, sep, BS,')
    header='''/- SPDX-License-Identifier: Apache-2.0
Preparation only. W9A2 actual-kernel quantitative localization, including
all original separated root-exterior branches and reflected orientations.
The symbolic root argument derives from the attributed accepted root_cover.
No new numerical payload, anchor, guard or kernel evaluation is introduced.
No compiler or kernel has checked this generated file yet.
-/
import StructuralW9A220261020.Graph

set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Finset
open AMW.Cert AMW.Cert.PCell
open AMW.Cert.PC9QB6M AMW.Cert.PC9QB6MData
open Zeta23Ext.BridgeW
open StructuralW9A220261020.Graph

namespace StructuralW9A220261020.Localization
def sep : ℝ := 17 / 20
def base : ℝ := (cN : ℝ) / SA
def goodThreshold : ℝ := (qGoodTarget : ℝ) / SA
def dagThreshold : ℝ := ((cN + qDagIncrement : ℕ) : ℝ) / SA

'''
    tail='''theorem ordered_quant (g : ℕ → ℝ) (hsep : ∀ r < 8, sep ≤ g r)
    (horder : g 0 ≤ g 7) :
    (qGoodTarget : ℝ) ≤ Fg 8 BS TS g ∨
      ∃ k, k < 24 ∧ InCell 8 PR (qCell k) g ∧
        ((cN + qCost k : ℕ) : ℝ) ≤ Fg 8 BS TS g := by
  rcases root_QuantGoal g hsep with h | ⟨k, hk, hc, h⟩
  · rcases h with h | h
    · exact Or.inl h
    · exact False.elim ((not_lt_of_ge horder) h)
  · rcases h with h | h
    · exact Or.inr ⟨k, hk, hc, h⟩
    · exact False.elim ((not_lt_of_ge horder) h)

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
  simpa [reverse8] using AMW.Cert.PC9QB6M_G_rev
    (g 0) (g 1) (g 2) (g 3) (g 4) (g 5) (g 6) (g 7)

theorem finite_ordered_quant (g : Fin 8 → ℝ) (hsep : ∀ r, sep ≤ g r)
    (horder : g 0 ≤ g 7) :
    goodThreshold ≤ Fw RiemannFail.W9 g ∨
      ∃ k, k < 24 ∧ InCell 8 PR (qCell k) (natGaps g) ∧
        ((cN + qCost k : ℕ) : ℝ) / SA ≤ Fw RiemannFail.W9 g := by
  have hsep' : ∀ r < 8, sep ≤ natGaps g r := by
    intro r hr
    rw [natGaps_apply g hr]
    exact hsep _
  have horder' : natGaps g 0 ≤ natGaps g 7 := by simpa [natGaps] using horder
  have hSA : (0 : ℝ) < SA := by norm_num [SA]
  rcases ordered_quant (natGaps g) hsep' horder' with h | ⟨k, hk, hc, h⟩
  · left
    rw [scaled_energy] at h
    exact (div_le_iff₀ hSA).2 (by simpa only [mul_comm] using h)
  · right
    refine ⟨k, hk, hc, ?_⟩
    rw [scaled_energy] at h
    exact (div_le_iff₀ hSA).2 (by simpa only [mul_comm] using h)

theorem base_floor (g : Fin 8 → ℝ) (hg : ∀ r, 0 ≤ g r) :
    base ≤ Fw RiemannFail.W9 g := by
  simpa [base, cN, SA] using RiemannFail.cert_AM g hg

'''
    text=header+body+tail
    # The actual StateAt constructor tail is stored separately for review and
    # appended once the Graph interface is fixed; no placeholder theorem exists.
    write(HERE/'Localization-prefix.lean.txt',text.encode('utf-8'))
    print(json.dumps({'status':'PREFIX_PREPARED_ONLY_NOT_COMPILED','bytes':len(text.encode()),'sha256':sha256(text.encode()).hexdigest(),'Graph_constructor_tail_pending':True}))

if __name__=='__main__':main()
