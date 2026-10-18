/-
SPDX-License-Identifier: Apache-2.0
Preparation only. Actual tiny s1R instance, independent of this development
runtime's older trusted CandidateSpec. No trusted constant is redefined.
Final website export requires a fresh trusted specification and Comparator.
-/
import StructuralS1RTiny20261018.Phase1.Localization
import StructuralS1RTiny20261018.Dev.Counting

set_option Elab.async false
set_option maxHeartbeats 0

noncomputable section
open Zeta23 Zeta23Ext.BridgeW

namespace StructuralS1RTiny20261018.Dev.Final

def tinyKappa : ℝ :=
  3337839448633819172184136761695440236797 /
    4955319193827760237900000000000000000000

/-- Literal frozen baseline, not a replacement for trusted currentRecordKappa. -/
def baselineKappa : ℝ :=
  3337839448633819172184136761695440236797 /
    4955319193847235264050000000000000000000

def pressure : ℝ := 456111945004000000 / 100000000000000000000

theorem strict_improvement : baselineKappa < tinyKappa := by
  norm_num [baselineKappa, tinyKappa]

private theorem hc : (0 : ℝ) < StructuralS1RTiny20261018.Dev.Localization.c := by
  norm_num [StructuralS1RTiny20261018.Dev.Localization.c,
    StructuralS1RTiny20261018.Dev.Localization.base,
    StructuralS1RTiny20261018.Dev.Localization.delta,
    AMW.Cert.PC9Tiny.cN, AMW.Cert.PC9Tiny.tinyDeltaN, AMW.Cert.PC9Tiny.SA]

private theorem hdelta : (0 : ℝ) ≤ StructuralS1RTiny20261018.Dev.Localization.delta := by
  norm_num [StructuralS1RTiny20261018.Dev.Localization.delta,
    AMW.Cert.PC9Tiny.tinyDeltaN, AMW.Cert.PC9Tiny.SA]

private theorem hdeltac : StructuralS1RTiny20261018.Dev.Localization.delta ≤
    StructuralS1RTiny20261018.Dev.Localization.c := by
  norm_num [StructuralS1RTiny20261018.Dev.Localization.c,
    StructuralS1RTiny20261018.Dev.Localization.base,
    StructuralS1RTiny20261018.Dev.Localization.delta,
    AMW.Cert.PC9Tiny.cN, AMW.Cert.PC9Tiny.tinyDeltaN, AMW.Cert.PC9Tiny.SA]

private theorem hc64 : StructuralS1RTiny20261018.Dev.Localization.c ≤ (1 : ℝ)/64 := by
  norm_num [StructuralS1RTiny20261018.Dev.Localization.c,
    StructuralS1RTiny20261018.Dev.Localization.base,
    StructuralS1RTiny20261018.Dev.Localization.delta,
    AMW.Cert.PC9Tiny.cN, AMW.Cert.PC9Tiny.tinyDeltaN, AMW.Cert.PC9Tiny.SA]

private theorem hB : RiemannFail.W9.B = pressure := by
  simpa only [pressure] using RiemannFail.W9_B

private theorem hbase (g : Fin 8 → ℝ) (hg : ∀ r, 0 ≤ g r) :
    StructuralS1RTiny20261018.Dev.Localization.c -
      StructuralS1RTiny20261018.Dev.Localization.delta ≤ Fw RiemannFail.W9 g := by
  simpa only [StructuralS1RTiny20261018.Dev.Localization.c, add_sub_cancel_right] using
    StructuralS1RTiny20261018.Dev.Localization.base_floor g hg

private theorem hpair (g : Fin 9 → ℝ) (hg : ∀ r, (17 : ℝ)/20 ≤ g r) :
    2 * StructuralS1RTiny20261018.Dev.Localization.c ≤
      Fw RiemannFail.W9 (StructuralS1RTiny20261018.Counting.leftGaps g) +
      Fw RiemannFail.W9 (StructuralS1RTiny20261018.Counting.rightGaps g) := by
  simpa only [StructuralS1RTiny20261018.Counting.leftGaps,
    StructuralS1RTiny20261018.Counting.rightGaps,
    StructuralS1RTiny20261018.Dev.Localization.leftGaps,
    StructuralS1RTiny20261018.Dev.Localization.rightGaps] using
      StructuralS1RTiny20261018.Dev.Localization.pair_floor g hg

private theorem ratio_exact :
    StructuralS1RTiny20261018.Counting.ratio
      StructuralS1RTiny20261018.Dev.Localization.c pressure = tinyKappa := by
  norm_num [StructuralS1RTiny20261018.Counting.ratio, pressure, tinyKappa,
    StructuralS1RTiny20261018.Dev.Localization.c,
    StructuralS1RTiny20261018.Dev.Localization.base,
    StructuralS1RTiny20261018.Dev.Localization.delta,
    AMW.Cert.PC9Tiny.cN, AMW.Cert.PC9Tiny.tinyDeltaN, AMW.Cert.PC9Tiny.SA]

theorem actual_dyadic :
    ∀ epsilon > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0,
      (tinyKappa - epsilon) * (Ncount T (2*T) : ℝ) ≤ N0star T (2*T) := by
  have h := StructuralS1RTiny20261018.Counting.actual_dyadic_of_pair
    RiemannFail.W9 RiemannFail.W9_adm hc hdelta hdeltac hc64 hB hbase hpair
  simpa only [ratio_exact] using h

theorem actual_cumulative :
    ∀ epsilon > (0 : ℝ), ∃ T0 : ℝ, ∀ T ≥ T0,
      (tinyKappa - epsilon) * (Ncount 0 T : ℝ) ≤ N0star 0 T := by
  have h := StructuralS1RTiny20261018.Counting.actual_cumulative_of_pair
    RiemannFail.W9 RiemannFail.W9_adm hc hdelta hdeltac hc64 hB hbase hpair
  simpa only [ratio_exact] using h

end StructuralS1RTiny20261018.Dev.Final

set_option pp.fullNames true
#print axioms AMW.Cert.PC9TinyData.run
#print axioms RiemannFail.cert_AM
#print axioms StructuralS1RTiny20261018.Dev.Localization.pair_floor
#print axioms StructuralS1RTiny20261018.Dev.Final.strict_improvement
#print axioms StructuralS1RTiny20261018.Dev.Final.actual_dyadic
#print axioms StructuralS1RTiny20261018.Dev.Final.actual_cumulative
end
