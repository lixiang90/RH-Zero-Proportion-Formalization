/- SPDX-License-Identifier: Apache-2.0
Concrete close-pair payment at the larger matching threshold 123/128.
The old kernel theorem covers [0,17/20]; the frozen lower-bound pyramid
covers the short added interval. Consult the source-bound kernel receipts.
This file does not assert any new separated W10 floor or zeta proportion.
-/
import StructuralW10Followup20261016.MatchingThreshold
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section
open Zeta23Ext.Bridge
namespace StructuralW10Followup20261016.KernelPair123128

theorem table_payment :
    86600000 ≤ AMW.Cert.Pyr.lb AMW.Cert.PC9QB6MData.TOP
      AMW.Cert.PC9QB6MData.BK 27852 31488 := by
  decide +kernel

/-- The complete interval, not just the new endpoint, pays 433/50000. -/
theorem kernel_square_ge {t : ℝ} (ht : |t| ≤ (123 / 128 : ℝ)) :
    (433 / 50000 : ℝ) ≤ wfun t := by
  by_cases hsmall : |t| ≤ (17 / 20 : ℝ)
  · have h : (1 / 64 : ℝ) ≤ wfun t := Opeth.AMClosePair.kernel_square_ge hsmall
    linarith
  · have hlo : (27852 : ℝ) / AMW.Cert.SC ≤ |t| := by
      norm_num only [AMW.Cert.SC]
      linarith only [lt_of_not_ge hsmall]
    have hhi : |t| ≤ (31488 : ℝ) / AMW.Cert.SC := by
      norm_num only [AMW.Cert.SC]
      linarith only [ht]
    have hlb := AMW.Cert.PC9QB6MData.lbS 27852 31488 |t| hlo hhi
    have hnum : (86600000 : ℝ) ≤
        (AMW.Cert.Pyr.lb AMW.Cert.PC9QB6MData.TOP
          AMW.Cert.PC9QB6MData.BK 27852 31488 : ℝ) := by
      exact_mod_cast table_payment
    have hpay : (433 / 50000 : ℝ) ≤ AMW.Cert.wfun |t| := by
      linarith only [hlb, hnum]
    have habs : wfun |t| = wfun t := by
      by_cases ht0 : 0 ≤ t
      · rw [abs_of_nonneg ht0]
      · rw [abs_of_neg (lt_of_not_ge ht0), wfun_neg]
    rw [RiemannFail.cert_wfun_eq, habs] at hpay
    exact hpay

theorem threshold_ge_original : (17 / 20 : ℝ) ≤ 123 / 128 := by norm_num

#print axioms table_payment
#print axioms kernel_square_ge
end StructuralW10Followup20261016.KernelPair123128
end
