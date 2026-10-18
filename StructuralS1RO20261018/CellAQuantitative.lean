/- SPDX-License-Identifier: Apache-2.0
Quantitative form of the current s1R CellA second-derivative enclosure.
Only the actual current-prefix definitions are imported.
-/
import StructuralS1RM20261018.CurrentPrefix
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open AMW AMW.G
namespace StructuralS1RO20261018.CellAQuantitative

def lower (c : CellA) : ℝ := 2 * c.W2L.v / (DZ : ℝ)^2

/-- Preserve the numerical lower endpoint that `CellA.w2_nonneg` discards.
No sign hypothesis on W2L is needed for this quantitative enclosure. -/
theorem lower_le_w2 (c : CellA) (hc : c.ok = true)
    (hE2 : 0 < c.E2L) (hE3 : 0 < c.E3L) {x : ℝ}
    (hx1 : (c.LN : ℝ) / SC ≤ x) (hx2 : x ≤ (c.UN : ℝ) / SC) :
    lower c ≤ w2AM x := by
  have hD := DZ_pos
  have hK1 := c.K1_enc hc hE2 hx1 hx2
  have hKK := IV.enc_mul (c.K0_enc hc hx1 hx2)
    (c.K2_enc hc hE2 hE3 hx1 hx2)
  have hs0 := mabs_nonneg c.K1
  have hsk := mabs_le hK1
  have hsq : (mabs c.K1).v * (mabs c.K1).v ≤
      (k1AM x)^2 * (DZ : ℝ)^2 := by
    have h := mul_le_mul hsk hsk hs0 (hs0.trans hsk)
    rw [show |k1AM x| * DZ * (|k1AM x| * DZ) =
      |k1AM x|^2 * DZ^2 by ring, sq_abs] at h
    exact h
  have hq := hKK.1
  have hq' : (c.K0.mul c.K2).lo.v ≤
      (kfunAM x * k2AM x) * DZ := (div_le_iff₀ hD).mp hq
  have hkk : (c.K0.mul c.K2).lo.v * DZ ≤
      (kfunAM x * k2AM x) * (DZ : ℝ)^2 := by
    have h := mul_le_mul_of_nonneg_right hq' hD.le
    nlinarith only [h]
  have hbound : c.W2L.v ≤
      ((k1AM x)^2 + kfunAM x * k2AM x) * (DZ : ℝ)^2 := by
    rw [AMW.G.CellA.W2L_eq, SZ.v_add, SZ.v_mul, SZ.v_muln]
    nlinarith only [hsq, hkk]
  have hD2 : (0 : ℝ) < (DZ : ℝ)^2 := by positivity
  unfold lower
  apply (div_le_iff₀ hD2).mpr
  unfold w2AM
  nlinarith only [hbound]

theorem lower_nonneg (c : CellA) (hW : c.W2L.nonneg = true) :
    0 ≤ lower c := by
  have h := (SZ.nonneg_iff _).mp hW
  unfold lower
  exact div_nonneg (mul_nonneg (by norm_num) h) (sq_nonneg _)

/-- Direct entry point from the existing `convOk` certificate.
The old boolean still supplies all CellA and positive-denominator guards. -/
theorem cellN_lower (c : AMW.Cert.CellN) (hc : c.convOk = true) {x : ℝ}
    (hx1 : (c.LN : ℝ) / AMW.Cert.SC ≤ x)
    (hx2 : x ≤ (c.UN : ℝ) / AMW.Cert.SC) :
    0 ≤ lower c.A ∧ lower c.A ≤ AMW.Cert.w2 x := by
  simp only [AMW.Cert.CellN.convOk, AMW.Cert.CellN.okD,
    Bool.and_eq_true, Nat.blt_eq] at hc
  obtain ⟨⟨⟨hok, hE2⟩, hE3⟩, hW⟩ := hc
  refine ⟨lower_nonneg c.A hW, ?_⟩
  exact lower_le_w2 c.A hok hE2 hE3 hx1 hx2

set_option pp.fullNames true
#print axioms lower_le_w2
#print axioms lower_nonneg
#print axioms cellN_lower
end StructuralS1RO20261018.CellAQuantitative
end
