/- SPDX-License-Identifier: Apache-2.0
Only the real algebra at the end of the Fourier-minorant route is proved here.
The energy premise is explicit. This does not prove Poisson summation for
the candidate, the existence of an auxiliary h, or any new zeta bound.
Check the source hash and ordinary Lean verification receipt for this module.
-/
import GramDefect20261015.Core
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section

namespace StructuralW10Followup20261016.FourierMinorantTransfer

/-- Convert a density-square energy bound to a linear pressure payment.
`h0` denotes h(0), but no function h or analytic premise is hidden here. -/
theorem pressure_payment {E B H N R T h0 : ℝ}
    (hB : 0 ≤ B) (hH : 0 ≤ H) (_hN : 0 ≤ N)
    (hR : 0 ≤ R) (hT : 0 < T)
    (hE : H * N ^ 2 / (R + T) - h0 * N ≤ E) :
    (2 * Real.sqrt (B * H) - h0) * N - B * T ≤ E + B * R := by
  have hL : 0 < R + T := add_pos_of_nonneg_of_pos hR hT
  have hEmul : H * N ^ 2 ≤ (E + h0 * N) * (R + T) := by
    apply (div_le_iff₀ hL).mp
    linarith only [hE]
  have hs := sq_nonneg (Real.sqrt H * N - Real.sqrt B * (R + T))
  simp only [sub_sq, mul_pow, Real.sq_sqrt hH, Real.sq_sqrt hB] at hs
  have hquad : 2 * Real.sqrt (B * H) * N * (R + T) ≤
      H * N ^ 2 + B * (R + T) ^ 2 := by
    rw [Real.sqrt_mul hB H]
    nlinarith only [hs]
  by_contra hbad
  have hpos := mul_pos (sub_pos.mpr (lt_of_not_ge hbad)) hL
  nlinarith only [hEmul, hquad, hpos]

#print axioms pressure_payment
end StructuralW10Followup20261016.FourierMinorantTransfer
end
