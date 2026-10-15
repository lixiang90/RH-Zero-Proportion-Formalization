/-
SPDX-License-Identifier: Apache-2.0

Affine support extraction for the inherited, proved TVal interface.
No numerical floor, finite coverage certificate, or new zeta bound is asserted.
-/
import GramDefect20261015.Core

noncomputable section

namespace StructuralResearch20261016.TangentSupport

/-- A tangent with an enclosed slope yields one affine lower bound throughout
an interval. The enclosure error is charged once at its left endpoint. -/
theorem affine_of_enclosed_tangent {value slope low high p L x E : ℝ}
    (hlow : low ≤ slope) (hhigh : slope ≤ high) (hx : L ≤ x)
    (htan : value + slope * (x - p) ≤ E) :
    value + low * (x - p) - (high - low) * max (p - L) 0 ≤ E := by
  have herr : 0 ≤ high - low := sub_nonneg.mpr (hlow.trans hhigh)
  have hmax : 0 ≤ max (p - L) 0 := le_max_right _ _
  have hmax' : p - L ≤ max (p - L) 0 := le_max_left _ _
  by_cases hxp : p ≤ x
  · have hmul := mul_le_mul_of_nonneg_right hlow (sub_nonneg.mpr hxp)
    have hpen : 0 ≤ (high - low) * max (p - L) 0 := mul_nonneg herr hmax
    nlinarith only [htan, hmul, hpen]
  · have hxp' : x ≤ p := le_of_not_ge hxp
    have hmul := mul_le_mul_of_nonpos_right hhigh (sub_nonpos.mpr hxp')
    have hdist : p - x ≤ max (p - L) 0 := by linarith only [hx, hmax']
    have hpen := mul_le_mul_of_nonneg_left hdist herr
    nlinarith only [htan, hmul, hpen]

open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD

/-- This is the real-valued support used by the exact exploratory replay.
`TVal` is the inherited kernel-checked analytic certificate. In particular,
the search program cannot invent a tangent by supplying its decimal value. -/
theorem affine_of_TVal {f : ℕ → ℕ} {L U p : ℕ}
    (h : TVal f L U p) {s left : ℝ}
    (hsL : (L : ℝ) / SC ≤ s) (hsU : s ≤ (U : ℝ) / SC)
    (hleft : left ≤ s) :
    (lo32 (f p) : ℝ) / 10000000000 +
      (((lo32 (hi32 (f p)) : ℝ) - 2000000000) / 1000000000) *
        (s - (p : ℝ) / SC) -
      ((4000000000 - (lo32 (hi32 (f p)) : ℝ) - (hi32 (hi32 (f p)) : ℝ)) /
        1000000000) * max ((p : ℝ) / SC - left) 0 ≤ AMW.Cert.wfun s := by
  obtain ⟨_, _, hlo, hhi, ht⟩ := h
  have hlo' : ((lo32 (hi32 (f p)) : ℝ) - 2000000000) / 1000000000 ≤
      AMW.Cert.w1 ((p : ℝ) / SC) := by linarith only [hlo]
  have hhi' : AMW.Cert.w1 ((p : ℝ) / SC) ≤
      (2000000000 - (hi32 (hi32 (f p)) : ℝ)) / 1000000000 := by
    linarith only [hhi]
  have hh := affine_of_enclosed_tangent hlo' hhi' hleft (ht s hsL hsU)
  convert hh using 1 <;> ring

end StructuralResearch20261016.TangentSupport

end
