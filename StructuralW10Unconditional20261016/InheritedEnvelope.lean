/- SPDX-License-Identifier: Apache-2.0
Connect directly decoded inherited PVI points to fixed affine minorants.
This adds no new analytic assumption and asserts no global W10 coverage.
-/
import StructuralW10Unconditional20261016.QuadraticEnvelope
import StructuralW10Cert20261016.LocalChecker

noncomputable section
open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell
namespace StructuralW10Unconditional20261016.InheritedEnvelope

def pointValue (word : ℕ) : ℝ := (lo32 (trip word) : ℝ) / 10000000000
def pointSlope (word : ℕ) : ℝ :=
  ((lo32 (hi32 (trip word)) : ℝ)-2000000000)/1000000000
def pointError (word : ℕ) : ℝ :=
  (4000000000-(lo32 (hi32 (trip word)) : ℝ)-(hi32 (hi32 (trip word)) : ℝ))/1000000000
def affine (p word : ℕ) (lower x : ℝ) : ℝ :=
  pointValue word+pointSlope word*(x-(p : ℝ)/SC)-
    pointError word*max ((p : ℝ)/SC-lower) 0

theorem pvi_affine {p word : ℕ} (hp : PVI p word) (hb : ivB word ≠ 0)
    {lower upper x : ℝ}
    (hl : (ivA word : ℝ)/SC ≤ lower) (hu : upper ≤ (ivB word : ℝ)/SC)
    (hxl : lower ≤ x) (hxu : x ≤ upper) : affine p word lower x ≤ wfun x := by
  obtain ⟨_, _, hs, he, htan⟩ := hp.2 hb
  have hsl : pointSlope word ≤ w1 ((p : ℝ)/SC) := by
    unfold pointSlope
    apply (div_le_iff₀ (by norm_num : (0 : ℝ)<1000000000)).mpr
    simpa only [mul_comm] using hs
  have hsu : w1 ((p : ℝ)/SC) ≤ pointSlope word+pointError word := by
    unfold pointSlope pointError
    linarith only [he]
  exact QuadraticEnvelope.uncertain_tangent hsl hsu hxl (htan x (hl.trans hxl) (hxu.trans hu))

/-- The original point table discharges the complete analytic input. -/
theorem frozen_affine (p : ℕ) (hb : ivB (PC9QB6MData.PT p) ≠ 0)
    {lower upper x : ℝ}
    (hl : (ivA (PC9QB6MData.PT p) : ℝ)/SC ≤ lower)
    (hu : upper ≤ (ivB (PC9QB6MData.PT p) : ℝ)/SC)
    (hxl : lower ≤ x) (hxu : x ≤ upper) :
    affine p (PC9QB6MData.PT p) lower x ≤ wfun x :=
  pvi_affine (PC9QB6MData.ptS p) hb hl hu hxl hxu

#print axioms pvi_affine
#print axioms frozen_affine
end StructuralW10Unconditional20261016.InheritedEnvelope
end
