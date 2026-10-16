/- SPDX-License-Identifier: Apache-2.0
Actual minimizers survive a certified affine directional Newton step.
The two flow bounds and rational outward rounding are finite certificate
obligations. The vanishing derivative comes from actual global minimality
and support strictly inside the original separated orthant.
-/
import StructuralGoal20261016.WindowDirectionalAffine
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real
open scoped BigOperators
namespace StructuralGoal20261016.WindowNewtonRetention
open WindowDirectionalAffine
open StructuralW10Followup20261016.NewLedger (W)

theorem retain {sep : ℝ} {g : Fin 9 → ℝ}
 (hg : WindowMinimizerCover.Relevant sep g) (d : Fin 9 → ℝ)
 (hsupport : ∀ r, d r ≠ 0 → sep < g r)
 (a b epsilon : Fin 41 → ℝ)
 (hscalar : ∀ e, |WindowGapEnergy.w1 (WindowGramTransfer.span g e)-
   (a e+b e*WindowGramTransfer.span g e)| ≤ epsilon e)
 (i : Fin 9) (C tau R E L U lower upper : ℝ)
 (htau : 0 < tau) (herror : error d epsilon ≤ E)
 (hmodel : intercept d a+∑ r, coefficient d b r*g r = C+tau*g i+R)
 (hrest : L ≤ R ∧ R ≤ U)
 (hroundLower : lower ≤ (-E-C-U)/tau)
 (hroundUpper : (E-C-L)/tau ≤ upper) : lower ≤ g i ∧ g i ≤ upper := by
 have hz := zero_at_relevant hg d hsupport
 have he := (enclosure g d a b epsilon hscalar).trans herror
 rw [hz,hmodel] at he
 obtain ⟨hl,hu⟩ := abs_le.mp he
 have hlo : (-E-C-U)/tau ≤ g i := by
   apply (div_le_iff₀ htau).mpr
   nlinarith [hrest.2]
 have hhi : g i ≤ (E-C-L)/tau := by
   apply (le_div_iff₀ htau).mpr
   nlinarith [hrest.1]
 exact ⟨hroundLower.trans hlo,hhi.trans hroundUpper⟩

theorem boundary_face {sep : ℝ} {g : Fin 9 → ℝ}
 (hg : WindowMinimizerCover.Relevant sep g) (d : Fin 9 → ℝ) (i : Fin 9)
 (hsupport : ∀ r, d r ≠ 0 → r ≠ i → sep < g r)
 (a b epsilon : Fin 41 → ℝ)
 (hscalar : ∀ e, |WindowGapEnergy.w1 (WindowGramTransfer.span g e)-
   (a e+b e*WindowGramTransfer.span g e)| ≤ epsilon e)
 (hnegative : (intercept d a+∑ r, coefficient d b r*g r)+error d epsilon < 0) :
 g i = sep := by
 by_contra hne
 have hi : sep < g i := lt_of_le_of_ne (hg.1 i) (Ne.symm hne)
 have hz := zero_at_relevant hg d (by
   intro r hr
   by_cases hri : r = i
   · simpa only [hri] using hi
   · exact hsupport r hr hri)
 have he := (abs_le.mp (enclosure g d a b epsilon hscalar)).2
 rw [hz] at he
 linarith

set_option pp.fullNames true
#print axioms retain
#print axioms boundary_face
end StructuralGoal20261016.WindowNewtonRetention
end
