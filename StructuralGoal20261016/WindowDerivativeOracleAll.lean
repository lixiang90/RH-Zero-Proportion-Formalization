/- SPDX-License-Identifier: Apache-2.0
Fully connected scalar directional-oracle consumers. Both premises are
finite Boolean certificate checks; all actual Fourier coefficients and
all selected whole-cell third-derivative bounds are supplied by checked
integer-centre and separated-grid theorems.
-/
import StructuralGoal20261016.WindowGridAll
import StructuralGoal20261016.WindowDerivativeAffineOracle
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowDerivativeOracleAll

theorem affine {n k0 k1 : ℕ} {a b p v s M E L U : ℚ}
 (hpoint : WindowDerivativeAffineOracle.check n a b p v s M E = true)
 (hgrid : WindowGridRange.check k0 k1 a b L U M = true)
 {x : ℝ} (hx : x ∈ Icc (a:ℝ) b) :
 |WindowGapEnergy.w1 x-((v:ℝ)+(s:ℝ)*(x-p))| ≤ (E:ℝ) :=
 WindowDerivativeAffineOracle.actual hpoint
   (fun y hy => (WindowGridAll.range_sound hgrid hy).2.2) hx

theorem interval {k0 k1 : ℕ} {a b L U M v E : ℚ}
 (hgrid : WindowGridRange.check k0 k1 a b L U M = true)
 (hl : v-E ≤ L) (hu : U ≤ v+E)
 {x : ℝ} (hx : x ∈ Icc (a:ℝ) b) : |WindowGapEnergy.w1 x-(v:ℝ)| ≤ (E:ℝ) := by
 have h := WindowGridAll.range_sound hgrid hx
 have hl' : ((v-E:ℚ):ℝ) ≤ (L:ℝ) := Rat.cast_le.mpr hl
 have hu' : (U:ℝ) ≤ ((v+E:ℚ):ℝ) := Rat.cast_le.mpr hu
 push_cast at hl' hu'
 rw [abs_le]
 constructor <;> linarith [h.1,h.2.1]

set_option pp.fullNames true
#print axioms affine
#print axioms interval
end StructuralGoal20261016.WindowDerivativeOracleAll
end
