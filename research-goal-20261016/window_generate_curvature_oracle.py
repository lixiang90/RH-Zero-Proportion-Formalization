"""Write the order-two analogue of the frozen actual derivative oracle.

Only a new module is written. Existing passed sources are read-only inputs.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
original = (ROOT / 'StructuralGoal20261016/WindowDerivativeAffineOracle.lean').read_text(encoding='utf8')
local = original[original.index('theorem local_remainder'):original.index('def pointBox')]
local = local.replace('WindowGapEnergy.w1', '(iteratedDeriv 2 f)')
local = local.replace('iteratedDeriv 3 f', 'iteratedDeriv 4 f')
local = local.replace('iteratedDeriv 2 f p', 'iteratedDeriv 3 f p')
# Restore the order-two function values changed by the previous replacement.
local = local.replace('(iteratedDeriv 3 f p)', '(iteratedDeriv 2 f p)')
local = local.replace('iterated_one_eq', 'iterated_two_eq_unused')
local = local.replace('rw [← iterated_two_eq_unused,iterated_iterated]', 'rw [iterated_iterated]')
local = local.replace('hthird', 'hfourth')
local = local.replace('taylor_one', 'taylor_two')

tail = original[original.index('def radius'):original.index('set_option pp.fullNames true')]
tail = tail.replace('pointError n 1 22 p v', 'WindowDerivativeAffineOracle.pointError n 2 21 p v')
tail = tail.replace('pointError n 2 21 p s', 'WindowDerivativeAffineOracle.pointError n 3 20 p s')
tail = tail.replace('iteratedDeriv 3 f', 'iteratedDeriv 4 f')
tail = tail.replace('WindowGapEnergy.w1', '(iteratedDeriv 2 f)')
tail = tail.replace('hthird', 'hfourth')
tail = tail.replace('have hv := point_error hh.1 hh.2.1 (by norm_num : 1+22+1 = 24) p v\n rw [iterated_one_eq] at hv',
    'have hv := WindowDerivativeAffineOracle.point_error hh.1 hh.2.1 (by norm_num : 2+21+1 = 24) p v')
tail = tail.replace('have hs := point_error hh.1 hh.2.1 (by norm_num : 2+21+1 = 24) p s',
    'have hs := WindowDerivativeAffineOracle.point_error hh.1 hh.2.1 (by norm_num : 3+20+1 = 24) p s')

head = '''/- SPDX-License-Identifier: Apache-2.0
Actual local affine enclosures for the second derivative of the new
window. Point errors use the same frozen normalized coefficients and
the proved order-24 remainder. A whole-cell fourth-derivative bound
is the only analytic input and will be supplied by selected checked cells.
-/
import StructuralGoal20261016.WindowDerivativeAffineOracle
import StructuralGoal20261016.WindowSecondVariation
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowCurvatureOracle
open WindowScalarMinorant WindowConvexityCertificate

theorem smooth (r : ℕ) : ContDiff ℝ r (iteratedDeriv 2 f) :=
 w_iterated_contDiff 24 WindowKernel.d24 2 r

theorem hasDerivAt (x : ℝ) :
 HasDerivAt (iteratedDeriv 2 f) (iteratedDeriv 3 f x) x :=
 WindowFiniteMoveScalar.w_iterated_hasDerivAt 2 x

theorem taylor_two (p x : ℝ) :
 taylorPoly (iteratedDeriv 2 f) 1 p x =
 iteratedDeriv 2 f p+iteratedDeriv 3 f p*(x-p) := by
 simp only [taylorPoly,Finset.sum_range_succ,Finset.sum_range_zero,
   zero_add,Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,div_one,
   pow_zero,pow_one,mul_one,iteratedDeriv_zero,iteratedDeriv_one]
 rw [(hasDerivAt p).deriv]

'''
end = '''theorem actual_w2 {n : ℕ} {a b p v s M E : ℚ}
 (hc : check n a b p v s M E = true)
 (hfourth : ∀ y ∈ Icc (a:ℝ) b, |iteratedDeriv 4 f y| ≤ (M:ℝ))
 {x : ℝ} (hx : x ∈ Icc (a:ℝ) b) :
 |WindowSecondVariation.w2 x-((v:ℝ)+(s:ℝ)*(x-p))| ≤ (E:ℝ) := by
 rw [WindowSecondVariation.w2_eq_actual]
 exact actual hc hfourth hx

set_option pp.fullNames true
#print axioms local_remainder
#print axioms affine_enclosure
#print axioms actual
#print axioms actual_w2
end StructuralGoal20261016.WindowCurvatureOracle
end
'''
(ROOT/'StructuralGoal20261016/WindowCurvatureOracle.lean').write_text(head+local+tail+end,encoding='utf8',newline='\n')
print('WindowCurvatureOracle.lean written; not yet Lean checked')
