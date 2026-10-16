"""Generalize Core's analytic cosine-window energy proof without new axioms.

The source is an attributed adaptation of the immutable Core proof. This driver
only generates source; ordinary Lean checking is a separate recorded step.
"""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
core = (ROOT / 'GramDefect20261015/Core.lean').read_text(encoding='utf-8')
start = core.index('theorem kernel_vAM {s : ℝ}')
stop = core.index('theorem euler_lagrange (n : ℕ)', start)
part1 = core[start:stop]
start2 = core.index('theorem energy_total :', stop)
stop2 = core.index('def HW : ℝ', start2)
part2 = core[start2:stop2]
part = part1 + part2
part = part.replace('Finset.range 12', 'Finset.range N')
part = part.replace('kernel_vAM', 'kernel_v').replace('vAM_add_kernel', 'v_add_kernel')
part = part.replace('integral_vAM_ek', 'integral_v_ek').replace('integral_vAM', 'integral_v')
part = part.replace('rV_continuous', 'r_continuous')
part = part.replace('vAM_continuous', '(v_continuous N d)')
part = part.replace("vAM_eq'", 'v_eq')
part = re.sub(r'\bvAM\b', 'V', part)
part = re.sub(r'\bdAM\b', 'd', part)
part = re.sub(r'\bbetaV\b', 'B', part)
part = re.sub(r'\brV\b', 'R', part)
part = re.sub(r'\bPAM\b', 'P', part)
part = part.replace('def B : ℝ :=', 'def beta (N : ℕ) (d : ℕ → ℝ) : ℝ :=')
part = part.replace('def R (s : ℝ) : ℝ :=', 'def r (N : ℕ) (d : ℕ → ℝ) (s : ℝ) : ℝ :=')
part = part.replace('theorem r_continuous', 'local notation "B" => beta N d\nlocal notation "R" => r N d\n\ntheorem r_continuous')
part = part.replace('theorem energy_total :', 'def penalty (N : ℕ) (d : ℕ → ℝ) : ℝ :=\n ∑ n ∈ Finset.range N, d n ^ 2 * (1 / 2 - 1 / (4 * π ^ 2 * ((n : ℝ) + 1) ^ 2))\n\nlocal notation "P" => penalty N d\n\ntheorem energy_total :')
part = part.replace('unfold R', 'unfold r').replace('unfold B R', 'unfold beta r')
part = part.replace('unfold B P', 'unfold beta penalty').replace('[alg, R,', '[alg, r,')
part = part.replace('continuous_const.add r_continuous', 'continuous_const.add (r_continuous N d)')
part = part.replace('kernel_v hs1 hs2', 'kernel_v N d hs1 hs2')
part = part.replace('v_add_kernel hs\'.1 hs\'.2', 'v_add_kernel N d hs\'.1 hs\'.2')
part = part.replace('integral_v_ek hn', 'integral_v_ek N d hn')
head = '''/- SPDX-License-Identifier: Apache-2.0
Arbitrary finite cosine-window energy identity.
Adapted from AMW.kernel_vAM through AMW.energy_total in the attributed Core.
The profile and both integrals are actual analytic functions, not premises.
No zero-counting or global gap floor is asserted by this module.
-/
import StructuralW10Followup20261016.NewWindows
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set MeasureTheory
open scoped BigOperators
open AMW
namespace StructuralGoal20261016.WindowEnergy

def v (N : ℕ) (d : ℕ → ℝ) (t : ℝ) : ℝ :=
 Real.cos (Real.sqrt 2 * t) + ∑ n ∈ Finset.range N, d n * AMW.ek n t

theorem v_continuous (N : ℕ) (d : ℕ → ℝ) : Continuous (v N d) := by
 unfold v
 exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).add
   (continuous_finsetSum _ fun n _ => continuous_const.mul (AMW.ek_continuous n))

variable (N : ℕ) (d : ℕ → ℝ)
local notation "V" => v N d

theorem v_eq (t : ℝ) :
 V t = Real.cos (Real.sqrt 2 * t) + ∑ n ∈ Finset.range N, d n * ek n t := rfl

'''
tail = '''
def H (N : ℕ) (d : ℕ → ℝ) : ℝ :=
  2 - ((∫ t in (-(1:ℝ)/2)..(1/2), v N d t ^ 2) +
    (∫ s in (-(1:ℝ)/2)..(1/2), v N d s *
      ∫ t in (-(1:ℝ)/2)..(1/2), |s-t| * v N d t)) /
    (∫ t in (-(1:ℝ)/2)..(1/2), v N d t) ^ 2

theorem H_eq : H N d =
  3 / 2 - Real.cos (Real.sqrt 2 / 2) /
    (Real.sqrt 2 * Real.sin (Real.sqrt 2 / 2)) -
    penalty N d / (2 * Real.sin (Real.sqrt 2 / 2) ^ 2) := by
  unfold H
  rw [energy_total, integral_v]
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hsin := AMW.sin_theta0_pos
  rw [mul_pow, hsq]
  field_simp
  ring_nf
  rw [hsq]
  ring

#print axioms kernel_v
#print axioms integral_v
#print axioms integral_v_ek
#print axioms energy_total
#print axioms H_eq
end StructuralGoal20261016.WindowEnergy
end
'''
out = ROOT / 'StructuralGoal20261016/WindowEnergy.lean'
out.write_text(head + part + tail, encoding='utf-8', newline='\n')
print(out.relative_to(ROOT), out.stat().st_size)
