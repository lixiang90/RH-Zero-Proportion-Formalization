"""Assemble the sixteen actual convexity wells and their rational lower bounds."""
from pathlib import Path
from fractions import Fraction as F
import json
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent
J=json.loads((HERE/'window_normalized_interval.json').read_bytes())
s='/- SPDX-License-Identifier: Apache-2.0\nThe actual second derivative is bounded below on every required integer well.\n-/\n'
s+=''.join(f'import StructuralGoal20261016.WindowLinearConvexityPiece{n:02}\n'for n in range(1,17))
s+='''set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
open Real Set
namespace StructuralGoal20261016.WindowConvexityAll
open WindowLinearConvexityPieces WindowConvexityCertificate
def lower (n : ℕ) : ℚ := match n with
'''
for n in range(1,17):
 q=F(J['curvature_checks'][n-1]['original_twice_alpha']);s+=f' | {n} => ({q.numerator}/{q.denominator}:ℚ)\n'
s+=''' | _ => 0

theorem lower_sound {n : ℕ} (hn0 : 1 ≤ n) (hn1 : n ≤ 16) :
 ∀ x ∈ Icc ((n:ℝ)-21/100) ((n:ℝ)+21/100), (lower n:ℝ) ≤ wSecond x := by
 interval_cases n
'''
for n in range(1,17):s+=f' · convert second_lower_{n} using 1 <;> norm_num [lower]\n'
s+='set_option pp.fullNames true\n#print axioms lower_sound\nend StructuralGoal20261016.WindowConvexityAll\nend\n'
(ROOT/'StructuralGoal20261016/WindowConvexityAll.lean').write_text(s,encoding='utf8',newline='\n')
print(len(s.encode()))
