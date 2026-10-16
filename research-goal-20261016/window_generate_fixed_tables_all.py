"""Assemble the 32 separately checked integer centre coefficient tables."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
s='/- SPDX-License-Identifier: Apache-2.0\nActual normalized coefficients at every required integer centre.\n-/\n'
s+=''.join(f'import StructuralGoal20261016.WindowFixedKernelCenter{n:02}\n'for n in range(1,33))
s+='''set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
namespace StructuralGoal20261016.WindowFixedTablesAll
open WindowRationalInterval WindowNormalizedJets WindowJetTableData WindowFixedKernelCenters
'''
for k,t in [('k','K'),('w','W')]:
 s+=f'''\ntheorem {k}_sound {{n : ℕ}} (hn0 : 1 ≤ n) (hn1 : n ≤ 32) (r : ℕ) (hr : r ≤ 23) :
 Holds ({t} n r) ({k}c 24 WindowKernel.d24 r (n:ℝ)) := by
 interval_cases n
'''
 for n in range(1,33):s+=f' · simpa only [Nat.cast_one,Nat.cast_ofNat] using {k}_{n} r hr\n'
 s+=f'set_option pp.fullNames true\n#print axioms {k}_sound\n'
s+='end StructuralGoal20261016.WindowFixedTablesAll\nend\n'
(ROOT/'StructuralGoal20261016/WindowFixedTablesAll.lean').write_text(s,encoding='utf8',newline='\n')
print(len(s.encode()))
