"""Untrusted raw integer endpoints for fast use of the proved W table."""
from pathlib import Path
from fractions import Fraction as F
import json
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent;Q=10**30
J=json.loads((HERE/'window_normalized_interval.json').read_bytes())
s='''/- SPDX-License-Identifier: Apache-2.0
Untrusted integer endpoints for already checked normalized w coefficients.
A separate finite equality check connects these literals to the rational table.
-/
import StructuralGoal20261016.WindowFixedInterval
set_option Elab.async false
set_option maxHeartbeats 0
namespace StructuralGoal20261016.WindowRawCoefficientData
open WindowFixedInterval
def iw (l width : ℤ) : FI := (l,l+width)
def values : List (List FI) := [
'''
rows=[]
for n in range(1,33):
 values=[]
 for l,u in J['integer_w_Taylor_coefficients'][str(n)]:
  a,b=F(l)*Q,F(u)*Q;assert a.denominator==b.denominator==1
  values.append(f'iw ({a.numerator}) ({b.numerator-a.numerator})')
 rows.append('['+', '.join(values)+']')
s+=',\n '.join(rows)+']\n\ndef W (n r : ℕ) : FI := (values.getD (n-1) []).getD r (0,0)\nend StructuralGoal20261016.WindowRawCoefficientData\n'
(ROOT/'StructuralGoal20261016/WindowRawCoefficientData.lean').write_text(s,encoding='utf8',newline='\n')
print(json.dumps({'centres':32,'coefficients':768,'source_bytes':len(s.encode())}))
