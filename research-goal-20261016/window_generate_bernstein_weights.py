"""Cache exact subinterval Bernstein weights; each cache equality is proved."""
from pathlib import Path
from fractions import Fraction as F
from math import comb
import json
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent
def q(x):x=F(x);return f'({x.numerator}/{x.denominator}:ℚ)'
mods=[]
for s in range(8):
 l=F(-21,100)+F(21,400)*s;h=F(21,400)
 def w(k,i):return sum(F(comb(i,j))*l**(i-j)*h**j*F(comb(k,j),comb(13,j))for j in range(min(i,k)+1))
 vals='['+',\n '.join('['+', '.join(q(w(k,i))for i in range(14))+']'for k in range(14))+']'
 name=f'WindowBernsteinWeights{s:02}'
 src=f'''/- SPDX-License-Identifier: Apache-2.0
Exact cached Bernstein weights for relative subinterval {s} of an integer well.
-/
import StructuralGoal20261016.WindowBernsteinLinear
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowBernsteinWeights
open WindowBernsteinLinear
def values{s} : List (List ℚ) := {vals}
def weights{s} (k i : ℕ) : ℚ := (values{s}.getD k []).getD i 0
theorem weights{s}_eq : ∀ k : Fin 14, ∀ i : Fin 14,
 weights{s} k i = weightQ {q(l)} {q(h)} k i := by
 intro k i
 fin_cases k <;> fin_cases i <;>
   norm_num [weights{s},values{s},weightQ,Finset.sum_range_succ,Nat.choose]
set_option pp.fullNames true
#print axioms weights{s}_eq
end StructuralGoal20261016.WindowBernsteinWeights
'''
 (ROOT/f'StructuralGoal20261016/{name}.lean').write_text(src,encoding='utf8',newline='\n')
 mods.append('StructuralGoal20261016.'+name)
(HERE/'window_bernstein_weight_modules.json').write_text(json.dumps(mods,indent=2)+'\n',encoding='utf8')
print(json.dumps({'modules':8,'entries':8*14*14,'bytes':sum((ROOT/(m.replace('.','/')+'.lean')).stat().st_size for m in mods)}))
