"""Emit exact common-denominator aggregate data and small coefficient checks.

The aggregate is recomputed from actual selected atoms and the actual energy
packet, then compared against an untrusted integer row. No rounding is used.
"""
from pathlib import Path
from fractions import Fraction as F
import hashlib
import json
import argparse
from window_moment_frozen_write import write_lean

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
sha=lambda raw:hashlib.sha256(raw).hexdigest()
raw=(HERE/'cover-cross-moment-exact-aggregate.json').read_bytes()
assert sha(raw)=='dd86691b901c1f210054fb4de0992cba2d75a66cfab4561496e84f4a28769ee9'
cert=json.loads(raw)
case_raw=(HERE/'cover-cross-moment-factor-friendly-cases.json').read_bytes()
assert sha(case_raw)=='bf45540baf5919358a8a4182fe41c323be2157c89f3897f2620602a8581629a7'
cases=json.loads(case_raw)['cases']
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--hq-case',type=int,choices=[0,1],help='Rewrite only unproved H/Q tactics in this case; preserve every other source.')
ap.add_argument('--q-only',action='store_true',help='Together with --hq-case, preserve that case H source as well.')
ap.add_argument('--h-only',action='store_true',help='Together with --hq-case, rewrite only that case H source.')
ap.add_argument('--direct-h',action='store_true',help='Use the proved one/two-entry H collection formula in the selected H source.')
args=ap.parse_args()
def write(name,body):
 if args.hq_case is not None and name not in [f'WindowMomentAggregate{args.hq_case}{s}'for s in ['H','Q0','Q1','Q2']]:return
 if args.q_only and name.endswith('H'):return
 if args.h_only and not name.endswith('H'):return
 write_lean(ROOT/f'StructuralGoal20261016/{name}.lean',body)
opts='set_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
def vec(values):return '!['+','.join(f'({int(v)})'for v in values)+']'
source='''/- SPDX-License-Identifier: Apache-2.0
Untrusted exact integer aggregates. Every coefficient remains a finite
checking obligation against the sum of the actual grouped RLT/energy rows.
-/
import StructuralGoal20261016.WindowMomentFormSum
import StructuralGoal20261016.WindowMomentEnergyPolynomial
import StructuralGoal20261016.WindowMomentAtomsAll
import StructuralGoal20261016.WindowMomentBoxData
import StructuralGoal20261016.WindowMomentGlobalBox
import StructuralGoal20261016.WindowMomentExactInteger
'''+opts+'''namespace StructuralGoal20261016.WindowMomentAggregateData
open scoped BigOperators
open WindowMomentPolynomial WindowMomentAtomData WindowMomentEnergyData WindowMomentBoxData
def boxScale : ℤ := 32768000000000000000
'''
for k,(row,case) in enumerate(zip(cert['cases'],cases)):
 assert row['path']==case['path']
 n=len(case['factors']);D0=int(row['rational_row_denominator'])
 coeff=[0]*464
 for i,v in row['integer_coefficients']:coeff[i]=int(v)
 source+=f'''def groups{k} (i : Fin {n}) : RatForm :=
 grouped (WindowLiftedKKT.form cell{k} (atoms{k} i)) box{k}.center box{k}.radius
   ((factorA{k} i:ℚ)/(WindowDirectionalFlow.denominator:ℚ))
   (fun r => (factorB{k} i r:ℚ)/(WindowDirectionalFlow.denominator:ℚ))
def energy{k} : RatForm := WindowMomentFormSum.scale ({case['energy_weight']}:ℚ)
 (WindowMomentEnergyPolynomial.energyForm packet{k} box{k}.center box{k}.radius (11/1250))
def aggregate{k} : RatForm := WindowMomentFormSum.add
 (WindowMomentFormSum.sumForms groups{k}) energy{k}
def den{k} : ℤ := {D0}
'''
 for block in range(8):
  source+=f'def coeff{k}_{block:02} : List ℤ := ['+','.join(f'({v})'for v in coeff[block*64:(block+1)*64])+']\n'
 source+=f'def coeff{k} (i : Fin 464) : ℤ :=\n match (i:ℕ)/64 with\n'
 for block in range(8):source+=f' | {block} => coeff{k}_{block:02}.getD ((i:ℕ)%64) 0\n'
 source+=' | _ => 0\n'
 source+=f'def row{k} : WindowBoundedMomentFarkas.Row 464 := ⟨coeff{k},({row["integer_bound"]})⟩\n'
 lo,hi=case['cell']
 source+=f'def gapLower{k} : Fin 9 → ℤ := '+vec(v*10**15 for v in lo[:9])+'\n'
 source+=f'def gapUpper{k} : Fin 9 → ℤ := '+vec(v*10**15 for v in hi[:9])+'\n'
 source+=f'''def lower{k} (i : Fin 464) : ℤ :=
 if h0 : (i:ℕ) < 9 then gapLower{k} ⟨i,by omega⟩
 else if (i:ℕ) < 50 then -7*boxScale
 else if h2 : (i:ℕ) < 95 then
   if WindowMomentLayout.hFirst ⟨(i:ℕ)-50,by omega⟩ = WindowMomentLayout.hSecond ⟨(i:ℕ)-50,by omega⟩ then 0 else -boxScale
 else -7*boxScale
def upper{k} (i : Fin 464) : ℤ :=
 if h0 : (i:ℕ) < 9 then gapUpper{k} ⟨i,by omega⟩
 else if (i:ℕ) < 50 then 7*boxScale
 else if (i:ℕ) < 95 then boxScale else 7*boxScale
'''
source+='end StructuralGoal20261016.WindowMomentAggregateData\n'
write('WindowMomentAggregateData',source)
modules=['StructuralGoal20261016.WindowMomentAggregateData']
for k in range(2):
 for label,typ,idx in [('Gap','Fin 9','WindowMomentLayout.gapIndex j'),('Scalar','Fin 41','WindowMomentLayout.uIndex j'),('H','Fin 45','WindowMomentLayout.hIndex j')]:
  name=f'WindowMomentAggregate{k}{label}'
  tactic='decide +kernel'
  if label=='H':tactic=f'''
 have hf (j : Fin 45) : flatten aggregate{k} (WindowMomentLayout.hIndex j) = aggregate{k}.h j :=
   flatten_encode aggregate{k} (.inr (.inr (.inl j)))
 simp only [hf]
 simp only [aggregate{k},WindowMomentFormSum.add,WindowMomentFormSum.sumForms,
   groups{k},grouped,energy{k},WindowMomentFormSum.scale,
   WindowMomentEnergyPolynomial.energyForm,WindowMomentEnergyPolynomial.form,
   {'WindowMomentCollectHDirect.direct' if args.direct_h else 'collectH,Fintype.sum_prod_type'}]
 intro j
 fin_cases j <;> decide +kernel'''
  extra_import='import StructuralGoal20261016.WindowMomentCollectHDirect\n' if label=='H' and args.direct_h else ''
  source='/- SPDX-License-Identifier: Apache-2.0 -/\nimport StructuralGoal20261016.WindowMomentAggregateData\n'+extra_import+opts+f'''namespace StructuralGoal20261016.WindowMomentAggregateChecks
open WindowMomentAggregateData WindowMomentPolynomial
theorem check{k}{label} : ∀ j : {typ}, ((row{k}.coeff ({idx})):ℚ) =
 (den{k}:ℚ)*flatten aggregate{k} ({idx}) := by {tactic}
set_option pp.fullNames true
#print axioms check{k}{label}
end StructuralGoal20261016.WindowMomentAggregateChecks
'''
  write(name,source);modules.append('StructuralGoal20261016.'+name)
 for block in range(3):
  name=f'WindowMomentAggregate{k}Q{block}'
  source='/- SPDX-License-Identifier: Apache-2.0 -/\nimport StructuralGoal20261016.WindowMomentAggregateData\n'+opts+f'''namespace StructuralGoal20261016.WindowMomentAggregateChecks
open WindowMomentAggregateData WindowMomentPolynomial
theorem check{k}Q{block} : ∀ s : Fin 3, ∀ e : Fin 41,
 ((row{k}.coeff (WindowMomentLayout.qIndex ⟨{block}*3+(s:ℕ),by omega⟩ e)):ℚ) =
 (den{k}:ℚ)*flatten aggregate{k} (WindowMomentLayout.qIndex ⟨{block}*3+(s:ℕ),by omega⟩ e) := by
 have hf (s : Fin 3) (e : Fin 41) :
     flatten aggregate{k} (WindowMomentLayout.qIndex ⟨{block}*3+(s:ℕ),by omega⟩ e) =
       aggregate{k}.q ⟨{block}*3+(s:ℕ),by omega⟩ e :=
   flatten_encode aggregate{k} (.inr (.inr (.inr (⟨{block}*3+(s:ℕ),by omega⟩,e))))
 simp only [hf]
 simp only [aggregate{k},WindowMomentFormSum.add,WindowMomentFormSum.sumForms,
   groups{k},grouped,energy{k},WindowMomentFormSum.scale,
   WindowMomentEnergyPolynomial.energyForm,WindowMomentEnergyPolynomial.form]
 intro s e
 fin_cases s <;> fin_cases e <;> decide +kernel
set_option pp.fullNames true
#print axioms check{k}Q{block}
end StructuralGoal20261016.WindowMomentAggregateChecks
'''
  write(name,source);modules.append('StructuralGoal20261016.'+name)
 name=f'WindowMomentAggregate{k}Bounds'
 source='/- SPDX-License-Identifier: Apache-2.0 -/\nimport StructuralGoal20261016.WindowMomentAggregateData\n'+opts+f'''namespace StructuralGoal20261016.WindowMomentAggregateChecks
open WindowMomentAggregateData WindowMomentPolynomial
theorem check{k}Bound : (row{k}.bound:ℚ) = (den{k}:ℚ)*aggregate{k}.bound := by decide +kernel
theorem check{k}Scale : (0:ℤ) < den{k} := by decide +kernel
theorem check{k}Box : ∀ i : Fin 464,
 ((lower{k} i:ℚ)/(boxScale:ℚ)) = WindowMomentBox.lower (WindowMomentGlobalBox.global WindowMomentBoxData.box{k}) i ∧
 ((upper{k} i:ℚ)/(boxScale:ℚ)) = WindowMomentBox.upper (WindowMomentGlobalBox.global WindowMomentBoxData.box{k}) i := by decide +kernel
theorem check{k}Strict : WindowMomentExactInteger.strictCheck boxScale row{k} lower{k} upper{k} = true := by decide +kernel
set_option pp.fullNames true
#print axioms check{k}Bound
#print axioms check{k}Scale
#print axioms check{k}Box
#print axioms check{k}Strict
end StructuralGoal20261016.WindowMomentAggregateChecks
'''
 write(name,source);modules.append('StructuralGoal20261016.'+name)
out={'exact_aggregate_sha256':sha(raw),'grouped_cases_sha256':sha(case_raw),'modules':modules,
     'ordinary_Lean_verified':False,'actual_Lean_exclusions':False,'complete_global_cover':False}
if args.hq_case is None:(HERE/'window_moment_aggregate_modules.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
print(json.dumps({'generated_modules':len(modules),'actual_Lean_exclusions':False}))
