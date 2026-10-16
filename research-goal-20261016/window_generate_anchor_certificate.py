"""Compact data and ordinary-kernel checks for the 1567 actual Gram anchors."""
from pathlib import Path
from fractions import Fraction as F
import json
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent
gram=json.loads((HERE/'cover-newwindow-gram.json').read_bytes());anchors={}
for g in gram['results']:
 for s in g['scalar_minorants']:
  p=F(s['anchor']);v=(F(s['value_lower']),F(s['slope']),F(s['slope_error_loss']),s['integer_center'])
  if p in anchors:assert anchors[p]==v
  anchors[p]=v
keys=list(anchors);B=64;N=len(keys);G=(N+B-1)//B
def q(x):x=F(x);return f'({x.numerator}/{x.denominator}:ℚ)'
def row(p):
 v,s,loss,m=anchors[p];n=round(p);e=loss/(F(21,100)+abs(p-m))
 return f'⟨{n},{q(p)},{q(v)},{q(s)},{q(e)}⟩'
data='''/- SPDX-License-Identifier: Apache-2.0
Untrusted compact rows for the frozen actual Gram anchor inequalities.
-/
import StructuralGoal20261016.WindowAnchorCertificate
set_option Elab.async false
set_option maxHeartbeats 0
namespace StructuralGoal20261016.WindowAnchorCertificateData
open WindowAnchorCertificate
'''
for g in range(G):data+=f'def rows{g:02} : List Row := ['+',\n '.join(row(p)for p in keys[g*B:(g+1)*B])+']\n\n'
data+='def row (i : ℕ) : Row :=\n match i/64 with\n'
for g in range(G):data+=f' | {g} => rows{g:02}.getD (i%64) defaultRow\n'
data+=' | _ => defaultRow\nend StructuralGoal20261016.WindowAnchorCertificateData\n'
(ROOT/'StructuralGoal20261016/WindowAnchorCertificateData.lean').write_text(data,encoding='utf8',newline='\n')
mods=['StructuralGoal20261016.WindowAnchorCertificate','StructuralGoal20261016.WindowAnchorCertificateData']
for g in range(G):
 name=f'WindowAnchorChecks{g:02}'
 src=f'''/- SPDX-License-Identifier: Apache-2.0
Actual value/slope finite checks for anchor indices {g*B}..{min((g+1)*B,N)-1}.
-/
import StructuralGoal20261016.WindowAnchorCertificateData
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace StructuralGoal20261016.WindowAnchorChecks
open WindowAnchorCertificate WindowAnchorCertificateData
theorem checks{g:02} : ∀ j : Fin 64, {g}*64+(j:ℕ) < {N} →
 check (row ({g}*64+(j:ℕ))) = true := by decide +kernel
set_option pp.fullNames true
#print axioms checks{g:02}
end StructuralGoal20261016.WindowAnchorChecks
'''
 (ROOT/f'StructuralGoal20261016/{name}.lean').write_text(src,encoding='utf8',newline='\n')
 mods.append('StructuralGoal20261016.'+name)
(HERE/'window_anchor_certificate_modules.json').write_text(json.dumps(mods,indent=2)+'\n',encoding='utf8')
(HERE/'window_anchor_map.json').write_text(json.dumps({str(p):i for i,p in enumerate(keys)},indent=2)+'\n',encoding='utf8')
print(json.dumps({'anchors':N,'chunks':G,'data_bytes':len(data.encode()),'source_bytes':sum((ROOT/(m.replace('.','/')+'.lean')).stat().st_size for m in mods)}))
