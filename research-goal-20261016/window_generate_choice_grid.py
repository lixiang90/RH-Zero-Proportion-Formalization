"""Produce compact Horner corner masks for the frozen separated-cell oracle.

Masks are untrusted witnesses. Lean rechecks each selected product and its
final quantized derivative bounds using WindowCellDerivative.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import json,time
import cover_correlated_replay as replay
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent
Q=10**30;DS=10**15
J=json.loads((HERE/'window_normalized_interval.json').read_bytes())
W={int(n):[(int(F(a)*Q),int(F(b)*Q))for a,b in v]for n,v in J['integer_w_Taylor_coefficients'].items()}
old=json.loads((HERE/'cover_newjet.json').read_bytes());scalar=replay.ScalarReplay(old)
def add(I,J):return I[0]+J[0],I[1]+J[1]
def polynomial(n,k,q):
 d=23-q;X=((k-64*n)*Q//64,(k+1-64*n)*Q//64)
 C=[tuple(v*(factorial(j+q)//factorial(j))for v in W[n][j+q])for j in range(d+1)]
 value=C[d];mask=0
 for j in range(d-1,-1,-1):
  p=[value[0]*X[0],value[0]*X[1],value[1]*X[0],value[1]*X[1]]
  lo=p.index(min(p));hi=p.index(max(p));mask+=(lo+4*hi)*16**j
  value=add(C[j],(p[lo]//Q,-((-p[hi])//Q)))
 return value,mask
def main():
 t=time.monotonic();rows=[];margin=None
 for k in range(61,2048):
  n=(k+32)//64;v,m1=polynomial(n,k,1);z,m3=polynomial(n,k,3)
  R1=F(44,7)**24*F(1,2)**23/factorial(23);R3=F(44,7)**24*F(1,2)**21/factorial(21)
  dl,du=old['ranges'][k];M3=scalar.third[k]
  gaps=[F(v[0],Q)-R1-F(dl,DS),F(du,DS)-F(v[1],Q)-R1,F(M3,DS)-max(abs(F(z[0],Q)-R3),abs(F(z[1],Q)+R3))]
  assert min(gaps)>=0,(k,gaps)
  margin=min(gaps)if margin is None else min(margin,*gaps)
  rows.append([m1,m3,dl,du,M3])
 out={'scope':__doc__,'first_cell':61,'last_cell':2047,'rows':rows,'minimum_quantized_margin':str(margin),'ordinary_Lean_proven':False,'seconds':time.monotonic()-t}
 (HERE/'window_choice_grid.json').write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8')
 s='''/- SPDX-License-Identifier: Apache-2.0
Untrusted corner masks and frozen quantized separated-cell derivative bounds.
-/
import StructuralGoal20261016.WindowGridCertificate
set_option Elab.async false
set_option maxHeartbeats 0
namespace StructuralGoal20261016.WindowGridCertificateData
open WindowGridCertificate
'''
 G=(len(rows)+63)//64
 for g in range(G):s+=f'def rows{g:02} : List Row := ['+',\n '.join('⟨'+','.join(map(str,r))+'⟩'for r in rows[g*64:(g+1)*64])+']\n\n'
 s+='def row (i : ℕ) : Row :=\n match i/64 with\n'
 for g in range(G):s+=f' | {g} => rows{g:02}.getD (i%64) defaultRow\n'
 s+=' | _ => defaultRow\nend StructuralGoal20261016.WindowGridCertificateData\n'
 (ROOT/'StructuralGoal20261016/WindowGridCertificateData.lean').write_text(s,encoding='utf8',newline='\n')
 print(json.dumps({'cells':len(rows),'data_bytes':len(s.encode()),'minimum_margin':float(margin),'seconds':time.monotonic()-t}))
if __name__=='__main__':main()
