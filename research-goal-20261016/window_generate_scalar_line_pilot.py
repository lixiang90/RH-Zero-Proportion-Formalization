"""Small actual constant/tangent pilots; no global partition is asserted.

Constant floors are taken from the original independent sinc oracle, while
their point intervals are recomputed from the frozen 10^-30 K table using
the same integer Horner arithmetic and 22/7 Taylor errors as the Lean check.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import hashlib,json,re
import window_global_cover as cover

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;S=10**30;SC=32768
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def floor(x):return x.numerator//x.denominator
def ceil(x):return -floor(-x)
def q(x):
    x=F(x);return f'({x.numerator}/{x.denominator}:ℚ)'
def scale(a,x):
    a0,a1=a
    if x<0:a0,a1=a1,a0
    return floor(a0*x),ceil(a1*x)
def poly(c,x):
    lo,hi=0,0
    for a,b in reversed(c):
        lo,hi=scale((lo,hi),x);lo+=a;hi+=b
    return lo,hi

def main():
    table=ROOT/'StructuralGoal20261016/WindowJetTableData.lean'
    text=table.read_text(encoding='utf8').split('def kValues :',1)[1].split('def wValues :',1)[0]
    values=[tuple(map(int,m))for m in re.findall(r'qi30 \((-?\d+)\) \((-?\d+)\)',text)]
    assert len(values)==33*24
    constants=[];lines=['/- Generated actual scalar checks. Partial pilots only. -/',
      'import StructuralGoal20261016.WindowScalarLine','set_option Elab.async false',
      'set_option maxHeartbeats 0','set_option maxRecDepth 100000',
      'namespace StructuralGoal20261016.WindowScalarLinePilot']
    for k,p0 in enumerate([F(9,8),F(21,8),F(67,8),F(63,4)]):
        p=int(p0*SC);l,u=p-32,p+32;n=round(p0);delta=p0-n
        coeff=values[n*24:(n+1)*24]
        v=poly(coeff,delta)
        d=poly([scale(coeff[j+1],F(j+1))for j in range(23)],delta)
        ev=F(22,7)**24*abs(delta)**24/factorial(24)
        ed=F(22,7)**24*abs(delta)**23/factorial(23)
        qs=10**20
        kl=F(floor((F(v[0],S)-ev)*qs),qs);ku=F(ceil((F(v[1],S)+ev)*qs),qs)
        dl=F(floor((F(d[0],S)-ed)*qs),qs);du=F(ceil((F(d[1],S)+ed)*qs),qs)
        r=F(32,SC);error=max(abs(dl),abs(du))*r+2*r*r
        low,up=kl-error,ku+error
        value=cover.constant_lower(l,u)
        assert (0<=low and F(value,10**10)<=low*low)or(up<=0 and F(value,10**10)<=up*up)
        assert value>0
        lines += [f'def c{k} : WindowConstantSupport.Support :=',
          f'  ⟨{n},{p},{q(kl)},{q(ku)},{q(dl)},{q(du)},{q(r)},{value}⟩',
          f'theorem constant_check{k} : WindowScalarLine.check (.constant c{k}) {l} {u} = true := by decide +kernel',
          f'theorem constant_bound{k} (x : ℝ) (hx : ({l}:ℝ)/32768 ≤ x ∧ x ≤ ({u}:ℝ)/32768) :',
          f'    ({value}:ℝ)/10000000000 ≤ WindowKernel.w 24 WindowKernel.d24 x :=',
          f'  WindowConstantSupport.sound constant_check{k} hx']
        constants.append({'center':n,'anchor':p,'lower':l,'upper':u,'k_lower':str(kl),'k_upper':str(ku),
          'd_lower':str(dl),'d_upper':str(du),'radius':str(r),'original_value_numerator':value})
    tangents=[]
    for k,p0 in enumerate([F(7,8),F(9,8),F(31,8),F(33,8)]):
        p=int(p0*SC);l,u=p-64,p+64
        pl,pu,v,sl,err=cover.support(p)
        assert pl<=l and u<=pu
        lines += [f'def t{k} : WindowSupportCertificate.Support := ⟨{round(p0)},{p},{v},{sl},{err}⟩',
          f'theorem tangent_check{k} : WindowScalarLine.check (.tangent t{k}) {l} {u} = true := by decide +kernel',
          f'theorem tangent_bound{k} (x : ℝ) (hx : ({l}:ℝ)/32768 ≤ x ∧ x ≤ ({u}:ℝ)/32768) :',
          f'    WindowValueFlow.line (WindowScalarLine.plane (.tangent t{k}) {l}) x ≤ WindowKernel.w 24 WindowKernel.d24 x :=',
          f'  WindowScalarLine.sound tangent_check{k} hx']
        tangents.append({'anchor':p,'lower':l,'upper':u,'value':v,'slope':sl,'error':err})
    lines+=['set_option pp.fullNames true']+[f'#print axioms constant_bound{k}'for k in range(4)]+[
      f'#print axioms tangent_bound{k}'for k in range(4)]+['end StructuralGoal20261016.WindowScalarLinePilot']
    dest=ROOT/'StructuralGoal20261016/WindowScalarLinePilot.lean';dest.write_text('\n'.join(lines)+'\n',encoding='utf8',newline='\n')
    out={'scope':__doc__,'script_sha256':sha(Path(__file__)),'K_table_sha256':sha(table),
      'original_scalar_oracle_sha256':sha(HERE/'window_global_cover.py'),
      'generated_sha256':sha(dest),'constant_pilots':constants,'tangent_pilots':tangents,
      'original_constant_floors_preserved':True,'ordinary_Lean_passed':False,
      'global_floor_proven':False,'submission_ready':False}
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:out[k]for k in ['generated_sha256','original_constant_floors_preserved','ordinary_Lean_passed']}))

if __name__=='__main__':main()
