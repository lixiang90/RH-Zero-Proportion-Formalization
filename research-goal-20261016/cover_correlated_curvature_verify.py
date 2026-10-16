"""Independent rational replay of correlated negative second variations.

Imports no producer, NumPy, SciPy, or flow optimizer. Rebuilds all scalar
w''/w'''/w'''' enclosures, directions, affine coefficients and flow balances.
The probe mode also replays every successful leaf's prior OBBT/Newton chain.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import argparse,functools,hashlib,json,time
from cover_correlated_replay import ScalarReplay,J,SC,DS,a,ceil

HERE=Path(__file__).parent

class CurvatureReplay:
    def __init__(self,table):
        self.scalar=table if isinstance(table,ScalarReplay) else ScalarReplay(table)
        self.width=self.scalar.width;self.step=self.scalar.step
        self.second=[];self.fourth=[];M=self.scalar.M
        r2=M*F(1,2)**22/factorial(22);r4=M*F(1,2)**20/factorial(20)
        for k in range(32*self.step):
            n=round(F(2*k+1,2*self.step));x=J(F(k,self.step)-n,F(k+1,self.step)-n)
            v=self.scalar.poly(n,x,1);s=self.scalar.poly(n,x,3)
            self.second.append((((v.l-r2)*DS).numerator//((v.l-r2)*DS).denominator,ceil((v.u+r2)*DS)))
            self.fourth.append(ceil(max(abs(s.l-r4),abs(s.u+r4))*DS))
    @functools.lru_cache(200000)
    def point(self,P):
        p=F(P,2*SC);n=round(p);x=p-n;M=self.scalar.M
        v=self.scalar.poly(n,J(x),1);s=self.scalar.poly(n,J(x),2)
        ev=M*abs(x)**22/factorial(22);es=M*abs(x)**21/factorial(21)
        return J(v.l-ev,v.u+ev),J(s.l-es,s.u+es)
    def check(self,l,u,row):
        P,m0,m1,err,kind=row;P=int(P);m0=int(m0);m1=int(m1);err=int(err)
        assert P==l+u and err>=0 and l>=0
        first=l//self.width;last=(max(l+1,u)+self.width-1)//self.width
        if kind=='interval':
            dl,du=(-40*DS,40*DS) if u>32*SC else (min(v[0] for v in self.second[first:last]),max(v[1] for v in self.second[first:last]))
            assert m1==0 and m0-err<=dl and du<=m0+err
        else:
            assert kind=='affine' and u<=32*SC
            v,s=self.point(P);radius=F(u-l,2*SC);fourth=max(self.fourth[first:last])
            required=ceil(max(abs(v.l*DS-m0),abs(v.u*DS-m0))+max(abs(s.l*DS-m1),abs(s.u*DS-m1))*radius+F(fourth)*radius**2/2)
            assert err>=required,('insufficient second variation Taylor remainder',l,u,err,required)
        return P,m0,m1,err,kind

def verify(state,result,params,table):
    checker=table if isinstance(table,CurvatureReplay) else CurvatureReplay(table)
    a.closure_valid(state);terms=[tuple(r) for r in params['a_upper'] if r[2]];D=params['denominator']
    assert D==10**10 and result['kind']=='correlated_negative_curvature'
    d=list(map(int,result['direction']));assert len(d)==9 and any(d)
    assert all(v==0 or state[0][i]>123*SC//128 for i,v in enumerate(d))
    assert len(result['scalar_affine_data'])==len(terms)
    C=E=0;coeff=[0]*9
    for (i,j,w),raw in zip(terms,result['scalar_affine_data']):
        P,m0,m1,err,kind=checker.check(state[0][a.INDEX[i,j]],state[1][a.INDEX[i,j]],raw)
        q=w*sum(d[i:j])**2;C+=q*(2*SC*m0-m1*P);E+=2*SC*q*err
        for k in range(i,j):coeff[k]+=2*q*m1
    flow=result['exact_flow'];assert int(flow['constant'])==C and int(flow['error'])==E and list(map(int,flow['coefficient']))==coeff
    wanted=[coeff[0]]+[coeff[i]-coeff[i-1] for i in range(1,9)]+[-coeff[8]];balance=[0]*10;cost=0
    for i,j,amount,u in flow['flow']['nonzero_flow']:
        amount=int(amount);assert amount>=0 and i!=j and u==a.edge_value(state,i,j)
        balance[i]+=amount;balance[j]-=amount;cost+=amount*u
    assert balance==wanted==list(map(int,flow['flow']['divergence']))
    assert cost==int(flow['flow']['cost']) and -cost==int(flow['negative_maximum'])
    upper=C+E+cost;assert upper==int(result['upper_numerator'])<0
    assert int(result['denominator'])==2*SC*D*DS
    return {'passed':True,'strict_curvature_margin':str(-upper)}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'cover-correlated-curvature.json')
    ap.add_argument('--source',type=Path,default=HERE/'cover-sublevel-obbt.json');ap.add_argument('--output',type=Path,default=HERE/'cover-correlated-curvature-replay.json')
    args=ap.parse_args();start=time.monotonic();raw=args.input.read_bytes();doc=json.loads(raw);priorraw=args.source.read_bytes()
    assert hashlib.sha256(priorraw).hexdigest()==doc['receipt']['input_sha256'];prior=json.loads(priorraw);rows={r['path']:r for r in prior['contractions']}
    import cover_sublevel_obbt_verify as obbt
    import cover_contractor_verify as newton
    params=json.loads((HERE.parent/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    tabraw=(HERE/'cover_newjet.json').read_bytes();assert hashlib.sha256(tabraw).hexdigest()==doc['receipt']['table_sha256']
    checker=CurvatureReplay(json.loads(tabraw));bounds=steps=0;margins=[]
    for row in doc['exclusions']:
        old=rows[row['path']];assert old['result'] is None
        obbt.verify(old,int(prior['receipt']['target_numerator']),checker.scalar);bounds+=len(old['certificates']);state=old['new_cell']
        for step in row['newton_steps']:
            state=newton.verify_step(state,step,params,checker.scalar);steps+=1
        assert state==row['cell'];margins.append(int(verify(state,row['result'],params,checker)['strict_curvature_margin']))
    receipt={'scope':__doc__,'input_sha256':hashlib.sha256(raw).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'checked_curvature_chains':len(margins),'checked_prior_OBBT_bounds':bounds,'checked_prior_Newton_steps':steps,'all_passed':True,
      'minimum_strict_curvature_margin':str(min(margins)) if margins else None,'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,
      'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
