"""Independent stdlib-only arithmetic replay of correlated descent witnesses.

Rebuilds scalar Taylor bounds from frozen interval coefficients, all cell
geometry from the frozen prefix, directional feasibility, flow divergence,
flow edge costs, and the strict negative upper bound. Imports no producer,
optimization package, or numerical library. Analytic equality of interval
jets to the actual kernel and the Lean KKT bridge remain explicit duties.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import argparse, functools, gzip, hashlib, importlib.util, json, time
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent;SC=32768;DS=10**15;D=10**10
spec=importlib.util.spec_from_file_location('independent_correlated_geometry',ROOT/'research-20261016-w10-cert/independent_integer_audit.py')
a=importlib.util.module_from_spec(spec);spec.loader.exec_module(a)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def ceil(x):return -((-x.numerator)//x.denominator)

class J:
    def __init__(self,l,u=None):self.l=F(l);self.u=F(l if u is None else u);assert self.l<=self.u
    def __add__(self,x):
        if not isinstance(x,J):x=J(x)
        return J(self.l+x.l,self.u+x.u)
    __radd__=__add__
    def __mul__(self,x):
        if not isinstance(x,J):x=J(x)
        v=[self.l*x.l,self.l*x.u,self.u*x.l,self.u*x.u];return J(min(v),max(v))
    __rmul__=__mul__

class ScalarReplay:
    def __init__(self,doc):
        self.coeff={int(n):[J(l,u) for l,u in cs] for n,cs in doc['integer_taylor_coefficients'].items()}
        self.ranges=doc['ranges'];self.step=doc['receipt']['grid_step'];self.width=SC//self.step
        self.third=[];self.M=F(44,7)**24
        for k in range(32*self.step):
            n=round(F(2*k+1,2*self.step));v=self.poly(n,J(F(k,self.step)-n,F(k+1,self.step)-n),2)
            rem=self.M*F(1,2)**21/factorial(21)
            self.third.append(ceil(max(abs(v.l-rem),abs(v.u+rem))*DS))
    def poly(self,n,x,r):
        value=J(0);coeff=self.coeff[n]
        for j in range(len(coeff)-1,r-1,-1):value=value*x+coeff[j]*F(factorial(j),factorial(j-r))
        return value
    @functools.lru_cache(200000)
    def point(self,P):
        p=F(P,2*SC);n=round(p);x=p-n
        v=self.poly(n,J(x),0);s=self.poly(n,J(x),1)
        ev=self.M*abs(x)**23/factorial(23);es=self.M*abs(x)**22/factorial(22)
        return J(v.l-ev,v.u+ev),J(s.l-es,s.u+es)
    @functools.lru_cache(200000)
    def third_bound(self,l,u):
        if u>32*SC:return ceil(F(44,7)**3*DS)
        return max(self.third[l//self.width:(max(l+1,u)+self.width-1)//self.width])
    @functools.lru_cache(200000)
    def derivative_range(self,l,u):
        if u>32*SC:return -7*DS,7*DS
        rows=self.ranges[l//self.width:(max(l+1,u)+self.width-1)//self.width]
        return min(r[0] for r in rows),max(r[1] for r in rows)
    def check(self,l,u,row):
        P,m0,m1,err,kind=row;P=int(P);m0=int(m0);m1=int(m1);err=int(err)
        assert P==l+u and err>=0
        if kind=='interval':
            dl,du=self.derivative_range(l,u)
            assert m1==0 and m0-err<=dl and du<=m0+err
        else:
            assert kind=='affine' and u<=32*SC
            v,s=self.point(P);radius=F(u-l,2*SC)
            required=ceil(max(abs(v.l*DS-m0),abs(v.u*DS-m0))+max(abs(s.l*DS-m1),abs(s.u*DS-m1))*radius+F(self.third_bound(l,u))*radius**2/2)
            assert err>=required,('insufficient Taylor error',l,u,err,required)
        return P,m0,m1,err,kind

def main():
    ap=argparse.ArgumentParser();ap.add_argument('witness',type=Path)
    ap.add_argument('--oracle',type=Path,default=HERE/'cover_newjet.json')
    ap.add_argument('--input',type=Path);ap.add_argument('--output',type=Path,default=HERE/'cover-correlated-replay.json')
    args=ap.parse_args();start=time.monotonic();proof=json.loads(args.witness.read_bytes())
    snapshot=args.input or args.witness.with_suffix('.input.json.gz');raw=gzip.decompress(snapshot.read_bytes());source=json.loads(raw)
    assert hashlib.sha256(raw).hexdigest()==proof['receipt']['input_sha256']
    oracle_doc=json.loads(args.oracle.read_bytes());assert sha(args.oracle)==proof['receipt']['oracle_sha256']
    scalar=ScalarReplay(oracle_doc)
    parameter=ROOT/'research-20261016-followup/window_reweight_rational.json';P=json.loads(parameter.read_bytes())
    assert sha(parameter)==oracle_doc['receipt']['parameter_sha256'];bs=P['b_numerators'];terms=[tuple(t) for t in P['a_upper'] if t[2]]
    branches={r['path']:r for r in source['branches']};rows={r['path']:r['result'] for r in proof['exclusions']}
    needed={p[:k] for p in rows for k in range(1,len(p)+1)}
    sep=123*SC//128;budget=88400000*SC-sum(bs)*sep
    up=[sep+ceil(F(budget,b)) for b in bs]
    lo=[(j-i)*sep for i,j in a.PAIRS]
    hi=[min(sum(up[i:j]),(j-i)*sep+ceil(F(budget,min(bs[i:j])))) for i,j in a.PAIRS]
    assert source['root']==[lo,hi];root=[lo,hi];a.closure_valid(root)
    todo=[('r',root)];checked=0;minmargin=None
    while todo:
        path,state=todo.pop()
        if path not in needed:continue
        if path in rows:
            row=rows[path];direction=list(map(int,row['direction']));assert len(direction)==9
            assert all(v>=0 or state[0][i]>sep for i,v in enumerate(direction))
            data=[scalar.check(state[0][a.INDEX[i,j]],state[1][a.INDEX[i,j]],r) for (i,j,w),r in zip(terms,row['scalar_affine_data'])]
            assert len(data)==len(terms)
            constant=2*SC*sum(b*DS*v for b,v in zip(bs,direction));error=0;coeff=[0]*9
            for (i,j,w),(anchor,m0,m1,err,kind) in zip(terms,data):
                c=sum(direction[i:j]);constant+=w*c*(2*SC*m0-m1*anchor);error+=2*SC*w*abs(c)*err
                for k in range(i,j):coeff[k]+=2*w*c*m1
            flow=row['exact_flow'];assert constant==int(flow['constant']) and error==int(flow['error']) and coeff==list(map(int,flow['coefficient']))
            desired=[coeff[0]]+[coeff[i]-coeff[i-1] for i in range(1,9)]+[-coeff[8]];balance=[0]*10;cost=0
            for i,j,y,u in flow['flow']['nonzero_flow']:
                y=int(y);assert y>=0 and i!=j and u==a.edge_value(state,i,j)
                balance[i]+=y;balance[j]-=y;cost+=y*u
            assert balance==desired==list(map(int,flow['flow']['divergence']))
            assert cost==int(flow['flow']['cost']) and -cost==int(flow['negative_maximum'])
            upper=constant+error+cost
            assert upper==int(row['upper_numerator'])<0
            minmargin=-upper if minmargin is None else min(minmargin,-upper);checked+=1
        if path in branches:
            r=branches[path];z=r['axis'];cut=r['cut'];assert state[0][z]<cut<state[1][z]
            for bit,upper in [('1',False),('0',True)]:
                if path+bit in needed:
                    child=a.child(state,z,cut,upper);assert child is not None;todo.append((path+bit,child))
        if checked and checked%250==0 and path in rows:print(json.dumps({'checked':checked,'seconds':time.monotonic()-start}),flush=True)
    assert checked==len(rows)
    receipt={'scope':__doc__,'passed':True,'witness_sha256':sha(args.witness),'snapshot_sha256':sha(snapshot),'oracle_sha256':sha(args.oracle),
      'script_sha256':sha(Path(__file__)),'geometry_helper_sha256':sha(Path(a.__file__)),'parameter_sha256':sha(parameter),
      'checked_correlated_descent_cells':checked,'minimum_strict_integer_margin':str(minmargin),
      'all_geometry_rebuilt':True,'all_scalar_Taylor_errors_recomputed':True,'all_feasible_directions_checked':True,'all_flow_balances_and_costs_checked':True,
      'actual_kernel_jet_Lean_connection':False,'global_minimizer_cover_complete':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
