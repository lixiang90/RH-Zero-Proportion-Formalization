"""Independent rational replay of strict global integer-move improvements.

The scalar checker subtracts same-phase coefficients independently, rebuilds
integer kernel values and all Taylor remainder payments, checks original
orthant feasibility of every move, and verifies the final flow balance/cost.
No LP or flow optimizer is called. In probe mode successful leaves also
replay their entire prior OBBT/Newton chain, where applicable.
"""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import argparse,functools,hashlib,json,time
from cover_correlated_replay import J,SC,DS,a,ceil
from cover_newwindow_gram_replay import Values

HERE=Path(__file__).parent

class DifferenceReplay:
    def __init__(self,table):
        self.values=Values(table);self.scalar=self.values.scalar;self.width=self.scalar.width;self.step=self.scalar.step
    @functools.lru_cache(200000)
    def point(self,P,shift):
        p=F(P,2*SC);v0,d0=self.values.at(p);v1,d1=self.values.at(p+shift)
        return J(v1.l-v0.u,v1.u-v0.l),J(d1.l-d0.u,d1.u-d0.l)
    @functools.lru_cache(100000)
    def grid(self,shift,k):
        n=round(F(2*k+1,2*self.step));x=J(F(k,self.step)-n,F(k+1,self.step)-n)
        base=self.scalar.coeff[n];other=self.scalar.coeff[n+shift];v=J(0)
        for j in range(len(base)-1,0,-1):v=v*x+J(other[j].l-base[j].u,other[j].u-base[j].l)*j
        rem=2*self.scalar.M*F(1,2)**22/factorial(22)
        return ceil(max(abs(v.l-rem),abs(v.u+rem))*DS)
    @functools.lru_cache(200000)
    def second_bound(self,l,u,shift):
        if shift<0:return self.second_bound(l+shift*SC,u+shift*SC,-shift)
        assert shift>0 and l>=0 and u+shift*SC<=32*SC
        return max(self.grid(shift,k) for k in range(l//self.width,(max(l+1,u)+self.width-1)//self.width))
    def check(self,l,u,shift,row):
        P,m0,m1,err=map(int,row);assert P==l+u and err>=0
        assert min(l,l+shift*SC)>=0 and max(u,u+shift*SC)<=32*SC
        v,s=self.point(P,shift);radius=F(u-l,2*SC)
        required=ceil(max(abs(v.l*DS-m0),abs(v.u*DS-m0))+max(abs(s.l*DS-m1),abs(s.u*DS-m1))*radius+F(self.second_bound(l,u,shift))*radius**2/2)
        assert err>=required,('insufficient finite difference Taylor payment',shift,l,u,err,required)
        return P,m0,m1,err

def verify(state,result,params,table):
    checker=table if isinstance(table,DifferenceReplay) else DifferenceReplay(table)
    a.closure_valid(state);bs=params['b_numerators'];terms=[tuple(r) for r in params['a_upper'] if r[2]];D=params['denominator']
    assert D==10**10 and result['kind']=='integer_move'
    delta=result['delta'];assert len(delta)==9 and any(delta) and all(isinstance(v,int) for v in delta)
    assert all(state[0][i]+SC*delta[i]>=123*SC//128 for i in range(9))
    affected=[t for t,(i,j,aw) in enumerate(terms) if sum(delta[i:j])]
    assert [row[0] for row in result['scalar_difference_data']]==affected
    C=2*SC*DS*sum(b*d for b,d in zip(bs,delta));E=0;coeff=[0]*9
    for t,*row in result['scalar_difference_data']:
        i,j,aw=terms[t];z=a.INDEX[i,j];P,m0,m1,err=checker.check(state[0][z],state[1][z],sum(delta[i:j]),row)
        C+=aw*(2*SC*m0-m1*P);E+=2*SC*aw*err
        for k in range(i,j):coeff[k]+=2*aw*m1
    flow=result['exact_flow'];assert C==int(flow['constant']) and E==int(flow['error']) and coeff==list(map(int,flow['coefficient']))
    desired=[coeff[0]]+[coeff[k]-coeff[k-1] for k in range(1,9)]+[-coeff[-1]];balance=[0]*10;cost=0
    for i,j,amount,u in flow['flow']['nonzero_flow']:
        amount=int(amount);assert amount>=0 and i!=j and u==a.edge_value(state,i,j)
        balance[i]+=amount;balance[j]-=amount;cost+=amount*u
    assert balance==desired==list(map(int,flow['flow']['divergence']))
    assert cost==int(flow['flow']['cost']) and -cost==int(flow['negative_maximum'])
    upper=C+E+cost;assert upper==int(result['upper_numerator'])<0 and int(result['denominator'])==2*SC*D*DS
    return {'passed':True,'strict_integer_margin':str(-upper),'affected_positive_weight_spans':len(affected)}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'cover-integer-move-newton.json')
    ap.add_argument('--source',type=Path,default=HERE/'cover-sublevel-obbt.json')
    ap.add_argument('--output',type=Path,default=HERE/'cover-integer-move-replay.json');args=ap.parse_args();start=time.monotonic()
    raw=args.input.read_bytes();doc=json.loads(raw);source=args.source.read_bytes();original=json.loads(source)
    assert hashlib.sha256(source).hexdigest()==doc['receipt']['input_sha256']
    frontier=doc['receipt']['input_kind']=='frontier';records=original['frontier'] if frontier else original['contractions'];lookup={r['path']:r for r in records}
    table=(HERE/'cover_newjet.json').read_bytes();assert hashlib.sha256(table).hexdigest()==doc['receipt']['table_sha256']
    checker=DifferenceReplay(json.loads(table));params=json.loads((HERE.parent/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    import cover_sublevel_obbt_verify as obbt
    import cover_contractor_verify as newton
    bounds=steps=0;margins=[]
    for row in doc['exclusions']:
        old=lookup[row['path']]
        if frontier:state=old['state']
        else:
            assert old['result'] is None
            obbt.verify(old,int(original['receipt']['target_numerator']),checker.scalar);bounds+=len(old['certificates']);state=old['new_cell']
        for step in row['newton_steps']:
            state=newton.verify_step(state,step,params,checker.scalar);steps+=1
        assert state==row['cell'];margins.append(int(verify(state,row['result'],params,checker)['strict_integer_margin']))
    receipt={'scope':__doc__,'input_sha256':hashlib.sha256(raw).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'checked_integer_move_chains':len(margins),'checked_prior_OBBT_bounds':bounds,'checked_prior_Newton_steps':steps,'all_passed':True,
      'minimum_strict_move_margin':str(min(margins)) if margins else None,'frontier_ancestor_geometry_rebuilt':False if frontier else None,
      'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
