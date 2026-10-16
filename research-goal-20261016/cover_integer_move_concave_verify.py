"""Replay the one-sided concave difference bound and its preceding refinements."""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import argparse,functools,hashlib,json,time
import cover_integer_move_verify as base
from cover_correlated_replay import J,SC,DS,a,ceil
HERE=Path(__file__).parent

class ConcaveDifferenceReplay(base.DifferenceReplay):
    @functools.lru_cache(100000)
    def grid_range(self,shift,k):
        n=round(F(2*k+1,2*self.step));x=J(F(k,self.step)-n,F(k+1,self.step)-n)
        old=self.scalar.coeff[n];new=self.scalar.coeff[n+shift];v=J(0)
        for j in range(len(old)-1,0,-1):v=v*x+J(new[j].l-old[j].u,new[j].u-old[j].l)*j
        rem=2*self.scalar.M*F(1,2)**22/factorial(22);l=(v.l-rem)*DS
        return l.numerator//l.denominator,ceil((v.u+rem)*DS)
    @functools.lru_cache(200000)
    def second_range(self,l,u,shift):
        if shift<0:
            low,up=self.second_range(l+shift*SC,u+shift*SC,-shift);return -up,-low
        assert shift>0 and l>=0 and u+shift*SC<=32*SC
        rows=[self.grid_range(shift,k) for k in range(l//self.width,(max(l+1,u)+self.width-1)//self.width)]
        return min(r[0] for r in rows),max(r[1] for r in rows)
    def check(self,l,u,shift,row):
        P,m0,m1,err=map(int,row);assert P==l+u and err>=0
        assert min(l,l+shift*SC)>=0 and max(u,u+shift*SC)<=32*SC
        v,s=self.point(P,shift);r=F(u-l,2*SC);B=max(0,self.second_range(l,u,shift)[1])
        needed=ceil(max(abs(v.l*DS-m0),abs(v.u*DS-m0))+max(abs(s.l*DS-m1),abs(s.u*DS-m1))*r+F(B)*r*r/2)
        assert err>=needed,('insufficient one-sided Taylor error',l,u,shift,err,needed)
        return P,m0,m1,err

def verify(state,result,params,checker):
    assert result['scalar_recipe']=='signed-difference-upper-v1'
    return base.verify(state,result,params,checker)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'cover-integer-move-concave.json')
    ap.add_argument('--source',type=Path,default=HERE/'cover-sublevel-obbt.json')
    ap.add_argument('--output',type=Path,default=HERE/'cover-integer-move-concave-replay.json');args=ap.parse_args();start=time.monotonic()
    raw=args.input.read_bytes();doc=json.loads(raw);source=args.source.read_bytes();old=json.loads(source)
    assert hashlib.sha256(source).hexdigest()==doc['receipt']['input_sha256']
    frontier=doc['receipt']['input_kind']=='frontier';lookup={r['path']:r for r in old['frontier'] if frontier} if frontier else {r['path']:r for r in old['contractions']}
    table=(HERE/'cover_newjet.json').read_bytes();assert hashlib.sha256(table).hexdigest()==doc['receipt']['table_sha256']
    checker=ConcaveDifferenceReplay(json.loads(table));params=json.loads((HERE.parent/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    import cover_sublevel_obbt_verify as obbt
    import cover_contractor_verify as newton
    target=int(doc['receipt']['target_numerator']);bounds=steps=0;margins=[]
    for row in doc['exclusions']:
        original=lookup[row['path']]
        if frontier:state=original['state']
        else:
            assert original['result'] is None;obbt.verify(original,target,checker.scalar);bounds+=len(original['certificates']);state=original['new_cell']
        if row['extra_sublevel_step']:
            extra=row['extra_sublevel_step'];assert extra['old_cell']==state
            obbt.verify({**extra,'result':None},target,checker.scalar);bounds+=len(extra['certificates']);state=extra['new_cell']
        for step in row['newton_steps']:
            state=newton.verify_step(state,step,params,checker.scalar);steps+=1
        assert state==row['cell'];margins.append(int(verify(state,row['result'],params,checker)['strict_integer_margin']))
    receipt={'scope':__doc__,'input_sha256':hashlib.sha256(raw).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'checked_integer_move_chains':len(margins),'checked_prior_OBBT_bounds':bounds,'checked_prior_Newton_steps':steps,'all_passed':True,
      'minimum_strict_move_margin':str(min(margins)) if margins else None,'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,
      'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
