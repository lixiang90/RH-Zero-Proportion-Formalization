"""Independent exact replay of sublevel-conditioned global competitor bounds."""
from pathlib import Path
from fractions import Fraction as F
import argparse,hashlib,json,time
import cover_integer_move_concave_verify as scalar
from cover_correlated_replay import SC,DS,a,ceil
from cover_contractor_verify import flow_bound
import cover_sublevel_verify as energy
HERE=Path(__file__).parent

def check_line(checker,l,u,shift,row):
    P,m0,m1,err=map(int,row);assert 2*l<=P<=2*u and err>=0
    assert min(l,l+shift*SC)>=0 and max(u,u+shift*SC)<=32*SC
    v,s=checker.point(P,shift);r=F(max(P-2*l,2*u-P),2*SC);B=max(0,checker.second_range(l,u,shift)[1])
    needed=ceil(max(abs(v.l*DS-m0),abs(v.u*DS-m0))+max(abs(s.l*DS-m1),abs(s.u*DS-m1))*r+F(B)*r*r/2)
    assert err>=needed,('insufficient noncentral upper tangent payment',err,needed)
    return P,m0,m1,err

def verify(state,result,target,params,checker):
    a.closure_valid(state);terms=[tuple(r) for r in params['a_upper'] if r[2]];bs=params['b_numerators'];D=params['denominator']
    assert D==10**10 and result['kind']=='global_move_epigraph';LD=int(result['difference_mixture_denominator']);assert LD==10**12
    delta=result['delta'];assert len(delta)==9 and any(delta) and all(isinstance(v,int) for v in delta)
    assert all(state[0][k]+SC*delta[k]>=123*SC//128 for k in range(9))
    affected={t for t,(i,j,aw) in enumerate(terms) if sum(delta[i:j])};mass=[0]*len(terms)
    C=2*SC*DS*(LD//D)*sum(b*d for b,d in zip(bs,delta));E=0;coeff=[0]*9
    for t,P,weight0,m0,m1,err in result['difference_upper_mixture']:
        weight=int(weight0);assert weight>0 and t in affected
        i,j,aw=terms[t];z=a.INDEX[i,j]
        P,m0,m1,err=check_line(checker,state[0][z],state[1][z],sum(delta[i:j]),[P,m0,m1,err])
        mass[t]+=weight;C+=weight*(2*SC*m0-m1*P);E+=2*SC*weight*err
        for k in range(i,j):coeff[k]+=2*weight*m1
    assert all(mass[t]==(aw*(LD//D) if t in affected else 0) for t,(i,j,aw) in enumerate(terms))
    p=int(result['energy_multiplier_numerator']);K=int(result['energy_multiplier_denominator']);assert p>=0 and K>0
    if p:
        EC,ecoeff,_=energy.minorant(state,result['energy_minorant'])
    else:
        assert result['energy_minorant'] is None;EC=0;ecoeff=[0]*9
    den=2*SC*LD*DS;ratio=int(result['energy_scale_ratio']);assert ratio*energy.g.DEN==den
    combined=[K*c-p*ratio*e for c,e in zip(coeff,ecoeff)];constant=K*C+p*ratio*(target-EC)
    assert combined==list(map(int,result['combined_coefficient'])) and constant==int(result['combined_constant'])
    assert K*E==int(result['difference_error'])
    minimum=flow_bound(state,[-v for v in combined],result['flow']);assert minimum==int(result['negative_maximum'])
    upper=constant+K*E-minimum;assert upper==int(result['upper_numerator'])<0 and int(result['denominator'])==K*den
    return {'passed':True,'strict_global_move_margin':str(-upper),'difference_upper_lines':len(result['difference_upper_mixture']),
      'energy_multiplier_nonzero':p>0}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'cover-global-move-epigraph-pilot.json')
    ap.add_argument('--source',type=Path,default=HERE/'cover-sublevel-obbt.json')
    ap.add_argument('--output',type=Path,default=HERE/'cover-global-move-epigraph-pilot-replay.json');args=ap.parse_args();start=time.monotonic()
    raw=args.input.read_bytes();doc=json.loads(raw);source=args.source.read_bytes();old=json.loads(source)
    assert hashlib.sha256(source).hexdigest()==doc['receipt']['input_sha256'];lookup={r['path']:r for r in old['contractions']}
    table=(HERE/'cover_newjet.json').read_bytes();assert hashlib.sha256(table).hexdigest()==doc['receipt']['table_sha256']
    checker=scalar.ConcaveDifferenceReplay(json.loads(table));params=json.loads((HERE.parent/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    import cover_sublevel_obbt_verify as obbt
    import cover_contractor_verify as newton
    target=int(doc['receipt']['target_numerator']);bounds=steps=nonzero=0;margins=[]
    for row in doc['exclusions']:
        original=lookup[row['path']];assert original['result'] is None
        obbt.verify(original,target,checker.scalar);bounds+=len(original['certificates']);state=original['new_cell']
        for step in row['newton_steps']:
            state=newton.verify_step(state,step,params,checker.scalar);steps+=1
        assert state==row['cell'];out=verify(state,row['result'],target,params,checker)
        margins.append(int(out['strict_global_move_margin']));nonzero+=out['energy_multiplier_nonzero']
    receipt={'scope':__doc__,'input_sha256':hashlib.sha256(raw).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'checked_global_move_chains':len(margins),'checked_prior_OBBT_bounds':bounds,'checked_prior_Newton_steps':steps,'all_passed':True,
      'nonzero_sublevel_multiplier_certificates':nonzero,'minimum_strict_move_margin':str(min(margins)) if margins else None,
      'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
