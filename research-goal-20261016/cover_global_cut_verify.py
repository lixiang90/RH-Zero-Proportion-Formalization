"""Independent verification of global-minimum-only finite-move OBBT cuts."""
from pathlib import Path
from fractions import Fraction as F
import argparse,hashlib,json,time
import cover_integer_move_concave_verify as difference
import cover_sublevel_verify as energy
import cover_correlated_verify as directional
from cover_contractor_verify import flow_bound,close
from cover_correlated_replay import SC,DS,a,ceil
HERE=Path(__file__).parent

def model(state,row,params,checker):
    terms=[tuple(r) for r in params['a_upper'] if r[2]];delta=row['delta'];bs=params['b_numerators']
    assert len(delta)==9 and any(delta) and all(isinstance(v,int) for v in delta)
    assert all(state[0][k]+SC*delta[k]>=123*SC//128 for k in range(9))
    affected=[t for t,(i,j,aw) in enumerate(terms) if sum(delta[i:j])]
    assert [r[0] for r in row['scalar_difference_data']]==affected
    C=2*SC*DS*sum(b*d for b,d in zip(bs,delta));E=0;coeff=[0]*9
    for t,*data in row['scalar_difference_data']:
        i,j,aw=terms[t];z=a.INDEX[i,j];P,m0,m1,err=checker.check(state[0][z],state[1][z],sum(delta[i:j]),data)
        C+=aw*(2*SC*m0-m1*P);E+=2*SC*aw*err
        for k in range(i,j):coeff[k]+=2*aw*m1
    return C,E,coeff

def verify_step(state,step,target,params,checker):
    state=[list(state[0]),list(state[1])];a.closure_valid(state);assert step['old_cell']==state
    models=[model(state,row,params,checker) for row in step['models']];assert models
    lower=state[0].copy();upper=state[1].copy();seen=set();D=params['denominator'];assert D==10**10;den=2*SC*D*DS;ratio=den//energy.g.DEN
    assert ratio*energy.g.DEN==den
    for cert in step['certificates']:
        z=cert['axis'];sign=cert['sign'];K=cert['multiplier_denominator'];p=cert['energy_multiplier'];gamma=cert['move_multipliers']
        assert 0<=z<9 and sign in [-1,1] and (z,sign) not in seen;seen.add((z,sign))
        assert isinstance(K,int) and K>0 and isinstance(p,int) and p>=0
        assert len(gamma)==len(models) and all(isinstance(v,int) and v>=0 for v in gamma) and any(gamma)
        if p:EC,ecoeff,_=energy.minorant(state,cert['energy_minorant'])
        else:assert cert['energy_minorant'] is None;EC=0;ecoeff=[0]*9
        C=p*SC*ratio*EC-SC*sum(v*(m[0]+m[1]) for v,m in zip(gamma,models))
        coeff=[p*SC*ratio*ecoeff[k]-SC*sum(v*m[2][k] for v,m in zip(gamma,models))+(sign*K*den if k==z else 0) for k in range(9)]
        assert C==int(cert['constant']) and coeff==list(map(int,cert['coefficient']))
        minimum=C+flow_bound(state,coeff,cert['flow']);assert minimum==int(cert['minimum_numerator'])
        bound=F(minimum-p*SC*ratio*target,K*den) if sign==1 else F(p*SC*ratio*target-minimum,K*den)
        assert bound==F(cert['bound'])
        lo=max(lower[z],bound.numerator//bound.denominator) if sign==1 else lower[z]
        hi=min(upper[z],ceil(bound)) if sign==-1 else upper[z]
        assert lo==cert['new_lower'] and hi==cert['new_upper'];lower[z]=lo;upper[z]=hi
    assert seen;refined=close([lower,upper]);assert refined==step['new_cell']
    return refined

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'cover-global-cut-contractor.json')
    ap.add_argument('--output',type=Path,default=HERE/'cover-global-cut-contractor-replay.json');args=ap.parse_args();start=time.monotonic()
    raw=args.input.read_bytes();doc=json.loads(raw);sourceraw=(HERE/'cover-sublevel-obbt.json').read_bytes();source=json.loads(sourceraw)
    assert hashlib.sha256(sourceraw).hexdigest()==doc['receipt']['input_sha256'];lookup={r['path']:r for r in source['contractions']}
    table=(HERE/'cover_newjet.json').read_bytes();assert hashlib.sha256(table).hexdigest()==source['receipt']['api_sources']['derivative_table_sha256']
    checker=difference.ConcaveDifferenceReplay(json.loads(table));params=json.loads((HERE.parent/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    import cover_sublevel_obbt_verify as obbt
    import cover_contractor_verify as newton
    target=int(doc['receipt']['target_numerator']);priorbounds=priorsteps=cutsteps=cutbounds=closed=0
    for row in doc['contractions']:
        original=lookup[row['path']];assert original['result'] is None;obbt.verify(original,target,checker.scalar)
        priorbounds+=len(original['certificates']);state=original['new_cell']
        for step in row['prior_newton_steps']:
            state=newton.verify_step(state,step,params,checker.scalar);priorsteps+=1
        for step in row['steps']:
            assert state is not None;state=verify_step(state,step,target,params,checker);cutsteps+=1;cutbounds+=len(step['certificates'])
        result=row['result']
        if result:
            if result['kind']=='empty':assert state is None
            elif result['kind']=='stationary':directional.verify(state,result['result'],params,checker.scalar)
            else:
                assert result['kind']=='value';_,_,floor=energy.minorant(state,result['result']['certificate'])
                assert floor==int(result['result']['floor_numerator']) and floor>=target
            closed+=1
    out={'scope':__doc__,'input_sha256':hashlib.sha256(raw).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'all_passed':True,'global_cut_paths':len(doc['contractions']),'global_cut_steps':cutsteps,'global_cut_bounds':cutbounds,'closed':closed,
      'prior_OBBT_bounds':priorbounds,'prior_Newton_steps':priorsteps,'preserves_all_KKT_points':False,'preserves_original_global_minima_below_target':True,
      'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8');print(json.dumps(out),flush=True)
if __name__=='__main__':main()
