"""Independent exact replay of nonnegative finite-competitor portfolios."""
from pathlib import Path
import argparse,hashlib,json,time
import cover_integer_move_concave_verify as difference
import cover_sublevel_verify as energy
from cover_contractor_verify import flow_bound
from cover_correlated_replay import SC,DS,a
HERE=Path(__file__).parent

def verify(state,result,target,params,checker):
    a.closure_valid(state);terms=[tuple(r) for r in params['a_upper'] if r[2]];bs=params['b_numerators'];D=params['denominator']
    assert D==10**10 and result['kind']=='global_move_portfolio';C=E=0;coeff=[0]*9;assert result['models']
    for model in result['models']:
        theta=model['weight'];delta=model['delta'];assert isinstance(theta,int) and theta>0
        assert len(delta)==9 and any(delta) and all(isinstance(v,int) for v in delta)
        assert all(state[0][k]+SC*delta[k]>=123*SC//128 for k in range(9))
        affected=[t for t,(i,j,aw) in enumerate(terms) if sum(delta[i:j])]
        assert [r[0] for r in model['scalar_difference_data']]==affected
        c=2*SC*DS*sum(b*d for b,d in zip(bs,delta));e=0;co=[0]*9
        for t,*row in model['scalar_difference_data']:
            i,j,aw=terms[t];z=a.INDEX[i,j]
            P,m0,m1,err=checker.check(state[0][z],state[1][z],sum(delta[i:j]),row)
            c+=aw*(2*SC*m0-m1*P);e+=2*SC*aw*err
            for k in range(i,j):co[k]+=2*aw*m1
        C+=theta*c;E+=theta*e
        for k in range(9):coeff[k]+=theta*co[k]
    p=result['energy_multiplier'];assert isinstance(p,int) and p>=0
    if p:EC,ecoeff,_=energy.minorant(state,result['energy_minorant'])
    else:assert result['energy_minorant'] is None;EC=0;ecoeff=[0]*9
    den=2*SC*D*DS;ratio=result['energy_scale_ratio'];assert ratio*energy.g.DEN==den
    combined=[c-p*ratio*e for c,e in zip(coeff,ecoeff)];constant=C+p*ratio*(target-EC)
    assert combined==list(map(int,result['combined_coefficient'])) and constant==int(result['combined_constant']) and E==int(result['difference_error'])
    minimum=flow_bound(state,[-v for v in combined],result['flow']);assert minimum==int(result['negative_maximum'])
    upper=constant+E-minimum;assert upper==int(result['upper_numerator'])<0 and den==int(result['denominator'])
    return {'passed':True,'strict_portfolio_margin':str(-upper),'competitors':len(result['models']),'energy_multiplier_nonzero':p>0}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'cover-global-move-portfolio-pilot.json')
    ap.add_argument('--source',type=Path,default=HERE/'cover-sublevel-obbt.json')
    ap.add_argument('--output',type=Path,default=HERE/'cover-global-move-portfolio-pilot-replay.json');args=ap.parse_args();start=time.monotonic()
    raw=args.input.read_bytes();doc=json.loads(raw);source=args.source.read_bytes();old=json.loads(source)
    assert hashlib.sha256(source).hexdigest()==doc['receipt']['input_sha256'];lookup={r['path']:r for r in old['contractions']}
    table=(HERE/'cover_newjet.json').read_bytes();assert hashlib.sha256(table).hexdigest()==old['receipt']['api_sources']['derivative_table_sha256']
    checker=difference.ConcaveDifferenceReplay(json.loads(table));params=json.loads((HERE.parent/'research-20261016-followup/window_reweight_rational.json').read_bytes())
    import cover_sublevel_obbt_verify as obbt
    import cover_contractor_verify as newton
    target=int(doc['receipt']['target_numerator']);bounds=steps=0;margins=[];modelcounts=[]
    for row in doc['exclusions']:
        original=lookup[row['path']];assert original['result'] is None;obbt.verify(original,target,checker.scalar)
        bounds+=len(original['certificates']);state=original['new_cell']
        for step in row['newton_steps']:
            state=newton.verify_step(state,step,params,checker.scalar);steps+=1
        assert state==row['cell'];out=verify(state,row['result'],target,params,checker);margins.append(int(out['strict_portfolio_margin']));modelcounts.append(out['competitors'])
    receipt={'scope':__doc__,'input_sha256':hashlib.sha256(raw).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'checked_portfolio_chains':len(margins),'checked_prior_OBBT_bounds':bounds,'checked_prior_Newton_steps':steps,'all_passed':True,
      'competitors_per_certificate':modelcounts,'minimum_strict_portfolio_margin':str(min(margins)) if margins else None,
      'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
