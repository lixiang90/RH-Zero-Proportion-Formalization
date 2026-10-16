"""Single-midpoint energy/RLT test on the six remaining frozen parents.

The first two cases are excluded from this fixed batch.  Each parent uses
one DBM-feasible prefix midpoint, one energy-slack LP, no PSD cut rounds,
no new sampling and no threshold change. A floating positive slack is
accepted only after outward integer rows and a strict Fraction box check.
Analytic input replay and actual Lean instantiation are separate stages.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,gzip,hashlib,json,time
import numpy as np
from scipy.sparse import csr_matrix,vstack,hstack
import cover_cross_moment_probe as base
import cover_cross_moment_energy_probe as energy
import cover_cross_moment_exact_rows as exact

HERE=Path(__file__).parent;ROOT=HERE.parent;g=base.g;SC=g.SC
sha=lambda b:hashlib.sha256(b).hexdigest()


def softened_solve(state,taylor,graph,packet):
    erow=np.zeros(base.V)
    for k,v in packet['row']:erow[k]=float(F(v))
    B=float(F(packet['bound']));scale=max(1.,max(abs(erow)),abs(B));erow/=scale;B/=scale
    original=base.linprog;dual={}
    def softened(c,**kw):
        nr=kw['A_ub'].shape[0];A=vstack([kw['A_ub'],csr_matrix(erow[None,:])],format='csr')
        column=np.r_[np.zeros(nr),[-1/scale]][:,None];rhs=np.r_[kw['b_ub'],B]
        lp=original(np.r_[np.zeros(base.V),1.],A_ub=hstack([A,csr_matrix(column)],format='csr'),
          b_ub=rhs,bounds=kw['bounds']+[(0,None)],method=kw['method'])
        dual.update({'LP_status':int(lp.status),'LP_success':bool(lp.success),'base_rows':nr,'energy_rows':1,'energy_row_scales':[scale]})
        if lp.success:
            dual.update({'minimum_energy_slack_hint':float(lp.fun),
              'nonzero_row_dual_weights':[[k,float(-v)] for k,v in enumerate(lp.ineqlin.marginals) if -v>1e-14],
              'minimum_softened_row_slack_hint':float(min(rhs-A@lp.x[:-1]-column[:,0]*lp.x[-1])),
              'raw_primal_with_energy_slack':lp.x.tolist()})
            lp.x=lp.x[:-1]
        return lp
    base.linprog=softened
    try:result=base.solve(state,taylor,graph,0)
    finally:base.linprog=original
    assert not result['integer_PSD_cut_vectors'] and len(result['history'])==1
    return dual,result


def integer_certificate(state,taylor,graph,packet,dual):
    rr,bb,integer,meta,data,obj,stats=base.old.build(state,taylor,graph,True);ubounds=[]
    for i,j,aw in g.TERMS:
        z=g.LOOK[i,j];facets,n=graph.facets(state[0][z],state[1][z])
        U=min(F(C,SC*base.old.DS) for sign,S,C in facets if sign==1 and S==0)
        L=max(F(C,SC*base.old.DS) for sign,S,C in facets if sign==-1 and S==0);ubounds.append((L,U))
    model=exact.inputs(state,integer,meta,ubounds,[packet]);assert len(model['rows'])==dual['base_rows']+1
    selected=dual['nonzero_row_dual_weights'];indices=[i for i,w in selected]
    coefficients=[w/float(model['rows'][i]['scale']) for i,w in selected];mx=max(coefficients)
    integers=[exact.integerize(model['rows'][i],model['bounds'],10**30) for i in indices]
    attempts=[];chosen=None
    for power in [32,48,64]:
        weights=[round(w/mx*2**power) for w in coefficients]
        weighted=[(i,mu) for i,mu in enumerate(weights) if mu]
        checked=exact.verify_aggregate(integers,weighted,model['bounds'])
        attempts.append({'power':power,'strict':checked['strict_exclusion'],'margin':str(checked['strict_margin'])})
        if checked['strict_exclusion']:chosen=(power,weights,checked);break
    if chosen is None:return None,attempts
    power,weights,checked=chosen;saved=[];kinds={}
    for index,mu,row in zip(indices,weights,integers):
        if not mu:continue
        kind=row['meta'][0];kinds[kind]=kinds.get(kind,0)+1
        saved.append({'row_index':index,'meta':row['meta'],'weight':str(mu),
          'integer_coefficients':[[k,str(a)] for k,a in sorted(row['coeff'].items())],
          'integer_bound':str(row['bound']),'rounding_payment':str(row['rounding_payment'])})
    aggregate={k:([[i,str(v)] for i,v in sorted(value.items())] if k=='coefficient' else str(value) if isinstance(value,(F,int)) and not isinstance(value,bool) else value) for k,value in checked.items()}
    return {'old_integer_rows':[[list(ag),list(au),str(B)] for ag,au,B in integer],
      'old_meta':meta,'scalar_affine_data':[[P,str(m0),str(m1),str(err),kind] for P,m0,m1,err,kind in data],
      'u_bounds':[[str(l),str(u)] for l,u in ubounds],'energy_packets':[packet],
      'integerization_denominator':str(10**30),'dual_weight_power':power,'selected_integer_rows':saved,
      'selected_row_kind_counts':kinds,'box_bounds':[[str(l),str(u)] for l,u in model['bounds']],
      'aggregate':aggregate,'attempts':attempts,'strict_integer_system_contradiction':True,
      'analytic_input_soundness_independently_verified':False,'actual_Lean_exclusion_proven':False},attempts


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);args=ap.parse_args();assert not args.output.exists(),'Use a new output.'
    start=time.monotonic();input_path=HERE/'cover-curvature-parent64.input.json.gz';raw=input_path.read_bytes();doc=json.loads(gzip.decompress(raw));cases={r['path']:r for r in doc['cases']}
    selection_raw=(HERE/'cover-lifted-graph-energy8.json').read_bytes();selection=json.loads(selection_raw);paths=[r['path'] for r in selection['rows']]
    assert paths[:2]==['r001000001000001101011101','r001000001000001110011100'] and len(paths)==8;paths=paths[2:]
    source_paths=[Path(base.__file__),Path(energy.__file__),Path(exact.__file__),Path(base.old.__file__),HERE/'cover_newjet.json']
    guards={p.name:sha(p.read_bytes()) for p in source_paths}
    table=HERE/'cover_newjet.json';taylor=base.old.context.curvature.first.TaylorOracle(table)
    second=base.old.context.curvature.second.SecondOracle(taylor);graph=base.old.GraphOracle(table);rows=[]
    for path in paths:
        case_start=time.monotonic();state=tuple(cases[path]['before'])
        prefix=[F(0)]+[F(state[0][g.LOOK[0,j]]+state[1][g.LOOK[0,j]],2*SC) for j in range(1,10)]
        point=[prefix[j+1]-prefix[j] for j in range(9)];packet=energy.packet(state,point,second)
        dual,result=softened_solve(state,taylor,graph,packet);candidate=None;attempts=[]
        if dual.get('minimum_energy_slack_hint',0)>1e-10:candidate,attempts=integer_certificate(state,taylor,graph,packet,dual)
        row={'path':path,'cell':[list(v) for v in state],'energy_packets':[packet],'dual_hint':dual,'base_result':result,
          'integer_certificate':candidate,'integer_attempts':attempts,'position_PSD_cut_rounds':0,'sample_points_evaluated':0,
          'recorded_old_work':cases[path].get('recorded_old_work'),'seconds':time.monotonic()-case_start};rows.append(row)
        assert all(sha(p.read_bytes())==guards[p.name] for p in source_paths),'An imported frozen input changed.'
        out={'receipt':{'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'source_guards':guards,
          'parent64_input_sha256':sha(raw),'selection_sha256':sha(selection_raw),'target':'11/1250','case_count':len(rows),'planned_cases':6,
          'strict_integer_systems':sum(r['integer_certificate'] is not None for r in rows),
          'independent_input_replay_passed':False,'actual_Lean_exclusions':0,'complete_global_cover':False,
          'new_zero_proportion_proven':False,'seconds':time.monotonic()-start},'rows':rows}
        args.output.write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8')
        print(json.dumps({'path':path,'case':len(rows),'energy_slack_hint':dual.get('minimum_energy_slack_hint'),
          'strict_integer':candidate is not None,'weighted_rows':len(candidate['selected_integer_rows']) if candidate else 0,
          'selected_kinds':candidate and candidate['selected_row_kind_counts'],'seconds':time.monotonic()-start}),flush=True)
    assert len(rows)==6
if __name__=='__main__':main()
