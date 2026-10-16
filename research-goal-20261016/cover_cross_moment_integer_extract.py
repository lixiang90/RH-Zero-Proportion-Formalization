"""Reconstruct outward integer Farkas candidates from floating dual hints.

Discovery imports are confined to rebuilding the already frozen old graph
ingredients. All row products, integerization, residual boxes and strict
sign tests use the separate Fraction-only exact row implementation. This
stage does not independently prove the analytic input intervals or Lean
soundness; a later independent replay must recheck those obligations.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,gzip,hashlib,json,time
import cover_lifted_graph_probe as old
import cover_cross_moment_exact_rows as exact

HERE=Path(__file__).parent;sha=lambda b:hashlib.sha256(b).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();assert not args.output.exists(),'Use a new output.'
    start=time.monotonic();input_paths=[HERE/'cover-cross-moment-energy-dual-two.json',HERE/'cover-cross-moment-energy-two.json',HERE/'cover-curvature-parent64.input.json.gz',HERE/'cover_newjet.json']
    raw=[p.read_bytes() for p in input_paths];duals=json.loads(raw[0]);energy=json.loads(raw[1]);doc=json.loads(gzip.decompress(raw[2]))
    cases={c['path']:c for c in doc['cases']};packets={c['path']:c['energy_packets'] for c in energy['rows']}
    taylor=old.context.curvature.first.TaylorOracle(input_paths[3]);graph=old.GraphOracle(input_paths[3]);results=[]
    for case in duals['rows']:
        path=case['path'];state=tuple(cases[path]['before']);dh=case['dual_hint'];assert dh['LP_success'] and dh['minimum_energy_slack_hint']>0
        rr,bb,integer,meta,data,obj,stats=old.build(state,taylor,graph,True)
        ubounds=[]
        for i,j,aw in old.g.TERMS:
            z=old.g.LOOK[i,j];facets,n=graph.facets(state[0][z],state[1][z])
            U=min(F(C,old.SC*old.DS) for sign,S,C in facets if sign==1 and S==0)
            L=max(F(C,old.SC*old.DS) for sign,S,C in facets if sign==-1 and S==0);ubounds.append((L,U))
        model=exact.inputs(state,integer,meta,ubounds,packets[path]);assert len(model['rows'])==dh['base_rows']+dh['energy_rows']
        selected=dh['nonzero_row_dual_weights'];indices=[i for i,w in selected]
        coefficients=[w/float(model['rows'][i]['scale']) for i,w in selected];mx=max(coefficients)
        integers=[exact.integerize(model['rows'][i],model['bounds'],10**30) for i in indices]
        attempts=[];chosen=None
        for power in [32,48,64]:
            weights=[round(w/mx*2**power) for w in coefficients]
            weighted=[(i,mu) for i,mu in enumerate(weights) if mu]
            checked=exact.verify_aggregate(integers,weighted,model['bounds']);attempts.append({'power':power,'strict':checked['strict_exclusion'],'margin':str(checked['strict_margin'])})
            if checked['strict_exclusion']:
                chosen=(power,weights,checked);break
        assert chosen is not None,attempts
        power,weights,checked=chosen
        saved=[]
        for index,mu,row in zip(indices,weights,integers):
            if not mu:continue
            saved.append({'row_index':index,'meta':row['meta'],'weight':str(mu),
              'integer_coefficients':[[k,str(a)] for k,a in sorted(row['coeff'].items())],
              'integer_bound':str(row['bound']),'rounding_payment':str(row['rounding_payment'])})
        aggregate={k:([[i,str(v)] for i,v in sorted(value.items())] if k=='coefficient' else str(value) if isinstance(value,(F,int)) and not isinstance(value,bool) else value) for k,value in checked.items()}
        result={'path':path,'cell':[list(x) for x in state],'old_integer_rows':[[list(ag),list(au),str(B)] for ag,au,B in integer],
          'old_meta':meta,'scalar_affine_data':[[P,str(m0),str(m1),str(err),kind] for P,m0,m1,err,kind in data],
          'u_bounds':[[str(l),str(u)] for l,u in ubounds],'energy_packets':packets[path],
          'integerization_denominator':str(10**30),'dual_weight_power':power,'selected_integer_rows':saved,
          'box_bounds':[[str(l),str(u)] for l,u in model['bounds']],
          'aggregate':aggregate,'attempts':attempts,'strict_integer_system_contradiction':True,
          'analytic_input_soundness_independently_verified':False,'actual_Lean_exclusion_proven':False}
        results.append(result)
        print(json.dumps({'path':path,'strict':True,'weighted_rows':len(saved),'power':power,'margin_divided_by_row_scale_and_weight_sum':float(checked['strict_margin']/(10**30*sum(weights))),'seconds':time.monotonic()-start}),flush=True)
    receipt={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'exact_rows_sha256':sha(Path(exact.__file__).read_bytes()),
      'old_graph_producer_sha256':sha(Path(old.__file__).read_bytes()),'inputs':{p.name:sha(b) for p,b in zip(input_paths,raw)},
      'strict_integer_systems':len(results),'analytic_inputs_verified_here':False,'actual_Lean_exclusions':0,
      'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    args.output.write_text(json.dumps({'receipt':receipt,'rows':results},separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
