"""One existing whole-cell derivative test per sampled separating direction.

The directions are selected by the frozen finite-gradient diagnostic.  Both
interval-only and correlated-affine bounds are exact rational arithmetic.
A nonpositive resulting lower bound gives no cell exclusion. Reoptimizing
a linear gradient objective over the old lifted graph would repeat its
already feasible zero-KKT model, so that redundant LP is deliberately skipped.
"""
from pathlib import Path
from fractions import Fraction as F
import gzip,hashlib,json,time
import cover_correlated_direction as engine
HERE=Path(__file__).parent;g=engine.g;SC=g.SC;DS=engine.DS
sha=lambda b:hashlib.sha256(b).hexdigest()


def main():
    start=time.monotonic();raw=(HERE/'cover-gradient-mixture.json').read_bytes();doc=json.loads(raw)
    packed=(HERE/'cover-curvature-parent64.input.json.gz').read_bytes();assert sha(packed)==doc['receipt']['input_sha256']
    oracle=engine.TaylorOracle(HERE/'cover_newjet.json');rows=[];den=1000000
    for row in doc['rows']:
        state=tuple(row['cell']);direction=[round(v*den) for v in row['nearest_gradient_mixture_hint']['separating_direction_hint']]
        # exact_upper is an upper bound on a feasible descent direction;
        # the negative direction tests whether +direction.gradient>0.
        neg=[-x for x in direction];data=[oracle.affine(state[0][g.LOOK[i,j]],state[1][g.LOOK[i,j]]) for i,j,a in g.TERMS]
        upper,flow=engine.exact_upper(state,data,neg);denominator=2*SC*g.D*DS*den
        grid=sum(b*x*DS for b,x in zip(g.BS,direction))
        for i,j,a in g.TERMS:
            z=g.LOOK[i,j];l,u=engine.w.derivative_range(state[0][z],state[1][z]);c=sum(direction[i:j]);grid+=a*c*(l if c>=0 else u)
        rows.append({'path':row['path'],'cell':state,'positive_sample_separating_direction':direction,'direction_scale':den,
          'sampled_directional_derivative_lower_hint':row['nearest_gradient_mixture_hint']['minimum_sample_directional_derivative_hint'],
          'interval_only_whole_cell_lower':str(F(grid,g.D*DS*den)),
          'correlated_whole_cell_lower':str(F(-upper,denominator)),
          'strict_new_cell_exclusion':bool(upper<0),'negative_direction':neg,'upper_numerator':str(upper),
          'unscaled_denominator':str(2*SC*g.D*DS),
          'scalar_affine_data':[[P,str(m0),str(m1),str(err),kind] for P,m0,m1,err,kind in data],'exact_flow':flow,
          'old_graph_fixed_direction_LP_skipped_as_redundant':True})
    receipt={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'input_sha256':sha(raw),
      'parent64_input_sha256':sha(packed),'derivative_table_sha256':oracle.sha,'engine_sha256':sha(Path(engine.__file__).read_bytes()),
      'whole_cell_directions_tested':len(rows),'strict_new_cell_exclusions':sum(r['strict_new_cell_exclusion'] for r in rows),
      'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    (HERE/'cover-gradient-mixture-direction.json').write_text(json.dumps({'receipt':receipt,'rows':rows},separators=(',',':'))+'\n',encoding='utf8')
    print(json.dumps({'receipt':receipt,'bounds':[{k:r[k] for k in ['path','interval_only_whole_cell_lower','correlated_whole_cell_lower','strict_new_cell_exclusion']} for r in rows]}),flush=True)
if __name__=='__main__':main()
