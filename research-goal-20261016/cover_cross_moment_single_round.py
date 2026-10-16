"""Read-only single-round aggregate variant of the global-box Friendly proof.

Generate by direct affine-factor expansion and exact summation. The verify
mode instead uses the frozen replay's canonical nonnegative RLT decomposition
and independent outward-rounding routine. No LP or new kernel evaluation.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,gzip,hashlib,json,time
import cover_cross_moment_global_box as wide
old=wide.old;exact=wide.exact;factor=wide.factor
HERE=Path(__file__).parent;ROOT=HERE.parent;sha=lambda b:hashlib.sha256(b).hexdigest()


def inputs():
    folder=HERE/'cover-cross-moment-global-box-evidence';packed=(folder/'proof.json.gz').read_bytes();doc=json.loads(gzip.decompress(packed))
    params_raw=(ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes();table_raw=(HERE/'cover_newjet.json').read_bytes()
    assert sha(params_raw)==doc['provenance']['parameters_sha256'] and sha(table_raw)==doc['provenance']['derivative_table_sha256']
    params=json.loads(params_raw);checker=old.support.graph.GraphReplay(json.loads(table_raw));states={r['path']:r['before'] for r in doc['source']['cases']}
    compare=json.loads(gzip.decompress((folder/'comparison.json.gz').read_bytes()));cmap={r['path']:r for r in compare['records']}
    return packed,doc,params,checker,states,cmap


def generate():
    start=time.monotonic();packed,doc,params,checker,states,cmap=inputs();cases=[]
    for case in doc['records']:
        state=states[case['path']];bounds,center,radius=wide.global_bounds(state);slabs=dict(case['scalar_affine_data']);combined={'coeff':{},'bound':F(0)}
        for f in case['factors']:
            row=old.old_row(f['old_meta'],state,slabs,params,checker);row['meta']=['base',-1,f['old_meta']];b=[0]*9
            for i,v in f['b']:b[i]=int(v)
            group=factor.factor_row(row,center,radius,int(f['A']),b);factor.add_weighted(combined,group,1)
        p=case['energy_packet'];mu=int(case['energy_weight']);factor.add_weighted(combined,{'coeff':{i:F(v) for i,v in p['row']},'bound':F(p['bound'])},mu)
        assert factor.digest_row(combined)==case['unrounded_full_464_row_sha256'];combined['meta']=['single_exact_aggregate']
        integer=exact.integerize(combined,bounds,10**30);checked=exact.verify_aggregate([integer],[(0,1)],bounds);assert checked['strict_exclusion']
        weight_sum=mu+sum(int(w) for terms in cmap[case['path']]['unmerged_terms_by_factor'] for s,sign,w in terms)
        cases.append({'path':case['path'],'box_policy':wide.POLICY,'unrounded_full_464_row_sha256':factor.digest_row(combined),
          'exact_sparse_coefficients':[[i,str(v)] for i,v in sorted(combined['coeff'].items())],
          'exact_bound':str(combined['bound']),'exact_residual_constant':str(-combined['bound']),
          'integerization_denominator':str(10**30),'outward_integer_coefficients':[[i,str(v)] for i,v in sorted(integer['coeff'].items())],
          'outward_integer_bound':str(integer['bound']),'outward_integer_residual_constant':str(-integer['bound']),
          'rounding_payment':str(integer['rounding_payment']),'box_minimum':str(checked['box_minimum']),'strict_margin':str(checked['strict_margin']),
          'normalized_margin_original_weight_sum':str(checked['strict_margin']/(10**30*weight_sum)),
          'grouped_rounding_margin':case['expected_strict_margin'],'margin_change_from_grouped':str(checked['strict_margin']-F(case['expected_strict_margin'])),
          'original_weight_sum':str(weight_sum),'exact_nonzero_coefficients':len(combined['coeff']),'outward_integer_nonzero_coefficients':len(integer['coeff'])})
        print(json.dumps({'path':case['path'],'single_round_strict':True,'coefficients':len(combined['coeff']),
          'normalized_margin':float(checked['strict_margin']/(10**30*weight_sum))}),flush=True)
    out={'schema':'global-box-exact-aggregate-single-round-v1','scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),
      'source_global_box_proof_gzip_sha256':sha(packed),'box_policy':wide.POLICY,
      'row_convention':'sum_i coefficient_i*variable_i <= bound; residual constant is -bound',
      'all_factors_and_energy_weights_unchanged':True,'rounding_operations_per_case':1,'tight_scalar_box_queries_required':0,
      'cases':cases,'independent_arithmetic_replay_passed':False,'new_cell_exclusions':0,'actual_Lean_exclusions':0,
      'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    p=HERE/'cover-cross-moment-single-round.json';p.write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8')
    print(json.dumps({'single_round_bytes':p.stat().st_size,'single_round_sha256':sha(p.read_bytes()),'seconds':out['seconds']}),flush=True)


def verify():
    start=time.monotonic();packed,doc,params,checker,states,cmap=inputs();raw=(HERE/'cover-cross-moment-single-round.json').read_bytes();data=json.loads(raw)
    assert data['script_sha256']==sha(Path(__file__).read_bytes()) and data['source_global_box_proof_gzip_sha256']==sha(packed)
    # A new box constructor is passed only through the frozen replay hook.
    # It cannot perform scalar tight-box grid queries.
    old.boxes=lambda state,params,checker:wide.global_bounds(state)
    results=[];lookup={c['path']:c for c in data['cases']}
    for case in doc['records']:
        rows,_,bounds,_,_=old.group_rows(case,states[case['path']],params,checker);combined={'coeff':{},'bound':F(0)}
        for row in rows:old.add(combined,row)
        stored=lookup[case['path']];assert old.digest(combined)==stored['unrounded_full_464_row_sha256']==case['unrounded_full_464_row_sha256']
        assert sorted(combined['coeff'].items())==[(i,F(v)) for i,v in stored['exact_sparse_coefficients']]
        assert combined['bound']==F(stored['exact_bound'])==-F(stored['exact_residual_constant'])
        coeff,B,payment=old.support.independent_integer_row(combined,bounds,10**30)
        assert sorted(coeff.items())==[(i,int(v)) for i,v in stored['outward_integer_coefficients']]
        assert B==int(stored['outward_integer_bound'])==-int(stored['outward_integer_residual_constant']) and payment==F(stored['rounding_payment'])
        minimum=sum(v*bounds[i][0 if v>=0 else 1] for i,v in coeff.items());margin=minimum-B
        assert minimum==F(stored['box_minimum']) and margin==F(stored['strict_margin'])>0
        results.append({'path':case['path'],'canonical_RLT_aggregate_matches':True,'single_outward_rounding_matches':True,
          'strict_margin':str(margin),'strict_integer_system':True,'tight_box_queries':0})
    out={'scope':'Independent arithmetic paths: canonical RLT vs direct factors, exact aggregate, independent single outward round and global-box strict margin.',
      'script_sha256':sha(Path(__file__).read_bytes()),'input_sha256':sha(raw),'source_global_box_proof_gzip_sha256':sha(packed),
      'dependency_sources_sha256':old.support.dependency_hashes(),'all_checks_passed':True,'cases':results,
      'no_new_LP_sampling_kernel_queries':True,'new_cell_exclusions':0,'actual_Lean_exclusions':0,
      'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    p=HERE/'cover-cross-moment-single-round-replay.json';p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'single_round_replay_passed':True,'receipt_sha256':sha(p.read_bytes()),'seconds':out['seconds']}),flush=True)


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--verify',action='store_true');args=ap.parse_args()
    verify() if args.verify else generate()
