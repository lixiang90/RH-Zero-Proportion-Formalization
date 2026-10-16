"""Re-round the frozen Friendly grouped proof with global u/q boxes +/-7.

All 103/106 nonnegative affine factors and energy weights are unchanged.
Gap boxes stay at the cell limits; H has diagonal [0,1] and off-diagonal
[-1,1]. No 41-term tight scalar-box query, LP, sample, point-kernel query,
PSD round, threshold change or old-file edit is used.
"""
from pathlib import Path
from fractions import Fraction as F
import copy,gzip,hashlib,json,time
import cover_cross_moment_factor_replay as old
import cover_cross_moment_factor_compress as factor
HERE=Path(__file__).parent;ROOT=HERE.parent;exact=old.exact
sha=lambda b:hashlib.sha256(b).hexdigest()
POLICY='cell-g/unit-H/global7-u-q-v1'


def global_bounds(state):
    l=[F(x,32768) for x in state[0][:9]];u=[F(x,32768) for x in state[1][:9]]
    center=[(a+b)/2 for a,b in zip(l,u)];radius=[(b-a)/2 for a,b in zip(l,u)];assert min(radius)>0
    bounds=list(zip(l,u))+[(F(-7),F(7)) for _ in range(41)]
    bounds += [(F(0),F(1)) if i==j else (F(-1),F(1)) for i in range(9) for j in range(i,9)]
    bounds += [(F(-7),F(7)) for _ in range(369)]
    assert len(bounds)==464;return bounds,center,radius


def main():
    start=time.monotonic();source_folder=HERE/'cover-cross-moment-factor-friendly-evidence'
    source_raw=(source_folder/'proof.json.gz').read_bytes();source=json.loads(gzip.decompress(source_raw))
    comparison=json.loads(gzip.decompress((source_folder/'comparison.json.gz').read_bytes()));cmap={r['path']:r for r in comparison['records']}
    params_raw=(ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes();params=json.loads(params_raw)
    table_raw=(HERE/'cover_newjet.json').read_bytes();checker=old.support.graph.GraphReplay(json.loads(table_raw))
    assert sha(params_raw)==source['provenance']['parameters_sha256'] and sha(table_raw)==source['provenance']['derivative_table_sha256']
    result=copy.deepcopy(source);states={r['path']:r['before'] for r in source['source']['cases']};statistics=[];consumer_cases=[]
    for case,original in zip(result['records'],source['records']):
        state=states[case['path']];bounds,center,radius=global_bounds(state);slabs={t:r for t,r in case['scalar_affine_data']};groups=[]
        for f in case['factors']:
            row=old.old_row(f['old_meta'],state,slabs,params,checker);row['meta']=['base',-1,f['old_meta']]
            A=int(f['A']);b=[0]*9
            for s,v in f['b']:assert 0<=s<9 and not b[s];b[s]=int(v)
            assert A>=sum(map(abs,b));groups.append(factor.factor_row(row,center,radius,A,b))
        energy=case['energy_packet'];mu=int(case['energy_weight']);assert mu>0
        groups.append({'coeff':{i:mu*F(v) for i,v in energy['row']},'bound':mu*F(energy['bound']),'meta':['weighted_energy',0]})
        combined={'coeff':{},'bound':F(0)}
        for row in groups:factor.add_weighted(combined,row,1)
        assert factor.digest_row(combined)==case['unrounded_full_464_row_sha256']
        converted=[exact.integerize(r,bounds,10**30) for r in groups]
        check=exact.verify_aggregate(converted,[(i,1) for i in range(len(converted))],bounds);assert check['strict_exclusion']
        assert case['factors']==original['factors'] and case['energy_packet']==original['energy_packet'] and case['energy_weight']==original['energy_weight']
        case.update({'box_policy':POLICY,'global_derivative_bound':'7','expected_strict_margin':str(check['strict_margin']),
          'expected_box_minimum':str(check['box_minimum']),'expected_aggregate_bound':str(check['bound'])})
        weight_sum=mu+sum(int(w) for terms in cmap[case['path']]['unmerged_terms_by_factor'] for s,sign,w in terms)
        normalized=check['strict_margin']/(10**30*weight_sum)
        statistics.append({'path':case['path'],'affine_factor_groups':len(case['factors']),'energy_weight_unchanged':True,
          'all_464_unrounded_coefficients_and_constant_unchanged':True,'strict_margin':str(check['strict_margin']),
          'normalized_margin_original_weight_sum':str(normalized),'outward_group_rounding_payment':str(sum(r['rounding_payment'] for r in converted))})
        consumer=copy.deepcopy(case);consumer.update({'cell':state,'physical_gap_center':list(map(str,center)),
          'physical_gap_radius':list(map(str,radius))});consumer_cases.append(consumer)
        print(json.dumps({'path':case['path'],'groups':len(case['factors']),'strict':True,'normalized_margin':float(normalized)}),flush=True)
    result['schema']='quadratic-energy-affine-factor-global-box-v1';result['box_policy']=POLICY
    result['provenance']['source_friendly_grouped_proof_gzip_sha256']=sha(source_raw)
    folder=HERE/'cover-cross-moment-global-box-evidence';folder.mkdir(exist_ok=True)
    data=(json.dumps(result,separators=(',',':'))+'\n').encode();packed=gzip.compress(data,mtime=0);(folder/'proof.json.gz').write_bytes(packed)
    comparison['proof_gzip_sha256']=sha(packed);cdata=(json.dumps(comparison,separators=(',',':'))+'\n').encode();cpacked=gzip.compress(cdata,mtime=0);(folder/'comparison.json.gz').write_bytes(cpacked)
    view={'schema':'affine-factor-friendly-global-box-consumer-v1','coordinate_scale':32768,'parameter_denominator':10**10,
      'old_row_denominator':str(old.Q),'integerization_denominator':str(10**30),'box_policy':POLICY,
      'variable_layout':{'g':[0,9],'u':[9,50],'h_upper_triangle':[50,95],'q_row_major_9x41':[95,464]},
      'proof_gzip_sha256':sha(packed),'provenance':result['provenance'],'cases':consumer_cases,
      'tight_derivative_box_queries_required':0,'actual_Lean_exclusions':0,'complete_global_cover':False,'new_zero_proportion_proven':False}
    view_path=HERE/'cover-cross-moment-global-box-cases.json';view_path.write_text(json.dumps(view,separators=(',',':'))+'\n',encoding='utf8')
    manifest={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'base_grouped_source_sha256':sha(source_raw),
      'proof_gzip_sha256':sha(packed),'proof_gzip_bytes':len(packed),'proof_uncompressed_sha256':sha(data),'proof_uncompressed_bytes':len(data),
      'comparison_gzip_sha256':sha(cpacked),'comparison_gzip_bytes':len(cpacked),'consumer_view_sha256':sha(view_path.read_bytes()),
      'consumer_view_bytes':view_path.stat().st_size,'box_policy':POLICY,'cases':statistics,
      'all_old_factors_and_energy_weights_preserved':True,'tight_derivative_box_queries_required':0,
      'strict_local_integer_systems':2,'independent_replay_passed':False,'new_cell_exclusions':0,'actual_Lean_exclusions':0,
      'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    (folder/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'proof_bytes':len(packed),'consumer_view_bytes':view_path.stat().st_size,'seconds':manifest['seconds']}),flush=True)
if __name__=='__main__':main()
