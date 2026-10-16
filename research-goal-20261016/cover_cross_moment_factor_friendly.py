"""Retain grouped old-row multipliers and substitute only Friendly energy0.

No LP, sampling or point-kernel evaluation. All affine factors and original
energy weights remain byte-for-value identical. The coarser energy row is
weighted before the single 1e30 outward rounding and strict box replay.
"""
from pathlib import Path
from fractions import Fraction as F
import copy,gzip,hashlib,json,time
import cover_cross_moment_factor_replay as replay
HERE=Path(__file__).parent;ROOT=HERE.parent;sha=lambda b:hashlib.sha256(b).hexdigest()


def main():
    start=time.monotonic();old_folder=HERE/'cover-cross-moment-factor-evidence';old_raw=(old_folder/'proof.json.gz').read_bytes();doc=json.loads(gzip.decompress(old_raw))
    comparison=json.loads(gzip.decompress((old_folder/'comparison.json.gz').read_bytes()));cmap={r['path']:r for r in comparison['records']}
    friendly_path=HERE/'window-moment-friendly-packets.json';friendly_raw=friendly_path.read_bytes();friendly=json.loads(friendly_raw);fmap={r['path']:r for r in friendly['rows']}
    assert friendly['inputs_sha256']['strict_original']==doc['provenance']['original_integer_certificate_sha256']
    params_raw=(ROOT/'research-20261016-followup/window_reweight_rational.json').read_bytes();params=json.loads(params_raw)
    table_raw=(HERE/'cover_newjet.json').read_bytes();checker=replay.support.graph.GraphReplay(json.loads(table_raw));states={r['path']:r['before'] for r in doc['source']['cases']}
    result=copy.deepcopy(doc);audits=[];stats=[]
    for case in result['records']:
        original_case=next(r for r in doc['records'] if r['path']==case['path']);fcase=fmap[case['path']]
        case['energy_packet']=fcase['energy0'];case['energy_packet_kind']='friendly-centre-zero'
        assert case['energy_weight']==cmap[case['path']]['original_energy_weight'] and case['factors']==original_case['factors']
        rows,old,bounds,mid,rad=replay.group_rows(case,states[case['path']],params,checker);replay.energy_algebra(case,states[case['path']],params)
        combined={'coeff':{},'bound':F(0)}
        for row in rows:replay.add(combined,row)
        audit=copy.deepcopy(cmap[case['path']]);original={'coeff':{},'bound':F(0)};weight_sum=int(case['energy_weight'])
        for old_row,terms in zip(old,audit['unmerged_terms_by_factor']):
            for s,sign,mu in terms:
                mu=int(mu);weight_sum+=mu;replay.add(original,old_row if s==-1 else replay.rlt(old_row,mid,rad,s,sign),mu)
        replay.add(original,rows[-1]);assert original==combined
        case['unrounded_full_464_row_sha256']=replay.digest(combined)
        audit['unrounded_original_464_row_sha256']=audit['unrounded_grouped_464_row_sha256']=replay.digest(combined);audits.append(audit)
        coeff,B,minimum,margin,payment=replay.aggregate(rows,bounds,10**30);assert margin>0
        case['expected_strict_margin']=str(margin);case['expected_box_minimum']=str(minimum);case['expected_aggregate_bound']=str(B)
        stats.append({'path':case['path'],'affine_factor_groups':len(case['factors']),'all_factors_and_energy_weight_preserved':True,
          'unrounded_original_after_energy_substitution_equals_grouped':True,'new_strict_margin':str(margin),
          'new_normalized_margin_original_weight_sum':str(margin/(10**30*weight_sum)),
          'original_ungrouped_friendly_normalized_margin':fcase['normalized_strict_margin'],
          'new_group_rounding_payment':str(payment)})
        print(json.dumps({'path':case['path'],'strict':True,'groups':len(case['factors']),'normalized_margin':float(margin/(10**30*weight_sum))}),flush=True)
    result['provenance']['base_factor_proof_gzip_sha256']=sha(old_raw);result['provenance']['friendly_packets_path']=friendly_path.relative_to(ROOT).as_posix()
    result['provenance']['friendly_packets_sha256']=sha(friendly_raw)
    folder=HERE/'cover-cross-moment-factor-friendly-evidence';folder.mkdir(exist_ok=True)
    data=(json.dumps(result,separators=(',',':'))+'\n').encode();packed=gzip.compress(data,mtime=0);(folder/'proof.json.gz').write_bytes(packed)
    audit_data=(json.dumps({'schema':'affine-factor-original-multiplier-comparison-v1','proof_gzip_sha256':sha(packed),'records':audits},separators=(',',':'))+'\n').encode()
    audit_packed=gzip.compress(audit_data,mtime=0);(folder/'comparison.json.gz').write_bytes(audit_packed)
    manifest={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'base_proof_gzip_sha256':sha(old_raw),
      'friendly_packets_sha256':sha(friendly_raw),'proof_gzip_sha256':sha(packed),'proof_gzip_bytes':len(packed),
      'proof_uncompressed_sha256':sha(data),'proof_uncompressed_bytes':len(data),'comparison_gzip_sha256':sha(audit_packed),
      'comparison_gzip_bytes':len(audit_packed),'cases':stats,'all_unrounded_polynomials_equal_after_energy_substitution':True,
      'strict_integer_systems':2,'independent_replay_passed':False,'new_cell_exclusions':0,'actual_Lean_exclusions':0,
      'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    (folder/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'proof_bytes':len(packed),'comparison_bytes':len(audit_packed),'seconds':manifest['seconds']}),flush=True)
if __name__=='__main__':main()
