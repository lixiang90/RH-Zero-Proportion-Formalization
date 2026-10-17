"""Static active-dependency, reuse and source-byte inventory of one fixed ray.

Read existing integers, rationals, schemas and source only. No optimizer,
eigensolver, transcendental/actual-function evaluation, precision/rank
choice, new point, Lean invocation or certificate recombination occurs.
Default read-only; --write-receipt creates an absent inventory.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse
import gzip
import hashlib
import json
import re
import time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
OUT=HERE/'static-inventory.json'


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def load(p):
    raw=p.read_bytes()
    return json.loads(gzip.decompress(raw) if p.suffix=='.gz' else raw)


def array_bytes(values):return len(('#['+','.join(map(str,values))+']').encode('utf8'))


def own_closure(names):
    seen={};external=set();pending=list(names)
    while pending:
        name=pending.pop()
        if name in seen:continue
        path=ROOT/(name.replace('.','/')+'.lean')
        if not path.exists():external.add(name);continue
        text=path.read_text(encoding='utf8')
        seen[name]={'path':path.relative_to(ROOT).as_posix(),'bytes':path.stat().st_size,'sha256':sha(path)}
        for line in text.splitlines():
            match=re.match(r'^import\s+(.+)',line)
            if match:pending.extend(match.group(1).split('--')[0].split())
    return list(seen.values()),sorted(external)


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists()
    began=time.monotonic()
    names=['research-goal-20261017-actual-sextic-exact-ray/quantized-ray.json.gz',
        'research-goal-20261017-actual-sextic-exact-ray/quantization.json',
        'research-goal-20261017-actual-sextic-exact-ray/exact-enclosure-certificate.json',
        'research-goal-20261017-actual-sextic-exact-ray/exact-combination.json',
        'research-goal-20261017-degree6-static/degree6-model.json.gz',
        'research-goal-20261017-quartic/quartic-model.json.gz',
        'research-goal-20261017-swap-family-quartic/swap-family-normalized.json.gz',
        'research-goal-20261017-actual-sextic-static/actual-sextic.json.gz',
        'research-goal-20261016/cover-residual-psd-rational-inputs.json',
        'research-goal-20261016/window-moment-friendly-packets.json',
        'StructuralGoal20261016/WindowMomentEnergyCertificate.lean',
        'StructuralGoal20261016/WindowCellDerivative.lean',
        'StructuralGoal20261016/WindowFixedDerivative.lean',
        'StructuralGoal20261016/WindowDerivativeTableArithmetic.lean',
        'StructuralGoal20261016/WindowRationalInterval.lean',
        'StructuralGoal20261016/WindowConvexityCertificate.lean',
        'StructuralGoal20261016/WindowGlobalCompetitor.lean',
        'StructuralGoal20261016/WindowBoundedMomentFarkas.lean',
        'research-goal-20261016/DIRECTION.zh.md']
    paths=[Path(__file__)]+[ROOT/name for name in names]
    initial={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    ray,quant,cert,comb,model,old,family,new,inputs,friendly=[load(ROOT/name) for name in names[:10]]
    assert sha(ROOT/names[0])=='4862b3437fbc68766e1870afdabda9ea466b18750e2715cbe953e0b8cd363805'
    assert sha(ROOT/names[2])=='7935f4945013c087357141c6f4406ef1b83c03fd9c8cfef61a7cd397f21e57a0'
    lam=ray['scalar_weight_numerators'];factors=ray['PSD_factors']
    assert len(lam)==14564 and all(isinstance(v,int) and v>=0 for v in lam)
    assert [i for i,v in enumerate(lam) if not v]==[5793,5794]
    assert len(factors)==73 and all(any(any(row) for row in f['factor_numerators_by_row']) for f in factors)
    assert sum(f['column_count'] for f in factors)==3010
    assert all(f['column_count']==f['size'] for f in factors)
    active_groups=[]
    for block,factor in zip(model['blocks'],factors):
        q=model['multipliers'][block['multiplier_id']]
        active_groups.append({'block_id':factor['block_id'],'name':block['name'],'basis_size':factor['size'],
            'factor_columns':factor['column_count'],'multiplier_meta':q['meta'],'multiplier_terms':len(q['terms'])})
    new_anchor_map={F(e['anchor']):e for e in new['edges']}
    family_by_anchor={}
    for e in family['scalar_packets']:family_by_anchor.setdefault(F(e['anchor']),[]).append(e)
    reused=[]
    for eid,e in enumerate(new['edges']):
        exact=[p['id'] for p in family_by_anchor.get(F(e['anchor']),[]) if
               p['anchor_derivative_intervals_orders_0_to_4']==e['point_intervals_orders_0_to_6'][:5]]
        if exact:reused.append([eid,exact])
    old_anchors={F(e['anchor']) for e in old['edge_packets']}
    new_anchors={F(e['anchor']) for e in new['edges']}
    swap_anchors={F(e['anchor']) for e in family['scalar_packets']}
    proved_anchors={F(e['p']) for e in friendly['point_rows']}
    old_q5=set();swap_q5=set();new_q7=set()
    for edge in old['edge_packets']:old_q5.update(edge['whole_span_w5_grid_cells'])
    for edge in family['scalar_packets']:swap_q5.update(edge['whole_span_w5_grid_cells'])
    for edge in new['edges']:new_q7.update(edge['whole_span_w7_grid_cells'])
    assert len(new_q7)==658 and len(swap_q5)==622 and len(old_q5)==658
    integers=[v for factor in factors for row in factor['factor_numerators_by_row'] for v in row]
    assert len(integers)==190150
    lambda_bytes=array_bytes(lam)
    factor_bytes=sum(array_bytes(v for row in factor['factor_numerators_by_row'] for v in row) for factor in factors)
    interval_bytes=array_bytes(cert['coefficient_lower_numerators'])+array_bytes(cert['coefficient_upper_numerators'])
    api_names=['StructuralGoal20261016.'+name for name in ['WindowBoundedMomentFarkas','WindowRationalInterval',
        'WindowDerivativeTableArithmetic','WindowGramExpansion','WindowDirectionalAffine',
        'WindowGlobalCompetitor','WindowKKTInstance','WindowMomentEnergy','WindowRecordLowerFloor']]
    closure,external=own_closure(api_names)
    sources={rec['path']:rec['sha256'] for rec in closure}
    for name,h in sources.items():assert sha(ROOT/name)==h
    point_rows=friendly['rows'];old_packet=inputs['energy_packets'][0]
    report={'scope':__doc__,'status':'fixed_all_active_dependency_and_source_inventory_complete',
        'source_sha256_start':initial,'source_sha256_end':initial,'all_inputs_unchanged':True,
        'fixed_denominators':{'scalar':ray['scalar_weight_denominator'],'factor':factors[0]['factor_denominator'],
                              'atom_enclosure':cert['fixed_interval_denominator']},
        'active_scalar_rows':sum(v!=0 for v in lam),'only_zero_scalar_rows':[5793,5794],
        'active_old_scalar_metadata_counts':cert['active_old_scalar_metadata_counts'],
        'active_new_rows':181,'active_Gram_blocks':active_groups,
        'old_common_anchor_equals_new_layout_center':old['common_anchor']==new['normalized_gap_center'],
        'old_common_anchor_equals_inputs_energy0':old['common_anchor']==old_packet['centre'],
        'existing_proved_friendly_energy_paths':[r['path'] for r in point_rows],
        'current_cell_path':old['path'],'current_cell_has_same_path_as_proved_friendly_packet':any(r['path']==old['path'] for r in point_rows),
        'point_provider_counts':{'old_P3_anchors':len(old_anchors),'new_sextic_anchors':len(new_anchors),
            'swap_normalized_anchors':len(swap_anchors),'proved_friendly_anchors':len(proved_anchors),
            'old_P3_anchor_matches_to_friendly':len(old_anchors&proved_anchors),
            'new_sextic_anchor_matches_to_friendly':len(new_anchors&proved_anchors),
            'swap_anchor_matches_to_friendly':len(swap_anchors&proved_anchors),
            'old_P3_integer_anchors':sum(a.denominator==1 for a in old_anchors),
            'new_sextic_integer_anchors':sum(a.denominator==1 for a in new_anchors),
            'swap_integer_anchors':sum(a.denominator==1 for a in swap_anchors),
            'new_sextic_orders0to4_exact_matches_in_swap_packets':len(reused)},
        'exact_shared_point_packets':reused,
        'grid_provider_counts':{'old_q5_cells':len(old_q5),'swap_q5_cells':len(swap_q5),'new_q7_cells':len(new_q7),
            'old_q5_minus_swap_q5':len(old_q5-swap_q5),'swap_q5_minus_old_q5':len(swap_q5-old_q5),
            'union_cell_indices':len(old_q5|swap_q5|new_q7)},
        'literal_data_inventory':{'scalar_integer_count':len(lam),'Gram_integer_count':len(integers),
            'Gram_positive_columns':sum(f['column_count'] for f in factors),'scalar_max_bit_length':max(v.bit_length() for v in lam),
            'factor_max_absolute_bit_length':max(abs(v).bit_length() for v in integers),
            'scalar_flat_decimal_array_bytes':lambda_bytes,'factor_flat_decimal_arrays_bytes':factor_bytes,
            'weights_and_factors_decimal_array_bytes':lambda_bytes+factor_bytes,
            'two_coefficient_endpoint_decimal_arrays_bytes':interval_bytes,
            'weights_factors_and_endpoints_decimal_array_bytes':lambda_bytes+factor_bytes+interval_bytes,
            'fixed_quantized_packet_gzip_bytes':(ROOT/names[0]).stat().st_size,
            'fixed_quantized_packet_uncompressed_bytes':quant['quantized_packet']['uncompressed_bytes'],
            'full_metadata_certificate_bytes':(ROOT/names[2]).stat().st_size},
        'naive_selected_existing_API_import_closure':{'root_modules':api_names,'module_count':len(closure),
            'own_unminified_source_bytes':sum(rec['bytes'] for rec in closure),'files':closure,'external_imports':external,
            'includes_current_unused_helpers':True,'future_new_analytic_and_SOS_sources_not_included':True},
        'exact_certificate_replayed_here':False,'fixed_ray_recombined_here':False,
        'dependency_transfer_payments_computed':False,'new_kernel_evaluations':0,'new_points':0,
        'optimizer_calls':0,'eigensolver_calls':0,'Lean_invocations':0,'parameter_or_rank_changes':0,
        'actual_cell_exclusion_proven':False,'global_floor_proved':False,'single_file_size_contract_proved':False}
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert initial==final
    report['source_sha256_end']=final;report['elapsed_milliseconds']=int((time.monotonic()-began)*1000)
    if args.write_receipt:OUT.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:report[k] for k in ['status','point_provider_counts','grid_provider_counts','literal_data_inventory']}))
    print(json.dumps({'naive_existing_API_modules':len(closure),'naive_existing_API_source_bytes':sum(rec['bytes'] for rec in closure),
                      'elapsed_milliseconds':report['elapsed_milliseconds']}))


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
