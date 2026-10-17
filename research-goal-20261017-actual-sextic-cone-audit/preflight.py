"""Independent pre-solver replay of all 181 exact actual-sextic rows.

Stdlib only: integer moment-ID accumulation, exact Fraction row hashes,
the prescribed rank-one packing identity, old scalar adapter and every
rounded CSR double decoded directly from NPZ/NPY. No producer imports,
solver, Lean, fit, new anchor or actual-function evaluation. Default is
read-only; --write-receipt creates an absent immutable receipt.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations_with_replacement
from array import array
import argparse
import ast
import gzip
import hashlib
import json
import math
import struct
import sys
import time
import zipfile

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
CONE=ROOT/'research-goal-20261017-actual-sextic-cone'
OUT=HERE/'independent-preflight.json'


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def zipped_json(p):return json.loads(gzip.decompress(p.read_bytes()))


def accumulate(target,source,scalar=F(1)):
    for moment,value in source.items():
        updated=target.get(moment,F(0))+scalar*value
        if updated:target[moment]=updated
        else:target.pop(moment,None)


def decode_npy(raw,kind):
    assert raw[:6]==b'\x93NUMPY'
    major,minor=raw[6:8]
    if major==1:hlen=struct.unpack('<H',raw[8:10])[0];offset=10
    else:
        assert major in [2,3];hlen=struct.unpack('<I',raw[8:12])[0];offset=12
    header=ast.literal_eval(raw[offset:offset+hlen].decode('ascii'))
    assert header['fortran_order'] is False and len(header['shape'])==1
    descr=header['descr'];assert descr in (['<f8'] if kind=='d' else ['<i4'])
    body=raw[offset+hlen:];width=8 if kind=='d' else 4
    assert len(body)==header['shape'][0]*width
    values=array(kind);values.frombytes(body)
    if sys.byteorder!='little':values.byteswap()
    if kind=='d':assert all(math.isfinite(x) for x in values)
    return values,body,header


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists(),'Receipt is immutable.'
    began=time.monotonic()
    aggregation_path=CONE/'aggregation.json';hash_path=CONE/'new-row-hashes.json';float_path=CONE/'new-rows-float.npz'
    aggregation=json.loads(aggregation_path.read_bytes());rowhashes=json.loads(hash_path.read_bytes())
    paths=[Path(__file__),aggregation_path,hash_path,float_path]
    assert aggregation['source_sha256_start']==aggregation['source_sha256_end']
    for name,h in aggregation['source_sha256_start'].items():
        p=ROOT/name;assert sha(p)==h
        if p not in paths:paths.append(p)
    extras=['research-goal-20261017-quartic/quartic-model.json.gz',
        'research-goal-20261017-swap-family-quartic/swap-family-normalized.json.gz',
        'research-goal-20261017-degree6-audit/independent-replay.json']
    for name in extras:
        p=ROOT/name
        if p not in paths:paths.append(p)
    initial={p.relative_to(ROOT).as_posix():sha(p) for p in paths}
    assert initial[hash_path.relative_to(ROOT).as_posix()]=='2923c46ac7c57c0a563a339282254a5a78c8842fc59901f85898c122d3a97ac0'
    assert initial[float_path.relative_to(ROOT).as_posix()]=='213be8da6f73755e582763ef63ea2685041aed5d1af6b98f44a0116672f4009c'
    for rec in [aggregation['row_hashes_file'],aggregation['numeric_CSR_file']]:
        p=ROOT/rec['path'];assert p.stat().st_size==rec['bytes'] and sha(p)==rec['sha256']
    packet=zipped_json(ROOT/'research-goal-20261017-actual-sextic-static/actual-sextic.json.gz')
    base=zipped_json(ROOT/'research-goal-20261017-degree6-static/degree6-model.json.gz')
    old=zipped_json(ROOT/extras[0]);family=zipped_json(ROOT/extras[1])
    mon=[tuple(m) for m in packet['monomials']]
    assert mon==[m for degree in range(7) for m in combinations_with_replacement(range(9),degree)]
    assert mon==[tuple(m) for m in base['monomials']] and len(mon)==5005
    index={m:k for k,m in enumerate(mon)}
    assert packet['energy_slack_column']==base['energy_slack_column']==5004

    # Rehash every old row after the sole old slack-column remap.
    legacy=old['linear_rows']+family['additional_linear_rows'];assert len(legacy)==5803
    adapter=base['old_row_adapter'];assert adapter['only_column_map']==[[714,5004]] and adapter['rows']==5803
    old_digest=hashlib.sha256();slack_rows=[]
    for rid,row in enumerate(legacy):
        assert all(0<=k<=714 for k,_ in row['coefficients'])
        coefficients=[[5004 if k==714 else k,v] for k,v in row['coefficients']]
        mapped={**row,'coefficients':coefficients}
        old_digest.update(json.dumps(mapped,sort_keys=True,separators=(',',':')).encode()+b'\n')
        if any(k==714 for k,_ in row['coefficients']):slack_rows.append(rid)
    assert old_digest.hexdigest()==adapter['mapped_canonical_JSONL_sha256']
    assert slack_rows==[5793,5794]
    expected_boxes=[]
    for mid,m in enumerate(mon[715:],715):
        even=all(m.count(r)%2==0 for r in set(m))
        expected_boxes.append([mid-1,0 if even else -1,1])
    assert expected_boxes==base['new_moment_boxes'] and len(expected_boxes)*2==8580
    assert len(base['blocks'])==73

    # Independently decode the saved NPY payloads; never import numpy.
    arrays={};bodies={};headers={}
    with zipfile.ZipFile(float_path) as archive:
        assert sorted(archive.namelist())==['b.npy','data.npy','indices.npy','indptr.npy','shape.npy']
        for name in ['data','indices','indptr','b','shape']:
            values,body,header=decode_npy(archive.read(name+'.npy'),'d' if name in ['data','b'] else 'i')
            arrays[name]=values;bodies[name]=body;headers[name]=header
    assert list(arrays['shape'])==[181,5005]
    assert len(arrays['indptr'])==182 and arrays['indptr'][0]==0
    assert arrays['indptr'][-1]==len(arrays['indices'])==len(arrays['data'])==905724
    assert len(arrays['b'])==181

    powers=[{k:F(v) for k,v in row['terms']} for row in packet['span_powers']]
    edges=packet['edges'];incident=packet['coordinate_incident_edges'];assert len(edges)==41
    field_names=['absolute_L6_coefficients_in_d','derivative_U5_coefficients_in_d','derivative_E6_coefficients_in_d']
    # Integer moment IDs avoid producer polynomial-key manipulation.
    edge_polys=[]
    for edge in edges:
        w=F(edge['weight']);components=[]
        for field in field_names:
            poly={}
            for degree,c in enumerate(edge[field]):accumulate(poly,powers[edge['power_ids'][degree]],w*F(c))
            components.append(poly)
        edge_polys.append(components)
    L={k:F(v) for k,v in packet['pressure_polynomial']}
    for ep in edge_polys:accumulate(L,ep[0])
    P=[];E=[];pressure=list(map(F,packet['pressure_coefficients_b']))
    for r in range(9):
        pr={0:pressure[r]};er={}
        for eid in incident[r]:accumulate(pr,edge_polys[eid][1]);accumulate(er,edge_polys[eid][2])
        P.append(pr);E.append(er)

    y=[F((-1)**r*(r+1),19) for r in range(9)]
    assert y==list(map(F,rowhashes['fixed_rank1_y']))
    assert rowhashes['fixed_rank1_is_only_packing_test_not_warm_seed_or_feasibility_claim'] is True
    moment_values=[]
    for m in mon:
        v=F(1)
        for r in m:v*=y[r]
        moment_values.append(v)
    # Factor values independently avoid a second evaluation of expanded rows.
    edge_values=[]
    for edge in edges:
        d=sum(F(v)*moment_values[k] for k,v in edge['d_polynomial'])
        w=F(edge['weight'])
        edge_values.append([w*sum(F(c)*d**k for k,c in enumerate(edge[field])) for field in field_names])
    factor_L=sum(F(v)*moment_values[k] for k,v in packet['pressure_polynomial'])+sum(v[0] for v in edge_values)
    factor_P=[pressure[r]+sum(edge_values[eid][1] for eid in incident[r]) for r in range(9)]
    factor_E=[sum(edge_values[eid][2] for eid in incident[r]) for r in range(9)]
    stream=hashlib.sha256();rounded=0;nonzero=0;identities=0
    records=rowhashes['rows'];descriptors=packet['new_scalar_rows']
    assert len(records)==len(descriptors)==181
    for rid,(descriptor,record) in enumerate(zip(descriptors,records)):
        assert rid==descriptor['id']==record['row']
        if rid==0:
            assert descriptor['kind']=='absolute_energy_L6'
            bound=F(packet['target'])-L.get(0,F(0))
            coeff={mid-1:value for mid,value in L.items() if mid}
            meta=['actual_sextic_absolute_energy_unsoftened']
            expected_slack=F(packet['target'])-factor_L
        else:
            r=descriptor['coordinate'];test=descriptor['test_monomial_id'];sign=descriptor['sign']
            q=E[r].copy()
            for mid,value in P[r].items():
                shifted=index[tuple(sorted(mon[mid]+mon[test]))]
                accumulate(q,{shifted:value},F(sign))
            bound=q.get(0,F(0));coeff={mid-1:-value for mid,value in q.items() if mid}
            meta=['actual_sextic_free_KKT',r,test,sign]
            expected_slack=factor_E[r]+sign*moment_values[test]*factor_P[r]
        assert all(0<=column<5004 for column in coeff)
        scale=max(F(1,1000),abs(bound),max(map(abs,coeff.values()),default=F(0)))
        ordered=sorted(coeff.items())
        canonical={'coefficients':[[k,str(v)] for k,v in ordered],'bound':str(bound),'scale':str(scale),'meta':meta}
        raw=json.dumps(canonical,sort_keys=True,separators=(',',':')).encode()
        digest=hashlib.sha256(raw).hexdigest();stream.update(raw+b'\n')
        assert digest==record['exact_canonical_row_sha256']
        assert record['meta']==meta and F(record['bound'])==bound and F(record['scale'])==scale
        assert record['nonzero_coefficients']==len(coeff)
        exact=bound-sum(v*moment_values[k+1] for k,v in ordered)
        assert exact==expected_slack==F(record['fixed_rational_rank1_exact_slack'])
        assert exact/scale==F(record['fixed_rational_rank1_normalized_slack'])
        assert record['energy_slack_coefficient_absent'] is True;identities+=1
        start=arrays['indptr'][rid];end=arrays['indptr'][rid+1]
        assert end-start==len(ordered) and list(arrays['indices'][start:end])==[k for k,_ in ordered]
        for offset,(column,value) in enumerate(ordered,start):
            expected=struct.pack('<d',float(value/scale))
            assert bodies['data'][offset*8:(offset+1)*8]==expected
            rounded+=1
        assert bodies['b'][rid*8:(rid+1)*8]==struct.pack('<d',float(bound/scale));rounded+=1
        nonzero+=len(ordered)
    assert stream.hexdigest()==rowhashes['exact_canonical_rows_JSONL_sha256']==aggregation['exact_canonical_rows_JSONL_sha256']
    assert stream.hexdigest()=='3491df37b6f36e00359c1af20ee89f15fe2ccfddba50892286064b77828b2475'
    assert nonzero==905724 and rounded==905905 and identities==181
    assert not any(name.split('.')[0] in ['numpy','scipy','scs'] for name in sys.modules)
    final={p.relative_to(ROOT).as_posix():sha(p) for p in paths};assert final==initial
    report={'scope':__doc__,'status':'all181_exact_rows_old_adapter_and_every_CSR_float_independently_passed',
        'source_sha256_start':initial,'source_sha256_end':final,'all_inputs_unchanged':True,
        'new_exact_canonical_rows_checked':181,'exact_canonical_rows_JSONL_sha256':stream.hexdigest(),
        'row_bounds_scales_and_meta_checked':181,'fixed_rank1_packing_identities_checked':identities,
        'fixed_rank1_is_not_a_feasibility_or_seed_claim':True,'numeric_CSR_shape':[181,5005],
        'exact_nonzero_coefficients_checked':nonzero,'IEEE754_float64_values_checked_bitwise':rounded,
        'CSR_indices_and_indptr_exact':True,'new_rows_energy_slack_column_absent':True,
        'old_adapter_rows_checked':5803,'only_old_column_remap':[714,5004],
        'mapped_old_rows_JSONL_sha256':old_digest.hexdigest(),'legacy_slack_row_indices':slack_rows,
        'high_degree_moment_boxes_checked':4290,'box_scalar_rows':8580,'old_PSD_blocks_retained_by_hash':73,
        'NPY_headers':headers,'producer_imported':False,'pure_stdlib':True,
        'new_points_or_fits':0,'new_actual_function_evaluations':0,'solver_calls':0,'Lean_invocations':0,
        'numerical_feasibility_or_exclusion_claimed':False,'strict_projection_shrink_proved':False,
        'global_floor_proved':False,'new_zero_proportion_proven':False,
        'elapsed_milliseconds':int((time.monotonic()-began)*1000)}
    if args.write_receipt:OUT.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({k:report[k] for k in ['status','new_exact_canonical_rows_checked',
        'exact_nonzero_coefficients_checked','IEEE754_float64_values_checked_bitwise','elapsed_milliseconds']}))


if __name__=='__main__':
    if not __debug__:raise RuntimeError('Assertions must remain enabled')
    main()
