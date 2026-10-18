"""Prepared O fixed1322606 curvature opportunity gate; no work at import."""
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
import argparse
import gzip
import importlib.util
import json
import os
import sys
import time
import traceback
sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
N2=ROOT/'research-goal-20261018-stageN2-pooled-component-resumption'
SOURCE=ROOT/'research-goal-20261018-record-source-audit/snapshot/Solution.lean'
BASE=ROOT/'research-goal-20261018-record-baseline-replay'
PINS={
 'research-goal-20261018-record-source-audit/snapshot/Solution.lean':'f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf',
 'research-goal-20261018-stageN2-pooled-component-resumption/files.json':'327db7c23c63aeb0ad49236b59303d04fea93a9fcde524caa5998bcd3637369f',
 'research-goal-20261018-stageN2-independent-below/audit-files.json':'8a793215fd7d0e64e8fbcaa388cb99c384d007584a9acdcf78a303ac9a61c39b',
 'research-goal-20261018-stageN2-independent-below/independent-review.json':'ed007f28ad6544935f76af982d09f93dbbce339ac648368ea3a7d21454cd2a5a',
 'research-goal-20261018-stageN2-curvature-interface-static/files.json':'849fba32fc08736e880d28888f0edc7579766afd419520294ab98767ffd67fba',
 'research-goal-20261018-record-baseline-replay/packing_parser_v3.py':'6ccb60ece1069521ace855a1f640365e3cad06a2e68033d9a40e657a3604219a'
}
Q=32768
KAPPA=Q*1024*10**10
TARGET=4*KAPPA*893766123055294719
PAYMENT_METHODS=['group_variance_clamp','one_exact_component_gauge_Laplace']
EXTERNAL_RUNTIME={
 'C:/Python314/python.exe':'3adbbf2af609e206e3ca18cd55fc7c4b52f5c8bb8218dd99fd5a9e50d7a193cd',
 'C:/Python314/python314.dll':'18310593c50ad109fc5c95db1fd5c92ecec9e1bfc66c976df9fc11dd62616d5a'
}
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False).encode('ascii')+b'\n'
def pin(p):
    h=sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''):h.update(block)
    return h.hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def write(p,x):
    with p.open('xb') as f:f.write(canonical(x));f.flush();os.fsync(f.fileno())
def rel(p):return p.relative_to(ROOT).as_posix()
def checked(name):
    p=(ROOT/name).resolve();assert p.is_relative_to(ROOT);return p
def imported(p,name):
    spec=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
def member(desc):
    p=checked(desc['path'])
    with p.open('rb') as f:f.seek(desc['offset']);data=f.read(desc['bytes'])
    assert len(data)==desc['bytes'] and sha256(data).hexdigest()==desc['compressed_member_sha256']
    raw=gzip.decompress(data);assert sha256(raw).hexdigest()==desc['decoded_sha256']
    value=json.loads(raw);assert canonical(value)==raw;return value
def package(p,expected,refs):
    assert pin(p)==expected;refs[rel(p)]=expected
    for key in ['files','read_only_dependencies','dependencies']:
        for item in load(p).get(key,[]):
            q=checked(item['path']);assert pin(q)==item['sha256']
            if 'bytes' in item:assert q.stat().st_size==item['bytes']
            if rel(q) in refs:assert refs[rel(q)]==item['sha256']
            refs[rel(q)]=item['sha256']
def runtime_hashes():
    out={}
    for name,h in EXTERNAL_RUNTIME.items():
        p=Path(name);out[str(p)]=pin(p);assert out[str(p)]==h
    assert str(Path(sys.executable))==str(Path('C:/Python314/python.exe'))
    return out
class WorkLimit(Exception):pass
def limit(start,g):
    if time.monotonic()-start>g['work_limits']['elapsed_seconds']:raise WorkLimit('soft_elapsed_limit')
    if sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())>g['work_limits']['closed_output_bytes']:raise WorkLimit('soft_output_limit')

def cover_original_chain(params,hlo,hhi):
    """Only original consecutive REG cells, no refinement or new intervals."""
    assert hlo<=hhi
    reg=params['REG'];mask=1048575;A=int(reg['packed_A']);B=int(reg['packed_B'])
    for k,chain in enumerate(reg['chains']):
        if not chain:continue
        lo=(A>>(20*k))&mask;hi=(B>>(20*k))&mask
        if not (lo<=hlo<=hhi<=hi):continue
        cells=[c for c in reg['cells'] if c['chain']==k and c['U']>=hlo and c['L']<=hhi]
        assert cells and cells[0]['L']<=hlo and hhi<=cells[-1]['U']
        assert all(a['U']==b['L'] for a,b in zip(cells,cells[1:]))
        return cells
    return None

def fixed_rows(record,source):
    """Read two already independently audited FS packets, no new FS decoding."""
    windows=[member(record['original_components'][str(cid)]) for cid in record['pair']]
    chart=record['chart'];reverses=[c=='rev' for c in chart.split('/')]
    rows=[];rid=155;intervals={};components=[]
    for wi,(w,off,rev) in enumerate(zip(windows,[0,1],reverses)):
        assert w['cell_id']==record['pair'][wi] and len(w['terms'])==34
        for term in w['terms']:
            ti=term['term_id'];i,j=term['edge'];a=term['external_weight_numerator']
            assert source['TS'][ti][:3]==(i,j,a) or list(source['TS'][ti][:3])==[i,j,a]
            edge=(off+8-j,off+8-i) if rev else (off+i,off+j)
            L,U=term['original_term_bounds'];L0=term['original_L0']
            lo=max(F(L,Q),F(17*(edge[1]-edge[0]),20));hi=F(U,Q)
            if edge in intervals:
                oldlo,oldhi=intervals[edge];lo=max(lo,oldlo);hi=min(hi,oldhi)
            assert lo<=hi;intervals[edge]=(lo,hi)
            components.append({'row_id':rid,'kind':'constant','physical_span':list(edge),'source_window':wi,'source_term':ti});rid+=1
            for slot,(mass,p) in enumerate(zip([term['mass_first'],term['mass_second']],term['FS'][2:])):
                if not mass:continue
                assert mass>0 and p in source['PTraw'];raw=source['PTraw'][p]
                vl=max(0,p-((raw>>96)&((1<<20)-1)));vu=p+(raw>>116)
                assert vu>0 and vl<=L<=p<=U<=vu and L0<=L
                row={'row_id':rid,'kind':'anchor','physical_span':list(edge),'source_window':wi,'cell_id':w['cell_id'],
                    'source_term':ti,'source_slot':slot,'source_original_positive_mass':mass,'q_integer':p,
                    'q_physical':str(F(p,Q)),'original_L0':L0,'original_guard':[vl,L,p,U,vu],
                    'original_state_sha256':w['state_sha256'],'original_witness':w['witness']}
                components.append(row);rid+=1
    assert rid==305 and len(components)==150 and len(intervals)==42
    dual=record['normalized_exact_reconstruction']['exact_dual'];mu=list(map(F,dual['raw_row_weights']))
    assert len(mu)==305 and all(v>=0 for v in mu) and dual['checks']['valid']
    for row in components:
        row['raw_dual_weight']=str(mu[row['row_id']])
        if row['kind']=='anchor' and mu[row['row_id']]>0:rows.append(row)
    return rows,intervals,dual,components

def execute(gate_path,gate_sha):
    for name in ['started.json','result.json','failure.json','curvature-packet.json']:
        assert not (HERE/name).exists(),('refuse_retry_or_overwrite',name)
    start=time.monotonic();stage='inputs';refs={};queries=0;last_cell=None;external={}
    try:
        assert pin(gate_path)==gate_sha;g=load(gate_path)
        assert g['fixed_curvature_opportunity_passes_authorized']==1 and g['fixed_G_index']==1322606
        assert g['fixed_pair']==[278,665] and g['fixed_chart']=='rev/id'
        assert g['interval_policy']=='original_REG_consecutive_cells_only_no_subdivision'
        assert g['span_interval_policy']=='direct_original_member_bounds_intersection_plus_sep'
        assert g['payment_methods']==PAYMENT_METHODS and g['new_kernel_anchors_FS_solver_or_Lean_authorized']==0
        assert g['source_CellA_quantitative_replay_authorized'] is True and g['exact_Laplace_linear_solve_calls_authorized']==1
        for name in ['elapsed_seconds','closed_output_bytes']:assert 0<g['work_limits'][name]<g['resource_limits'][name]
        refs[rel(gate_path)]=gate_sha
        for name,h in PINS.items():
            p=checked(name);assert pin(p)==h;refs[name]=h
            if p.name in ['files.json','audit-files.json']:package(p,h,refs)
        package(HERE/'prepared-files.json',g['prepared_manifest_sha256'],refs)
        review=load(ROOT/'research-goal-20261018-stageN2-independent-below/independent-review.json')
        assert review['passed'] and review['fixed_G_index']==1322606 and review['fixed_case_math']['original_dual_rechecked']['valid']
        external=runtime_hashes()
        write(HERE/'started.json',{'pid':os.getpid(),'inputs_sha256':refs,'gate_sha256':gate_sha,
            'external_runtime_sha256_start':external,
            'fixed_G_index':1322606,'new_FS_or_kernel_anchors':0,'source_REG_cells_only':True})
        provider=imported(HERE/'cellA_quantitative.py','O_CellA_source_transcription')
        network=imported(HERE/'weighted_network.py','O_exact_quadratic_algebra')
        parser=imported(BASE/'packing_parser_v3.py','O_frozen_literal_parser');source=parser.load_model()
        params=provider.parameters(SOURCE.read_text(encoding='utf-8'));readout=load(N2/'first-Below-readout.json')
        record=member(readout['proof_record']);assert record['G_index']==1322606 and record['outcome']=='Below'
        rows,intervals,dual,components=fixed_rows(record,source)
        cost=F(dual['checks']['raw_lower_bound']);deficit=F(TARGET)-cost
        assert str(cost)==review['fixed_case_math']['original_dual_rechecked']['cost'] and deficit>0
        assert 0<g['maximum_original_REG_cell_queries']<=len(params['REG']['cells']);limit(start,g)
        cache={};weighted=[];stage='fixed_existing_REG_curvature_cells'
        for row in rows:
            limit(start,g)
            edge=tuple(row['physical_span']);lo,hi=intervals[edge];p=row['q_integer']
            hlo=min(F(p),Q*lo);hhi=max(F(p),Q*hi);cover=cover_original_chain(params,hlo,hhi)
            item={**row,'joint_direct_span_interval':list(map(str,[lo,hi])),
                'required_hull_in_Q_units':list(map(str,[hlo,hhi]))}
            if cover is None:
                item.update({'coverage':'outside_existing_REG_chain','m':'0','c_raw':'0','original_cells':[]})
            else:
                entries=[]
                for cell in cover:
                    key=(cell['L'],cell['U'])
                    if key not in cache:
                        assert queries<g['maximum_original_REG_cell_queries'];queries+=1
                        last_cell={**cell,'active_row_id':row['row_id']};limit(start,g)
                        cache[key]=provider.evaluate_original_cell(params,*key)
                    entries.append(cache[key])
                m=min(F(c['m_quantitative']) for c in entries);assert m>=0
                c=F(row['raw_dual_weight'])*KAPPA*m/2
                item.update({'coverage':'complete_original_REG_chain','original_cells':cover,'m':str(m),'c_raw':str(c)})
            weighted.append(item)
        stage='one_fixed_variance_and_stationary_network_payment'
        limit(start,g)
        variance,vproof=network.variance_clamp(weighted,intervals)
        laplace,lproof=network.laplace_payment(weighted)
        payment=max(variance,laplace);closed=cost+payment>=TARGET
        packet={'schema':'O-fixed-original-REG-quantitative-curvature-opportunity-v1','G_index':1322606,
            'pair':[278,665],'chart':'rev/id','raw_target':str(TARGET),'frozen_raw_dual_cost':str(cost),
            'raw_dual_deficit':str(deficit),'all_original_component_rows':components,'weighted_anchor_rows':weighted,
            'physical_span_intervals':[{'edge':list(e),'interval':list(map(str,v))} for e,v in sorted(intervals.items())],
            'selected_original_CellA_cells':[cache[k] for k in sorted(cache)],'original_REG_cell_queries':queries,
            'variance_clamp_payment':str(variance),'variance_proof':vproof,
            'laplace_payment':str(laplace),'laplace_proof':lproof,'chosen_uniform_payment':str(payment),
            'uniform_raw_lower_bound':str(cost+payment),'minus_target':str(cost+payment-TARGET),
            'conditional_fixed_pair_floor_closes':closed,
            'analytic_condition':'New quantitative CellA lower bridge and strong tangent remainder must be formalized.',
            'all_source_curvature_cells_preexisting_REG':True,'new_subdivision_kernel_anchors_FS_LP_or_Lean_runs':0}
        write(HERE/'curvature-packet.json',packet)
        after={name:pin(ROOT/name) for name in refs};assert after==refs and runtime_hashes()==external
        result={'schema':'O-fixed-curvature-opportunity-result-v1','pid':os.getpid(),'seconds':time.monotonic()-start,
            'inputs_sha256_start':refs,'inputs_sha256_end':after,'original_REG_cell_queries':queries,
            'external_runtime_sha256_start':external,'external_runtime_sha256_end':runtime_hashes(),
            'source_CellA_only':True,'positive_raw_dual_anchor_rows':len(rows),
            'covered_anchor_rows':sum(r['coverage']=='complete_original_REG_chain' for r in weighted),
            'conditional_fixed_pair_floor_closes':closed,'raw_deficit':str(deficit),'uniform_payment':str(payment),
            'raw_margin':str(cost+payment-TARGET),'packet_sha256':pin(HERE/'curvature-packet.json'),
            'new_subdivision_kernel_anchors_FS_LP_or_Lean_runs':0,'exact_Laplace_solve_calls':1,
            'independent_math_and_actual_Lean_transfer_pending':True,'whole_domain_or_unconditional_kappa_proven':False,
            'source_runtime_submission_budget':'unknown','automatic_retry':False}
        write(HERE/'result.json',result)
        print(json.dumps({'fixed_pair_conditional_closes':closed,'selected_original_REG_cells':queries,
            'covered_positive_anchor_rows':result['covered_anchor_rows'],'seconds':result['seconds']}),flush=True)
    except WorkLimit as exc:
        write(HERE/'inconclusive.json',{'stage':stage,'reason':str(exc),'seconds':time.monotonic()-start,
            'source_CellA_queries_started':queries,'last_cell':last_cell,'automatic_retry':False})
    except BaseException as exc:
        write(HERE/'failure.json',{'stage':stage,'error':repr(exc),'traceback':traceback.format_exc(),
            'pid':os.getpid(),'seconds':time.monotonic()-start,'source_CellA_queries_started':queries,
            'last_cell':last_cell,'automatic_retry':False})
        raise
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--execute-authorized-fixed-curvature-O',action='store_true')
    ap.add_argument('--gate');ap.add_argument('--gate-sha256');a=ap.parse_args()
    if not a.execute_authorized_fixed_curvature_O:
        print(json.dumps({'prepared_only':True,'kernel_or_curvature_or_matrix_runs':0}));return
    assert a.gate and a.gate_sha256;execute(checked(a.gate),a.gate_sha256)
if __name__=='__main__':main()
