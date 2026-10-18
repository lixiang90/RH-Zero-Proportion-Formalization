"""Prepared E: original scalar leaf floors first, then unchanged exact DBM.

No implicit execution. Requires new gate, frozen general floor proof and D
independent review. Fixed B data and targets only; no new kernel/FS/points/LP.
"""
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
from collections import Counter
import argparse
import gzip
import importlib.util
import json
import os
import sys
import time
import traceback

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
B=ROOT/'research-goal-20261018-stageB-classification'
B_PIN='3f9408f2cf1ceae12339456da034d9e8f175f828cf2d53a652339ee79eec89ad'
ENGINE_PATH=ROOT/'research-goal-20261018-stageC-dbm/scan_once.py'
ENGINE_PIN='323ca76957f6cd9055d09037f69af8abef5d1f9af0dfa1c2153254a3124a1522'
SC=32768
V=10**10
R=1024
KAPPA=SC*V*R
SA=10**20
CN=893616123055294719
TAU_N=893916123055294719
C_N=893766123055294719
DELTA_N=TAU_N-CN
PAYMENT_THRESHOLD=KAPPA*DELTA_N
N=1187
ORIS=('id/id','id/rev','rev/id','rev/rev')
TOTAL=len(ORIS)*N*N
MAGIC=b'RZE1\n'
MAX_SECONDS=300
MAX_BYTES=20000000

def pin(p):
    h=sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''):h.update(block)
    return h.hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def rel(p):return p.relative_to(ROOT).as_posix()
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode('ascii')+b'\n'
def write_new(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())

def inputs(gate_path,gate_sha):
    assert gate_path.is_relative_to(ROOT) and pin(gate_path)==gate_sha
    g=load(gate_path)
    assert g['pair_model_passes_authorized']==1
    assert g['stageB_producer_manifest_sha256']==B_PIN
    assert int(g['tau_numerator'])==TAU_N and int(g['c9_numerator'])==CN
    assert int(g['c_numerator'])==C_N and int(g['denominator'])==SA
    assert g['separation']=='17/20' and g['exception_count']==N
    assert tuple(g['orientations'])==ORIS
    assert g['resource_limits']=={'elapsed_seconds':MAX_SECONDS,'closed_output_bytes':MAX_BYTES}
    assert 2*C_N==CN+TAU_N and DELTA_N==3*10**14
    assert PAYMENT_THRESHOLD==2*KAPPA*(C_N-CN)
    assert int(g['kappa'])==KAPPA and int(g['payment_threshold'])==PAYMENT_THRESHOLD
    assert g['total_cases']==TOTAL and g['stop_at_first_underpaid_feasible'] is True
    refs={rel(gate_path):gate_sha,rel(ENGINE_PATH):ENGINE_PIN}
    for p in [Path(__file__),HERE/'run_once.py',HERE/'replay_witnesses.py']:refs[rel(p)]=pin(p)
    manifests=[(B/'files.json',B_PIN),
        (ROOT/g['stageB_independent_manifest_path'],g['stageB_independent_manifest_sha256']),
        (ROOT/g['source_floor_static_manifest_path'],g['source_floor_static_manifest_sha256']),
        (ROOT/g['stageD_independent_manifest_path'],g['stageD_independent_manifest_sha256']),
        (ROOT/g['stageE_static_manifest_path'],g['stageE_static_manifest_sha256'])]
    for p,expected in manifests:
        assert p.is_relative_to(ROOT) and pin(p)==expected;refs[rel(p)]=expected
        package=load(p)
        for field in ['files','package_files','read_only_dependencies','dependency_files','dependencies','read_only_existing_references']:
            for row in package.get(field,[]):
                q=ROOT/row['path'];assert q.is_relative_to(ROOT) and pin(q)==row['sha256']
                if 'bytes' in row:assert q.stat().st_size==row['bytes']
                if row['path'] in refs:assert refs[row['path']]==row['sha256']
                refs[row['path']]=row['sha256']
    assert pin(ENGINE_PATH)==ENGINE_PIN
    spec=importlib.util.spec_from_file_location('frozen_stageC_geometry_for_E',ENGINE_PATH)
    engine=importlib.util.module_from_spec(spec);spec.loader.exec_module(engine)
    b=load(B/'classification.json')
    assert b['passed'] and b['original_cN']==CN and b['tau_numerator']==TAU_N
    assert int(b['integer_debit'])==PAYMENT_THRESHOLD
    assert b['classification_counts']=={'closed_numeric_at_tau':11859,'exception':N,'reflection_ordered_half_exclusions':595}
    spans=[tuple(x) for x in b['pair_order_from_source']]
    assert len(spans)==36 and set(spans)=={(i,j) for i in range(9) for j in range(i+1,9)}
    assert spans[:8]==[(r,r+1) for r in range(8)]
    assert spans[8:]==[tuple(x) for x in b['PR_order_from_source']]
    packet=b['outputs']['exceptions'];p=ROOT/packet['path'];assert pin(p)==packet['sha256']
    cells=[];margins=[]
    with gzip.open(p,'rt',encoding='ascii') as f:
        for line in f:
            c=json.loads(line);s=c['state'];lo=s['L']+s['A'];hi=s['U']+s['B']
            assert c['exception_id']==len(cells) and c['kind']=='exception'
            assert s['M']==0 and len(lo)==len(hi)==36
            assert c['coordinate_scale']==SC and c['separation']=='17/20' and c['relaxed_orientation'] is True
            state=[v for pair in zip(lo,hi) for v in pair]+[0]
            assert sha256(canonical(state)).hexdigest()==c['state_sha256']
            m=int(c['original_margin']);mt=int(c['tau_margin'])
            assert m>=0 and mt==m-PAYMENT_THRESHOLD<0
            cells.append(c);margins.append(m)
    assert len(cells)==N
    return refs,engine,spans,cells,margins

class ResourceStop(Exception):pass

def execute(gate_path,gate_sha):
    assert __debug__
    for name in ['started.json','model.json','failure.json','inconclusive.json','witness-prefix.bin.gz']:
        assert not (HERE/name).exists(),('existing_attempt',name)
    started=time.monotonic();checked=0;cycles=0;counts=Counter();current=None;refs={};rawhash=sha256();nraw=0
    def limit():
        if time.monotonic()-started>MAX_SECONDS:raise ResourceStop('elapsed_300_seconds')
        if sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())>MAX_BYTES:raise ResourceStop('closed_output_20000000_bytes')
    try:
        refs,geom,spans,cells,margins=inputs(gate_path,gate_sha)
        write_new(HERE/'started.json',{'schema':'fixed-E-scalar-floor-and-DBM-start-v1','pid':os.getpid(),
            'time_unix':time.time(),'model_attempt':1,'inputs_sha256':refs,'case_order':'orientation-major then prefix id then suffix id',
            'total_cases':TOTAL,'KAPPA':KAPPA,'delta_numerator':DELTA_N,'payment_threshold':str(PAYMENT_THRESHOLD)})
        orient=[[geom.make_orientation(c,reverse,spans) for c in cells] for reverse in [False,True]]
        single_cache={}
        def single(cid,rev):
            key=cid,rev
            if key not in single_cache:
                edges=orient[int(rev)][cid]['edges']+[(r+1,r,-17*SC) for r in range(8)]
                cycle,_=geom.bellman_ford(edges,9);single_cache[key]=cycle
            return single_cache[key]
        feasible=None
        with (HERE/'witness-prefix.bin.gz').open('xb') as raw:
            with gzip.GzipFile(fileobj=raw,filename='',mtime=0,mode='wb') as stream:
                stream.write(MAGIC);rawhash.update(MAGIC);nraw+=len(MAGIC)
                for oi,(pr,sr) in enumerate([(False,False),(False,True),(True,False),(True,True)]):
                    if feasible:break
                    for i in range(N):
                        if feasible:break
                        P=orient[int(pr)][i]
                        for j in range(N):
                            current={'case_ordinal':oi*N*N+i*N+j,'orientation':ORIS[oi],
                                'prefix_exception_id':i,'suffix_exception_id':j}
                            assert current['case_ordinal']==checked
                            total_margin=margins[i]+margins[j]
                            if total_margin>=PAYMENT_THRESHOLD:
                                data=b'\x40';counts['original_scalar_floors_pay_target']+=1
                            else:
                                S=orient[int(sr)][j];ids=geom.shared_conflict(P,S);method=0
                                if ids is None:
                                    old=single(i,pr)
                                    if old is not None:ids=[k if k<72 else 144+k-72 for k in old];method=1
                                    else:
                                        old=single(j,sr)
                                        if old is not None:ids=[72+k if k<72 else 145+k-72 for k in old];method=2
                                edges=None
                                if ids is None:
                                    edges=geom.full_edges(P,S);ids,point=geom.bellman_ford(edges,10);method=3
                                    if ids is None:
                                        assert len(point)==10 and point[0]==0
                                        assert all(point[v]-point[u]<=w for u,v,w in edges)
                                        a=geom.ordered_test(point,pr,0);b=geom.ordered_test(point,sr,1)
                                        holds=a['ordered_condition_holds'] and b['ordered_condition_holds']
                                        feasible={**current,'prefix_cell':cells[i],'suffix_cell':cells[j],
                                            'prefix_M0':str(margins[i]),'suffix_M0':str(margins[j]),
                                            'sum_M0':str(total_margin),'payment_threshold':str(PAYMENT_THRESHOLD),
                                            'underpayment':str(PAYMENT_THRESHOLD-total_margin),
                                            'sum_original_floor_minus_twice_c':str(F(total_margin-PAYMENT_THRESHOLD,KAPPA*SA)),
                                            'X_integer_potential':point,'X_scale':20*SC,
                                            'positions':[str(F(x,20*SC)) for x in point],
                                            'all153_edges':[{'edge_id':k,'u':u,'v':v,'bound':w,
                                                'actual_difference':point[v]-point[u],'slack':w-point[v]+point[u]}
                                                for k,(u,v,w) in enumerate(edges)],
                                            'all153_edges_verified':True,'prefix_ordered':a,'suffix_ordered':b,
                                            'ordered_conditions_hold':holds,
                                            'outcome':'underpaid_DBM_feasible_ordered_holds' if holds else 'underpaid_relaxed_DBM_feasible_ordered_violated',
                                            'is_actual_low_energy_or_counterexample':False}
                                        data=b'\xf0';counts['underpaid_feasible_case']+=1
                                    else:counts['underpaid_full_BF_negative_cycle']+=1
                                if ids is not None:
                                    if edges is None:
                                        selected=[geom.source_edge(P,S,k) for k in ids]
                                        geom.check_cycle(selected,list(range(len(ids))))
                                    else:geom.check_cycle(edges,ids)
                                    if method==0:counts['underpaid_shared_span_two_edge_conflict']+=1
                                    elif method==1:counts['underpaid_prefix_single_state_sep_negative_cycle']+=1
                                    elif method==2:counts['underpaid_suffix_single_state_sep_negative_cycle']+=1
                                    data=bytes([(method<<4)|len(ids),*ids]);cycles+=1
                            stream.write(data);rawhash.update(data);nraw+=len(data);checked+=1
                            if checked%1024==0:limit()
                            if checked%16384==0:
                                progress={'pid':os.getpid(),'stage':'fixed_scalar_floor_then_DBM','cases_checked':checked,
                                    'total_cases':TOTAL,'current':current,'counts':dict(counts),'seconds':time.monotonic()-started}
                                (HERE/'progress.json').write_text(json.dumps(progress,indent=2)+'\n',encoding='utf-8')
                                print(json.dumps(progress),flush=True)
                            if feasible:break
        after={name:pin(ROOT/name) for name in refs};assert after==refs
        assert sum(counts.values())==checked
        if feasible:
            assert int(feasible['sum_M0'])<PAYMENT_THRESHOLD
            write_new(HERE/'first-underpaid-feasible.json',feasible);outcome=feasible['outcome'];complete=False
        else:
            assert checked==TOTAL;outcome='all_pairs_paid_or_geometrically_infeasible';complete=True
        result={'schema':'fixed-E-scalar-floor-and-DBM-opportunity-v1','passed':True,'pid':os.getpid(),
            'seconds':time.monotonic()-started,'model_passes':1,'inputs_sha256_start':refs,'inputs_sha256_end':after,
            'KAPPA':KAPPA,'SA':SA,'original_c9_numerator':CN,'target_c_numerator':C_N,'tau_numerator':TAU_N,
            'delta_numerator':DELTA_N,'payment_threshold':str(PAYMENT_THRESHOLD),
            'threshold_identity':'KAPPA*(tauN-c9N)=2*KAPPA*(cN-c9N)',
            'outcome':outcome,'cases_checked':checked,'total_cases':TOTAL,'counts':dict(counts),
            'all_cases_covered':complete,'stopped_at_first_underpaid_relaxed_feasible':feasible is not None,
            'first_underpaid_feasible_case':current if feasible else None,'negative_cycle_records':cycles,
            'proof_stream':{'path':rel(HERE/'witness-prefix.bin.gz'),'sha256':pin(HERE/'witness-prefix.bin.gz'),
                'uncompressed_sha256':rawhash.hexdigest(),'uncompressed_bytes':nraw,
                'schema':'magic RZE1 newline; implicit ordinal;0x40 scalar paid; method*16+cyclelength then edgeids for geometry;0xf0 terminal underpaid feasible'},
            'original_floors':'f_i=c9+M_i/(KAPPA*SA) on original closed cell; reversal transports same constant.',
            'geometry_engine_sha256':ENGINE_PIN,'all_geometry_constraints_unchanged':True,
            'ordered_constraints_not_added_to_DBM':True,'ordered_violation_does_not_continue_scan':True,
            'new_kernel_queries':0,'new_FS_or_points_or_cuts':0,'optimizer_calls':0,'Lean_runs':0,
            'complete_source_and_runtime_budget':'unknown','complete_source_gate_passed':False,
            'new_joint_floor_proven':False,'new_unconditional_zero_proportion_proven':False,
            'website_submission_ready':False,'independent_replay_pending':True}
        limit();write_new(HERE/'model.json',result);limit()
        print(json.dumps({'passed':True,'outcome':outcome,'cases_checked':checked,'counts':dict(counts),'seconds':result['seconds']}),flush=True)
    except ResourceStop as exc:
        write_new(HERE/'inconclusive.json',{'passed':False,'outcome':'inconclusive','reason':str(exc),'pid':os.getpid(),
            'seconds':time.monotonic()-started,'cases_checked':checked,'current':current,'counts':dict(counts),
            'all_cases_covered':False,'automatic_retry_allowed':False,'inputs_sha256_start':refs})
        raise SystemExit(2)
    except BaseException as exc:
        write_new(HERE/'failure.json',{'passed':False,'error':repr(exc),'traceback':traceback.format_exc(),
            'pid':os.getpid(),'seconds':time.monotonic()-started,'cases_checked':checked,'current':current,
            'all_cases_covered':False,'automatic_retry_allowed':False,'inputs_sha256_start':refs})
        raise

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--execute-authorized-fixed-model',action='store_true')
    ap.add_argument('--gate');ap.add_argument('--gate-sha256');args=ap.parse_args()
    if not args.execute_authorized_fixed_model:
        print(json.dumps({'prepared_only':True,'model_runs':0,'requires_new_gate_and_frozen_static_D_review':True}));return
    assert args.gate and args.gate_sha256
    execute((ROOT/args.gate).resolve(),args.gate_sha256)

if __name__=='__main__':main()
