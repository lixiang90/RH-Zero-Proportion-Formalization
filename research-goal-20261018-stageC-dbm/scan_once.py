"""Prepared fixed four-orientation DBM opportunity scan. No implicit execution.

Needs a new written root gate and frozen independent Stage B package.  Uses no
kernel values, leaf models, optimizers, new cuts, threshold changes or Lean.
One relaxed feasible case ends the scan even if ordered conditions fail.
"""
from pathlib import Path
from fractions import Fraction
from hashlib import sha256
from contextlib import ExitStack
from collections import Counter
import argparse
import gzip
import json
import os
import time
import traceback

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
B=ROOT/'research-goal-20261018-stageB-classification'
B_PIN='3f9408f2cf1ceae12339456da034d9e8f175f828cf2d53a652339ee79eec89ad'
SOURCE=ROOT/'research-goal-20261018-record-source-audit/snapshot/Solution.lean'
SOURCE_PIN='f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf'
TAU_N=893916123055294719
SC=32768
N=1187
ORIENTATIONS=('id/id','id/rev','rev/id','rev/rev')
TOTAL=4*N*N
MAGIC=b'RZDBM1\n'
MAX_SECONDS=300
MAX_BYTES=20000000

def pin(p):
    h=sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
    return h.hexdigest()

def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode('ascii')
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def write_new(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def relative(p):return p.relative_to(ROOT).as_posix()

def inputs(gate_path,gate_sha):
    assert gate_path.is_relative_to(ROOT) and pin(gate_path)==gate_sha
    gate=load(gate_path)
    assert gate['pair_scan_passes_authorized']==1
    assert gate['stageB_producer_manifest_sha256']==B_PIN
    assert gate['stageB_producer_manifest_path']==relative(B/'files.json')
    assert int(gate['tau_numerator'])==TAU_N and int(gate['denominator'])==10**20
    assert gate['separation']=='17/20' and gate['exception_count']==N
    assert tuple(gate['orientations'])==ORIENTATIONS
    assert gate['complete_ordered_pair_case_count']==TOTAL and gate['stop_at_first_feasible'] is True
    assert gate['resource_limits']=={'elapsed_seconds':MAX_SECONDS,'closed_output_bytes':MAX_BYTES}
    refs={relative(gate_path):gate_sha,relative(SOURCE):SOURCE_PIN}
    for p in [Path(__file__),HERE/'run_once.py',HERE/'replay_cycles.py']:
        refs[relative(p)]=pin(p)
    independent=ROOT/gate['stageB_independent_manifest_path']
    assert independent.is_relative_to(ROOT)
    manifests=[(B/'files.json',B_PIN),(independent,gate['stageB_independent_manifest_sha256'])]
    for p,expected in manifests:
        assert pin(p)==expected;refs[relative(p)]=expected
        manifest=load(p)
        if p==independent:
            assert manifest['one_independent_execution_terminal_exit_zero'] is True
            assert manifest['all13046_numeric_rows_and1187_full_exception_rows_equal'] is True
            assert manifest['classification_counts']=={'closed':11859,'exception':1187,'reflection':595}
        for field in ['files','package_files','read_only_dependencies','dependency_files','dependencies']:
            for row in manifest.get(field,[]):
                path=ROOT/row['path'];assert path.is_relative_to(ROOT)
                assert pin(path)==row['sha256']
                if 'bytes' in row:assert path.stat().st_size==row['bytes']
                if row['path'] in refs:assert refs[row['path']]==row['sha256']
                refs[row['path']]=row['sha256']
    assert pin(SOURCE)==SOURCE_PIN
    classification=load(B/'classification.json')
    assert classification['passed'] and classification['classification_counts']['exception']==N
    assert classification['tau_numerator']==TAU_N and classification['separation']=='17/20'
    assert classification['orientation_relaxed_for_exception_cells'] is True
    spans=[tuple(x) for x in classification['pair_order_from_source']]
    assert len(spans)==36 and set(spans)=={(i,j) for i in range(9) for j in range(i+1,9)}
    assert spans[:8]==[(i,i+1) for i in range(8)]
    assert spans[8:]==[tuple(x) for x in classification['PR_order_from_source']]
    packet=classification['outputs']['exceptions'];p=ROOT/packet['path']
    assert pin(p)==packet['sha256'];cells=[]
    with gzip.open(p,'rt',encoding='ascii') as f:
        for line in f:
            row=json.loads(line);s=row['state']
            assert row['exception_id']==len(cells) and row['kind']=='exception'
            assert row['coordinate_scale']==SC and row['separation']=='17/20'
            assert row['relaxed_orientation'] is True and s['M']==0
            assert len(s['L'])==len(s['U'])==8 and len(s['A'])==len(s['B'])==28
            lo=s['L']+s['A'];hi=s['U']+s['B']
            assert all(type(v) is int for v in lo+hi)
            flat=[v for pair in zip(lo,hi) for v in pair]+[0]
            assert sha256(canonical(flat)+b'\n').hexdigest()==row['state_sha256']
            cells.append(row)
    assert len(cells)==N
    return refs,gate,classification,spans,cells

def make_orientation(cell,rev,spans):
    s=cell['state'];lo=s['L']+s['A'];hi=s['U']+s['B']
    edges=[];lookup={}
    for k,((i,j),l,u) in enumerate(zip(spans,lo,hi)):
        a,b=(8-j,8-i) if rev else (i,j)
        edges.extend([(a,b,20*u),(b,a,-20*l)])
        lookup[a,b]=(20*l,20*u,2*k,2*k+1)
    assert len(edges)==72 and len(lookup)==36
    return {'edges':edges,'lookup':lookup}

def check_cycle(edges,ids):
    assert 1<=len(ids)<=10 and all(0<=k<len(edges) for k in ids)
    assert all(edges[a][1]==edges[b][0] for a,b in zip(ids,ids[1:]+ids[:1]))
    value=sum(edges[k][2] for k in ids)
    assert value<0
    return value

def bellman_ford(edges,n):
    """All-zero super-source. Returns exact negative cycle or integer potential."""
    d=[0]*n;pred=[None]*n
    for _ in range(n):
        changed=None
        for eid,(u,v,w) in enumerate(edges):
            new=d[u]+w
            if d[v]>new:d[v]=new;pred[v]=eid;changed=v
        if changed is None:
            d=[x-d[0] for x in d]
            assert all(d[v]-d[u]<=w for u,v,w in edges)
            return None,d
    v=changed
    for _ in range(n):
        assert pred[v] is not None
        v=edges[pred[v]][0]
    start=v;back=[]
    while True:
        eid=pred[v];assert eid is not None
        back.append(eid);v=edges[eid][0]
        if v==start:break
        assert len(back)<n
    ids=list(reversed(back));check_cycle(edges,ids)
    return ids,None

def shared_conflict(prefix,suffix):
    # All 28 positive spans on shared global vertices 1,...,8, lexicographic.
    for i in range(1,8):
        for j in range(i+1,9):
            pl,pu,pupper,plower=prefix['lookup'][i,j]
            sl,su,supper,slower=suffix['lookup'][i-1,j-1]
            if pl>su:return [72+supper,plower]
            if sl>pu:return [pupper,72+slower]
    return None

def full_edges(prefix,suffix):
    edges=prefix['edges']+[(a+1,b+1,w) for a,b,w in suffix['edges']]
    edges += [(r+1,r,-17*SC) for r in range(9)]
    assert len(edges)==153
    return edges

def source_edge(prefix,suffix,eid):
    """Index the same153 edges lazily when checking a short cycle."""
    assert 0<=eid<153
    if eid<72:return prefix['edges'][eid]
    if eid<144:
        a,b,w=suffix['edges'][eid-72];return a+1,b+1,w
    r=eid-144;return r+1,r,-17*SC

def ordered_test(point,rev,offset):
    gaps=[point[offset+i+1]-point[offset+i] for i in range(8)]
    lhs,rhs=(gaps[-1],gaps[0]) if rev else (gaps[0],gaps[-1])
    return {'orientation':'rev' if rev else 'id','offset':offset,
            'original_h0_scaled':lhs,'original_h7_scaled':rhs,
            'four_point_left_minus_right_scaled':lhs-rhs,'ordered_condition_holds':lhs<=rhs}

class ResourceStop(Exception):pass

def scan(gate_path,gate_sha):
    assert __debug__
    for name in ['started.json','scan.json','failure.json','inconclusive.json','cycle-prefix.bin.gz']:
        assert not (HERE/name).exists(), ('existing_attempt',name)
    started=time.monotonic();refs={};count=Counter();current=None;checked=0;proof_records=0
    rawhash=sha256();rawbytes=0;single_cache={}
    def limit():
        if time.monotonic()-started>MAX_SECONDS:raise ResourceStop('elapsed_300_seconds')
        if sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())>MAX_BYTES:raise ResourceStop('closed_output_20000000_bytes')
    try:
        refs,gate,classification,spans,cells=inputs(gate_path,gate_sha)
        write_new(HERE/'started.json',{'schema':'fixed-four-orientation-DBM-start-v1',
            'pid':os.getpid(),'time_unix':time.time(),'inputs_sha256':refs,'scan_attempt':1,
            'case_order':'orientation-major [id/id,id/rev,rev/id,rev/rev], prefix id ascending, suffix id ascending',
            'total_cases':TOTAL,'threshold_numerator':TAU_N,'limits':{'seconds':MAX_SECONDS,'closed_output_bytes':MAX_BYTES}})
        oriented=[[make_orientation(c,rev,spans) for c in cells] for rev in [False,True]]
        def single(cellid,rev):
            key=(cellid,rev)
            if key not in single_cache:
                edges=oriented[int(rev)][cellid]['edges']+[(r+1,r,-17*SC) for r in range(8)]
                cycle,_potential=bellman_ford(edges,9)
                single_cache[key]=cycle
            return single_cache[key]
        feasible=None
        with (HERE/'cycle-prefix.bin.gz').open('xb') as raw:
            with gzip.GzipFile(fileobj=raw,filename='',mode='wb',mtime=0) as proof:
                proof.write(MAGIC);rawhash.update(MAGIC);rawbytes+=len(MAGIC)
                for ori,(pr,sr) in enumerate([(False,False),(False,True),(True,False),(True,True)]):
                    if feasible:break
                    for i in range(N):
                        if feasible:break
                        P=oriented[int(pr)][i]
                        for j in range(N):
                            current={'case_ordinal':ori*N*N+i*N+j,'orientation':ORIENTATIONS[ori],
                                     'prefix_exception_id':i,'suffix_exception_id':j}
                            assert current['case_ordinal']==checked
                            S=oriented[int(sr)][j]
                            ids=shared_conflict(P,S);method=0
                            if ids is None:
                                old=single(i,pr)
                                if old is not None:
                                    ids=[k if k<72 else 144+k-72 for k in old];method=1
                                else:
                                    old=single(j,sr)
                                    if old is not None:
                                        ids=[72+k if k<72 else 145+k-72 for k in old];method=2
                            edges=None
                            if ids is None:
                                edges=full_edges(P,S);ids,point=bellman_ford(edges,10);method=3
                                if ids is None:
                                    assert all(point[v]-point[u]<=w for u,v,w in edges)
                                    assert point[0]==0 and len(point)==10
                                    ptest=ordered_test(point,pr,0);stest=ordered_test(point,sr,1)
                                    ordered=ptest['ordered_condition_holds'] and stest['ordered_condition_holds']
                                    feasible={**current,'prefix_cell':cells[i],'suffix_cell':cells[j],
                                        'X_integer_potential':point,'X_scale':20*SC,
                                        'positions':[str(Fraction(x,20*SC)) for x in point],
                                        'all153_edges':[{'edge_id':k,'u':u,'v':v,'bound':w,
                                            'actual_difference':point[v]-point[u],'slack':w-point[v]+point[u]}
                                            for k,(u,v,w) in enumerate(edges)],
                                        'all153_edges_verified':True,'prefix_ordered':ptest,'suffix_ordered':stest,
                                        'ordered_conditions_hold':ordered,
                                        'outcome':'ordered_conditions_hold' if ordered else 'relaxed_box_feasible_ordered_violated',
                                        'is_actual_low_energy_or_counterexample':False}
                                    data=b'\xf0';count['feasible_case']+=1
                                else:count['full_BF_negative_cycle']+=1
                            if ids is not None:
                                if edges is None:
                                    selected=[source_edge(P,S,k) for k in ids]
                                    check_cycle(selected,list(range(len(ids))))
                                else:check_cycle(edges,ids)
                                if method==0:count['shared_28_span_two_edge_conflict']+=1
                                elif method==1:count['prefix_single_state_sep_negative_cycle']+=1
                                elif method==2:count['suffix_single_state_sep_negative_cycle']+=1
                                data=bytes([(method<<4)|len(ids),*ids])
                                proof_records+=1
                            proof.write(data);rawhash.update(data);rawbytes+=len(data);checked+=1
                            if checked%1024==0:
                                limit()
                                progress={'pid':os.getpid(),'stage':'fixed_DBM_scan','checked':checked,'total_cases':TOTAL,
                                    'current':current,'counts':dict(count),'seconds':time.monotonic()-started}
                                (HERE/'progress.json').write_text(json.dumps(progress,indent=2)+'\n',encoding='utf-8')
                                print(json.dumps(progress),flush=True)
                            if feasible:break
        after={name:pin(ROOT/name) for name in refs};assert after==refs
        assert sum(count.values())==checked and proof_records==checked-int(feasible is not None)
        if feasible:
            write_new(HERE/'first-feasible.json',feasible)
            outcome=feasible['outcome'];complete=False
        else:
            assert checked==TOTAL and proof_records==TOTAL
            outcome='all_relaxed_DBM_cases_infeasible';complete=True
        limit()
        result={'schema':'fixed-four-orientation-DBM-opportunity-v1','passed':True,'pid':os.getpid(),
            'seconds':time.monotonic()-started,'outcome':outcome,'inputs_sha256_start':refs,'inputs_sha256_end':after,
            'scan_passes':1,'cases_checked':checked,'total_cases':TOTAL,'negative_cycle_records':proof_records,
            'counts':dict(count),'all_cases_covered':complete,'stopped_at_first_relaxed_feasible':feasible is not None,
            'feasible_case':current if feasible else None,'all153_edge_contract':True,
            'edge_numbering':'0..71 prefix,72..143 suffix; 2*k upper/2*k+1 lower in original36span order after orientation;144+r sep Xr-X(r+1)<=-17*32768',
            'shared_filter':'28 shared positive spans; strict lower>upper only; touching retained',
            'proof_stream':{'path':relative(HERE/'cycle-prefix.bin.gz'),'sha256':pin(HERE/'cycle-prefix.bin.gz'),
                'uncompressed_sha256':rawhash.hexdigest(),'uncompressed_bytes':rawbytes,
                'schema':'magic RZDBM1 newline; implicit consecutive case ordinal; tag method*16+cyclelength then uint8 edgeids; final feasible tag0xf0 no payload'},
            'orientation_conditions_added_to_DBM':False,'ordered_violated_feasible_point_was_not_discarded':True,
            'variables':'X=20*32768*p real; integer feasible potentials are witnesses, not a restriction on the covered real domain',
            'new_kernel_queries':0,'new_witnesses_or_cuts':0,'optimizer_calls':0,'Lean_runs':0,
            'complete_source_and_runtime_budget':'unknown','complete_source_gate_passed':False,
            'new_joint_floor_proven':False,'new_unconditional_zero_proportion_proven':False,
            'website_submission_ready':False,'independent_replay_pending':True}
        write_new(HERE/'scan.json',result);limit()
        print(json.dumps({'passed':True,'outcome':outcome,'cases_checked':checked,'counts':dict(count),
            'seconds':result['seconds']}),flush=True)
    except ResourceStop as exc:
        write_new(HERE/'inconclusive.json',{'schema':'fixed-DBM-resource-stop-v1','passed':False,
            'outcome':'inconclusive','reason':str(exc),'pid':os.getpid(),'seconds':time.monotonic()-started,
            'cases_checked':checked,'current':current,'counts':dict(count),'all_cases_covered':False,
            'automatic_retry_allowed':False,'source_and_inputs_sha256_start':refs})
        raise SystemExit(2)
    except BaseException as exc:
        write_new(HERE/'failure.json',{'schema':'fixed-DBM-guard-failure-v1','passed':False,
            'error':repr(exc),'traceback':traceback.format_exc(),'pid':os.getpid(),
            'seconds':time.monotonic()-started,'cases_checked':checked,'current':current,
            'all_cases_covered':False,'automatic_retry_allowed':False,'inputs_sha256_start':refs})
        raise

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--execute-authorized-fixed-scan',action='store_true')
    p.add_argument('--gate');p.add_argument('--gate-sha256')
    a=p.parse_args()
    if not a.execute_authorized_fixed_scan:
        print(json.dumps({'prepared_only':True,'scan_runs':0,'new_gate_and_frozen_B_independent_required':True,
            'total_cases':TOTAL,'orientations':ORIENTATIONS,'max_seconds':MAX_SECONDS,'max_bytes':MAX_BYTES}));return
    assert a.gate and a.gate_sha256
    scan((ROOT/a.gate).resolve(),a.gate_sha256)

if __name__=='__main__':main()
