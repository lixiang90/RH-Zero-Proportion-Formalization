"""Prepared G: complete fixed cheap classification, not a solver campaign.

Index=((i*N+j)*4+chart); statuses paid/projection/cycle/unresolved. Unresolved
means no exclusion certificate supplied, not geometrical nonemptiness. Only a
new immutable gate may start this script's mathematical pass.
"""
from pathlib import Path
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
ENGINE=ROOT/'research-goal-20261018-stageC-dbm/scan_once.py'
ENGINE_PIN='323ca76957f6cd9055d09037f69af8abef5d1f9af0dfa1c2153254a3124a1522'
CONTRACT=ROOT/'research-goal-20261018-global-delivery-static/contract-files.json'
CONTRACT_PIN='de2abe74665dfbf842f2c69f41ae87e8e0b268c7fd43a49d2b6843e9c940e021'
N=1187
Q=32768
SA=10**20
KAPPA=Q*10**10*1024
CN=893616123055294719
TAU_N=893916123055294719
C_N=893766123055294719
THRESHOLD=KAPPA*(TAU_N-CN)
CHARTS=('id/id','id/rev','rev/id','rev/rev')
TOTAL=N*N*len(CHARTS)
FRAME_CASES=8192
SOFT_SECONDS=270
SOFT_BYTES=19000000
HARD_SECONDS=300
HARD_BYTES=20000000
KNOWN_F_INDEX=((1*N+5)*4+0)
STATUS_NAMES=('paid','strict_projection','other_strict_cycle','unresolved')
STREAMS={'status':'classification.2bit.bin','bitmap':'unresolved.bitmap.bin',
         'projection':'projection.frames.gz','cycles':'cycles.frames.gz'}

def pin(p):
    h=sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''):h.update(block)
    return h.hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def rel(p):return p.relative_to(ROOT).as_posix()
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode('ascii')+b'\n'
def write_new(p,x):
    with p.open('xb') as f:f.write(canonical(x));f.flush();os.fsync(f.fileno())
def atomic_json(p,x):
    tmp=p.with_name(p.name+'.tmp')
    with tmp.open('wb') as f:f.write(canonical(x));f.flush();os.fsync(f.fileno())
    os.replace(tmp,p)
def package_bytes():return sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())

def inputs(gate_path,gate_sha):
    assert gate_path.is_relative_to(ROOT) and pin(gate_path)==gate_sha
    g=load(gate_path)
    assert g['complete_classification_passes_authorized']==1
    assert g['stageB_producer_manifest_sha256']==B_PIN and g['contract_manifest_sha256']==CONTRACT_PIN
    assert g['exception_count']==N and tuple(g['chart_order'])==CHARTS
    assert g['index_formula']=='((i*1187+j)*4+chart)' and g['total_cases']==TOTAL
    assert int(g['c9_numerator'])==CN and int(g['tau_numerator'])==TAU_N and int(g['c_numerator'])==C_N
    assert int(g['denominator'])==SA and g['separation']=='17/20'
    assert g['resource_limits']=={'elapsed_seconds':HARD_SECONDS,'closed_output_bytes':HARD_BYTES}
    assert g['work_limits']=={'elapsed_seconds':SOFT_SECONDS,'closed_output_bytes':SOFT_BYTES}
    assert g['commit_cases']==FRAME_CASES and g['known_F_index']==KNOWN_F_INDEX
    assert 2*C_N==CN+TAU_N and THRESHOLD==2*KAPPA*(C_N-CN)
    refs={rel(gate_path):gate_sha,rel(ENGINE):ENGINE_PIN}
    for p in [Path(__file__),HERE/'run_once.py',HERE/'replay_complete.py']:refs[rel(p)]=pin(p)
    manifests=[(B/'files.json',B_PIN),(CONTRACT,CONTRACT_PIN),
        (ROOT/g['stageB_independent_manifest_path'],g['stageB_independent_manifest_sha256'])]
    for p,expected in manifests:
        assert p.is_relative_to(ROOT) and pin(p)==expected;refs[rel(p)]=expected
        obj=load(p)
        for field in ['files','package_files','dependencies','dependency_files','read_only_dependencies','read_only_existing_references']:
            for row in obj.get(field,[]):
                q=ROOT/row['path'];assert q.is_relative_to(ROOT) and pin(q)==row['sha256']
                if 'bytes' in row:assert q.stat().st_size==row['bytes']
                if row['path'] in refs:assert refs[row['path']]==row['sha256']
                refs[row['path']]=row['sha256']
    assert pin(ENGINE)==ENGINE_PIN
    spec=importlib.util.spec_from_file_location('fixed_C_geometry_for_G',ENGINE)
    geom=importlib.util.module_from_spec(spec);spec.loader.exec_module(geom)
    b=load(B/'classification.json');assert b['passed'] and b['classification_counts']['exception']==N
    assert int(b['integer_debit'])==THRESHOLD
    spans=[tuple(x) for x in b['pair_order_from_source']]
    assert spans[:8]==[(r,r+1) for r in range(8)]
    assert spans[8:]==[tuple(x) for x in b['PR_order_from_source']]
    assert len(spans)==36 and set(spans)=={(i,j) for i in range(9) for j in range(i+1,9)}
    p=ROOT/b['outputs']['exceptions']['path'];assert pin(p)==b['outputs']['exceptions']['sha256']
    cells=[];margins=[]
    with gzip.open(p,'rt',encoding='ascii') as f:
        for line in f:
            c=json.loads(line);s=c['state'];lo=s['L']+s['A'];hi=s['U']+s['B']
            assert c['exception_id']==len(cells) and c['coordinate_scale']==Q and c['separation']=='17/20'
            assert s['M']==0 and len(lo)==len(hi)==36 and c['relaxed_orientation'] is True
            flat=[v for pair in zip(lo,hi) for v in pair]+[0]
            assert sha256(canonical(flat)).hexdigest()==c['state_sha256']
            m=int(c['original_margin']);assert 0<=m<THRESHOLD and int(c['tau_margin'])==m-THRESHOLD
            cells.append(c);margins.append(m)
    assert len(cells)==N
    return refs,geom,spans,cells,margins

def projection_certificate(P,S):
    sid=0
    for i in range(1,8):
        for j in range(i+1,9):
            pl,pu,pupper,plower=P['lookup'][i,j]
            sl,su,supper,slower=S['lookup'][i-1,j-1]
            if pl>su:return sid*2,[72+supper,plower]
            if sl>pu:return sid*2+1,[pupper,72+slower]
            sid+=1
    assert sid==28
    return None,None

class WorkLimit(Exception):pass

class CommittedStore:
    """Fixed-size in-memory frame; fsync streams/log before atomic publication."""
    def __init__(self):
        self.handles={k:(HERE/name).open('xb') for k,name in STREAMS.items()}
        self.log=(HERE/'commits.jsonl').open('xb');self.hashes={k:sha256() for k in STREAMS};self.loghash=sha256()
        self.end=0;self.counts=Counter();self.chain='0'*64;self.frames=0;self.first_sample=None;self.f_status=None
        self.reset()
    def reset(self):
        self.n=0;self.status=bytearray(FRAME_CASES//4);self.bitmap=bytearray(FRAME_CASES//8)
        self.projection=bytearray();self.cycles=bytearray();self.delta=Counter();self.pending_sample=None;self.pending_f=None
    def add(self,ordinal,status,proof=None,sample=None):
        assert ordinal==self.end+self.n and 0<=status<4 and self.n<FRAME_CASES
        self.status[self.n//4]|=status<<(2*(self.n%4))
        if status==3:self.bitmap[self.n//8]|=1<<(self.n%8)
        if status==1:
            assert type(proof) is int and 0<=proof<56;self.projection.append(proof)
        elif status==2:
            assert 1<=len(proof)<=10 and all(0<=x<153 for x in proof)
            self.cycles.extend([len(proof),*proof])
        else:assert proof is None
        self.delta[STATUS_NAMES[status]]+=1
        if status==3 and self.first_sample is None and self.pending_sample is None:self.pending_sample=sample
        if ordinal==KNOWN_F_INDEX:self.pending_f=status
        self.n+=1
    def commit(self,final=False):
        assert self.n>0 and (self.n==FRAME_CASES or final and self.end+self.n==TOTAL)
        raw={'status':bytes(self.status[:(self.n+3)//4]),'bitmap':bytes(self.bitmap[:(self.n+7)//8]),
             'projection':bytes(self.projection),'cycles':bytes(self.cycles)}
        data={k:gzip.compress(v,compresslevel=6,mtime=0) if k in ['projection','cycles'] else v for k,v in raw.items()}
        if package_bytes()+sum(map(len,data.values()))+16384>SOFT_BYTES:raise WorkLimit('soft_output_19MB_before_commit')
        segments={}
        for k,f in self.handles.items():
            begin=f.tell();f.write(data[k]);f.flush();os.fsync(f.fileno());self.hashes[k].update(data[k])
            segments[k]={'start_byte':begin,'end_byte':f.tell(),'encoded_bytes':len(data[k]),
                'raw_bytes':len(raw[k]),'raw_sha256':sha256(raw[k]).hexdigest(),
                'prefix_sha256':self.hashes[k].hexdigest()}
        counts=self.counts+self.delta
        body={'schema':'G-frame-commit-v1','frame':self.frames,'start':self.end,'count':self.n,'end':self.end+self.n,
            'counts':{name:counts[name] for name in STATUS_NAMES},
            'delta_counts':{name:self.delta[name] for name in STATUS_NAMES},
            'stream_segments':segments,'previous_commit_sha256':self.chain}
        commitsha=sha256(canonical(body)).hexdigest();line=canonical({'body':body,'sha256':commitsha})
        self.log.write(line);self.log.flush();os.fsync(self.log.fileno());self.loghash.update(line)
        sample=self.first_sample
        if sample is None and self.pending_sample is not None:
            sample=self.pending_sample;write_new(HERE/'first-unresolved-sample.json',sample)
        fs=self.f_status if self.pending_f is None else self.pending_f
        snapshot={'schema':'G-published-durable-prefix-v1','committed_cases':body['end'],'total_cases':TOTAL,
            'frame_count':self.frames+1,'counts':body['counts'],'last_commit_sha256':commitsha,
            'commit_log_bytes':self.log.tell(),'commit_log_sha256':self.loghash.hexdigest(),
            'streams':{k:{'path':rel(HERE/STREAMS[k]),'committed_bytes':f.tell(),'prefix_sha256':self.hashes[k].hexdigest()}
                for k,f in self.handles.items()},
            'known_F_annotation':{'index':KNOWN_F_INDEX,'counts_as_extra_G_closure':False,
                'status':STATUS_NAMES[fs] if fs is not None else None},
            'first_unresolved_sample_sha256':pin(HERE/'first-unresolved-sample.json') if sample is not None else None,
            'unprocessed_suffix_is_not_classified':True}
        atomic_json(HERE/'prefix.json',snapshot)
        self.end=body['end'];self.counts=counts;self.chain=commitsha;self.frames+=1;self.first_sample=sample;self.f_status=fs
        self.reset()
    def close(self):
        for f in self.handles.values():f.close()
        self.log.close()

def execute(gate_path,gate_sha):
    assert __debug__
    for name in ['started.json','classification.json','failure.json','prefix.json',*STREAMS.values()]:
        assert not (HERE/name).exists(),('existing_attempt',name)
    started=time.monotonic();refs={};store=None;processed=0;diagnostics=Counter();outcome='inconclusive';last=None
    try:
        refs,geom,spans,cells,margins=inputs(gate_path,gate_sha)
        write_new(HERE/'started.json',{'schema':'G-one-complete-fixed-classification-start-v1','pid':os.getpid(),
            'time_unix':time.time(),'classification_attempt':1,'inputs_sha256':refs,
            'index_formula':'((i*1187+j)*4+chart)','chart_order':CHARTS,'total_cases':TOTAL,
            'work_limits':{'seconds':SOFT_SECONDS,'bytes':SOFT_BYTES},'hard_limits':{'seconds':HARD_SECONDS,'bytes':HARD_BYTES}})
        print(json.dumps({'stage':'G_fixed_classification_live','pid':os.getpid()}),flush=True)
        oriented=[[geom.make_orientation(c,rev,spans) for c in cells] for rev in [False,True]]
        store=CommittedStore();single_cache={}
        def single(cid,rev):
            key=cid,rev
            if key not in single_cache:
                edges=oriented[int(rev)][cid]['edges']+[(r+1,r,-17*Q) for r in range(8)]
                try:
                    cycle,_=geom.bellman_ford(edges,9)
                    if cycle is not None:geom.check_cycle(edges,cycle)
                except AssertionError:cycle=None;diagnostics['single_BF_no_certified_cycle']+=1
                single_cache[key]=cycle
            return single_cache[key]
        for i in range(N):
            for j in range(N):
                paid=margins[i]+margins[j]>=THRESHOLD
                for chart,(pr,sr) in enumerate([(False,False),(False,True),(True,False),(True,True)]):
                    ordinal=((i*N+j)*4+chart);assert ordinal==processed
                    last={'index':ordinal,'prefix_exception_id':i,'suffix_exception_id':j,'chart':CHARTS[chart]}
                    proof=None;sample=None
                    if paid:status=0
                    else:
                        P=oriented[int(pr)][i];S=oriented[int(sr)][j]
                        code,ids=projection_certificate(P,S)
                        if ids is not None:
                            selected=[geom.source_edge(P,S,k) for k in ids]
                            geom.check_cycle(selected,list(range(len(ids))));status=1;proof=code
                        else:
                            ids=None;point=None;reason=None
                            cycle=single(i,pr)
                            if cycle is not None:ids=[k if k<72 else 144+k-72 for k in cycle]
                            else:
                                cycle=single(j,sr)
                                if cycle is not None:ids=[72+k if k<72 else 145+k-72 for k in cycle]
                            edges=None
                            if ids is None:
                                diagnostics['full_10vertex_BF_calls']+=1;edges=geom.full_edges(P,S)
                                try:ids,point=geom.bellman_ford(edges,10)
                                except AssertionError:reason='BF did not provide a verified cycle or point';ids=point=None
                            if ids is not None:
                                try:
                                    selected=[geom.source_edge(P,S,k) for k in ids]
                                    geom.check_cycle(selected,list(range(len(ids))))
                                except AssertionError:ids=None;point=None;reason='Returned cycle failed strict certificate check'
                            if ids is not None:status=2;proof=ids
                            else:
                                status=3
                                valid=point is not None and len(point)==10 and point[0]==0
                                if valid:
                                    if edges is None:edges=geom.full_edges(P,S)
                                    valid=all(point[v]-point[u]<=w for u,v,w in edges)
                                if not valid:diagnostics['unresolved_without_verified_point']+=1
                                if store.first_sample is None and store.pending_sample is None:
                                    sample={**last,'status':'unresolved','not_a_global_nonempty_claim':True,
                                        'potential_present':valid,'X_scale':20*Q,
                                        'X_integer_potential':point if valid else None,
                                        'all153_edges_verified':valid,'reason':reason,
                                        'prefix_state_sha256':cells[i]['state_sha256'],'suffix_state_sha256':cells[j]['state_sha256']}
                                    if valid:
                                        sample['prefix_ordered']=geom.ordered_test(point,pr,0)
                                        sample['suffix_ordered']=geom.ordered_test(point,sr,1)
                    store.add(ordinal,status,proof,sample);processed+=1
                    if store.n==FRAME_CASES:
                        if time.monotonic()-started>SOFT_SECONDS:raise WorkLimit('soft_work_270_seconds')
                        store.commit()
                        if store.frames%8==0:
                            print(json.dumps({'stage':'G_committed_prefix','cases':store.end,'total':TOTAL,
                                'counts':dict(store.counts),'seconds':time.monotonic()-started}),flush=True)
                    elif processed%256==0 and time.monotonic()-started>SOFT_SECONDS:raise WorkLimit('soft_work_270_seconds')
        if store.n:store.commit(final=True)
        assert processed==store.end==TOTAL and sum(store.counts.values())==TOTAL
        outcome='complete_fixed_classification'
    except WorkLimit as exc:
        outcome='inconclusive_valid_published_prefix';diagnostics['work_limit_reason']=str(exc)
    except BaseException as exc:
        write_new(HERE/'failure.json',{'passed':False,'pid':os.getpid(),'seconds':time.monotonic()-started,
            'error':repr(exc),'traceback':traceback.format_exc(),'last':last,
            'processed_in_memory':processed,'committed_cases':store.end if store else 0,
            'inputs_sha256_start':refs,'automatic_retry_allowed':False})
        raise
    finally:
        if store is not None:store.close()
    # Closure work is outside the270s work budget, still under300s parent cap.
    after={name:pin(ROOT/name) for name in refs};assert refs==after
    prefix=load(HERE/'prefix.json') if (HERE/'prefix.json').exists() else None
    complete=outcome=='complete_fixed_classification'
    if complete:
        assert prefix['committed_cases']==TOTAL
        for s in prefix['streams'].values():assert (ROOT/s['path']).stat().st_size==s['committed_bytes']
        assert prefix['streams']['status']['committed_bytes']==(TOTAL+3)//4
        assert prefix['streams']['bitmap']['committed_bytes']==(TOTAL+7)//8
    result={'schema':'G-complete-fixed-opportunity-classification-v1','passed':complete,'outcome':outcome,
        'pid':os.getpid(),'seconds':time.monotonic()-started,'classification_passes':1,
        'inputs_sha256_start':refs,'inputs_sha256_end':after,'total_cases':TOTAL,
        'committed_cases':prefix['committed_cases'] if prefix else 0,'processed_in_memory':processed,
        'uncommitted_cases_not_accepted':processed-(prefix['committed_cases'] if prefix else 0),
        'counts':prefix['counts'] if prefix else {name:0 for name in STATUS_NAMES},
        'complete_range_classified':complete,'unprocessed_suffix_has_no_status':not complete,
        'prefix_sha256':pin(HERE/'prefix.json') if prefix else None,
        'index_formula':'((i*1187+j)*4+chart)','chart_order':CHARTS,
        'status_codes':dict(enumerate(STATUS_NAMES)),
        'projection_byte':'2*lexicographic_shared_span_id+direction;0:P.lower>S.upper,1:S.lower>P.upper',
        'cycle_record':'one length byte(1..10) then original153edge IDs(uint8)',
        'unresolved_means':'No exclusion certificate supplied. Not a certified nonempty set and not actual low energy.',
        'known_F_annotation':prefix['known_F_annotation'] if prefix else {'index':KNOWN_F_INDEX,'counts_as_extra_G_closure':False},
        'diagnostics_not_independently_certified':dict(diagnostics),
        'new_kernel_queries':0,'new_FS_or_kernel_points_or_thresholds':0,'LP_calls':0,'Lean_runs':0,
        'new_global_joint_floor_proven':False,'new_unconditional_zero_proportion_proven':False,
        'whole_source_and_policy_runtime_budget':'unknown','website_submission_ready':False,
        'independent_complete_certificate_replay_pending':True,'automatic_retry_allowed':False}
    write_new(HERE/'classification.json',result)
    print(json.dumps({'passed':complete,'outcome':outcome,'committed_cases':result['committed_cases'],
        'counts':result['counts'],'seconds':result['seconds']}),flush=True)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--execute-authorized-complete-G',action='store_true')
    ap.add_argument('--gate');ap.add_argument('--gate-sha256');args=ap.parse_args()
    if not args.execute_authorized_complete_G:
        print(json.dumps({'prepared_only':True,'classification_runs':0,'new_immutable_gate_required':True}));return
    assert args.gate and args.gate_sha256
    execute((ROOT/args.gate).resolve(),args.gate_sha256)

if __name__=='__main__':main()
