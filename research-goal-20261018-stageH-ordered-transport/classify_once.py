"""Prepared H: one gated classification of the frozen G-unresolved cases.

All mathematics is behind the explicit CLI gate. No producer imports, LP,
new FS/kernel values, Lean, or implicit work at import. Found certificates
are checked in the original155 integer rows; absence means unresolved.
"""
from pathlib import Path
from hashlib import sha256
from collections import Counter
import argparse
import ast
import gzip
import itertools
import json
import os
import re
import struct
import sys
import time
import traceback

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
G=ROOT/'research-goal-20261018-stageG-complete-classification'
B=ROOT/'research-goal-20261018-stageB-classification'
SOURCE=ROOT/'research-goal-20261018-record-source-audit/snapshot/Solution.lean'
N=1187
Q=32768
G_TOTAL=N*N*4
EXPECTED=19838
KNOWN_FEASIBLE_G_INDEX=2417
CHARTS=('id/id','id/rev','rev/id','rev/rev')
RAYS_SAME=((1,0),(2,1),(1,1),(1,2),(0,1))
RAYS_OPPOSITE=((1,0),(1,1),(0,1))
MAGIC=b'HRC1\n'
COMMIT_RECORDS=256
SOFT_SECONDS=270
SOFT_BYTES=19000000
HARD_SECONDS=300
HARD_BYTES=20000000
G_COUNTS={'paid':2108692,'strict_projection':3507051,'other_strict_cycle':295,'unresolved':EXPECTED}
PINS={
 'research-goal-20261018-record-source-audit/snapshot/Solution.lean':'f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf',
 'research-goal-20261018-stageB-classification/files.json':'3f9408f2cf1ceae12339456da034d9e8f175f828cf2d53a652339ee79eec89ad',
 'research-goal-20261018-stageB-classification/classification.json':'5d24d22ba0649c11acd55af484ef3dd4d5a2aebe5d8ddb913c663a6a3500865b',
 'research-goal-20261018-stageB-classification/exception-cells.jsonl.gz':'180c27713c0473345fd0bb3c3373168a2d79f2e4bf518d5860e1c72cfa8a1ad0',
 'research-goal-20261018-stageG-complete-classification/files.json':'93d7b1af5248aac7867e81bed3f1866b5d9c844c622f0a0ca01f28db2656972b',
 'research-goal-20261018-stageG-complete-classification/classification.json':'f2be52b6daedf040b1199fb4894199bd5a586240a273eda074cb6b2f7f80e329',
 'research-goal-20261018-stageG-complete-classification/prefix.json':'afaf3c0a3d33585164fabc4722cf04ecd34a0d48a6513b5a1a7e5d174a8322cf',
 'research-goal-20261018-stageG-complete-classification/unresolved.bitmap.bin':'fd103f69ee92c5a918ded4c8a06662642b7ef652398204957620f1105bd2a9b1',
 'research-goal-20261018-stageG-complete-classification/classification.2bit.bin':'dd1ba64fb4202dd23a904830762b9a1ce23d83f0321ea5b2d12a8813d1b83c64',
 'research-goal-20261018-stageG-independent/audit-files.json':'af09979447c2054f1daaa5a19e6abc59d04decee7752dfc53fe66c0643e30dc6',
 'research-goal-20261018-stageG-independent/independent-review.json':'291f15a57642f8be1e0556671e41e5d4791d29380fb2fc057640c089976b5ce7',
 'research-goal-20261018-ordered-ray-fan-static/files.json':'84a0089fa3c4b1e079ff17af22ae3ea43e0716872540689488030ff4f018f00b',
}

def pin(p):
    h=sha256()
    with p.open('rb') as f:
        for data in iter(lambda:f.read(1048576),b''):h.update(data)
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
def checked_path(name):
    p=(ROOT/name).resolve();assert p.is_relative_to(ROOT);return p
def pin_package(path,expected,refs):
    assert pin(path)==expected;refs[rel(path)]=expected
    obj=load(path)
    for field in ['files','package_files','read_only_dependencies','dependency_files','dependencies','read_only_existing_references']:
        for row in obj.get(field,[]):
            p=checked_path(row['path']);assert pin(p)==row['sha256']
            if 'bytes' in row:assert p.stat().st_size==row['bytes']
            if rel(p) in refs:assert refs[rel(p)]==row['sha256']
            refs[rel(p)]=row['sha256']

def inputs(gate_path,gate_sha):
    assert gate_path.is_relative_to(ROOT) and pin(gate_path)==gate_sha
    gate=load(gate_path)
    assert gate['ordered_transport_classification_passes_authorized']==1
    assert gate['expected_G_unresolved']==EXPECTED and gate['total_G_cases']==G_TOTAL
    assert gate['index_formula']=='((i*1187+j)*4+chart)' and tuple(gate['chart_order'])==CHARTS
    assert gate['resource_limits']=={'elapsed_seconds':HARD_SECONDS,'closed_output_bytes':HARD_BYTES}
    assert gate['work_limits']=={'elapsed_seconds':SOFT_SECONDS,'closed_output_bytes':SOFT_BYTES}
    assert gate['commit_records']==COMMIT_RECORDS and gate['record_magic']=='HRC1\\n'
    assert gate['known_feasible_G_index']==KNOWN_FEASIBLE_G_INDEX
    assert gate['stop_at_first_unresolved'] is False and gate['LP_calls_authorized']==0
    assert gate['stageG_independent_manifest_path']=='research-goal-20261018-stageG-independent/audit-files.json'
    assert gate['stageG_independent_receipt_path']=='research-goal-20261018-stageG-independent/independent-review.json'
    assert gate['independent_checker_path']=='research-goal-20261018-stageH-independent/audit_h.py'
    refs={rel(gate_path):gate_sha}
    for name,expected in PINS.items():
        p=checked_path(name);assert pin(p)==expected;refs[name]=expected
    for p in [Path(__file__),HERE/'run_once.py']:refs[rel(p)]=pin(p)
    pin_package(HERE/'prepared-files.json',gate['prepared_manifest_sha256'],refs)
    for name in ['stageG_independent_manifest','stageG_independent_receipt','independent_checker']:
        p=checked_path(gate[name+'_path']);expected=gate[name+'_sha256'];assert pin(p)==expected;refs[rel(p)]=expected
        if name=='stageG_independent_manifest':pin_package(p,expected,refs)
    audit=load(checked_path(gate['stageG_independent_receipt_path']))
    assert audit['passed'] is True and audit['complete_range_classified'] is True
    assert audit['committed_cases']==G_TOTAL and audit['counts']==G_COUNTS
    for field,name in [('unresolved_bitmap_sha256','unresolved.bitmap.bin'),('classification_sha256','classification.json'),
                       ('status_file_sha256','classification.2bit.bin'),('prefix_sha256','prefix.json')]:
        assert audit[field]==PINS[rel(G/name)]
    assert audit['source_sha256']==PINS[rel(SOURCE)]
    known=audit['optional_first_unresolved_sample']
    assert known['index']==KNOWN_FEASIBLE_G_INDEX and known['potential153edges_checked'] is True
    assert known['ordered_at_sample']==[True,True]
    result=load(G/'classification.json');prefix=load(G/'prefix.json')
    assert result['passed'] is True and result['complete_range_classified'] is True
    assert result['committed_cases']==G_TOTAL and result['counts']==G_COUNTS
    assert result['prefix_sha256']==pin(G/'prefix.json') and result['counts']==prefix['counts']
    bitmap=(G/'unresolved.bitmap.bin').read_bytes();status=(G/'classification.2bit.bin').read_bytes()
    assert len(bitmap)==(G_TOTAL+7)//8 and len(status)==(G_TOTAL+3)//4
    if G_TOTAL%8:assert bitmap[-1]>>(G_TOTAL%8)==0
    indices=[];ih=sha256()
    for byte_index,value in enumerate(bitmap):
        if value:
            for bit in range(8):
                if value>>bit&1:
                    index=byte_index*8+bit;assert index<G_TOTAL
                    assert status[index//4]>>(2*(index%4))&3==3
                    indices.append(index);ih.update(struct.pack('<I',index))
    assert len(indices)==EXPECTED and indices==sorted(set(indices)) and KNOWN_FEASIBLE_G_INDEX in indices
    text=SOURCE.read_text(encoding='utf-8')
    cert=text[text.index('namespace AMW.Cert.PC9QB6M\n'):text.index('end AMW.Cert.PC9QB6MData')]
    found=re.findall(r'\bdef PR\s*:[^\n]*:= (\[[^\n]*\])',cert);assert len(found)==1
    spans=[(r,r+1) for r in range(8)]+[tuple(x) for x in ast.literal_eval(found[0])]
    assert len(spans)==36 and set(spans)=={(i,j) for i in range(9) for j in range(i+1,9)}
    b=load(B/'classification.json');assert spans==[tuple(x) for x in b['pair_order_from_source']]
    packet=checked_path(b['outputs']['exceptions']['path']);assert pin(packet)==PINS[rel(packet)]
    cells=[]
    with gzip.open(packet,'rt',encoding='ascii') as f:
        for line in f:
            c=json.loads(line);s=c['state'];lo=s['L']+s['A'];hi=s['U']+s['B']
            assert c['exception_id']==len(cells) and s['M']==0 and len(lo)==len(hi)==36
            assert all(type(x) is int for x in lo+hi)
            assert sha256(canonical([v for pair in zip(lo,hi) for v in pair]+[0])).hexdigest()==c['state_sha256']
            cells.append((lo,hi))
    assert len(cells)==N
    return refs,indices,ih.hexdigest(),spans,cells

def add_flow(a,b):
    out=a.copy()
    for k,v in b.items():out[k]=out.get(k,0)+v
    return out
def geometry(index,spans,cells):
    pair,chart=divmod(index,4);i,j=divmod(pair,N);pr=chart>=2;sr=chart%2==1
    edges=[]
    for cid,rev,off in [(i,pr,0),(j,sr,1)]:
        lo,hi=cells[cid]
        for k,(a,b) in enumerate(spans):
            if rev:a,b=8-b,8-a
            edges.extend([(a+off,b+off,20*hi[k]),(b+off,a+off,-20*lo[k])])
    edges.extend((r+1,r,-17*Q) for r in range(9));assert len(edges)==153
    o0=[-1,1,0,0,0,0,0,1,-1,0]
    o1=[0,-1,1,0,0,0,0,0,1,-1]
    if pr:o0=[-x for x in o0]
    if sr:o1=[-x for x in o1]
    return chart,edges,(o0,o1)
def valid_certificate(weights,edges,orders):
    if not weights or len(weights)>155:return False
    balance=[0]*10;cost=0
    for row,weight in weights.items():
        if type(row) is not int or not 0<=row<155 or type(weight) is not int or weight<=0:return False
        if row<153:
            u,v,w=edges[row];balance[u]-=weight;balance[v]+=weight;cost+=weight*w
        else:
            for v,a in enumerate(orders[row-153]):balance[v]+=weight*a
    return all(x==0 for x in balance) and cost<0
def floyd(edges):
    # Sparse nonnegative original-edge counts represent actual walks, avoiding
    # exponential explicit path lists even if a negative diagonal is found.
    d=[[None]*10 for _ in range(10)];routes=[[None]*10 for _ in range(10)]
    for i in range(10):d[i][i]=0;routes[i][i]={}
    for eid,(u,v,w) in enumerate(edges):
        if d[u][v] is None or w<d[u][v]:d[u][v]=w;routes[u][v]={eid:1}
    for k in range(10):
        for i in range(10):
            if d[i][k] is None:continue
            dik=d[i][k];rik=routes[i][k]
            for j in range(10):
                if d[k][j] is None:continue
                candidate=dik+d[k][j]
                if d[i][j] is None or candidate<d[i][j]:
                    d[i][j]=candidate;routes[i][j]=add_flow(rik,routes[k][j])
    return d,routes
def find_certificate(chart,edges,orders,diagnostics):
    d,routes=floyd(edges)
    for i in range(10):
        if d[i][i]<0:
            weights=routes[i][i]
            if valid_certificate(weights,edges,orders):return weights,'original_graph_negative_walk'
            diagnostics['candidate_certificate_rejected']+=1
    if any(d[i][j] is None for i in range(10) for j in range(10)):
        diagnostics['disconnected_graph_unresolved']+=1;return None,None
    rays=RAYS_SAME if chart in [0,3] else RAYS_OPPOSITE
    for a,b in rays:
        q=[-a*orders[0][v]-b*orders[1][v] for v in range(10)]
        supply=[v for v in range(10) for _ in range(max(-q[v],0))]
        demand=[v for v in range(10) for _ in range(max(q[v],0))]
        assert 1<=len(supply)==len(demand)<=4
        for assignment in itertools.permutations(demand):
            if sum(d[u][v] for u,v in zip(supply,assignment))>=0:continue
            weights={}
            for u,v in zip(supply,assignment):weights=add_flow(weights,routes[u][v])
            if a:weights[153]=a
            if b:weights[154]=b
            if valid_certificate(weights,edges,orders):return weights,'ray_'+str(a)+'_'+str(b)
            diagnostics['candidate_certificate_rejected']+=1
    return None,None

def uleb(value):
    assert type(value) is int and value>=0
    out=bytearray()
    while value>=128:out.append((value&127)|128);value>>=7
    out.append(value);return bytes(out)
def encode(index,weights):
    out=bytearray(struct.pack('<I',index));out.append(int(weights is not None))
    if weights is not None:
        out.extend(uleb(len(weights)))
        for row,weight in sorted(weights.items()):out.append(row);out.extend(uleb(weight))
    return bytes(out)

class WorkLimit(Exception):pass
class Store:
    def __init__(self,index_sha):
        self.cert=(HERE/'certificates.bin').open('xb');self.remaining=(HERE/'remaining-indices.u32.bin').open('xb')
        self.cert.write(MAGIC);self.cert.flush();os.fsync(self.cert.fileno())
        self.remaining.flush();os.fsync(self.remaining.fileno())
        self.ch=sha256(MAGIC);self.rh=sha256();self.ih=sha256();self.index_sha=index_sha
        self.committed=0;self.counts={'Empty':0,'unresolved':0};self.last=None;self.reset();self.publish()
    def reset(self):self.data=bytearray();self.rem=bytearray();self.ids=bytearray();self.delta=Counter();self.n=0;self.pending_last=None
    def add(self,index,weights):
        self.data.extend(encode(index,weights));packed=struct.pack('<I',index);self.ids.extend(packed)
        name='unresolved' if weights is None else 'Empty';self.delta[name]+=1
        if weights is None:self.rem.extend(packed)
        self.n+=1;self.pending_last=index
    def publish(self):
        atomic_json(HERE/'prefix.json',{'schema':'H-published-durable-prefix-v1','expected_records':EXPECTED,
            'committed_records':self.committed,'committed_bytes':self.cert.tell(),
            'certificate_path':rel(HERE/'certificates.bin'),'certificate_prefix_sha256':self.ch.hexdigest(),
            'counts':self.counts,'input_index_sequence_sha256':self.index_sha,
            'committed_index_sequence_sha256':self.ih.hexdigest(),'last_G_index':self.last,
            'remaining_indices_path':rel(HERE/'remaining-indices.u32.bin'),
            'committed_remaining_bytes':self.remaining.tell(),'remaining_indices_prefix_sha256':self.rh.hexdigest(),
            'unprocessed_suffix_has_no_status':True})
    def commit(self):
        assert self.n>0 and self.committed+self.n<=EXPECTED
        if package_bytes()+len(self.data)+len(self.rem)+16384>SOFT_BYTES:raise WorkLimit('soft_output_19MB_before_commit')
        self.cert.write(self.data);self.cert.flush();os.fsync(self.cert.fileno());self.ch.update(self.data)
        self.remaining.write(self.rem);self.remaining.flush();os.fsync(self.remaining.fileno());self.rh.update(self.rem)
        self.ih.update(self.ids);self.committed+=self.n
        self.counts={k:self.counts[k]+self.delta[k] for k in self.counts};self.last=self.pending_last
        self.publish();self.reset()
    def close(self):self.cert.close();self.remaining.close()

def execute(gate_path,gate_sha):
    assert __debug__
    for name in ['started.json','result.json','failure.json','prefix.json','certificates.bin','remaining-indices.u32.bin']:
        assert not (HERE/name).exists(),('existing_attempt',name)
    started=time.monotonic();refs={};store=None;processed=0;diagnostics=Counter();methods=Counter();last=None
    outcome='inconclusive_valid_published_prefix'
    try:
        refs,indices,index_sha,spans,cells=inputs(gate_path,gate_sha)
        write_new(HERE/'started.json',{'schema':'H-one-fixed-ordered-transport-start-v1','pid':os.getpid(),
            'time_unix':time.time(),'classification_attempt':1,'inputs_sha256':refs,
            'expected_records':EXPECTED,'total_G_cases':G_TOTAL,'input_index_sequence_sha256':index_sha,
            'record_magic':'HRC1\\n','index_formula':'((i*1187+j)*4+chart)','chart_order':CHARTS})
        store=Store(index_sha)
        for index in indices:
            if time.monotonic()-started>SOFT_SECONDS:raise WorkLimit('soft_work_270_seconds')
            last=index;chart,edges,orders=geometry(index,spans,cells)
            weights,method=find_certificate(chart,edges,orders,diagnostics)
            # G's separately audited sample satisfies all155 original rows.
            # Never suppress a contradictory proposal by just tagging it open.
            if index==KNOWN_FEASIBLE_G_INDEX:assert weights is None,'contradicts_audited_feasible_G_sample'
            if weights is not None:
                assert valid_certificate(weights,edges,orders);methods[method]+=1
            store.add(index,weights);processed+=1
            if store.n==COMMIT_RECORDS:
                if time.monotonic()-started>SOFT_SECONDS:raise WorkLimit('soft_work_270_seconds')
                store.commit()
                if store.committed%2048==0:print(json.dumps({'stage':'H_committed_prefix','records':store.committed,
                    'expected_records':EXPECTED,'counts':store.counts,'seconds':time.monotonic()-started}),flush=True)
        if store.n:store.commit()
        assert processed==store.committed==EXPECTED and store.ih.hexdigest()==index_sha
        outcome='complete_G_unresolved_classification'
    except WorkLimit as exc:diagnostics['work_limit_reason']=str(exc)
    except BaseException as exc:
        write_new(HERE/'failure.json',{'passed':False,'error':repr(exc),'traceback':traceback.format_exc(),
            'pid':os.getpid(),'seconds':time.monotonic()-started,'processed_in_memory':processed,
            'committed_records':store.committed if store else 0,'last_G_index':last,
            'inputs_sha256_start':refs,'automatic_retry_allowed':False})
        raise
    finally:
        if store is not None:store.close()
    after={name:pin(ROOT/name) for name in refs};assert after==refs
    prefix=load(HERE/'prefix.json') if (HERE/'prefix.json').exists() else None
    complete=outcome=='complete_G_unresolved_classification'
    if complete:
        assert prefix['committed_records']==EXPECTED and sum(prefix['counts'].values())==EXPECTED
        assert (HERE/'certificates.bin').stat().st_size==prefix['committed_bytes']
        assert (HERE/'remaining-indices.u32.bin').stat().st_size==prefix['committed_remaining_bytes']
    result={'schema':'H-fixed-G-unresolved-ordered-transport-classification-v1','passed':complete,'outcome':outcome,
        'pid':os.getpid(),'seconds':time.monotonic()-started,'classification_passes':1,
        'complete_G_unresolved_classification':complete,'expected_records':EXPECTED,'total_G_cases':G_TOTAL,
        'inputs_sha256_start':refs,'inputs_sha256_end':after,'processed_in_memory':processed,
        'uncommitted_records_not_accepted':processed-(prefix['committed_records'] if prefix else 0),
        'prefix_sha256':pin(HERE/'prefix.json') if prefix else None,
        'committed_records':prefix['committed_records'] if prefix else 0,
        'committed_bytes':prefix['committed_bytes'] if prefix else 0,
        'certificate_prefix_sha256':prefix['certificate_prefix_sha256'] if prefix else None,
        'counts':prefix['counts'] if prefix else {'Empty':0,'unresolved':0},
        'input_index_sequence_sha256':prefix['input_index_sequence_sha256'] if prefix else None,
        'committed_index_sequence_sha256':prefix['committed_index_sequence_sha256'] if prefix else None,
        'certificate_path':prefix['certificate_path'] if prefix else None,
        'remaining_indices_path':prefix['remaining_indices_path'] if prefix else None,
        'committed_remaining_bytes':prefix['committed_remaining_bytes'] if prefix else 0,
        'remaining_indices_prefix_sha256':prefix['remaining_indices_prefix_sha256'] if prefix else None,
        'last_G_index':prefix['last_G_index'] if prefix else None,
        'known_feasible_G_index':KNOWN_FEASIBLE_G_INDEX,
        'methods_not_independently_verified':dict(methods),'diagnostics_not_independently_verified':dict(diagnostics),
        'unresolved_means':'No original155row strict Farkas certificate supplied. No nonempty or energy claim.',
        'new_kernel_queries':0,'new_FS_or_points_or_thresholds':0,'LP_calls':0,'Lean_runs':0,
        'new_global_joint_floor_proven':False,'new_unconditional_zero_proportion_proven':False,
        'whole_source_and_policy_runtime_budget':'unknown','website_submission_ready':False,
        'independent_certificate_replay_pending':True,'automatic_retry_allowed':False}
    write_new(HERE/'result.json',result)
    print(json.dumps({'passed':complete,'outcome':outcome,'committed_records':result['committed_records'],
        'counts':result['counts'],'seconds':result['seconds']}),flush=True)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--execute-authorized-H',action='store_true')
    ap.add_argument('--gate');ap.add_argument('--gate-sha256');args=ap.parse_args()
    if not args.execute_authorized_H:
        print(json.dumps({'prepared_only':True,'classification_runs':0,'new_immutable_root_gate_required':True}));return
    assert args.gate and args.gate_sha256
    execute(checked_path(args.gate),args.gate_sha256)

if __name__=='__main__':main()
