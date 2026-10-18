"""Prepared independent stdlib G claimed-closure replay; no producer/BF import.

Verifies only published committed prefix, every claimed closed case, status and
bitmap identity, compressed proof EOF/hash. Unresolved requires no feasibility.
"""
from pathlib import Path
from hashlib import sha256
from collections import Counter
import argparse
import ast
import gzip
import json
import re
import time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
B=ROOT/'research-goal-20261018-stageB-classification'
SOURCE=ROOT/'research-goal-20261018-record-source-audit/snapshot/Solution.lean'
SOURCE_PIN='f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf'
B_PIN='3f9408f2cf1ceae12339456da034d9e8f175f828cf2d53a652339ee79eec89ad'
CONTRACT=ROOT/'research-goal-20261018-global-delivery-static/contract-files.json'
CONTRACT_PIN='de2abe74665dfbf842f2c69f41ae87e8e0b268c7fd43a49d2b6843e9c940e021'
N=1187
Q=32768
KAPPA=Q*10**10*1024
T=KAPPA*(893916123055294719-893616123055294719)
TOTAL=N*N*4
CHARTS=('id/id','id/rev','rev/id','rev/rev')
NAMES=('paid','strict_projection','other_strict_cycle','unresolved')

def pin(p):return sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode('ascii')+b'\n'

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write-receipt',action='store_true')
    ap.add_argument('--prefix-only',action='store_true');args=ap.parse_args()
    out=HERE/'independent-complete-replay.json'
    if args.write_receipt:assert not out.exists()
    started=time.monotonic();prefix=load(HERE/'prefix.json');begin=load(HERE/'started.json')
    result=load(HERE/'classification.json') if (HERE/'classification.json').exists() else None
    complete=bool(result and result['complete_range_classified'])
    if not complete:assert args.prefix_only,'Incomplete output needs explicit prefix-only verification'
    before=begin['inputs_sha256']
    for p,expected in [(SOURCE,SOURCE_PIN),(B/'files.json',B_PIN),(CONTRACT,CONTRACT_PIN)]:
        assert before[p.relative_to(ROOT).as_posix()]==expected and pin(p)==expected
    for name,expected in before.items():assert pin(ROOT/name)==expected
    if result:
        assert result['inputs_sha256_start']==result['inputs_sha256_end']==before
        assert result['prefix_sha256']==pin(HERE/'prefix.json')
        assert result['committed_cases']==prefix['committed_cases']
        assert result['counts']==prefix['counts'] and result['total_cases']==TOTAL
        assert result['index_formula']=='((i*1187+j)*4+chart)' and tuple(result['chart_order'])==CHARTS
        assert result['passed'] is complete and result['unprocessed_suffix_has_no_status'] is (not complete)
        assert result['outcome']==('complete_fixed_classification' if complete else 'inconclusive_valid_published_prefix')
        assert result['known_F_annotation']==prefix['known_F_annotation']
    text=SOURCE.read_text(encoding='utf-8');cert=text[text.index('namespace AMW.Cert.PC9QB6M\n'):text.index('end AMW.Cert.PC9QB6MData')]
    found=re.findall(r'\bdef PR\s*:[^\n]*:= (\[[^\n]*\])',cert);assert len(found)==1
    spans=[(r,r+1) for r in range(8)]+[tuple(x) for x in ast.literal_eval(found[0])]
    look={edge:k for k,edge in enumerate(spans)};assert len(look)==36
    b=load(B/'classification.json');assert spans==[tuple(x) for x in b['pair_order_from_source']]
    p=ROOT/b['outputs']['exceptions']['path'];assert pin(p)==b['outputs']['exceptions']['sha256']
    cells=[];ms=[]
    with gzip.open(p,'rt',encoding='ascii') as f:
        for line in f:
            c=json.loads(line);s=c['state'];assert c['exception_id']==len(cells) and s['M']==0
            lo=s['L']+s['A'];hi=s['U']+s['B'];assert len(lo)==len(hi)==36
            assert sha256(canonical([v for pair in zip(lo,hi) for v in pair]+[0])).hexdigest()==c['state_sha256']
            m=int(c['original_margin']);assert 0<=m<T and int(c['tau_margin'])==m-T
            cells.append((lo,hi,c['state_sha256']));ms.append(m)
    assert len(cells)==N
    def info(index):
        pair,chart=divmod(index,4);i,j=divmod(pair,N)
        return i,j,chart,chart>=2,chart%2==1
    def physical_bound(cid,rev,a,z):
        edge=(8-z,8-a) if rev else (a,z);k=look[edge];lo,hi,_sha=cells[cid]
        return 20*lo[k],20*hi[k],2*k,2*k+1
    def edge(index,eid):
        assert 0<=eid<153
        i,j,chart,pr,sr=info(index)
        if eid>=144:
            r=eid-144;return r+1,r,-17*Q
        off=0 if eid<72 else 1;cid=i if off==0 else j;rev=pr if off==0 else sr
        k,kind=divmod(eid-off*72,2);a,z=spans[k]
        if rev:a,z=8-z,8-a
        lo,hi,_sha=cells[cid]
        return (a+off,z+off,20*hi[k]) if kind==0 else (z+off,a+off,-20*lo[k])
    def strict_cycle(index,ids):
        assert 1<=len(ids)<=10;es=[edge(index,k) for k in ids]
        assert all(a[1]==b[0] for a,b in zip(es,es[1:]+es[:1])) and sum(w for _u,_v,w in es)<0
    shared=[(i,j) for i in range(1,8) for j in range(i+1,9)];assert len(shared)==28
    handles={k:(ROOT[s['path']]).open('rb') for k,s in prefix['streams'].items()}
    hashes={k:sha256() for k in handles};positions={k:0 for k in handles};loghash=sha256()
    counts=Counter();end=0;frame=0;chain='0'*64;known_status=None
    with (HERE/'commits.jsonl').open('rb') as log:
        while log.tell()<prefix['commit_log_bytes']:
            line=log.readline();assert line and log.tell()<=prefix['commit_log_bytes'];loghash.update(line)
            entry=json.loads(line);body=entry['body'];assert sha256(canonical(body)).hexdigest()==entry['sha256']
            assert body['previous_commit_sha256']==chain and body['frame']==frame and body['start']==end
            n=body['count'];assert 0<n<=8192 and body['end']==end+n<=TOTAL and end%8==0
            raw={}
            for k,h in handles.items():
                seg=body['stream_segments'][k];assert seg['start_byte']==positions[k]
                data=h.read(seg['end_byte']-seg['start_byte']);assert len(data)==seg['encoded_bytes']
                hashes[k].update(data);positions[k]+=len(data)
                assert hashes[k].hexdigest()==seg['prefix_sha256']
                raw[k]=gzip.decompress(data) if k in ['projection','cycles'] else data
                assert len(raw[k])==seg['raw_bytes'] and sha256(raw[k]).hexdigest()==seg['raw_sha256']
            assert len(raw['status'])==(n+3)//4 and len(raw['bitmap'])==(n+7)//8
            if n%4:assert raw['status'][-1]>>(2*(n%4))==0
            if n%8:assert raw['bitmap'][-1]>>(n%8)==0
            pc=cc=0;delta=Counter()
            for local in range(n):
                index=end+local;status=(raw['status'][local//4]>>(2*(local%4)))&3
                bit=(raw['bitmap'][local//8]>>(local%8))&1;assert bit==int(status==3)
                i,j,chart,pr,sr=info(index);paid=ms[i]+ms[j]>=T
                if status==0:assert paid
                else:
                    assert not paid
                    if status==1:
                        assert pc<len(raw['projection']);code=raw['projection'][pc];pc+=1;sid,direction=divmod(code,2)
                        assert sid<28;a,z=shared[sid]
                        pl,pu,pup,plow=physical_bound(i,pr,a,z)
                        sl,su,sup,slow=physical_bound(j,sr,a-1,z-1)
                        if direction==0:assert pl>su;ids=[72+sup,plow]
                        else:assert sl>pu;ids=[pup,72+slow]
                        strict_cycle(index,ids)
                    elif status==2:
                        assert cc<len(raw['cycles']);length=raw['cycles'][cc];cc+=1
                        assert 1<=length<=10 and cc+length<=len(raw['cycles'])
                        ids=list(raw['cycles'][cc:cc+length]);cc+=length;strict_cycle(index,ids)
                delta[NAMES[status]]+=1
                if index==((1*N+5)*4):known_status=NAMES[status]
            assert pc==len(raw['projection']) and cc==len(raw['cycles'])
            counts.update(delta)
            assert {k:delta[k] for k in NAMES}==body['delta_counts']
            assert {k:counts[k] for k in NAMES}==body['counts']
            end+=n;frame+=1;chain=entry['sha256']
        assert log.tell()==prefix['commit_log_bytes']
        if complete:assert log.read(1)==b''
    assert loghash.hexdigest()==prefix['commit_log_sha256'] and chain==prefix['last_commit_sha256']
    assert end==prefix['committed_cases'] and frame==prefix['frame_count']
    assert {k:counts[k] for k in NAMES}==prefix['counts']
    for k,h in handles.items():
        s=prefix['streams'][k];assert positions[k]==s['committed_bytes'] and hashes[k].hexdigest()==s['prefix_sha256']
        if complete:assert h.read(1)==b''
        h.close()
    if complete:
        assert end==TOTAL and positions['status']==N*N and positions['bitmap']==(TOTAL+7)//8
    assert prefix['known_F_annotation']=={'index':((1*N+5)*4),'counts_as_extra_G_closure':False,'status':known_status}
    if prefix['first_unresolved_sample_sha256']:
        sp=HERE/'first-unresolved-sample.json';assert pin(sp)==prefix['first_unresolved_sample_sha256'];s=load(sp)
        assert s['index']<end and s['status']=='unresolved' and s['not_a_global_nonempty_claim'] is True
        i,j,chart,pr,sr=info(s['index']);assert (i,j,CHARTS[chart])==(s['prefix_exception_id'],s['suffix_exception_id'],s['chart'])
        assert s['prefix_state_sha256']==cells[i][2] and s['suffix_state_sha256']==cells[j][2]
        statusstream=(ROOT/prefix['streams']['status']['path']).read_bytes()
        assert ((statusstream[s['index']//4]>>(2*(s['index']%4)))&3)==3
        if s['potential_present']:
            x=s['X_integer_potential'];assert len(x)==10 and x[0]==0 and all(type(v) is int for v in x)
            assert all(x[v]-x[u]<=w for u,v,w in (edge(s['index'],eid) for eid in range(153)))
    for name,expected in before.items():assert pin(ROOT/name)==expected
    record={'schema':'G-independent-claimed-closure-prefix-replay-v1','passed':True,'complete_range_classified':complete,
        'committed_cases':end,'total_cases':TOTAL,'counts':{k:counts[k] for k in NAMES},
        'every_claimed_closed_case_verified':True,'status_bitmap_index_and_frame_EOF_verified':True,
        'known_F_only_annotation':True,'unresolved_nonempty_claims_verified':False,
        'producer_modules_imported':0,'BF_or_LP_calls':0,'kernel_queries':0,'Lean_runs':0,
        'script_sha256':pin(Path(__file__)),'prefix_sha256':pin(HERE/'prefix.json'),
        'new_global_joint_floor_proven':False,'new_unconditional_zero_proportion_proven':False,
        'seconds':time.monotonic()-started,
        'scope':'Every claimed paid/projection/cycle in published prefix checked; unresolved remains open, unprocessed suffix not classified. No energy or complete formal proof claim.'}
    if args.write_receipt:write=out.open('x',encoding='utf-8');json.dump(record,write,indent=2);write.write('\n');write.close()
    print(json.dumps(record))

if __name__=='__main__':main()
