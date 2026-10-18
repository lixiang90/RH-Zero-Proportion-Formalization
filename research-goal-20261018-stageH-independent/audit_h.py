"""Independent H Empty-certificate audit, prepared only until root authorizes.

Rebuilds 155 original rows directly from source/B. It never imports production
Python and does not run graph, transport, LP, FS, kernel, or Lean algorithms.
The fixed HRC1 binary adapter is explicit below. Only a new immutable root
gate and a frozen production result allow the authorized audit CLI to run.
"""
from pathlib import Path
from hashlib import sha256
from collections import Counter
import argparse
import ast
import gzip
import json
import re
import struct
import os
import time
import traceback

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
SOURCE=ROOT/'research-goal-20261018-record-source-audit/snapshot/Solution.lean'
SOURCE_SHA='f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf'
B=ROOT/'research-goal-20261018-stageB-classification'
B_SHA='3f9408f2cf1ceae12339456da034d9e8f175f828cf2d53a652339ee79eec89ad'
G=ROOT/'research-goal-20261018-stageG-complete-classification'
G_SHA='93d7b1af5248aac7867e81bed3f1866b5d9c844c622f0a0ca01f28db2656972b'
G_INDEPENDENT=ROOT/'research-goal-20261018-stageG-independent/audit-files.json'
G_INDEPENDENT_SHA='af09979447c2054f1daaa5a19e6abc59d04decee7752dfc53fe66c0643e30dc6'
G_RECEIPT=ROOT/'research-goal-20261018-stageG-independent/independent-review.json'
G_RECEIPT_SHA='291f15a57642f8be1e0556671e41e5d4791d29380fb2fc057640c089976b5ce7'
N,Q,TOTAL=1187,32768,5635876
CHARTS=('id/id','id/rev','rev/id','rev/rev')
EXPECTED_UNRESOLVED=19838
KNOWN_ORDERED_FEASIBLE_INDEX=2417

def pin(p):
    h=sha256()
    with p.open('rb') as f:
        for chunk in iter(lambda:f.read(1048576),b''):h.update(chunk)
    return h.hexdigest()

def load(p):return json.loads(p.read_text(encoding='utf-8'))
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode('ascii')+b'\n'
def local_path(name):
    p=(ROOT/name).resolve();assert p.is_relative_to(ROOT);return p

def verify_manifest(path,expected):
    assert pin(path)==expected
    data=load(path)
    for key in ('files','package_files','read_only_dependencies','dependencies','dependency_files','read_only_existing_references'):
        for row in data.get(key,[]):
            p=local_path(row['path']);assert pin(p)==row['sha256']
            if 'bytes' in row:assert p.stat().st_size==row['bytes']
    return data

def original_geometry():
    """Read frozen literal geometry; called only during an authorized audit."""
    assert pin(SOURCE)==SOURCE_SHA
    verify_manifest(B/'files.json',B_SHA)
    text=SOURCE.read_text(encoding='utf-8')
    start=text.index('namespace AMW.Cert.PC9QB6M\n')
    end=text.index('end AMW.Cert.PC9QB6MData',start)
    prs=re.findall(r'\bdef PR\s*:[^\n]*:= (\[[^\n]*\])',text[start:end]);assert len(prs)==1
    pairs=[(r,r+1) for r in range(8)]+[tuple(v) for v in ast.literal_eval(prs[0])]
    assert len(pairs)==36 and set(pairs)=={(i,j) for i in range(9) for j in range(i+1,9)}
    summary=load(B/'classification.json');assert pairs==[tuple(v) for v in summary['pair_order_from_source']]
    row=summary['outputs']['exceptions'];path=local_path(row['path']);assert pin(path)==row['sha256']
    cells=[]
    with gzip.open(path,'rt',encoding='ascii') as f:
        for line in f:
            item=json.loads(line);s=item['state'];lo=s['L']+s['A'];hi=s['U']+s['B']
            assert item['exception_id']==len(cells) and s['M']==0 and len(lo)==len(hi)==36
            assert item['coordinate_scale']==Q and item['separation']=='17/20'
            flat=[v for z in zip(lo,hi) for v in z]+[0]
            assert sha256(canonical(flat)).hexdigest()==item['state_sha256']
            assert all(type(v) is int for v in lo+hi)
            cells.append((lo,hi,item['state_sha256']))
    assert len(cells)==N
    return pairs,cells

def unresolved_indices(g_independent_manifest,g_independent_sha):
    """Only enumerates already classified G status; never classifies geometry."""
    verify_manifest(G/'files.json',G_SHA)
    verify_manifest(g_independent_manifest,g_independent_sha)
    result=load(G/'classification.json');prefix=load(G/'prefix.json')
    assert result['complete_range_classified'] is True and prefix['committed_cases']==TOTAL
    assert result['prefix_sha256']==pin(G/'prefix.json')
    status_path=local_path(prefix['streams']['status']['path'])
    bitmap_path=local_path(prefix['streams']['bitmap']['path'])
    assert pin(status_path)==prefix['streams']['status']['prefix_sha256']
    assert pin(bitmap_path)==prefix['streams']['bitmap']['prefix_sha256']
    status=status_path.read_bytes();bitmap=bitmap_path.read_bytes()
    assert len(status)==(TOTAL+3)//4 and len(bitmap)==(TOTAL+7)//8
    if TOTAL%4:assert status[-1]>>(2*(TOTAL%4))==0
    if TOTAL%8:assert bitmap[-1]>>(TOTAL%8)==0
    found=[];h=sha256();counts=Counter()
    for index in range(TOTAL):
        tag=(status[index//4]>>(2*(index%4)))&3
        bit=(bitmap[index//8]>>(index%8))&1
        assert bit==int(tag==3);counts[tag]+=1
        if bit:found.append(index);h.update(struct.pack('<I',index))
    assert len(found)==EXPECTED_UNRESOLVED
    assert [counts[k] for k in range(4)]==[2108692,3507051,295,19838]
    return found,h.hexdigest()

def chart(index):
    assert type(index) is int and 0<=index<TOTAL
    pair,orientation=divmod(index,4);i,j=divmod(pair,N)
    return i,j,orientation,orientation>=2,orientation%2==1

def original_row(index,row_id,pairs,cells):
    """Return full ten-coordinate normal and RHS, not a gauge-reduced row."""
    assert type(row_id) is int and 0<=row_id<155
    i,j,orientation,prefix_rev,suffix_rev=chart(index)
    a=[0]*10
    if row_id<144:
        side,local=divmod(row_id,72);span_id,lower=divmod(local,2)
        cid=i if side==0 else j;rev=prefix_rev if side==0 else suffix_rev
        lo,hi,_=cells[cid];left,right=pairs[span_id]
        if rev:left,right=8-right,8-left
        left+=side;right+=side
        if lower:
            a[left]+=1;a[right]-=1;rhs=-20*lo[span_id]
        else:
            a[left]-=1;a[right]+=1;rhs=20*hi[span_id]
    elif row_id<153:
        r=row_id-144;a[r]+=1;a[r+1]-=1;rhs=-17*Q
    else:
        side=row_id-153;rev=prefix_rev if side==0 else suffix_rev
        sign=-1 if rev else 1
        for vertex,value in ((side,-1),(side+1,1),(side+7,1),(side+8,-1)):
            a[vertex]+=sign*value
        rhs=0
    assert len(a)==10 and sum(a)==0 and type(rhs) is int
    return a,rhs

def verify_empty(index,support,pairs,cells):
    """Weighted original upper rows imply 0 <= strict negative integer cost."""
    assert 1<=len(support)<=155
    ids=[entry[0] for entry in support]
    assert ids==sorted(set(ids))
    balance=[0]*10;cost=0
    for rid,weight in support:
        assert type(rid) is int and 0<=rid<155 and type(weight) is int and weight>0
        a,d=original_row(index,rid,pairs,cells)
        for vertex in range(10):balance[vertex]+=weight*a[vertex]
        cost+=weight*d
    assert balance==[0]*10 and cost<0
    return cost

def read_exact(stream,n):
    data=stream.read(n);assert len(data)==n,'premature_certificate_EOF';return data

def unsigned_leb128(stream):
    """Canonical arbitrary positive integer; no Float/Fraction conversion."""
    answer=shift=0
    while True:
        byte=read_exact(stream,1)[0]
        answer|=(byte&127)<<shift
        if byte<128:
            assert shift==0 or byte>0,'noncanonical_ULEB128'
            return answer
        shift+=7
        # The witness is already within the explicit root closed-output cap;
        # this check only rejects a pathological unclosed integer encoding.
        assert shift<160000000,'unbounded_ULEB128'

class PrefixReader:
    """Never accepts bytes outside one published H prefix."""
    def __init__(self,path,limit):
        assert type(limit) is int and limit>=5
        self.f=path.open('rb');self.limit=limit;self.position=0;self.sha=sha256()
    def read(self,n):
        assert type(n) is int and n>=0 and self.position+n<=self.limit
        data=self.f.read(n);self.position+=len(data);self.sha.update(data);return data
    def close(self):self.f.close()

def audit_certificates(path,prefix,complete,indices,pairs,cells):
    """Decode explicit G-index records and verify each claimed Empty once."""
    records=prefix['committed_records'];limit=prefix['committed_bytes']
    assert type(records) is int and 0<=records<=len(indices)
    if complete:assert records==len(indices)
    reader=PrefixReader(path,limit);counts=Counter();indexhash=sha256();remaining=bytearray()
    minimum_cost=None;maximum_support=0
    try:
        assert read_exact(reader,5)==b'HRC1\n'
        for ordinal in range(records):
            index_raw=read_exact(reader,4);index=struct.unpack('<I',index_raw)[0]
            assert index==indices[ordinal],'missing_duplicate_or_out_of_order_original_G_index'
            indexhash.update(index_raw);tag=read_exact(reader,1)[0]
            if index==KNOWN_ORDERED_FEASIBLE_INDEX:
                assert tag==0,'independently_verified_geometry_sample_cannot_be_Empty'
            if tag==0:
                counts['unresolved']+=1;remaining.extend(index_raw)
            else:
                assert tag==1,'unknown_H_status'
                length=unsigned_leb128(reader);assert 1<=length<=155
                support=[]
                for _ in range(length):
                    row_id=read_exact(reader,1)[0];weight=unsigned_leb128(reader)
                    support.append((row_id,weight))
                cost=verify_empty(index,support,pairs,cells)
                minimum_cost=cost if minimum_cost is None else min(cost,minimum_cost)
                maximum_support=max(maximum_support,length);counts['Empty']+=1
        assert reader.position==limit,'unconsumed_H_prefix_bytes'
        assert reader.sha.hexdigest()==prefix['certificate_prefix_sha256']
        if complete:assert reader.f.read(1)==b'','complete_H_certificate_has_trailing_bytes'
    finally:reader.close()
    assert {'Empty':counts['Empty'],'unresolved':counts['unresolved']}==prefix['counts']
    assert indexhash.hexdigest()==prefix['committed_index_sequence_sha256']
    return {'records':records,'counts':{'Empty':counts['Empty'],'unresolved':counts['unresolved']},
        'committed_index_sequence_sha256':indexhash.hexdigest(),
        'certificate_prefix_sha256':prefix['certificate_prefix_sha256'],
        'remaining_indices_bytes':bytes(remaining),'minimum_negative_integer_cost':minimum_cost,
        'maximum_Empty_support':maximum_support,'every_claimed_Empty_full10_balance_and_strict_cost_verified':True}

def write_new(path,data):
    with path.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(data,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify-authorized-H-result',action='store_true')
    parser.add_argument('--gate');parser.add_argument('--gate-sha256')
    parser.add_argument('--producer-manifest');parser.add_argument('--producer-manifest-sha256')
    parser.add_argument('--write-receipt',action='store_true');parser.add_argument('--prefix-only',action='store_true')
    args=parser.parse_args()
    if not args.verify_authorized_H_result:
        print(json.dumps({'prepared_only':True,'mathematical_audits_executed':0,'new_root_gate_required':True}));return
    assert args.gate and args.gate_sha256 and args.producer_manifest and args.producer_manifest_sha256
    started=time.monotonic();output=HERE/'independent-review.json'
    if args.write_receipt:assert not output.exists() and not (HERE/'failure.json').exists()
    refs={}
    def bind(path,expected=None):
        path=path.resolve();assert path.is_relative_to(ROOT)
        digest=pin(path)
        if expected is not None:assert digest==expected
        name=path.relative_to(ROOT).as_posix()
        if name in refs:assert refs[name]==digest
        refs[name]=digest;return path
    try:
        gate_path=bind(local_path(args.gate),args.gate_sha256);gate=load(gate_path)
        assert gate['independent_result_audit_calls_authorized']==1
        assert gate['independent_audit_script_path']==Path(__file__).relative_to(ROOT).as_posix()
        bind(Path(__file__),gate['independent_audit_script_sha256'])
        assert gate['stageG_producer_manifest_sha256']==G_SHA
        g_manifest=bind(local_path(gate['stageG_independent_manifest_path']),gate['stageG_independent_manifest_sha256'])
        g_receipt=bind(local_path(gate['stageG_independent_receipt_path']),gate['stageG_independent_receipt_sha256'])
        assert g_manifest==G_INDEPENDENT and pin(g_manifest)==G_INDEPENDENT_SHA
        assert g_receipt==G_RECEIPT and pin(g_receipt)==G_RECEIPT_SHA
        g_review=load(g_receipt)
        assert g_review['passed'] is True and g_review['complete_range_classified'] is True
        assert g_review['committed_cases']==TOTAL and g_review['every_claimed_closed_case_verified'] is True
        assert g_review['producer_manifest_sha256']==G_SHA
        assert g_review['counts']=={'paid':2108692,'strict_projection':3507051,'other_strict_cycle':295,'unresolved':19838}
        known=g_review['optional_first_unresolved_sample']
        assert known['index']==KNOWN_ORDERED_FEASIBLE_INDEX and known['potential153edges_checked'] is True
        assert known['ordered_at_sample']==[True,True]
        producer_manifest=bind(local_path(args.producer_manifest),args.producer_manifest_sha256)
        producer=producer_manifest.parent;verify_manifest(producer_manifest,args.producer_manifest_sha256)
        assert not producer.is_relative_to(HERE),'audit_outputs_cannot_replace_production'
        prefix_path=bind(producer/'prefix.json');prefix=load(prefix_path)
        begin=load(bind(producer/'started.json'));result_path=producer/'result.json'
        result=load(bind(result_path)) if result_path.exists() else None
        complete=bool(result and result['complete_G_unresolved_classification'])
        if not complete:assert args.prefix_only,'partial_H_requires_explicit_prefix_only'
        bind(G/'files.json',G_SHA);bind(B/'files.json',B_SHA);bind(SOURCE,SOURCE_SHA)
        for name,digest in begin['inputs_sha256'].items():bind(local_path(name),digest)
        indices,indexsha=unresolved_indices(g_manifest,gate['stageG_independent_manifest_sha256'])
        assert prefix['input_index_sequence_sha256']==indexsha
        pairs,cells=original_geometry()
        certificate_path=bind(local_path(prefix['certificate_path']))
        assert certificate_path==producer/'certificates.bin'
        checked=audit_certificates(certificate_path,prefix,complete,indices,pairs,cells)
        assert prefix['last_G_index']==(indices[checked['records']-1] if checked['records'] else None)
        remaining=checked.pop('remaining_indices_bytes')
        remaining_path=bind(local_path(prefix['remaining_indices_path']))
        assert remaining_path==producer/'remaining-indices.u32.bin'
        with remaining_path.open('rb') as f:
            assert f.read(len(remaining))==remaining
            if complete:assert f.read(1)==b''
        assert prefix['committed_remaining_bytes']==len(remaining)
        assert prefix['remaining_indices_prefix_sha256']==sha256(remaining).hexdigest()
        if result:
            assert result['prefix_sha256']==pin(prefix_path)
            assert result['inputs_sha256_start']==result['inputs_sha256_end']==begin['inputs_sha256']
            assert result['committed_records']==checked['records'] and result['counts']==checked['counts']
            for key in ('committed_bytes','committed_remaining_bytes','committed_index_sequence_sha256'):
                assert result[key]==prefix[key]
            assert result['complete_G_unresolved_classification'] is complete
            assert result['expected_records']==EXPECTED_UNRESOLVED and result['total_G_cases']==TOTAL
        after={name:pin(local_path(name)) for name in refs};assert after==refs
        record={'schema':'H-independent-original155row-Empty-prefix-review-v1','passed':True,
            'producer_manifest_sha256':args.producer_manifest_sha256,'stageG_producer_manifest_sha256':G_SHA,
            'stageG_independent_manifest_sha256':gate['stageG_independent_manifest_sha256'],
            'inputs_sha256_start':refs,'inputs_sha256_end':after,'seconds':time.monotonic()-started,
            'complete_input_range_processed':complete,'original_G_unresolved_input_count':len(indices),**checked,
            'remaining_indices_sha256':sha256(remaining).hexdigest(),
            'known_2417_ordered_feasible_sample_not_claimed_Empty':True,
            'producer_Python_modules_imported':0,'BF_Floyd_transport_LP_or_optimizer_calls':0,
            'kernel_FS_newpoint_or_Lean_runs':0,'unresolved_nonempty_claimed':False,
            'new_global_joint_floor_proven':False,'new_unconditional_zero_proportion_proven':False,
            'scope':'Only each supplied positive integer weighted original155row Empty certificate is verified; unresolved and unprocessed suffix remain open. No discovery algorithm or optimum assertion is trusted.'}
        if args.write_receipt:write_new(output,record)
        print(json.dumps({'passed':True,'complete_input_range_processed':complete,'counts':checked['counts'],
            'records':checked['records'],'seconds':record['seconds']}))
    except BaseException as exc:
        if args.write_receipt:write_new(HERE/'failure.json',{'passed':False,'error':repr(exc),
            'traceback':traceback.format_exc(),'seconds':time.monotonic()-started,'automatic_retry_allowed':False})
        raise

if __name__=='__main__':main()
