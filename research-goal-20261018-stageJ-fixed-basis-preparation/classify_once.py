"""Prepared J: one fixed-basis pass on the immutable H remaining index list.

No mathematics at import. Gated execution reuses original FS only, caches each
needed cell once, computes exactly four fixed candidate bases, and accepts
Lower only after original full10 integer balance/nonnegativity/cost checks.
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
import struct
import sys
import time
import traceback

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
BASE=ROOT/'research-goal-20261018-record-baseline-replay'
B=ROOT/'research-goal-20261018-stageB-classification'
I=ROOT/'research-goal-20261018-stageI-original-affine-point'
H=ROOT/'research-goal-20261018-stageH-ordered-transport'
N=1187
EXPECTED=15378
G_TOTAL=5635876
Q=32768
SA=10**20
KAPPA=Q*10**10*1024
C_N=893766123055294719
TARGET=4*KAPPA*C_N
SEED=(9,29,36,74,84,110,130,153,154)
CHARTS=('id/id','id/rev','rev/id','rev/rev')
MAGIC=b'JLB2\n'
TAGS={'negative_multiplier':0,'Lower':1,'valid_but_below_target':2,'singular_chart':3}
COMMIT=256
SOFT_SECONDS=270
SOFT_BYTES=19000000
HARD_SECONDS=300
HARD_BYTES=20000000
PINS={
 'research-goal-20261018-stageI-original-affine-point/files.json':'afaece4fee2e74d064258f689faff64d9732c53f8a412d0c71f6140d7653f482',
 'research-goal-20261018-stageI-original-affine-point/evaluate_once.py':'9170d9f229a0e8c4c659812467abdac163008ef89049123d58254bbb8e47e724',
 'research-goal-20261018-stageI-original-affine-point/result.json':'814f5473b6ab7f620759f2eed3dfdddf077b88e5a189e1ee9a9973cf1c99a42c',
 'research-goal-20261018-stageH-ordered-transport/remaining-indices.u32.bin':'c740852a5757983f462f3a78eb05d1aca5410ffb4077682e3afa48d6f7943559',
 'research-goal-20261018-stageH-independent/audit-files.json':'a0018aa4ce33e4cb6cea2019739e857fa3a1b58cc8b48f001e17d651e1dcbb3a',
 'research-goal-20261018-stageH-independent/independent-review.json':'c6d1c770c9ecb321f35e120df0594c12954d3766eeae1ce67ec64d452d175e0b'
}

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
def checked_path(name):
    p=(ROOT/name).resolve();assert p.is_relative_to(ROOT);return p
def pin_package(p,expected,refs):
    assert pin(p)==expected;refs[rel(p)]=expected
    manifest=load(p)
    for key in ['files','package_files','read_only_dependencies','dependencies','dependency_files','read_only_existing_references']:
        for row in manifest.get(key,[]):
            q=checked_path(row['path']);assert pin(q)==row['sha256']
            if 'bytes' in row:assert q.stat().st_size==row['bytes']
            if rel(q) in refs:assert refs[rel(q)]==row['sha256']
            refs[rel(q)]=row['sha256']
def import_frozen(p,name):
    spec=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
def package_bytes():return sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())
class WorkLimit(Exception):pass
def limit(start):
    if time.monotonic()-start>SOFT_SECONDS:raise WorkLimit('soft_work270seconds')
    if package_bytes()>SOFT_BYTES:raise WorkLimit('soft_output19MB')

def inputs(gate_path,gate_sha):
    assert gate_path.is_relative_to(ROOT) and pin(gate_path)==gate_sha;g=load(gate_path)
    assert g['fixed_basis_classification_passes_authorized']==1 and g['expected_H_remaining']==EXPECTED
    assert tuple(g['basis_row_ids'])==SEED and tuple(g['chart_order'])==CHARTS
    assert g['resource_limits']=={'elapsed_seconds':HARD_SECONDS,'closed_output_bytes':HARD_BYTES}
    assert g['work_limits']=={'elapsed_seconds':SOFT_SECONDS,'closed_output_bytes':SOFT_BYTES}
    assert g['stop_at_first_unresolved'] is False and g['alternate_basis_or_threshold_retry_allowed'] is False
    assert g['new_FS_kernel_points_LP_or_Lean_authorized']==0
    assert int(g['target_c_numerator'])==C_N and int(g['denominator'])==SA
    refs={rel(gate_path):gate_sha}
    for name,expected in PINS.items():
        p=checked_path(name);assert pin(p)==expected;refs[name]=expected
    pin_package(HERE/'prepared-files.json',g['prepared_manifest_sha256'],refs)
    pin_package(I/'files.json',PINS[rel(I/'files.json')],refs)
    for name in ['stageI_independent_manifest','stageI_independent_receipt']:
        p=checked_path(g[name+'_path']);expected=g[name+'_sha256'];assert pin(p)==expected;refs[rel(p)]=expected
        if name.endswith('manifest'):pin_package(p,expected,refs)
    review=load(checked_path(g['stageI_independent_receipt_path']));assert review['passed'] is True
    original=load(I/'result.json')
    assert original['passed'] is True and original['joint']['fixed_two_FS_model_obstructed_at_sample'] is False
    assert int(original['joint']['delta_integer'])>=0 and original['sample_G_index']==2417
    hreview=load(ROOT/'research-goal-20261018-stageH-independent/independent-review.json')
    assert hreview['passed'] is True and hreview['complete_input_range_processed'] is True
    assert hreview['counts']=={'Empty':4460,'unresolved':EXPECTED}
    data=(H/'remaining-indices.u32.bin').read_bytes();assert len(data)==4*EXPECTED
    indices=[x[0] for x in struct.iter_unpack('<I',data)]
    assert indices==sorted(set(indices)) and all(0<=x<G_TOTAL for x in indices)
    assert 2417 in indices and 4768 not in indices
    needed=set()
    for index in indices:
        pair,_chart=divmod(index,4);i,j=divmod(pair,N);needed.update([i,j])
    cells={}
    with gzip.open(B/'exception-cells.jsonl.gz','rt',encoding='ascii') as f:
        for line in f:
            c=json.loads(line);cid=c['exception_id']
            if cid not in needed:continue
            s=c['state'];w=c['witness'];lo=s['L']+s['A'];hi=s['U']+s['B']
            assert c['kind']=='exception' and c['coordinate_scale']==Q and c['separation']=='17/20' and s['M']==0
            assert len(lo)==len(hi)==36 and all(type(v) is int for v in lo+hi)
            assert sha256(canonical([v for p in zip(lo,hi) for v in p]+[0])).hexdigest()==c['state_sha256']
            assert w['WD']==c['root'] and w['original_leaf_position']==c['position']
            assert w['payload_bit_position']==c['position']+2 and c['end']-c['position']-2==w['consumed_payload_bits']
            assert 0<w['consumed_payload_bits']<=478
            assert w['original_rdw_block']==c['position']//32768 and w['original_rdw_shift']==c['position']%32768
            cells[cid]=c
    assert set(cells)==needed
    return refs,indices,cells,pin(H/'remaining-indices.u32.bin')

def normals(chart,pairs):
    rows=[]
    for off,rev in [(0,chart>=2),(1,chart%2==1)]:
        for i,j in pairs:
            if rev:i,j=8-j,8-i
            a=[0]*10;a[off+i]-=1;a[off+j]+=1;rows.extend([a,[-v for v in a]])
    for r in range(9):
        a=[0]*10;a[r]+=1;a[r+1]-=1;rows.append(a)
    for off,rev in [(0,chart>=2),(1,chart%2==1)]:
        a=[0]*10;sgn=-1 if rev else 1
        for v,c in [(off,-1),(off+1,1),(off+7,1),(off+8,-1)]:a[v]+=sgn*c
        rows.append(a)
    assert len(rows)==155 and all(sum(a)==0 for a in rows);return rows

def fixed_basis(chart,rows):
    # A=B^T: columns label selected rows, rows label physical coordinates1..9.
    A=[[rows[rid][v] for rid in SEED] for v in range(1,10)]
    aug=[[F(v) for v in row]+[F(int(i==j)) for j in range(9)] for i,row in enumerate(A)]
    rank=0;det=F(1);swaps=0
    for col in range(9):
        pivot=next((r for r in range(rank,9) if aug[r][col]),None)
        if pivot is None:continue
        if pivot!=rank:aug[pivot],aug[rank]=aug[rank],aug[pivot];swaps+=1
        value=aug[rank][col];det*=value;aug[rank]=[x/value for x in aug[rank]]
        for r in range(9):
            if r==rank:continue
            factor=aug[r][col]
            if factor:aug[r]=[x-factor*y for x,y in zip(aug[r],aug[rank])]
        rank+=1
    common={'chart':chart,'chart_name':CHARTS[chart],'basis_row_ids':list(SEED),
        'selected_full10_normals':[rows[r] for r in SEED],'A_transposed_reduced':A,'rank':rank}
    if rank<9:return {**common,'singular':True,'determinant':0,'denominator':None,'scaled_inverse':None}
    det*=(-1)**swaps;assert det.denominator==1 and det!=0
    determinant=det.numerator;den=abs(determinant);assert den<=4
    inverse=[row[9:] for row in aug]
    scaled=[]
    for row in inverse:
        values=[den*x for x in row];assert all(v.denominator==1 for v in values)
        scaled.append([v.numerator for v in values])
    assert all(sum(A[i][k]*scaled[k][j] for k in range(9))==den*int(i==j) for i in range(9) for j in range(9))
    return {**common,'singular':False,'determinant':determinant,'denominator':den,'scaled_inverse':scaled,
        'A_times_scaled_inverse_equals_denI':True}

def joint(index,caches):
    pair,chart=divmod(index,4);i,j=divmod(pair,N);jp=[0]*9
    for cid,off,rev in [(i,0,chart>=2),(j,1,chart%2==1)]:
        for r,value in enumerate(caches[cid]['canonical_J']):jp[off+(7-r if rev else r)]+=int(value)
    C=2*(int(caches[i]['canonical_Cstar'])+int(caches[j]['canonical_Cstar']))
    b=[-jp[0]]+[jp[r-1]-jp[r] for r in range(1,9)]+[jp[-1]];assert sum(b)==0
    return chart,i,j,C,b
def bounds(i,j,cells):
    rhs=[]
    for cid in [i,j]:
        s=cells[cid]['state'];lo=s['L']+s['A'];hi=s['U']+s['B']
        for l,u in zip(lo,hi):rhs.extend([20*u,-20*l])
    rhs.extend([-17*Q]*9);rhs.extend([0,0]);assert len(rhs)==155;return rhs
def lower(C,b,rhs,rows,basis):
    if basis['singular']:return 'singular_chart',None
    den=basis['denominator'];S=basis['scaled_inverse']
    nums=[-sum(S[i][j]*b[j+1] for j in range(9)) for i in range(9)]
    balance=[den*b[v]+sum(n*rows[rid][v] for n,rid in zip(nums,SEED)) for v in range(10)]
    assert balance==[0]*10,'fixed_basis_decoder_full10_balance_failure'
    if any(n<0 for n in nums):return 'negative_multiplier',None
    numerator=den*C-sum(n*rhs[rid] for n,rid in zip(nums,SEED))
    # Every valid certificate retains its exact N/d, including below target.
    assert all(n>=0 for n in nums) and den>0
    return ('Lower' if numerator>=den*TARGET else 'valid_but_below_target'),numerator

def uleb(v):
    assert type(v) is int and v>=0;out=bytearray()
    while v>=128:out.append((v&127)|128);v>>=7
    out.append(v);return bytes(out)
def signed_uleb(v):return uleb(2*v if v>=0 else -2*v-1)
class Store:
    def __init__(self,index_sha,cache_sha,basis_sha):
        self.f=(HERE/'classifications.bin').open('xb');self.r=(HERE/'remaining-indices.u32.bin').open('xb')
        self.f.write(MAGIC);self.f.flush();os.fsync(self.f.fileno());self.r.flush();os.fsync(self.r.fileno())
        self.fh=sha256(MAGIC);self.rh=sha256();self.ih=sha256();self.index_sha=index_sha
        self.cache_sha=cache_sha;self.basis_sha=basis_sha;self.committed=0;self.counts={k:0 for k in TAGS}
        self.reset();self.publish()
    def reset(self):self.buf=bytearray();self.rem=bytearray();self.ids=bytearray();self.delta=Counter();self.n=0
    def add(self,index,kind,numerator):
        data=struct.pack('<I',index);self.buf.extend(data);self.buf.append(TAGS[kind]);self.ids.extend(data)
        if kind in ['Lower','valid_but_below_target']:
            assert type(numerator) is int;self.buf.extend(signed_uleb(numerator))
        else:assert numerator is None
        if kind!='Lower':self.rem.extend(data)
        self.delta[kind]+=1
        self.n+=1
    def publish(self):
        atomic_json(HERE/'prefix.json',{'schema':'J-durable-fixed-basis-prefix-v1','expected_records':EXPECTED,
            'committed_records':self.committed,'counts':self.counts,'certificate_path':rel(HERE/'classifications.bin'),
            'committed_bytes':self.f.tell(),'certificate_prefix_sha256':self.fh.hexdigest(),
            'remaining_indices_path':rel(HERE/'remaining-indices.u32.bin'),'committed_remaining_bytes':self.r.tell(),
            'remaining_indices_prefix_sha256':self.rh.hexdigest(),'input_index_sequence_sha256':self.index_sha,
            'committed_index_sequence_sha256':self.ih.hexdigest(),'affine_cache_sha256':self.cache_sha,
            'basis_sha256':self.basis_sha,'target':str(TARGET),'unprocessed_suffix_has_no_status':True})
    def commit(self):
        assert self.n>0 and self.committed+self.n<=EXPECTED
        if package_bytes()+len(self.buf)+len(self.rem)+16384>SOFT_BYTES:raise WorkLimit('soft_output19MB_before_commit')
        self.f.write(self.buf);self.f.flush();os.fsync(self.f.fileno());self.fh.update(self.buf)
        self.r.write(self.rem);self.r.flush();os.fsync(self.r.fileno());self.rh.update(self.rem)
        self.ih.update(self.ids);self.committed+=self.n
        self.counts={k:self.counts[k]+self.delta[k] for k in self.counts};self.publish();self.reset()
    def close(self):self.f.close();self.r.close()

def execute(gate_path,gate_sha):
    assert __debug__
    for name in ['started.json','result.json','failure.json','inconclusive.json','basis.json','affine-cache.jsonl','prefix.json','classifications.bin','remaining-indices.u32.bin']:
        assert not (HERE/name).exists(),('existing_attempt',name)
    start=time.monotonic();stage='input_pins';refs={};store=None;processed=0;cache_count=0;reason_counts=Counter();last=None
    outcome='inconclusive_valid_published_prefix'
    try:
        refs,indices,cells,index_sha=inputs(gate_path,gate_sha);limit(start)
        write_new(HERE/'started.json',{'schema':'J-one-fixed-basis-start-v1','pid':os.getpid(),'time_unix':time.time(),
            'classification_passes':1,'inputs_sha256':refs,'expected_records':EXPECTED,'input_index_sequence_sha256':index_sha,
            'seed_rows':SEED,'chart_order':CHARTS})
        stage='frozen_source_model'
        original=import_frozen(I/'evaluate_once.py','frozen_I_pointfree_locator_for_J')
        parser=import_frozen(BASE/'packing_parser_v3.py','frozen_s1R_parser_for_J')
        math=import_frozen(BASE/'record_math.py','frozen_s1R_math_for_J')
        core=import_frozen(HERE/'original_affine_core.py','generalized_original_affine_core_for_J')
        core.ORIGINAL_LOCATOR=original.locate_original_payload
        model=parser.load_model();math.configure(model)
        assert model['CN']==893616123055294719 and model['SA']==SA
        wanted={c['root'] for c in cells.values()};traces={}
        with gzip.open(BASE/'baseline-events.jsonl.gz','rt',encoding='ascii') as f:
            for line in f:
                event=json.loads(line)
                if event['root'] in wanted:traces[event['root'],event['pos']]=event
        stage='exact_four_fixed_bases';all_rows=[normals(c,math.ALL) for c in range(4)]
        bases=[fixed_basis(c,all_rows[c]) for c in range(4)]
        write_new(HERE/'basis.json',{'schema':'J-fixed-four-chart-bases-v1','seed_row_ids':SEED,'charts':bases,'target':str(TARGET)})
        limit(start);stage='original_cell_FS_cache';caches={}
        with (HERE/'affine-cache.jsonl').open('xb') as cachefile:
            for cid in sorted(cells):
                last={'cell_id':cid};limit(start)
                full,_state=core.extract_original_affine(cells[cid],model,math,traces)
                item={k:full[k] for k in ['cell_id','original_root','original_path','position','end','state_sha256','witness',
                    'canonical_Cstar','canonical_J','original_compact_margin','original_printed_AST_margin','consumed_payload_bits']}
                item['original_term_components_sha256']=sha256(canonical(full['terms'])).hexdigest()
                item['guards_and_original_semantics_checked']=True
                caches[cid]=item;cachefile.write(canonical(item));cache_count+=1
                if cache_count%16==0:cachefile.flush();os.fsync(cachefile.fileno())
            cachefile.flush();os.fsync(cachefile.fileno())
        cache_sha=pin(HERE/'affine-cache.jsonl');basis_sha=pin(HERE/'basis.json')
        write_new(HERE/'cache-index.json',{'schema':'J-pointfree-original-affine-cache-index-v1','cells':sorted(caches),
            'cell_count':cache_count,'affine_cache_sha256':cache_sha,'affine_cache_bytes':(HERE/'affine-cache.jsonl').stat().st_size,
            'per_pair_terms_not_duplicated':True,'new_FS_selected':0,'new_kernel_or_point_queries':0})
        store=Store(index_sha,cache_sha,basis_sha);stage='complete_H_remaining_fixed_basis_classification'
        for index in indices:
            limit(start);last={'G_index':index}
            chart,i,j,C,b=joint(index,caches);rhs=bounds(i,j,cells)
            kind,numerator=lower(C,b,rhs,all_rows[chart],bases[chart]);reason_counts[kind]+=1
            store.add(index,kind,numerator);processed+=1
            if store.n==COMMIT:
                limit(start);store.commit()
                if store.committed%2048==0:print(json.dumps({'stage':'J_committed_prefix','records':store.committed,
                    'counts':store.counts,'seconds':time.monotonic()-start}),flush=True)
        if store.n:store.commit()
        assert processed==store.committed==EXPECTED and store.ih.hexdigest()==index_sha
        outcome='complete_fixed_basis_classification'
    except WorkLimit as exc:
        write_new(HERE/'inconclusive.json',{'passed':False,'reason':str(exc),'stage':stage,'last':last,
            'processed_in_memory':processed,'cache_cells_in_memory':cache_count,'inputs_sha256_start':refs,'automatic_retry_allowed':False})
    except BaseException as exc:
        end_hashes={name:pin(ROOT/name) for name in refs}
        write_new(HERE/'failure.json',{'passed':False,'error':repr(exc),'traceback':traceback.format_exc(),'stage':stage,
            'last':last,'seconds':time.monotonic()-start,'processed_in_memory':processed,'cache_cells_in_memory':cache_count,
            'inputs_sha256_start':refs,'inputs_sha256_end':end_hashes,'automatic_retry_allowed':False})
        raise
    finally:
        if store is not None:store.close()
    after={name:pin(ROOT/name) for name in refs};assert after==refs
    prefix=load(HERE/'prefix.json') if (HERE/'prefix.json').exists() else None;complete=outcome=='complete_fixed_basis_classification'
    if complete:
        assert prefix['committed_records']==EXPECTED and sum(prefix['counts'].values())==EXPECTED
        assert (HERE/'classifications.bin').stat().st_size==prefix['committed_bytes']
        assert (HERE/'remaining-indices.u32.bin').stat().st_size==prefix['committed_remaining_bytes']
    result={'schema':'J-one-fixed-basis-family-result-v1','passed':complete,'outcome':outcome,'pid':os.getpid(),
        'seconds':time.monotonic()-start,'classification_passes':1,'complete_H_remaining_classified':complete,
        'expected_records':EXPECTED,'committed_records':prefix['committed_records'] if prefix else 0,
        'counts':prefix['counts'] if prefix else {k:0 for k in TAGS},'inputs_sha256_start':refs,'inputs_sha256_end':after,
        'prefix_sha256':pin(HERE/'prefix.json') if prefix else None,'processed_in_memory':processed,
        'uncommitted_records_not_accepted':processed-(prefix['committed_records'] if prefix else 0),
        'cache_cells':cache_count,'reason_counts_not_independently_verified':dict(reason_counts),'seed_row_ids':SEED,
        'valid_below_target_exact_bounds_retained':True,'bound_fraction_convention':'N/d, with d from shared chart basis',
        'unresolved_records':(prefix['committed_records']-prefix['counts']['Lower']) if prefix else 0,
        'alternate_basis_or_threshold_retries':0,'optimizer_calls':0,'new_FS_selected':0,'kernel_or_point_queries':0,
        'Lean_runs':0,'independent_certificate_replay_pending':True,'new_global_actual_floor_proven':False,
        'new_unconditional_kappa_proven':False,'website_source_and_policy_runtime_budget':'unknown','website_submission_ready':False}
    write_new(HERE/'result.json',result)
    print(json.dumps({'passed':complete,'outcome':outcome,'records':result['committed_records'],
        'counts':result['counts'],'seconds':result['seconds']}),flush=True)

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--execute-authorized-fixed-J',action='store_true')
    ap.add_argument('--gate');ap.add_argument('--gate-sha256');a=ap.parse_args()
    if not a.execute_authorized_fixed_J:
        print(json.dumps({'prepared_only':True,'FS_extractions':0,'matrix_executions':0,'new_root_gate_required':True}));return
    assert a.gate and a.gate_sha256;execute(checked_path(a.gate),a.gate_sha256)

if __name__=='__main__':main()
