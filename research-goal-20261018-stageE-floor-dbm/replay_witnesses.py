"""Independent stdlib verification of E paid/cycle/potential records, no BF.

Does not import E or C producers and never evaluates the actual kernel/FS.
All payments use original B integer margins; edges come from original PR.
"""
from pathlib import Path
from hashlib import sha256
from fractions import Fraction as F
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
N=1187
SC=32768
SA=10**20
KAPPA=SC*10**10*1024
CN=893616123055294719
TAU_N=893916123055294719
C_N=893766123055294719
THRESHOLD=KAPPA*(TAU_N-CN)
ORIS=('id/id','id/rev','rev/id','rev/rev')
TOTAL=4*N*N

def pin(p):
    h=sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''):h.update(block)
    return h.hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode('ascii')+b'\n'

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    out=HERE/'independent-witness-replay.json'
    if args.write_receipt:assert not out.exists()
    start=time.monotonic();a=load(HERE/'model.json');assert a['passed'] and a['model_passes']==1
    assert a['inputs_sha256_start']==a['inputs_sha256_end']
    for path,expected in a['inputs_sha256_start'].items():assert pin(ROOT/path)==expected
    assert 2*C_N==CN+TAU_N and THRESHOLD==2*KAPPA*(C_N-CN)
    assert a['KAPPA']==KAPPA and int(a['payment_threshold'])==THRESHOLD
    raw=SOURCE.read_text(encoding='utf-8')
    cert=raw[raw.index('namespace AMW.Cert.PC9QB6M\n'):raw.index('end AMW.Cert.PC9QB6MData')]
    pr=re.findall(r'\bdef PR\s*:[^\n]*:= (\[[^\n]*\])',cert);assert len(pr)==1
    spans=[(r,r+1) for r in range(8)]+[tuple(x) for x in ast.literal_eval(pr[0])]
    assert len(spans)==36 and set(spans)=={(i,j) for i in range(9) for j in range(i+1,9)}
    bc=load(B/'classification.json');assert spans==[tuple(x) for x in bc['pair_order_from_source']]
    p=ROOT/bc['outputs']['exceptions']['path'];assert pin(p)==bc['outputs']['exceptions']['sha256']
    cells=[];margins=[]
    with gzip.open(p,'rt',encoding='ascii') as f:
        for line in f:
            c=json.loads(line);s=c['state'];lo=s['L']+s['A'];hi=s['U']+s['B']
            assert c['exception_id']==len(cells) and s['M']==0 and len(lo)==len(hi)==36
            assert c['coordinate_scale']==SC and c['separation']=='17/20' and c['relaxed_orientation'] is True
            state=[v for pair in zip(lo,hi) for v in pair]+[0]
            assert sha256(canonical(state)).hexdigest()==c['state_sha256']
            m=int(c['original_margin']);assert m>=0 and int(c['tau_margin'])==m-THRESHOLD<0
            cells.append(c);margins.append(m)
    assert len(cells)==N
    local={}
    for rev in [False,True]:
        for cid,c in enumerate(cells):
            s=c['state'];lo=s['L']+s['A'];hi=s['U']+s['B'];es=[]
            for k,(u,v) in enumerate(spans):
                if rev:u,v=8-v,8-u
                es.extend([(u,v,20*hi[k]),(v,u,-20*lo[k])])
            local[rev,cid]=es
    def info(ordinal):
        oi,rem=divmod(ordinal,N*N);i,j=divmod(rem,N)
        pr,sr=(x=='rev' for x in ORIS[oi].split('/'))
        return oi,i,j,pr,sr
    def edge(ordinal,eid):
        assert 0<=eid<153
        _oi,i,j,pr,sr=info(ordinal)
        if eid<72:return local[pr,i][eid]
        if eid<144:
            u,v,w=local[sr,j][eid-72];return u+1,v+1,w
        r=eid-144;return r+1,r,-17*SC
    expected=a['cases_checked'];assert 0<expected<=TOTAL
    proof=HERE/'witness-prefix.bin.gz';assert pin(proof)==a['proof_stream']['sha256']
    h=sha256();nbytes=0;counts=Counter();ncycle=0;feasible=None
    with gzip.open(proof,'rb') as f:
        magic=f.read(5);assert magic==b'RZE1\n';h.update(magic);nbytes+=len(magic)
        for ordinal in range(expected):
            tag=f.read(1);assert len(tag)==1;h.update(tag);nbytes+=1
            oi,i,j,pr,sr=info(ordinal);m=margins[i]+margins[j]
            if tag==b'\x40':
                assert m>=THRESHOLD
                counts['original_scalar_floors_pay_target']+=1
                continue
            assert m<THRESHOLD
            if tag==b'\xf0':
                assert ordinal==expected-1 and not a['all_cases_covered']
                feasible=load(HERE/'first-underpaid-feasible.json')
                assert feasible['case_ordinal']==ordinal and feasible['orientation']==ORIS[oi]
                assert feasible['prefix_exception_id']==i and feasible['suffix_exception_id']==j
                assert feasible['prefix_cell']==cells[i] and feasible['suffix_cell']==cells[j]
                assert int(feasible['prefix_M0'])==margins[i] and int(feasible['suffix_M0'])==margins[j]
                assert int(feasible['sum_M0'])==m and int(feasible['payment_threshold'])==THRESHOLD
                assert int(feasible['underpayment'])==THRESHOLD-m
                assert F(feasible['sum_original_floor_minus_twice_c'])==F(m-THRESHOLD,KAPPA*SA)<0
                x=feasible['X_integer_potential'];assert len(x)==10 and x[0]==0 and all(type(v) is int for v in x)
                assert feasible['X_scale']==20*SC and feasible['positions']==[str(F(v,20*SC)) for v in x]
                allrows=[]
                for eid in range(153):
                    u,v,w=edge(ordinal,eid);delta=x[v]-x[u];assert delta<=w
                    allrows.append({'edge_id':eid,'u':u,'v':v,'bound':w,'actual_difference':delta,'slack':w-delta})
                assert feasible['all153_edges']==allrows and feasible['all153_edges_verified'] is True
                ordered=[]
                for reverse,offset,key in [(pr,0,'prefix_ordered'),(sr,1,'suffix_ordered')]:
                    first=x[offset+1]-x[offset];last=x[offset+8]-x[offset+7]
                    left,right=(last,first) if reverse else (first,last)
                    obj={'orientation':'rev' if reverse else 'id','offset':offset,'original_h0_scaled':left,
                        'original_h7_scaled':right,'four_point_left_minus_right_scaled':left-right,
                        'ordered_condition_holds':left<=right}
                    assert feasible[key]==obj;ordered.append(left<=right)
                holds=all(ordered);assert feasible['ordered_conditions_hold']==holds
                label='underpaid_DBM_feasible_ordered_holds' if holds else 'underpaid_relaxed_DBM_feasible_ordered_violated'
                assert feasible['outcome']==a['outcome']==label
                counts['underpaid_feasible_case']+=1;continue
            method,length=divmod(tag[0],16);assert method in [0,1,2,3] and 1<=length<=10
            ids=list(f.read(length));assert len(ids)==length;h.update(bytes(ids));nbytes+=length
            es=[edge(ordinal,k) for k in ids]
            assert all(u[1]==v[0] for u,v in zip(es,es[1:]+es[:1])) and sum(e[2] for e in es)<0
            if method==0:
                assert length==2 and sum(k<72 for k in ids)==1 and sum(72<=k<144 for k in ids)==1
                assert all(1<=u<=8 and 1<=v<=8 for u,v,_ in es)
                counts['underpaid_shared_span_two_edge_conflict']+=1
            elif method==1:
                assert all(k<72 or 144<=k<=151 for k in ids)
                counts['underpaid_prefix_single_state_sep_negative_cycle']+=1
            elif method==2:
                assert all(72<=k<144 or 145<=k<=152 for k in ids)
                counts['underpaid_suffix_single_state_sep_negative_cycle']+=1
            else:counts['underpaid_full_BF_negative_cycle']+=1
            ncycle+=1
        assert f.read(1)==b''
    assert h.hexdigest()==a['proof_stream']['uncompressed_sha256'] and nbytes==a['proof_stream']['uncompressed_bytes']
    assert dict(counts)==a['counts'] and ncycle==a['negative_cycle_records']
    if feasible is None:
        assert a['all_cases_covered'] and expected==TOTAL
        assert a['outcome']=='all_pairs_paid_or_geometrically_infeasible'
    else:assert a['stopped_at_first_underpaid_relaxed_feasible'] and not a['all_cases_covered']
    for path,expected_sha in a['inputs_sha256_start'].items():assert pin(ROOT/path)==expected_sha
    result={'schema':'independent-E-scalar-cycle-potential-replay-v1','passed':True,
        'model_sha256':pin(HERE/'model.json'),'script_sha256':pin(Path(__file__)),
        'cases_checked':expected,'counts':dict(counts),'payment_threshold':str(THRESHOLD),
        'strict_negative_cycles_verified':ncycle,'underpaid_feasible_potential_verified':feasible is not None,
        'outcome':a['outcome'],'all_cases_covered':a['all_cases_covered'],
        'producer_modules_imported':0,'BF_or_optimizer_calls':0,'kernel_queries':0,'Lean_runs':0,
        'new_joint_floor_proven':False,'new_unconditional_zero_proportion_proven':False,
        'complete_source_and_runtime_budget':'unknown','seconds':time.monotonic()-start,
        'scope':'Existing scalar floors or exact cycle/potential replay. No actual energy, FS or point evaluation. Not formal source/kernel acceptance.'}
    if args.write_receipt:
        with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps(result))

if __name__=='__main__':main()
