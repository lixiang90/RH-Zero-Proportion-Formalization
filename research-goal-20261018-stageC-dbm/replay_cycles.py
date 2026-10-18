"""Independent stdlib witness verification; no producer import or BF solver.

Rebuild original36-span oriented edges directly from frozen B/source literals.
For every implicit case verify a supplied strict cycle or the single terminal
integer potential. This does not generate data or strengthen any constraints.
Prepared only until a separately authorized scan has closed outputs.
"""
from pathlib import Path
from hashlib import sha256
from fractions import Fraction
from collections import Counter
import argparse
import ast
import gzip
import json
import re
import time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
SC=32768
N=1187
ORIS=('id/id','id/rev','rev/id','rev/rev')
TOTAL=4*N*N
B=ROOT/'research-goal-20261018-stageB-classification'
SOURCE=ROOT/'research-goal-20261018-record-source-audit/snapshot/Solution.lean'
SOURCE_SHA='f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf'

def hash_file(p):
    h=sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode('ascii')+b'\n'

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write-receipt',action='store_true')
    args=ap.parse_args();out=HERE/'independent-cycle-replay.json'
    if args.write_receipt:assert not out.exists()
    t=time.monotonic();scan=load(HERE/'scan.json');assert scan['passed']
    assert scan['scan_passes']==1 and scan['total_cases']==TOTAL
    assert scan['inputs_sha256_start']==scan['inputs_sha256_end']
    for name,expected in scan['inputs_sha256_start'].items():assert hash_file(ROOT/name)==expected
    assert hash_file(SOURCE)==SOURCE_SHA
    text=SOURCE.read_text(encoding='utf-8')
    text=text[text.index('namespace AMW.Cert.PC9QB6M\n'):text.index('end AMW.Cert.PC9QB6MData')]
    matches=re.findall(r'\bdef PR\s*:[^\n]*:= (\[[^\n]*\])',text)
    assert len(matches)==1;PR=[tuple(x) for x in ast.literal_eval(matches[0])]
    spans=[(r,r+1) for r in range(8)]+PR
    assert len(spans)==36 and set(spans)=={(i,j) for i in range(9) for j in range(i+1,9)}
    bc=load(B/'classification.json')
    assert spans==[tuple(x) for x in bc['pair_order_from_source']]
    p=ROOT/bc['outputs']['exceptions']['path'];assert hash_file(p)==bc['outputs']['exceptions']['sha256']
    cells=[]
    with gzip.open(p,'rt',encoding='ascii') as f:
        for line in f:
            c=json.loads(line);assert c['exception_id']==len(cells)
            s=c['state'];l=s['L']+s['A'];u=s['U']+s['B']
            assert len(l)==len(u)==36 and s['M']==0 and c['coordinate_scale']==SC
            assert c['separation']=='17/20' and c['relaxed_orientation'] is True
            state=[v for pair in zip(l,u) for v in pair]+[0]
            assert sha256(canonical(state)).hexdigest()==c['state_sha256']
            cells.append(c)
    assert len(cells)==N
    # Two local orientation tables, original span ids kept, no parser imports.
    local={}
    for reverse in [False,True]:
        for cid,c in enumerate(cells):
            s=c['state'];lo=s['L']+s['A'];hi=s['U']+s['B'];e=[]
            for k,(a,b) in enumerate(spans):
                if reverse:a,b=8-b,8-a
                e.append((a,b,hi[k]*20));e.append((b,a,-lo[k]*20))
            local[reverse,cid]=e
    def case_info(number):
        oi,rem=divmod(number,N*N);i,j=divmod(rem,N)
        pr,sr=[x=='rev' for x in ORIS[oi].split('/')]
        return oi,i,j,pr,sr
    def edge(number,eid):
        assert 0<=eid<153
        _oi,i,j,pr,sr=case_info(number)
        if eid<72:return local[pr,i][eid]
        if eid<144:
            a,b,w=local[sr,j][eid-72];return a+1,b+1,w
        r=eid-144;return r+1,r,-17*SC
    expected=scan['cases_checked'];assert 0<expected<=TOTAL
    proof=HERE/'cycle-prefix.bin.gz';assert hash_file(proof)==scan['proof_stream']['sha256']
    h=sha256();rawbytes=0;counts=Counter();negative=0;feasible=None
    with gzip.open(proof,'rb') as f:
        magic=f.read(7);assert magic==b'RZDBM1\n';h.update(magic);rawbytes+=7
        for ordinal in range(expected):
            head=f.read(1);assert len(head)==1;h.update(head);rawbytes+=1
            if head==b'\xf0':
                assert ordinal==expected-1 and not scan['all_cases_covered']
                feasible=load(HERE/'first-feasible.json');oi,i,j,pr,sr=case_info(ordinal)
                assert feasible['case_ordinal']==ordinal and feasible['orientation']==ORIS[oi]
                assert feasible['prefix_exception_id']==i and feasible['suffix_exception_id']==j
                assert feasible['prefix_cell']==cells[i] and feasible['suffix_cell']==cells[j]
                x=feasible['X_integer_potential'];assert len(x)==10 and all(type(a) is int for a in x) and x[0]==0
                assert feasible['X_scale']==20*SC
                assert feasible['positions']==[str(Fraction(a,20*SC)) for a in x]
                checks=[]
                for eid in range(153):
                    a,b,w=edge(ordinal,eid);actual=x[b]-x[a];assert actual<=w
                    checks.append({'edge_id':eid,'u':a,'v':b,'bound':w,'actual_difference':actual,'slack':w-actual})
                assert feasible['all153_edges']==checks and feasible['all153_edges_verified'] is True
                ordered=[]
                for reverse,offset,name in [(pr,0,'prefix_ordered'),(sr,1,'suffix_ordered')]:
                    first=x[offset+1]-x[offset];last=x[offset+8]-x[offset+7]
                    a,b=(last,first) if reverse else (first,last)
                    obj={'orientation':'rev' if reverse else 'id','offset':offset,
                         'original_h0_scaled':a,'original_h7_scaled':b,
                         'four_point_left_minus_right_scaled':a-b,'ordered_condition_holds':a<=b}
                    assert feasible[name]==obj;ordered.append(a<=b)
                holds=all(ordered)
                assert feasible['ordered_conditions_hold']==holds
                label='ordered_conditions_hold' if holds else 'relaxed_box_feasible_ordered_violated'
                assert feasible['outcome']==scan['outcome']==label
                counts['feasible_case']+=1
                continue
            tag=head[0];method,length=divmod(tag,16)
            assert method in [0,1,2,3] and 1<=length<=10
            body=f.read(length);assert len(body)==length;h.update(body);rawbytes+=length
            ids=list(body);edges=[edge(ordinal,k) for k in ids]
            assert all(a[1]==b[0] for a,b in zip(edges,edges[1:]+edges[:1]))
            assert sum(e[2] for e in edges)<0
            if method==0:
                assert length==2 and sum(k<72 for k in ids)==1 and sum(72<=k<144 for k in ids)==1
                assert all(1<=a<=8 and 1<=b<=8 for a,b,_ in edges)
                counts['shared_28_span_two_edge_conflict']+=1
            elif method==1:
                assert all(k<72 or 144<=k<=151 for k in ids)
                counts['prefix_single_state_sep_negative_cycle']+=1
            elif method==2:
                assert all(72<=k<144 or 145<=k<=152 for k in ids)
                counts['suffix_single_state_sep_negative_cycle']+=1
            else:counts['full_BF_negative_cycle']+=1
            negative+=1
        assert f.read(1)==b''
    assert h.hexdigest()==scan['proof_stream']['uncompressed_sha256']
    assert rawbytes==scan['proof_stream']['uncompressed_bytes']
    assert negative==scan['negative_cycle_records'] and dict(counts)==scan['counts']
    if feasible is None:
        assert expected==negative==TOTAL and scan['all_cases_covered'] is True
        assert scan['outcome']=='all_relaxed_DBM_cases_infeasible'
    else:
        assert scan['stopped_at_first_relaxed_feasible'] and negative+1==expected
    for name,expected_sha in scan['inputs_sha256_start'].items():assert hash_file(ROOT/name)==expected_sha
    result={'schema':'independent-fixed-DBM-cycle-or-potential-replay-v1','passed':True,
        'producer_scan_sha256':hash_file(HERE/'scan.json'),'script_sha256':hash_file(Path(__file__)),
        'source_sha256':SOURCE_SHA,'cases_checked':expected,'negative_cycles_verified':negative,
        'terminal_feasible_potential_verified':feasible is not None,'all153_edges_verified_at_feasible':feasible is not None,
        'outcome':scan['outcome'],'counts':dict(counts),'all_cases_covered':scan['all_cases_covered'],
        'proof_uncompressed_sha256':h.hexdigest(),'producer_modules_imported':0,
        'BF_solver_calls':0,'kernel_queries':0,'Lean_runs':0,'new_joint_floor_proven':False,
        'new_unconditional_zero_proportion_proven':False,'complete_source_budget':'unknown',
        'seconds':time.monotonic()-t,
        'scope':'Exact cycle/potential witness replay only. A relaxed feasible point is not actual F<tau or a counterexample; no original energy data are evaluated.'}
    if args.write_receipt:
        with out.open('x',encoding='utf-8',newline='\n') as f:json.dump(result,f,indent=2);f.write('\n')
    print(json.dumps(result))

if __name__=='__main__':main()
