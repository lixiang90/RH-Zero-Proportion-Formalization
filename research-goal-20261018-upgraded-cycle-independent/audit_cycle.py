"""Independent fixed-nine-edge L checker; preparation does no mathematics.

K and the complete J independent replays are explicit frozen premises. Only
JLB2 decoding, nine weights, their original directed closure and exact sum are
replayed. No producer import, FS, matrix, point, graph search, LP or Lean.
"""
from pathlib import Path
from hashlib import sha256
from collections import Counter
import argparse
import json
import os
import struct
import time
import traceback

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
EXPECTED=(2867814,23816,90540,390637,1543511,484431,157722,1232184,2912941)
TARGET=4*32768*10**10*1024*893766123055294719
PINS={
 'research-goal-20261018-upgraded-cycle/result.json':'c81c6e46d6d3f0135fcbd86abd596ce2a8c4e458cae480a0911b010470dee5cd',
 'research-goal-20261018-stageJ-independent/audit-files.json':'32de2e9381d1c103209c89b8f007d29815746a398c5c3d197f7762a727f55005',
 'research-goal-20261018-stageJ-independent/independent-review.json':'57abac20579238798df6eed99bf211cf019b75bddc0617d760c6297faea61ec1',
 'research-goal-20261018-window-potential-cycle-independent/audit-files.json':'98983c69e3fb9070149afbd79e01f5877138a5983641b2e0b7523698bf6a635d',
 'research-goal-20261018-window-potential-cycle-independent/independent-review.json':'2b21a5a0a8c1a628a2aa14c8f7530de34d5ba9714adb30998013a1951e405d14',
 'research-goal-20261018-window-potential-cycle/result.json':'df5a67d1c1660e93519608c91400cb5d628845b96d9a5d27413a314796ffd585',
 'research-goal-20261018-stageJ-fixed-basis-preparation/basis.json':'a5eb97d2565dd7ce6da675781070c8baa94a3dd9f7e5692f88f1115c153424ea',
 'research-goal-20261018-stageJ-fixed-basis-preparation/classifications.bin':'1ac39ccd421abab2feac88f85c8baa9d8cff4c9fbdd85f8b946558eca018fe25',
 'research-goal-20261018-stageH-ordered-transport/remaining-indices.u32.bin':'c740852a5757983f462f3a78eb05d1aca5410ffb4077682e3afa48d6f7943559',
 'research-goal-20261018-window-potential-static/JOINT-EDGE-EXTENSION.zh.md':'0f8f4721de9de2297e35d72bac5fe7b5148f31035856e9c396cc1fb94b0b9540',
 'research-goal-20261018-window-potential-static/EDGE-REVIEW.zh.md':'3f19eac364ccb2635152dc9c0a417f044b9e0318253680eeb92c8305d771f9ec'}

def pin(p):return sha256(p.read_bytes()).hexdigest()
def local(name):
    p=(ROOT/name).resolve();assert p.is_relative_to(ROOT);return p
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def write(name,obj):
    with (HERE/name).open('x',encoding='utf-8',newline='\n') as f:
        json.dump(obj,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())

def parse_records(data,indices):
    """Independent canonical ULEB and zigzag decoder, complete original order."""
    assert data[:5]==b'JLB2\n';position=5;selected={};counts=Counter()
    for expected in indices:
        assert position+5<=len(data)
        index=int.from_bytes(data[position:position+4],'little');tag=data[position+4];position+=5
        assert index==expected and tag in (0,1,2,3)
        numerator=None
        if tag in (1,2):
            value=shift=0
            while True:
                assert position<len(data) and shift<100000
                byte=data[position];position+=1;value+=(byte&127)*(1<<shift)
                if byte<128:
                    assert shift==0 or byte!=0,'noncanonical_unsigned_LEB'
                    break
                shift+=7
            numerator=(value>>1)^-(value&1)
        if index in EXPECTED:selected[index]=(tag,numerator)
        counts[tag]+=1
    assert position==len(data) and tuple(sorted(selected))==tuple(sorted(EXPECTED))
    assert [counts[k] for k in range(4)]==[3141,1,359,11877]
    return selected

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--audit-authorized-fixed-cycle',action='store_true')
    ap.add_argument('--gate');ap.add_argument('--gate-sha256');args=ap.parse_args()
    if not args.audit_authorized_fixed_cycle:
        print(json.dumps({'prepared_only':True,'math_executions':0}));return
    assert args.gate and args.gate_sha256
    assert not (HERE/'independent-review.json').exists() and not (HERE/'failure.json').exists()
    began=time.monotonic();refs={}
    try:
        gp=local(args.gate);assert pin(gp)==args.gate_sha256;gate=load(gp)
        assert gate['independent_fixed_cycle_audits_authorized']==1
        assert gate['audit_script_path']==Path(__file__).relative_to(ROOT).as_posix()
        assert pin(Path(__file__))==gate['audit_script_sha256']
        refs={args.gate:args.gate_sha256,Path(__file__).relative_to(ROOT).as_posix():gate['audit_script_sha256'],**PINS}
        for name,h in refs.items():assert pin(local(name))==h
        jr=load(local('research-goal-20261018-stageJ-independent/independent-review.json'))
        kr=load(local('research-goal-20261018-window-potential-cycle-independent/independent-review.json'))
        assert jr['passed'] is True and jr['complete_original_H_input_range_audited'] is True and jr['records']==15378
        assert jr['all_effective_N_over_d_checked_including_below_target'] is True
        assert kr['passed'] is True
        original=load(local('research-goal-20261018-window-potential-cycle/result.json'))['cycle']
        assert tuple(e['index'] for e in original)==EXPECTED
        index_bytes=local('research-goal-20261018-stageH-ordered-transport/remaining-indices.u32.bin').read_bytes()
        assert len(index_bytes)==15378*4
        indices=[entry[0] for entry in struct.iter_unpack('<I',index_bytes)]
        assert indices==sorted(set(indices))
        selected=parse_records(local('research-goal-20261018-stageJ-fixed-basis-preparation/classifications.bin').read_bytes(),indices)
        basis=load(local('research-goal-20261018-stageJ-fixed-basis-preparation/basis.json'))
        assert int(basis['target'])==TARGET and len(basis['charts'])==4
        edges=[]
        for e in original:
            q=e['index'];pair,chart=divmod(q,4);i,j=divmod(pair,1187)
            source,target=2*i+chart//2,2*j+chart%2
            assert (e['source'],e['target'],e['chart'])==(source,target,chart)
            tag,numerator=selected[q];baseline=24*int(e['weight']);improved=None;d=None
            if tag in (1,2):
                d=basis['charts'][chart]['denominator'];assert type(d) is int and 1<=d<=4 and 12%d==0
                assert (tag==1)==(numerator>=d*TARGET)
                improved=(12//d)*(numerator-d*TARGET)
            else:assert numerator is None
            w=baseline if improved is None else max(baseline,improved)
            edges.append({'index':q,'source':source,'target':target,'J_tag':tag,
                'J_N':str(numerator) if numerator is not None else None,'J_d':d,
                'baseline_weight':str(baseline),'valid_J_weight':str(improved) if improved is not None else None,
                'stronger_weight':str(w)})
        assert len({e['source'] for e in edges})==9
        assert all(e['target']==edges[(k+1)%9]['source'] for k,e in enumerate(edges))
        total=sum(int(e['stronger_weight']) for e in edges);old=sum(int(e['baseline_weight']) for e in edges)
        result=load(local('research-goal-20261018-upgraded-cycle/result.json'))
        assert result['passed'] is True and result['edges']==edges
        assert int(result['exact_original_scaled_weight'])==old and int(result['exact_upgraded_cycle_weight'])==total
        assert total>=old and result['fixed_J_enhanced_outer_potential_model_refuted'] is (total<0)
        for name,h in result['input_sha256_start'].items():assert pin(local(name))==h
        assert result['input_sha256_start']==result['input_sha256_end']
        after={name:pin(local(name)) for name in refs};assert after==refs
        record={'schema':'independent-fixed-nine-J-enhanced-cycle-review-v1','passed':True,'pid':os.getpid(),
            'seconds':time.monotonic()-began,'independent_audit_calls':1,'inputs_sha256_start':refs,'inputs_sha256_end':after,
            'J_original_records_parsed_to_exact_EOF':15378,'fixed_cycle_indices':list(EXPECTED),'edges':edges,
            'exact_original_scaled_weight':str(old),'exact_upgraded_cycle_weight':str(total),
            'fixed_J_enhanced_outer_potential_model_refuted':total<0,'producer_imports':0,
            'FS_matrix_graphsearch_point_kernel_optimizer_or_Lean_runs':0,
            'mixed_affine_global_floor_refuted':False,'actual_energy_or_physical_cycle_counterexample':False,
            'new_unconditional_zero_proportion_proven':False,
            'scope':'Only the prescribed J-enhanced outer potential model on the unchanged verified nine-edge K cycle; other bases/duals and actual F are not excluded.'}
        write('independent-review.json',record)
        print(json.dumps({'passed':True,'seconds':record['seconds'],'exact_sum':str(total),'fixed_outer_model_refuted':total<0}))
    except BaseException as exc:
        write('failure.json',{'passed':False,'error':repr(exc),'traceback':traceback.format_exc(),
            'seconds':time.monotonic()-began,'automatic_retry_allowed':False});raise

if __name__=='__main__':main()
