"""Prepared only: evaluate two ORIGINAL FS affine models at one frozen C point.

No actual kernel evaluation, new tangent/query, optimizer, geometry tightening,
point selection or mathematical witness search.  Requires a separate written
one-arithmetic gate after the source lemma/flow notes have been frozen.
"""
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
import argparse
import gzip
import json
import os
import re
import sys
import time
import traceback

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
BASE=ROOT/'research-goal-20261018-record-baseline-replay'
sys.path.insert(0,str(BASE))
import packing_parser_v3 as parser
import record_math as math

Q=32768
R=1024
D=10**9
V=10**10
SA=10**20
KAPPA=Q*V*R
K=SA*KAPPA
C_N=893766123055294719
CN=893616123055294719
TAU_N=893916123055294719
C_DIR=ROOT/'research-goal-20261018-stageC-dbm'
C_PIN='31e29433295f301c663fc2077d071bae4dfb89b1514eaa694e878fd9f5c8aae0'
POINT_SHA='bbb1c08a3d913a10b45cb40ec4b9ab3a0cfa5432419585d9922f0638ca222812'
STATIC_PIN='51220d528c3c7e7f3673dda216a462117c6def29f9cacb44d19fab41d0500637'
FLOW_PATH=ROOT/'research-goal-20261018-joint-affine-flow-proof/proof-files.json'
FLOW_PIN='e3d61af4a46aed20eaee334af3f2c3c9c95e8ceb1c06027a7e22e0de349064eb'

def canonical(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode('ascii')
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def pin(p):return sha256(p.read_bytes()).hexdigest()
def rel(p):return p.relative_to(ROOT).as_posix()
def write_new(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())

def input_guards(gate_path,gate_sha):
    assert gate_path.is_relative_to(ROOT) and pin(gate_path)==gate_sha
    gate=load(gate_path)
    assert gate['affine_evaluations_authorized']==1
    assert gate['stageC_producer_manifest_sha256']==C_PIN
    assert gate['first_feasible_witness_sha256']==POINT_SHA
    assert int(gate['c_numerator'])==C_N and int(gate['denominator'])==SA
    assert int(gate['baseline_c9_numerator'])==CN
    assert gate['source_static_manifest_sha256']==STATIC_PIN
    assert gate['resource_limits']=={'elapsed_seconds':60,'closed_output_bytes':8000000}
    refs={rel(Path(__file__)):pin(Path(__file__)),rel(gate_path):gate_sha,
          rel(HERE/'run_once.py'):pin(HERE/'run_once.py')}
    packets=[(C_DIR/'files.json',C_PIN),
        (ROOT/gate['stageC_independent_manifest_path'],gate['stageC_independent_manifest_sha256']),
        (ROOT/gate['source_static_manifest_path'],STATIC_PIN),(FLOW_PATH,FLOW_PIN)]
    for path,expected in packets:
        assert path.is_relative_to(ROOT) and pin(path)==expected;refs[rel(path)]=expected
        packet=load(path)
        for key in ['files','package_files','read_only_dependencies','dependency_files','dependencies','read_only_existing_references']:
            for row in packet.get(key,[]):
                p=ROOT/row['path'];assert p.is_relative_to(ROOT)
                assert pin(p)==row['sha256']
                if 'bytes' in row:assert p.stat().st_size==row['bytes']
                if row['path'] in refs:assert refs[row['path']]==row['sha256']
                refs[row['path']]=row['sha256']
    point=load(C_DIR/'first-feasible.json');assert pin(C_DIR/'first-feasible.json')==POINT_SHA
    assert point['orientation']=='id/id' and point['case_ordinal']==1
    assert point['prefix_exception_id']==0 and point['suffix_exception_id']==1
    assert point['ordered_conditions_hold'] is True and point['X_scale']==20*Q
    assert point['X_integer_potential']==[0,557056,1355776,2131556,2724876,3392856,3986176,4635136,6374116,8254976]
    assert gate['expected_X']==point['X_integer_potential'] and gate['X_scale']==20*Q
    assert gate['first_feasible_witness_path']==rel(C_DIR/'first-feasible.json')
    assert KAPPA==math.SLOPE==335544320000000000 and 2*C_N==CN+TAU_N
    return refs,point

def original_state_and_payload(cell,model,traces):
    """Follow only the original path, using original A cursors for child starts."""
    root=cell['root'];pos=1;state=math.root(model['roots'][root]['indices'])
    path=cell['path'];assert path.startswith('r') and set(path[1:])<=set('01')
    def bits(pos):return (model['WL'][root].get(pos//32768,0)>>(pos%32768))&((1<<480)-1)
    for turn in path[1:]:
        event=traces[root,pos];word=bits(pos)
        assert event['kind']=='branch' and word&1
        axis=(word>>1)&63;mode=(word>>7)&1
        assert axis==event['axis'] and mode==event['mode']
        i,j=math.ALL[axis]
        cut=math.bcut(state[0][axis],state[1][axis]) if mode else (state[0][axis]+state[1][axis])>>1
        assert cut==event['cut']
        state=math.split(state,i,j,cut,turn=='0')
        pos=event['left' if turn=='0' else 'right']
    assert pos==cell['position'] and traces[root,pos]['kind']=='numeric'
    flat=[v for pair in zip(*state) for v in pair]+[0]
    assert sha256(canonical(flat)).hexdigest()==cell['state_sha256']
    expected=cell['state']
    assert state==(expected['L']+expected['A'],expected['U']+expected['B'])
    word=bits(pos);assert not word&3 and not state[1][7]<state[0][0]
    return state,word>>2

def evaluate_window(cell,offset,point,model,traces):
    state,word=original_state_and_payload(cell,model,traces)
    lo,hi=state;scaled_gaps=[F(point['X_integer_potential'][k+1]-point['X_integer_potential'][k],20) for k in range(9)]
    g=[x/Q for x in scaled_gaps]
    for k,(i,j) in enumerate(math.ALL):
        span=sum(g[offset+i:offset+j])
        assert F(lo[k],Q)<=span<=F(hi[k],Q)
    fs=[];terms=[];o=0;constant=F(0);coeff=[F(0)]*9
    for r,b in enumerate(model['BS']):coeff[offset+r]+=F(b,SA)
    gamma=[D*R*b for b in model['BS']]
    weighted_mv=weighted_cp=weighted_cn=0
    for ti,(i,j,a,_slot) in enumerate(model['TS']):
        L,U=math.term_bounds(state,i,j);L0=sum(lo[i:j]);uc=max(L+1,U)
        assert L0<=L<=U
        f,o=math.dec(word,o,L,U);kind,lam,p,r=f;fs.append(f)
        l1,l2=math.weights(kind,lam);lc=R-l1-l2
        assert min(l1,l2,lc)>=0 and l1+l2+lc==R
        pt=[model['PTraw'].get(x,0)&((1<<96)-1) for x in [p,r]]
        guards=[]
        for amount,x in zip([l1,l2],[p,r]):
            if not amount:continue
            assert x in model['PTraw']
            raw=model['PTraw'][x];vl=max(0,x-((raw>>96)&((1<<20)-1)));vu=x+(raw>>116)
            assert 1<=vu and vl<=L<=x<=U<=vu
            guards.append({'mass':amount,'original_point':x,'valid_lower':vl,'valid_upper':vu,'guard_passed':True})
        lb=math.lb(L,uc)
        mv=lc*lb+l1*(pt[0]&math.MASK32)+l2*(pt[1]&math.MASK32)
        msl=l1*((pt[0]>>32)&math.MASK32)+l2*((pt[1]>>32)&math.MASK32)
        mass=l1+l2
        cp=sum(amount*max(0,(raw>>64)-2*D)*max(0,x-L0) for amount,raw,x in zip([l1,l2],pt,[p,r]))
        cn=sum(amount*max(0,2*D-(raw>>64))*max(0,x-L0) for amount,raw,x in zip([l1,l2],pt,[p,r]))
        sigma=F(msl-2*D*mass,D*R)
        beta=F(mv,V*R)+F(cp-cn,Q*D*R)-sigma*F(L0,Q)
        s=sum(g[offset+i:offset+j]);value=beta+sigma*s
        # Direct scaled numerator is independent of the beta rearrangement.
        num=Q*mv+10*(cp-cn)+10*(msl-2*D*mass)*(Q*s-L0)
        assert value==num/KAPPA
        constant+=F(a,SA)*beta
        for rr in range(i,j):
            coeff[offset+rr]+=F(a,SA)*sigma
            gamma[rr]+=a*(msl-2*D*mass)
        weighted_mv+=a*mv;weighted_cp+=a*cp;weighted_cn+=a*cn
        terms.append({'term_id':ti,'edge':[i,j],'external_weight_numerator':a,'external_weight_denominator':SA,
            'original_term_bounds':[L,U],'uc_upper':uc,'original_L0':L0,
            'FS':list(f),'mass_constant':lc,'mass_first':l1,'mass_second':l2,
            'original_lb_table_value':lb,'active_mokI_guards':guards,
            'mvT':mv,'mslT':msl,'mwT':mass,'mcpT':cp,'mcnT':cn,
            'beta':str(beta),'sigma':str(sigma),'span_at_fixed_point':str(s),
            'affine_value':str(value),'direct_scaled_numerator':str(num),
            'weighted_value':str(F(a,SA)*value)})
    P,S,flow_cp,flow_cm,consumed=math.ydec(word,o,state)
    semantic={'FS':fs,'P':P,'S':S,'Cp':flow_cp,'Cm':flow_cm,'consumed_bits':consumed}
    payload={'bits':consumed,'value':str(word&((1<<consumed)-1))}
    assert sha256(canonical(semantic)).hexdigest()==cell['witness']['decoded_semantic_sha256']
    assert sha256(canonical(payload)).hexdigest()==cell['witness']['packed_payload_sha256']
    compact,readbits=math.calc(state,word);direct=math.direct_mcheck_margin(state,word)
    assert compact==direct==int(cell['original_margin']) and readbits==consumed==cell['end']-cell['position']-2
    assert compact-KAPPA*(TAU_N-CN)==int(cell['tau_margin'])
    value=constant+sum(x*c for x,c in zip(g,coeff))
    pressure=sum(F(b,SA)*g[offset+r] for r,b in enumerate(model['BS']))
    assert value==pressure+sum(F(t['weighted_value']) for t in terms)
    whole_num=V*R*sum(b*scaled_gaps[offset+r] for r,b in enumerate(model['BS']))
    whole_num+=Q*weighted_mv+10*(weighted_cp-weighted_cn)
    whole_num+=10*sum(t['external_weight_numerator']*(t['mslT']-2*D*t['mwT'])*
        (sum(scaled_gaps[offset+t['edge'][0]:offset+t['edge'][1]])-t['original_L0']) for t in terms)
    assert value==whole_num/K
    penalty=sum((hi[r]-lo[r])*max(0,P[r]-S[r]-gamma[r]) for r in range(8))
    base=V*R*sum(b*l for b,l in zip(model['BS'],lo[:8]))+Q*weighted_mv+10*(weighted_cp-weighted_cn)
    certified_num=base+10*(flow_cm-flow_cp-penalty)
    assert certified_num-KAPPA*CN==compact
    certified_floor=F(certified_num,K)
    assert certified_floor>=F(CN,SA) and value>=certified_floor
    flow_at_point=sum((P[r]-S[r])*(scaled_gaps[offset+r]-lo[r]) for r in range(8))
    assert flow_at_point>=flow_cm-flow_cp
    return {'offset':offset,'original_cell':cell,'terms':terms,'pressure_at_fixed_point':str(pressure),
        'global9_affine_constant':str(constant),'global9_gap_coefficients':list(map(str,coeff)),
        'affine_value_at_fixed_point':str(value),'whole_direct_scaled_numerator':str(whole_num),
        'whole_direct_denominator':K,'all_beta_vs_direct_scaled_values_equal':True,
        'original_compact_margin':str(compact),'original_printed_AST_margin':str(direct),
        'original_tau_debit_margin':cell['tau_margin'],
        'original_flow':{'P':P,'S':S,'Cp':flow_cp,'Cm':flow_cm,'consumed_bits':consumed,
            'gamma_scaled':gamma,'box_penalty':penalty,'certified_numerator':str(certified_num),
            'certified_denominator':K,'certified_affine_floor':str(certified_floor),
            'flow_linear_value_at_fixed_point':str(flow_at_point),'flow_lower_bound':flow_cm-flow_cp,
            'original_c9_floor_certificate_reproduced':True},
        'flows_not_added_to_definition_of_affine_value':True,
        'new_kernel_or_point_queries':0,'original_table_lookups_only':True}

def execute(gate_path,gate_sha):
    assert __debug__
    for name in ['started.json','evaluation.json','failure.json']:assert not (HERE/name).exists()
    started=time.monotonic();refs={};stage='input_guards'
    try:
        refs,point=input_guards(gate_path,gate_sha)
        command={'argv':sys.argv,'cwd':str(Path.cwd())}
        write_new(HERE/'started.json',{'pid':os.getpid(),'time_unix':time.time(),'arithmetic_attempt':1,
            'inputs_sha256':refs,'command':command,'command_sha256':sha256(canonical(command)).hexdigest(),
            'script_sha256':pin(Path(__file__))})
        print(json.dumps({'stage':'fixed_two_FS_arithmetic_live','pid':os.getpid(),'script_sha256':pin(Path(__file__))}),flush=True)
        stage='original_source_and_two_fixed_states';model=parser.load_model();math.configure(model)
        assert model['CN']==CN and model['SA']==SA
        traces={};wanted={point['prefix_cell']['root'],point['suffix_cell']['root']}
        with gzip.open(BASE/'baseline-events.jsonl.gz','rt',encoding='ascii') as f:
            for line in f:
                event=json.loads(line)
                if event['root'] in wanted:traces[event['root'],event['pos']]=event
        stage='exact_two_FS_affine_arithmetic'
        windows=[evaluate_window(point['prefix_cell'],0,point,model,traces),
                 evaluate_window(point['suffix_cell'],1,point,model,traces)]
        values=[F(w['affine_value_at_fixed_point']) for w in windows]
        c=F(C_N,SA);c9=F(CN,SA);gap=sum(values)-2*c
        clipped=[max(c9,x) for x in values];clipped_gap=sum(clipped)-2*c
        combined_constant=sum(F(w['global9_affine_constant']) for w in windows)
        combined_coeff=[sum(F(w['global9_gap_coefficients'][r]) for w in windows) for r in range(9)]
        p=point['X_integer_potential'];g=[F(p[r+1]-p[r],20*Q) for r in range(9)]
        assert all(x>=F(17,20) for x in g)
        assert g[0]<=g[7] and g[1]<=g[8]
        assert clipped==values
        assert combined_constant+sum(a*x for a,x in zip(combined_coeff,g))==sum(values)
        after={name:pin(ROOT/name) for name in refs};assert after==refs
        theorem=re.findall(r'(?ms)^theorem mtermTI\b.*?(?=^end |^theorem )',model['text'])
        assert len(theorem)==1
        result={'schema':'fixed-two-original-FS-joint-affine-diagnostic-v1','passed':True,'pid':os.getpid(),
            'seconds':time.monotonic()-started,'arithmetic_passes':1,'inputs_sha256_start':refs,'inputs_sha256_end':after,
            'source_sha256':parser.SOURCE_SHA,'source_mtermTI_text_sha256':sha256(theorem[0].encode()).hexdigest(),
            'scales':{'Q':Q,'R':R,'D':D,'V':V,'SA':SA,'KAPPA':KAPPA,'K':K},
            'fixed_C_point_sha256':POINT_SHA,'fixed_9_gap_values':list(map(str,g)),
            'target_c_numerator':C_N,'target_c_denominator':SA,'windows':windows,
            'combined_constant':str(combined_constant),'combined_9_gap_coefficients':list(map(str,combined_coeff)),
            'left_affine_value':str(values[0]),'right_affine_value':str(values[1]),
            'sum_affine_values':str(sum(values)),'target_twice_c':str(2*c),'sum_minus_twice_c':str(gap),
            'baseline_c9':str(c9),'clipped_left_affine_value':str(clipped[0]),'clipped_right_affine_value':str(clipped[1]),
            'sum_clipped_affine_values':str(sum(clipped)),'clipped_sum_minus_twice_c':str(clipped_gap),
            'clipping_is_redundant_on_original_cells_by_original_flow_proof':True,
            'all153_original_bounds_and_sep_rechecked':True,'both_original_ordered_conditions_rechecked':True,
            'fixed_joint_affine_model_obstructed_at_this_point':gap<0,
            'fixed_joint_affine_plus_baseline_model_obstructed_at_this_point':clipped_gap<0,
            'interpretation':('This same feasible point has A_left+A_right<2c, so these two fixed affine models alone cannot prove the target on their joint cell. Actual F was not evaluated.'
                if gap<0 else 'This one point does not obstruct the two affine models; no whole-cell joint floor follows.'),
            'actual_kernel_values_computed':0,'new_point_or_tangent_queries':0,'optimizer_calls':0,'Lean_runs':0,
            'new_joint_floor_proven':False,'new_unconditional_zero_proportion_proven':False,
            'complete_source_and_runtime_budget':'unknown','website_submission_ready':False,
            'analytic_soundness_scope':'Source mtermTI plus frozen signed-affine and flow extraction notes remain analytic premises; this finite rational diagnostic does not kernel-check new lemmas.'}
        write_new(HERE/'evaluation.json',result)
        print(json.dumps({k:result[k] for k in ['passed','pid','seconds','left_affine_value','right_affine_value','sum_minus_twice_c','fixed_joint_affine_model_obstructed_at_this_point']}),flush=True)
    except BaseException as exc:
        write_new(HERE/'failure.json',{'passed':False,'stage':stage,'pid':os.getpid(),'seconds':time.monotonic()-started,
            'error':repr(exc),'traceback':traceback.format_exc(),'inputs_sha256_start':refs,'automatic_retry_allowed':False})
        raise

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--execute-authorized-once',action='store_true')
    ap.add_argument('--gate');ap.add_argument('--gate-sha256');args=ap.parse_args()
    if not args.execute_authorized_once:
        print(json.dumps({'prepared_only':True,'arithmetic_runs':0,'requires_new_written_gate':True}));return
    assert args.gate and args.gate_sha256
    execute((ROOT/args.gate).resolve(),args.gate_sha256)

if __name__=='__main__':main()
