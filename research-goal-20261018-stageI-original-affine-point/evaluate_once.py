"""Prepared I Phase1: one original two-FS affine evaluation at frozen G2417.

Only the explicitly gated main enters extraction. Preparation may AST-parse
this source, but must not import/run parser, math, FS, points, or any matrix.
No optimizer, new kernel/anchor/point, basis family, or Lean is present.
"""
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
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
BASE=ROOT/'research-goal-20261018-record-baseline-replay'
B=ROOT/'research-goal-20261018-stageB-classification'
SAMPLE=ROOT/'research-goal-20261018-stageG-complete-classification/first-unresolved-sample.json'
Q=32768
R=1024
D=10**9
V=10**10
SA=10**20
KAPPA=Q*V*R
K=KAPPA*SA
CN=893616123055294719
C_N=893766123055294719
TAU_N=893916123055294719
MAX_SECONDS=60
MAX_BYTES=8000000
FIXED_CELLS={
 0:{'root':0,'path':'r00000000000000000110','position':1460,'end':1832,'payload_bits':370,
    'state_sha256':'d2733ed2a846126a82a603be65573be8e1b998e0117257e146ec57f16611259b',
    'semantic_sha256':'161848d29fac7b4839fb95164edb00cdda9088b9c587316013ef02f00581bb38',
    'payload_sha256':'1f12c9aa021c702d41834165b32b30caa5e23f5f842261e34713328fdf30a98a'},
 604:{'root':32,'path':'r00000000000000100001000','position':3126,'end':3470,'payload_bits':342,
      'state_sha256':'ab644cd51e0c1487aa0159061eb619bbda8ca030753834c53ae0d148e2766c00',
      'semantic_sha256':'99c3b1646b52bfea1d91ba1c059db09791181ee87f4ef48218af0719f2bb11ae',
      'payload_sha256':'d543c2001eb162d668b9ab1a3f30f22ae5b85f4c80fd0e994876fbb6bde7793a'}
}
PINS={
 'research-goal-20261018-record-source-audit/snapshot/Solution.lean':'f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf',
 'research-goal-20261018-record-baseline-replay/packing_parser_v3.py':'6ccb60ece1069521ace855a1f640365e3cad06a2e68033d9a40e657a3604219a',
 'research-goal-20261018-record-baseline-replay/record_math.py':'7150ff5a45ac3cdf2e360c1421361e20044b7d9f2a2928e2f3bee5ea5178e4d3',
 'research-goal-20261018-record-baseline-replay/baseline-events.jsonl.gz':'b924bf5ce93cde2e3044e8f9aa80cefb660a74c0c9d7161e2b09c017dc0fe5fc',
 'research-goal-20261018-record-baseline-replay/files.json':'03f3426e29ab7355ed76729dcaa3a3ba754154ae39ff5e9632bae2c57eff069f',
 'research-goal-20261018-record-baseline-independent/audit-files.json':'2d2c8003ed6be6f74d0f53e8624cd631eb1c934415b22b5377a4f2d40c64791c',
 'research-goal-20261018-stageB-classification/files.json':'3f9408f2cf1ceae12339456da034d9e8f175f828cf2d53a652339ee79eec89ad',
 'research-goal-20261018-stageB-classification/exception-cells.jsonl.gz':'180c27713c0473345fd0bb3c3373168a2d79f2e4bf518d5860e1c72cfa8a1ad0',
 'research-goal-20261018-stageB-independent/audit-files.json':'e6458883bc7588a2302afe435c3b79a08c9236bb895ec3010655024c767d7288',
 'research-goal-20261018-stageG-complete-classification/first-unresolved-sample.json':'a3349919ca3c07c71346a6a753396b8daa211c5e5492299cdaf300198fbf2689',
 'research-goal-20261018-stageG-independent/audit-files.json':'af09979447c2054f1daaa5a19e6abc59d04decee7752dfc53fe66c0643e30dc6',
 'research-goal-20261018-stageH-ordered-transport/files.json':'327562525e30d7b706777e71af003e51ca93a218ac7cfd9bfa0994abe56f8f8c',
 'research-goal-20261018-stageH-ordered-transport/remaining-indices.u32.bin':'c740852a5757983f462f3a78eb05d1aca5410ffb4077682e3afa48d6f7943559',
 'research-goal-20261018-stageH-independent/audit-files.json':'a0018aa4ce33e4cb6cea2019739e857fa3a1b58cc8b48f001e17d651e1dcbb3a',
 'research-goal-20261018-stageI-static-contract/files.json':'f526477985915b2e26d9db1c81ecbcd246564ed7241a9724bc325fb7e0dfca76',
 'research-goal-20261018-fixed-joint-affine/evaluate_once.py':'55311de8fb0851368c2bd5684f6ddc1441b35313122bd31a739bfb9c3195bd76',
 'research-goal-20261018-stageF-exact-lp/solve_fixed_once.py':'b3b1125cbae80c2bb5c5860b85bf51b8f8b14f8a9775c90fd024a15cab88340f',
 'research-goal-20261018-joint-affine-flow-proof/proof-files.json':'e3d61af4a46aed20eaee334af3f2c3c9c95e8ceb1c06027a7e22e0de349064eb'
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
def checked_path(name):
    p=(ROOT/name).resolve();assert p.is_relative_to(ROOT);return p
def pin_package(path,expected,refs):
    assert pin(path)==expected;refs[rel(path)]=expected
    obj=load(path)
    for field in ['files','package_files','read_only_dependencies','dependency_files','dependencies','read_only_existing_references']:
        for rec in obj.get(field,[]):
            p=checked_path(rec['path']);assert pin(p)==rec['sha256']
            if 'bytes' in rec:assert p.stat().st_size==rec['bytes']
            if rel(p) in refs:assert refs[rel(p)]==rec['sha256']
            refs[rel(p)]=rec['sha256']
class ResourceStop(Exception):pass
def limit(start):
    if time.monotonic()-start>MAX_SECONDS:raise ResourceStop('elapsed60seconds')
    if sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())>MAX_BYTES:raise ResourceStop('closed_output8MB')
def import_frozen(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module

def inputs(gate_path,gate_sha):
    assert gate_path.is_relative_to(ROOT) and pin(gate_path)==gate_sha
    gate=load(gate_path)
    assert gate['original_affine_point_evaluations_authorized']==1
    assert gate['sample_G_index']==2417 and gate['cell_ids']==[0,604] and gate['chart']=='id/rev'
    assert gate['sample_sha256']==PINS[rel(SAMPLE)] and gate['X_scale']==20*Q
    assert int(gate['candidate_c_numerator'])==C_N and int(gate['denominator'])==SA
    assert gate['resource_limits']=={'elapsed_seconds':MAX_SECONDS,'closed_output_bytes':MAX_BYTES}
    assert gate['phase2_authorized'] is False and gate['same_model_retry_allowed'] is False
    assert gate['new_points_FS_or_kernel_values_authorized']==0 and gate['matrix_LP_or_Lean_calls_authorized']==0
    refs={rel(gate_path):gate_sha}
    for name,expected in PINS.items():
        p=checked_path(name);assert pin(p)==expected;refs[name]=expected
    pin_package(HERE/'prepared-files.json',gate['prepared_manifest_sha256'],refs)
    point=load(SAMPLE)
    assert point['index']==2417 and point['prefix_exception_id']==0 and point['suffix_exception_id']==604
    assert point['chart']=='id/rev' and point['potential_present'] is True and point['X_scale']==20*Q
    assert point['prefix_ordered']['ordered_condition_holds'] is True
    assert point['suffix_ordered']['ordered_condition_holds'] is True
    assert point['prefix_state_sha256']==FIXED_CELLS[0]['state_sha256']
    assert point['suffix_state_sha256']==FIXED_CELLS[604]['state_sha256']
    x=point['X_integer_potential'];assert len(x)==10 and x[0]==0 and all(type(v) is int for v in x)
    cells={}
    with gzip.open(B/'exception-cells.jsonl.gz','rt',encoding='ascii') as f:
        for line in f:
            cell=json.loads(line);cid=cell['exception_id']
            if cid in FIXED_CELLS:
                assert cell['kind']=='exception' and cell['coordinate_scale']==Q and cell['separation']=='17/20'
                assert cell['state']['M']==0
                expected=FIXED_CELLS[cid]
                for key in ['root','path','position','end','state_sha256']:assert cell[key]==expected[key]
                witness=cell['witness']
                assert witness['WD']==expected['root'] and witness['original_leaf_position']==expected['position']
                assert witness['payload_bit_position']==expected['position']+2
                assert witness['consumed_payload_bits']==expected['payload_bits']
                assert witness['original_rdw_block']==0 and witness['original_rdw_shift']==expected['position']
                assert witness['decoded_semantic_sha256']==expected['semantic_sha256']
                assert witness['packed_payload_sha256']==expected['payload_sha256']
                cells[cid]=cell
    assert set(cells)=={0,604}
    return refs,point,cells

def locate_original_payload(cell,model,math,traces):
    """Point-free adaptation of frozen D86-107: original path and A cursors."""
    root=cell['root'];pos=1;state=math.root(model['roots'][root]['indices'])
    path=cell['path'];assert path.startswith('r') and set(path[1:])<=set('01')
    def bits(position):return (model['WL'][root].get(position//32768,0)>>(position%32768))&((1<<480)-1)
    for turn in path[1:]:
        event=traces[root,pos];word=bits(pos);assert event['kind']=='branch' and word&1
        axis=(word>>1)&63;mode=(word>>7)&1
        assert axis==event['axis'] and mode==event['mode']
        i,j=math.ALL[axis]
        cut=math.bcut(state[0][axis],state[1][axis]) if mode else (state[0][axis]+state[1][axis])>>1
        assert cut==event['cut'];state=math.split(state,i,j,cut,turn=='0')
        pos=event['left' if turn=='0' else 'right']
    assert pos==cell['position'] and traces[root,pos]['kind']=='numeric' and traces[root,pos]['end']==cell['end']
    flat=[v for pair in zip(*state) for v in pair]+[0]
    assert sha256(canonical(flat)).hexdigest()==cell['state_sha256']
    s=cell['state'];assert state==(s['L']+s['A'],s['U']+s['B'])
    word=bits(pos);assert not word&3 and not state[1][7]<state[0][0]
    return state,word>>2

def extract_original_affine(cell,model,math,traces):
    """No physical test point, offset, chart or joint tightening is an input."""
    state,word=locate_original_payload(cell,model,math,traces);lo,hi=state
    cid=cell['exception_id'];fs=[];terms=[];o=0
    jcoef=[D*R*b for b in model['BS']];cstar=0;constant=F(0)
    coefficients=[F(b,SA) for b in model['BS']]
    weighted_mv=weighted_cp=weighted_cn=0
    for ti,(i,j,a,_slot) in enumerate(model['TS']):
        L,U=math.term_bounds(state,i,j);L0=sum(lo[i:j]);uc=max(L+1,U)
        assert L0<=L<=U
        f,o=math.dec(word,o,L,U);kind,lam,p,r=f;fs.append(f)
        l1,l2=math.weights(kind,lam);lc=R-l1-l2
        assert min(l1,l2,lc)>=0 and lc+l1+l2==R
        pt=[model['PTraw'].get(v,0)&((1<<96)-1) for v in [p,r]];guards=[]
        for amount,anchor in zip([l1,l2],[p,r]):
            if not amount:continue
            assert anchor in model['PTraw'];raw=model['PTraw'][anchor]
            vl=max(0,anchor-((raw>>96)&((1<<20)-1)));vu=anchor+(raw>>116)
            assert 1<=vu and vl<=L<=anchor<=U<=vu
            guards.append({'mass':amount,'original_anchor':anchor,'valid_lower':vl,'valid_upper':vu,'guard_passed':True})
        lb=math.lb(L,uc)
        mv=lc*lb+l1*(pt[0]&math.MASK32)+l2*(pt[1]&math.MASK32)
        msl=l1*((pt[0]>>32)&math.MASK32)+l2*((pt[1]>>32)&math.MASK32);mass=l1+l2
        cp=sum(amount*max(0,(raw>>64)-2*D)*max(0,anchor-L0) for amount,raw,anchor in zip([l1,l2],pt,[p,r]))
        cn=sum(amount*max(0,2*D-(raw>>64))*max(0,anchor-L0) for amount,raw,anchor in zip([l1,l2],pt,[p,r]))
        delta=msl-2*D*mass;sigma=F(delta,D*R)
        beta=F(mv,V*R)+F(cp-cn,Q*D*R)-sigma*F(L0,Q)
        cstar+=a*(Q*mv+10*(cp-cn-delta*L0));constant+=F(a,SA)*beta
        for rr in range(i,j):jcoef[rr]+=a*delta;coefficients[rr]+=F(a,SA)*sigma
        weighted_mv+=a*mv;weighted_cp+=a*cp;weighted_cn+=a*cn
        terms.append({'term_id':ti,'edge':[i,j],'external_weight_numerator':a,'external_weight_denominator':SA,
            'original_term_bounds':[L,U],'uc_upper':uc,'original_L0':L0,'FS':list(f),
            'mass_constant':lc,'mass_first':l1,'mass_second':l2,'original_lb_table_value':lb,
            'active_mokI_guards':guards,'mvT':mv,'mslT':msl,'mwT':mass,'mcpT':cp,'mcnT':cn,
            'signed_delta':delta,'beta':str(beta),'sigma':str(sigma)})
    P,S,Cp,Cm,consumed=math.ydec(word,o,state)
    semantic={'FS':fs,'P':P,'S':S,'Cp':Cp,'Cm':Cm,'consumed_bits':consumed}
    payload={'bits':consumed,'value':str(word&((1<<consumed)-1))}
    assert sha256(canonical(semantic)).hexdigest()==cell['witness']['decoded_semantic_sha256']
    assert sha256(canonical(payload)).hexdigest()==cell['witness']['packed_payload_sha256']
    compact,readbits=math.calc(state,word);printed=math.direct_mcheck_margin(state,word)
    assert compact==printed==int(cell['original_margin']) and compact>=0
    assert readbits==consumed==cell['end']-cell['position']-2==FIXED_CELLS[cid]['payload_bits']
    assert compact-KAPPA*(TAU_N-CN)==int(cell['tau_margin'])
    assert K*constant==cstar and coefficients==[F(v,D*R*SA) for v in jcoef]
    penalty=sum((hi[rr]-lo[rr])*max(0,P[rr]-S[rr]-jcoef[rr]) for rr in range(8))
    certified_num=V*R*sum(b*lo[rr] for rr,b in enumerate(model['BS']))
    certified_num+=Q*weighted_mv+10*(weighted_cp-weighted_cn+Cm-Cp-penalty)
    assert certified_num-KAPPA*CN==compact
    result={'cell_id':cid,'original_root':cell['root'],'original_path':cell['path'],
        'position':cell['position'],'end':cell['end'],'state_sha256':cell['state_sha256'],'witness':cell['witness'],
        'canonical_Cstar':str(cstar),'canonical_J':list(map(str,jcoef)),
        'canonical_affine_constant':str(constant),'canonical_gap_coefficients':list(map(str,coefficients)),
        'terms':terms,'original_compact_margin':str(compact),'original_printed_AST_margin':str(printed),
        'consumed_payload_bits':consumed,'original_flow':{'P':P,'S':S,'Cp':Cp,'Cm':Cm,
            'box_penalty':str(penalty),'certified_numerator':str(certified_num),'certified_denominator':str(K)},
        'point_free_extraction':True,'original_guard_state_and_cursor_unchanged':True}
    return result,state

def embed_and_evaluate(extracted,state,offset,reverse,x,model,math):
    indices=[offset+(7-r if reverse else r) for r in range(8)]
    gaps=[F(x[k+1]-x[k],20*Q) for k in indices]
    lo,hi=state
    for k,(i,j) in enumerate(math.ALL):
        span=sum(gaps[i:j]);assert F(lo[k],Q)<=span<=F(hi[k],Q)
    physical=[0]*9;jcoef=list(map(int,extracted['canonical_J']));cstar=int(extracted['canonical_Cstar'])
    for rr,k in enumerate(indices):physical[k]+=jcoef[rr]
    terms=[];term_value=F(0)
    for term in extracted['terms']:
        i,j=term['edge'];span=sum(gaps[i:j]);beta=F(term['beta']);sigma=F(term['sigma'])
        value=beta+sigma*span
        numerator=Q*term['mvT']+10*(term['mcpT']-term['mcnT'])+10*term['signed_delta']*(Q*span-term['original_L0'])
        assert value==numerator/KAPPA
        a=term['external_weight_numerator'];term_value+=F(a,SA)*value
        terms.append({**term,'span_at_fixed_point':str(span),'affine_value':str(value),
                      'direct_scaled_numerator':str(numerator),'weighted_value':str(F(a,SA)*value)})
    pressure=sum(F(b,SA)*g for b,g in zip(model['BS'],gaps))
    value=F(extracted['canonical_affine_constant'])+sum(F(a)*g for a,g in zip(extracted['canonical_gap_coefficients'],gaps))
    assert value==pressure+term_value
    twice_scaled=2*cstar+sum(jcoef[rr]*(x[k+1]-x[k]) for rr,k in enumerate(indices))
    assert 2*K*value==twice_scaled
    assert K*value==cstar+10*Q*sum(j*g for j,g in zip(jcoef,gaps))
    flow=extracted['original_flow']
    flow_linear=sum((flow['P'][rr]-flow['S'][rr])*(Q*gaps[rr]-lo[rr]) for rr in range(8))
    assert flow_linear>=flow['Cm']-flow['Cp']
    certified=F(int(flow['certified_numerator']),K);assert value>=certified>=F(CN,SA)
    return {**extracted,'offset':offset,'reverse':reverse,'physical_gap_indices':indices,
        'physical_J9':list(map(str,physical)),'canonical_gaps_at_point':list(map(str,gaps)),
        'affine_value':str(value),'twice_K_value':str(twice_scaled),'pressure_at_fixed_point':str(pressure),
        'terms':terms,'original_flow':{**flow,'flow_linear_value_at_point':str(flow_linear),
            'certified_affine_floor':str(certified)},'point_and_integer_formulas_match':True}

def original155(cells,pairs,x):
    rows=[]
    def add(a,rhs,kind):
        assert len(a)==10 and sum(a)==0
        lhs=sum(v*z for v,z in zip(a,x));assert lhs<=rhs
        rows.append({'row_id':len(rows),'coefficients':a,'rhs':rhs,'lhs':lhs,'slack':rhs-lhs,'kind':kind})
    for cid,off,reverse in [(0,0,False),(604,1,True)]:
        s=cells[cid]['state'];lo=s['L']+s['A'];hi=s['U']+s['B']
        for k,(i,j) in enumerate(pairs):
            if reverse:i,j=8-j,8-i
            a=[0]*10;a[off+i]-=1;a[off+j]+=1
            add(a,20*hi[k],'original_span_upper');add([-v for v in a],-20*lo[k],'original_span_lower')
    for rr in range(9):
        a=[0]*10;a[rr]+=1;a[rr+1]-=1;add(a,-17*Q,'original_separation')
    for off,reverse in [(0,False),(1,True)]:
        a=[0]*10;sign=-1 if reverse else 1
        for vertex,v in [(off,-1),(off+1,1),(off+7,1),(off+8,-1)]:a[vertex]+=sign*v
        add(a,0,'original_Ordered')
    assert len(rows)==155
    return {'all155_rows_verified':True,'both_Ordered_verified':True,'rows':rows}

def execute(gate_path,gate_sha):
    assert __debug__
    for name in ['started.json','result.json','failure.json','inconclusive.json']:
        assert not (HERE/name).exists(),('existing_attempt',name)
    start=time.monotonic();stage='input_pins';refs={}
    try:
        refs,point,cells=inputs(gate_path,gate_sha);limit(start)
        write_new(HERE/'started.json',{'schema':'I-one-fixed-original-affine-point-start-v1','pid':os.getpid(),
            'time_unix':time.time(),'arithmetic_evaluations':1,'inputs_sha256':refs,
            'sample_G_index':2417,'cell_ids':[0,604],'chart':'id/rev','sample_sha256':pin(SAMPLE)})
        stage='frozen_original_source_model'
        parser=import_frozen(BASE/'packing_parser_v3.py','fixed_s1R_parser_for_I')
        math=import_frozen(BASE/'record_math.py','fixed_s1R_integer_math_for_I')
        model=parser.load_model();math.configure(model)
        assert model['CN']==CN and model['SA']==SA and math.SLOPE==KAPPA
        traces={}
        with gzip.open(BASE/'baseline-events.jsonl.gz','rt',encoding='ascii') as f:
            for line in f:
                event=json.loads(line)
                if event['root'] in [0,32]:traces[event['root'],event['pos']]=event
        x=point['X_integer_potential'];limit(start);stage='fixed_original155domain'
        domain=original155(cells,math.ALL,x)
        stage='point_free_original_FS_extraction'
        left,left_state=extract_original_affine(cells[0],model,math,traces);limit(start)
        right,right_state=extract_original_affine(cells[604],model,math,traces);limit(start)
        stage='unchanged_point_id_reverse_embedding'
        windows=[embed_and_evaluate(left,left_state,0,False,x,model,math),
                 embed_and_evaluate(right,right_state,1,True,x,model,math)]
        joint_j=[sum(int(w['physical_J9'][rr]) for w in windows) for rr in range(9)]
        constant=2*sum(int(w['canonical_Cstar']) for w in windows)
        b=[-joint_j[0]]+[joint_j[rr-1]-joint_j[rr] for rr in range(1,9)]+[joint_j[-1]]
        assert sum(b)==0;target=4*KAPPA*C_N
        value=sum(F(w['affine_value']) for w in windows);scaled=constant+sum(a*v for a,v in zip(b,x))
        assert scaled==sum(int(w['twice_K_value']) for w in windows)==2*K*value
        delta=scaled-target;gap=value-2*F(C_N,SA);assert gap==F(delta,2*K)
        limit(start);stage='input_end_hashes'
        after={name:pin(ROOT/name) for name in refs};assert after==refs
        result={'schema':'I-one-fixed-original-affine-point-result-v1','passed':True,'pid':os.getpid(),
            'seconds':time.monotonic()-start,'arithmetic_evaluations':1,'sample_G_index':2417,
            'cell_ids':[0,604],'chart':'id/rev','sample_sha256':pin(SAMPLE),'inputs_sha256_start':refs,
            'inputs_sha256_end':after,'windows':windows,'domain_check':domain,
            'joint':{'C':str(constant),'b':list(map(str,b)),'Jphysical9':list(map(str,joint_j)),
                'target':str(target),'point_X':x,'X_scale':20*Q,'sum_affine_values':str(value),
                'target_twice_c':str(2*F(C_N,SA)),'delta_integer':str(delta),'sum_minus_twice_c':str(gap),
                'Delta_matches_fraction':True,'fixed_two_FS_model_obstructed_at_sample':delta<0},
            'stop_same_fixed_affine_family':delta<0,'point_unchanged':True,'new_points_or_kernel_values':0,
            'original_cells_FS_extracted':2,'new_FS_selected':0,'matrix_basis_LP_or_Lean_runs':0,
            'phase2_authorized':False,'same_model_retry_allowed':False,'independent_replay_pending':True,
            'interpretation':('This fixed faithful two-original-FS affine model cannot reach2c on its actual joint domain. No actualF evaluated.'
                if delta<0 else 'This one feasible point does not refute the fixed two-affine model; no uniform joint lower follows.'),
            'new_global_joint_floor_proven':False,'new_unconditional_zero_proportion_proven':False,
            'website_submission_ready':False,'whole_source_and_policy_runtime_budget':'unknown'}
        write_new(HERE/'result.json',result);limit(start)
        print(json.dumps({'passed':True,'seconds':result['seconds'],'delta_integer':str(delta),
            'sum_minus_twice_c':str(gap),'stop_same_fixed_affine_family':delta<0}),flush=True)
    except BaseException as exc:
        name='inconclusive.json' if isinstance(exc,ResourceStop) else 'failure.json'
        write_new(HERE/name,{'passed':False,'error':repr(exc),'traceback':traceback.format_exc(),
            'pid':os.getpid(),'stage':stage,'seconds':time.monotonic()-start,'inputs_sha256_start':refs,
            'automatic_retry_allowed':False,'no_parameter_or_basis_retry':True})
        raise

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--evaluate-authorized-fixed-I-point',action='store_true')
    ap.add_argument('--gate');ap.add_argument('--gate-sha256');a=ap.parse_args()
    if not a.evaluate_authorized_fixed_I_point:
        print(json.dumps({'prepared_only':True,'FS_extractions':0,'point_evaluations':0,'new_immutable_gate_required':True}));return
    assert a.gate and a.gate_sha256;execute(checked_path(a.gate),a.gate_sha256)

if __name__=='__main__':main()
