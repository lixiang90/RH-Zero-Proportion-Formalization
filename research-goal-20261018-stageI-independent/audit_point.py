"""Independent fixed-I audit. No new producer import or mathematical work by default.

Only the frozen Stage A parser/integer model are reused. Original FS decoding,
guards, signed Fraction lines, reflections and the fixed-point identity are
reconstructed here. A new root audit gate is required before execution.
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
PROD=ROOT/'research-goal-20261018-stageI-original-affine-point'
B=ROOT/'research-goal-20261018-stageB-classification'
SAMPLE=ROOT/'research-goal-20261018-stageG-complete-classification/first-unresolved-sample.json'
Q,R,D,V,SA=32768,1024,10**9,10**10,10**20
KAPPA=Q*V*R
K=KAPPA*SA
CN,TAU,NC=893616123055294719,893916123055294719,893766123055294719
PINS={
 'research-goal-20261018-record-source-audit/snapshot/Solution.lean':'f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf',
 'research-goal-20261018-record-baseline-replay/files.json':'03f3426e29ab7355ed76729dcaa3a3ba754154ae39ff5e9632bae2c57eff069f',
 'research-goal-20261018-record-baseline-replay/packing_parser_v3.py':'6ccb60ece1069521ace855a1f640365e3cad06a2e68033d9a40e657a3604219a',
 'research-goal-20261018-record-baseline-replay/record_math.py':'7150ff5a45ac3cdf2e360c1421361e20044b7d9f2a2928e2f3bee5ea5178e4d3',
 'research-goal-20261018-record-baseline-independent/audit-files.json':'2d2c8003ed6be6f74d0f53e8624cd631eb1c934415b22b5377a4f2d40c64791c',
 'research-goal-20261018-stageB-classification/files.json':'3f9408f2cf1ceae12339456da034d9e8f175f828cf2d53a652339ee79eec89ad',
 'research-goal-20261018-stageG-complete-classification/first-unresolved-sample.json':'a3349919ca3c07c71346a6a753396b8daa211c5e5492299cdaf300198fbf2689',
 'research-goal-20261018-stageI-static-contract/files.json':'f526477985915b2e26d9db1c81ecbcd246564ed7241a9724bc325fb7e0dfca76',
 'research-goal-20261018-stageI-original-affine-point/files.json':'afaece4fee2e74d064258f689faff64d9732c53f8a412d0c71f6140d7653f482'}

def pin(p):
    h=sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def canon(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode('ascii')
def local(name):
    p=(ROOT/name).resolve();assert p.is_relative_to(ROOT);return p
def write_new(path,obj):
    with path.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(obj,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def subset(expected,actual,path=''):
    if isinstance(expected,dict):
        for key,value in expected.items():assert key in actual,(path,key);subset(value,actual[key],path+'/'+key)
    else:assert expected==actual,(path,expected,actual)
def import_old(path,name):
    spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module);return module
def state_hash(state):return sha256(canon([v for pair in zip(*state) for v in pair]+[0])).hexdigest()

def locate(cell,model,math,events):
    root=cell['root'];position=1;state=math.root(model['roots'][root]['indices'])
    def word_at(p):return (model['WL'][root].get(p//32768,0)>>(p%32768))&((1<<480)-1)
    path=cell['path'];assert path.startswith('r') and set(path[1:])<=set('01')
    for choice in path[1:]:
        event=events[root,position];assert event['state_sha256']==state_hash(state)
        word=word_at(position);assert event['kind']=='branch' and word&1
        axis=(word>>1)&63;mode=(word>>7)&1;assert (axis,mode)==(event['axis'],event['mode'])
        lower,upper=state[0][axis],state[1][axis]
        cut=math.bcut(lower,upper) if mode else (lower+upper)//2
        assert cut==event['cut'];i,j=math.ALL[axis]
        state=math.split(state,i,j,cut,choice=='0');position=event['left' if choice=='0' else 'right']
    leaf=events[root,position]
    assert position==cell['position'] and leaf['kind']=='numeric' and leaf['end']==cell['end']
    assert leaf['state_sha256']==cell['state_sha256']==state_hash(state)
    s=cell['state'];assert state==(s['L']+s['A'],s['U']+s['B']) and s['M']==0
    word=word_at(position);assert word&3==0 and not state[1][7]<state[0][0]
    return state,word>>2

def audit_window(cell,offset,reverse,x,model,math,events):
    state,word=locate(cell,model,math,events);lo,hi=state
    # Canonical original coordinates first; only then permute physical gaps.
    mapping=[offset+(7-r if reverse else r) for r in range(8)]
    gaps=[F(x[k+1]-x[k],20*Q) for k in mapping]
    for k,(i,j) in enumerate(math.ALL):assert F(lo[k],Q)<=sum(gaps[i:j])<=F(hi[k],Q)
    constant=F(0);coefficient=[F(b,SA) for b in model['BS']]
    value=sum(F(b,SA)*g for b,g in zip(model['BS'],gaps))
    fs=[];term_rows=[];bit=0;mvsum=cpsum=cnsum=0
    cstar=0;jcoef=[D*R*b for b in model['BS']]
    for ti,(i,j,a,_slot) in enumerate(model['TS']):
        L=max(lo[math.LOOK[i,j]],sum(lo[i:j]));U=min(hi[math.LOOK[i,j]],sum(hi[i:j]));L0=sum(lo[i:j])
        assert L0<=L<=U
        decoded,bit=math.dec(word,bit,L,U);kind,lam,p,r=decoded;fs.append(decoded)
        masses=math.weights(kind,lam);lc=R-sum(masses);assert min(*masses,lc)>=0
        raw96=[model['PTraw'].get(v,0)&((1<<96)-1) for v in (p,r)];guards=[]
        for amount,anchor in zip(masses,(p,r)):
            if not amount:continue
            assert anchor in model['PTraw'];raw=model['PTraw'][anchor]
            vl=max(0,anchor-((raw>>96)&((1<<20)-1)));vu=anchor+(raw>>116)
            assert vu>0 and vl<=L<=anchor<=U<=vu
            guards.append({'mass':amount,'original_anchor':anchor,'valid_lower':vl,'valid_upper':vu,'guard_passed':True})
        lb=math.lb(L,max(L+1,U))
        mv=lc*lb+sum(amount*(raw&((1<<32)-1)) for amount,raw in zip(masses,raw96))
        msl=sum(amount*((raw>>32)&((1<<32)-1)) for amount,raw in zip(masses,raw96));mass=sum(masses)
        cp=sum(amount*max(0,(raw>>64)-2*D)*max(0,anchor-L0) for amount,raw,anchor in zip(masses,raw96,(p,r)))
        cn=sum(amount*max(0,2*D-(raw>>64))*max(0,anchor-L0) for amount,raw,anchor in zip(masses,raw96,(p,r)))
        delta=msl-2*D*mass;sigma=F(delta,D*R)
        beta=F(mv,V*R)+F(cp-cn,Q*D*R)-sigma*F(L0,Q)
        span=sum(gaps[i:j]);term_value=beta+sigma*span
        num=Q*mv+10*(cp-cn)+10*delta*(Q*span-L0);assert term_value==num/KAPPA
        constant+=F(a,SA)*beta;value+=F(a,SA)*term_value
        for rr in range(i,j):coefficient[rr]+=F(a,SA)*sigma;jcoef[rr]+=a*delta
        cstar+=a*(Q*mv+10*(cp-cn-delta*L0));mvsum+=a*mv;cpsum+=a*cp;cnsum+=a*cn
        term_rows.append({'term_id':ti,'edge':[i,j],'external_weight_numerator':a,'external_weight_denominator':SA,
            'FS':list(decoded),'original_term_bounds':[L,U],'uc_upper':max(L+1,U),'original_L0':L0,
            'mass_constant':lc,'mass_first':masses[0],'mass_second':masses[1],
            'original_lb_table_value':lb,'active_mokI_guards':guards,'mvT':mv,'mslT':msl,'mwT':mass,
            'mcpT':cp,'mcnT':cn,'signed_delta':delta,'beta':str(beta),'sigma':str(sigma),
            'span_at_fixed_point':str(span),'affine_value':str(term_value),
            'direct_scaled_numerator':str(num),'weighted_value':str(F(a,SA)*term_value)})
    # The original ydec payload is checked, but never added to A a second time.
    scan=bit
    for _ in range(42):
        if not (word>>scan)&1:break
        assert (word>>(scan+1))&31<28;scan+=21
    P,S,Cp,Cm,consumed=math.ydec(word,bit,state)
    semantic={'FS':fs,'P':P,'S':S,'Cp':Cp,'Cm':Cm,'consumed_bits':consumed}
    payload={'bits':consumed,'value':str(word&((1<<consumed)-1))}
    assert sha256(canon(semantic)).hexdigest()==cell['witness']['decoded_semantic_sha256']
    assert sha256(canon(payload)).hexdigest()==cell['witness']['packed_payload_sha256']
    compact,used=math.calc(state,word);printed=math.direct_mcheck_margin(state,word)
    assert compact==printed==int(cell['original_margin'])>=0
    assert used==consumed==cell['end']-cell['position']-2==cell['witness']['consumed_payload_bits']
    assert compact-KAPPA*(TAU-CN)==int(cell['tau_margin'])
    assert constant*K==cstar and coefficient==[F(j,D*R*SA) for j in jcoef]
    assert value==constant+sum(c*g for c,g in zip(coefficient,gaps))
    physical=[0]*9
    for r,k in enumerate(mapping):physical[k]+=jcoef[r]
    twice=2*cstar+sum(jcoef[r]*(x[k+1]-x[k]) for r,k in enumerate(mapping));assert twice==2*K*value
    penalty=sum((hi[r]-lo[r])*max(0,P[r]-S[r]-jcoef[r]) for r in range(8))
    floor_num=V*R*sum(b*lo[r] for r,b in enumerate(model['BS']))+Q*mvsum+10*(cpsum-cnsum+Cm-Cp-penalty)
    assert floor_num-KAPPA*CN==compact and value>=F(floor_num,K)>=F(CN,SA)
    flow_value=sum((P[r]-S[r])*(Q*gaps[r]-lo[r]) for r in range(8));assert flow_value>=Cm-Cp
    return {'cell_id':cell['exception_id'],'original_root':cell['root'],'original_path':cell['path'],
        'position':cell['position'],'end':cell['end'],'state_sha256':cell['state_sha256'],'witness':cell['witness'],
        'offset':offset,'reverse':reverse,'canonical_Cstar':str(cstar),'canonical_J':list(map(str,jcoef)),
        'canonical_affine_constant':str(constant),'canonical_gap_coefficients':list(map(str,coefficient)),
        'physical_J9':list(map(str,physical)),'physical_gap_indices':mapping,'canonical_gaps_at_point':list(map(str,gaps)),
        'affine_value':str(value),'twice_K_value':str(twice),'terms':term_rows,
        'original_compact_margin':str(compact),'original_printed_AST_margin':str(printed),
        'consumed_payload_bits':consumed,'original_flow':{'P':P,'S':S,'Cp':Cp,'Cm':Cm,
            'box_penalty':str(penalty),'certified_numerator':str(floor_num),'certified_denominator':str(K),
            'flow_linear_value_at_point':str(flow_value),'certified_affine_floor':str(F(floor_num,K))}}

def domain(cells,pairs,x):
    rows=[]
    def add(a,rhs,kind):
        lhs=sum(c*v for c,v in zip(a,x));assert sum(a)==0 and lhs<=rhs
        rows.append({'row_id':len(rows),'coefficients':a,'rhs':rhs,'lhs':lhs,'slack':rhs-lhs,'kind':kind})
    for cid,off,rev in ((0,0,False),(604,1,True)):
        st=cells[cid]['state'];lo=st['L']+st['A'];hi=st['U']+st['B']
        for k,(i,j) in enumerate(pairs):
            if rev:i,j=8-j,8-i
            a=[0]*10;a[off+i]-=1;a[off+j]+=1
            add(a,20*hi[k],'original_span_upper');add([-c for c in a],-20*lo[k],'original_span_lower')
    for r in range(9):
        a=[0]*10;a[r]+=1;a[r+1]-=1;add(a,-17*Q,'original_separation')
    for off,sign in ((0,1),(1,-1)):
        a=[0]*10
        for k,c in ((off,-1),(off+1,1),(off+7,1),(off+8,-1)):a[k]+=sign*c
        add(a,0,'original_Ordered')
    assert len(rows)==155;return rows

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--verify-authorized-fixed-I',action='store_true')
    ap.add_argument('--gate');ap.add_argument('--gate-sha256');a=ap.parse_args()
    if not a.verify_authorized_fixed_I:
        print(json.dumps({'prepared_only':True,'FS_extractions':0,'point_evaluations':0}));return
    assert a.gate and a.gate_sha256;assert not (HERE/'independent-review.json').exists() and not (HERE/'failure.json').exists()
    start=time.monotonic();refs={}
    def bind(p,digest=None):
        p=p.resolve();assert p.is_relative_to(ROOT);h=pin(p)
        if digest is not None:assert h==digest
        name=p.relative_to(ROOT).as_posix()
        if name in refs:assert refs[name]==h
        refs[name]=h;return p
    def package(p,h):
        bind(p,h);obj=load(p)
        for key in ('files','package_files','read_only_dependencies','dependencies','dependency_files','read_only_existing_references'):
            for row in obj.get(key,[]):bind(local(row['path']),row['sha256'])
    try:
        gate=load(bind(local(a.gate),a.gate_sha256));assert gate['independent_affine_audit_calls_authorized']==1
        assert gate['independent_audit_script_path']==Path(__file__).relative_to(ROOT).as_posix()
        bind(Path(__file__),gate['independent_audit_script_sha256'])
        for name,h in PINS.items():
            p=local(name)
            if p.name.endswith('.json') and p.name in ('files.json','audit-files.json'):package(p,h)
            else:bind(p,h)
        point=load(SAMPLE);assert point['index']==2417 and point['chart']=='id/rev'
        assert (point['prefix_exception_id'],point['suffix_exception_id'])==(0,604) and point['X_scale']==20*Q
        x=point['X_integer_potential'];assert len(x)==10 and x[0]==0 and all(type(v) is int for v in x)
        cells={}
        with gzip.open(B/'exception-cells.jsonl.gz','rt',encoding='ascii') as f:
            for line in f:
                cell=json.loads(line)
                if cell['exception_id'] in (0,604):cells[cell['exception_id']]=cell
        assert set(cells)=={0,604}
        parser=import_old(BASE/'packing_parser_v3.py','old_A_parser_for_independent_I')
        math=import_old(BASE/'record_math.py','old_A_math_for_independent_I')
        model=parser.load_model();math.configure(model);assert model['CN']==CN and model['SA']==SA
        events={};roots={c['root'] for c in cells.values()}
        with gzip.open(BASE/'baseline-events.jsonl.gz','rt',encoding='ascii') as f:
            for line in f:
                event=json.loads(line)
                if event['root'] in roots:events[event['root'],event['pos']]=event
        windows=[audit_window(cells[0],0,False,x,model,math,events),audit_window(cells[604],1,True,x,model,math,events)]
        rows=domain(cells,math.ALL,x);producer=load(bind(PROD/'result.json'))
        assert producer['passed'] is True and producer['arithmetic_evaluations']==1 and producer['sample_G_index']==2417
        assert producer['sample_sha256']==pin(SAMPLE) and producer['cell_ids']==[0,604] and producer['chart']=='id/rev'
        assert len(producer['windows'])==2
        for own,other in zip(windows,producer['windows']):subset(own,other)
        subset({'all155_rows_verified':True,'both_Ordered_verified':True,'rows':rows},producer['domain_check'])
        jp=[sum(int(w['physical_J9'][r]) for w in windows) for r in range(9)]
        c=2*sum(int(w['canonical_Cstar']) for w in windows)
        b=[-jp[0]]+[jp[r-1]-jp[r] for r in range(1,9)]+[jp[-1]];assert sum(b)==0
        target=4*KAPPA*NC;total=sum(F(w['affine_value']) for w in windows)
        integer=c+sum(v*z for v,z in zip(b,x));assert integer==2*K*total==sum(int(w['twice_K_value']) for w in windows)
        delta=integer-target;gap=total-2*F(NC,SA);assert gap==F(delta,2*K)
        expected={'C':str(c),'b':list(map(str,b)),'Jphysical9':list(map(str,jp)),
            'target':str(target),'point_X':x,'X_scale':20*Q,'sum_affine_values':str(total),
            'target_twice_c':str(2*F(NC,SA)),'delta_integer':str(delta),'sum_minus_twice_c':str(gap),
            'fixed_two_FS_model_obstructed_at_sample':delta<0}
        subset(expected,producer['joint']);assert producer['stop_same_fixed_affine_family'] is (delta<0)
        after={name:pin(local(name)) for name in refs};assert after==refs
        record={'schema':'I-independent-original-two-FS-Fraction-point-review-v1','passed':True,'pid':os.getpid(),
            'seconds':time.monotonic()-start,'independent_audit_calls':1,'source_sha256':PINS['research-goal-20261018-record-source-audit/snapshot/Solution.lean'],
            'producer_manifest_sha256':PINS['research-goal-20261018-stageI-original-affine-point/files.json'],
            'inputs_sha256_start':refs,'inputs_sha256_end':after,'sample_G_index':2417,'cells':[0,604],'chart':'id/rev',
            'original_state_cursor_FS_semantic_and_all_active_guards_verified':True,'original_compact_vs_AST_margin_verified':True,
            'terms_independently_decoded':68,'all155_original_domain_rows_verified':True,'joint':expected,
            'new_producer_Python_modules_imported':0,'old_A_parser_math_only_reused':True,
            'LP_matrix_inverse_newkernel_newFS_or_Lean_calls':0,'new_global_joint_floor_proven':False,
            'new_unconditional_zero_proportion_proven':False,
            'scope':'One unchanged existing feasible point only. Original signed Fraction beta/sigma values match the point-free integer forms; no uniform floor or actual energy comparison is proved.'}
        write_new(HERE/'independent-review.json',record)
        print(json.dumps({'passed':True,'seconds':record['seconds'],'delta_integer':str(delta),'sum_minus_twice_c':str(gap)}))
    except BaseException as exc:
        write_new(HERE/'failure.json',{'passed':False,'error':repr(exc),'traceback':traceback.format_exc(),
            'seconds':time.monotonic()-start,'automatic_retry_allowed':False});raise

if __name__=='__main__':main()
