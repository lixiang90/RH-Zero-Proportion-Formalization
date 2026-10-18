"""Independent raw M certificate audit; no mathematical execution by default.

Only the frozen independent A parser/model is imported after the root gate.
No M/I/J producer, optimizer, RREF, inverse, new point or kernel is used.
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
PROD=ROOT/'research-goal-20261018-stageM-component-envelope-preparation'
OWN_A=ROOT/'research-goal-20261018-record-baseline-independent/replay_independent.py'
BASE=ROOT/'research-goal-20261018-record-baseline-replay'
B=ROOT/'research-goal-20261018-stageB-classification'
Q,R,D,V,SA=32768,1024,10**9,10**10,10**20
KAPPA=Q*V*R
O=2*KAPPA*SA
CN,NC=893616123055294719,893766123055294719
TARGET=4*KAPPA*NC
PINS={
 'research-goal-20261018-record-baseline-independent/replay_independent.py':'c3f46e2ce79aa38e637e19a146071243d76c6998ff4b7de9710de83614d62af9',
 'research-goal-20261018-record-baseline-independent/audit-files.json':'2d2c8003ed6be6f74d0f53e8624cd631eb1c934415b22b5377a4f2d40c64791c',
 'research-goal-20261018-record-packing-independent/decode_packing.py':'cb4ff303c97c1788086d00f33dc64ca4e93d0c3693bc479740bd302c6921f28b',
 'research-goal-20261018-record-source-audit/snapshot/Solution.lean':'f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf',
 'research-goal-20261018-stageB-classification/files.json':'3f9408f2cf1ceae12339456da034d9e8f175f828cf2d53a652339ee79eec89ad',
 'research-goal-20261018-record-baseline-replay/baseline-events.jsonl.gz':'b924bf5ce93cde2e3044e8f9aa80cefb660a74c0c9d7161e2b09c017dc0fe5fc',
 'research-goal-20261018-stageG-complete-classification/first-unresolved-sample.json':'a3349919ca3c07c71346a6a753396b8daa211c5e5492299cdaf300198fbf2689',
 'research-goal-20261018-stageM-component-envelope-preparation/prepared-files.json':'b6cf0775e78fd7eb310a96393a43502584082b2824892244e15a9c13e2d04bbe'}

def pin(p):
    h=sha256()
    with p.open('rb') as f:
        for chunk in iter(lambda:f.read(1048576),b''):h.update(chunk)
    return h.hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def local(name):
    p=(ROOT/name).resolve();assert p.is_relative_to(ROOT);return p
def canon(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode('ascii')
def write_new(name,x):
    with (HERE/name).open('x',encoding='utf-8',newline='\n') as f:
        json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
def subset(expected,actual,path=''):
    if isinstance(expected,dict):
        for key,value in expected.items():assert key in actual,(path,key);subset(value,actual[key],path+'/'+key)
    else:assert expected==actual,(path,expected,actual)
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def inc(i,j):
    a=[0]*10;a[i]-=1;a[j]+=1;return a
def span(i,j,off,rev):return (off+8-j,off+8-i) if rev else (off+i,off+j)
def gap(r,off,rev):return off+(7-r if rev else r)

def locate(row,m,runner,events):
    root=row['root'];position=1;state=runner.root(m['roots'][root]['indices'])
    def word(p):return (m['dispatch_value']('WL'+str(root),p//Q)>>(p%Q))&((1<<480)-1)
    assert row['path'].startswith('r') and set(row['path'][1:])<=set('01')
    for turn in row['path'][1:]:
        event=events[root,position];assert event['state_sha256']==runner.hashstate(state)
        bits=word(position);assert event['kind']=='branch' and bits&1
        axis=(bits>>1)&63;mode=(bits>>7)&1;assert (axis,mode)==(event['axis'],event['mode'])
        l,u=state[0][axis],state[1][axis];cut=(l+u)//2
        if mode:
            legal=[z for z in m['BND'] if l+64<=z<=u-64]
            if legal:cut=min(legal,key=lambda z:abs(2*z-l-u))
        assert cut==event['cut'];i,j=m['ALL'][axis]
        state=runner.split(state,i,j,cut,turn=='0');position=event['left' if turn=='0' else 'right']
    leaf=events[root,position];s=row['state']
    assert row['coordinate_scale']==Q and row['separation']=='17/20'
    assert state==(s['L']+s['A'],s['U']+s['B']) and s['M']==0
    assert runner.hashstate(state)==row['state_sha256']==leaf['state_sha256']
    assert position==row['position'] and leaf['kind']=='numeric' and leaf['end']==row['end']
    witness=row['witness']
    assert witness['WD']==root and witness['original_leaf_position']==position
    assert witness['payload_bit_position']==position+2
    assert witness['original_rdw_block']==position//Q and witness['original_rdw_shift']==position%Q
    raw=word(position);assert raw&3==0 and not state[1][7]<state[0][0]
    return state,raw>>2

def original_terms(row,m,own,events):
    runner=own.Replay(m);state,word=locate(row,m,runner,events)
    used,margin=runner.numeric(state,word)
    assert used==row['end']-row['position']-2==row['witness']['consumed_payload_bits']
    assert margin==int(row['original_margin'])>=0
    assert margin-KAPPA*300000000000000==int(row['tau_margin'])
    terms=[];fs=[];at=0;cstar=0;jcoef=[D*R*b for b in m['BS']]
    for ti,(i,j,a,slot) in enumerate(m['TS']):
        L,U=runner.bounds(state,i,j);L0=sum(state[0][i:j]);assert L0<=L<=U
        fields,at=runner.decode_term(word,at,L,U);kind,mass,p,r=fields;fs.append(list(fields))
        amounts=runner.weights(kind,mass);lc=R-sum(amounts);assert min(lc,*amounts)>=0
        low=runner.lower_bound(L,max(L+1,U));anchors=[]
        mv=lc*low;msl=mw=cp=cn=0
        for n,(amount,anchor) in enumerate(zip(amounts,(p,r))):
            if not amount:continue
            assert anchor in m['pts'];raw=m['point_value'](anchor)
            vl=(raw>>96)&((1<<24)-1);vu=raw>>120
            assert vu>0 and vl<=L<=anchor<=U<=vu
            trip=raw&((1<<96)-1);v=trip&((1<<32)-1)
            dlo=((trip>>32)&((1<<32)-1))-2*D;dhi=2*D-(trip>>64)
            assert dlo<=dhi
            E=Q*R*v-10*R*(dlo*L0+dhi*(anchor-L0));S=(R//2)*dlo
            anchors.append({'slot':n,'amount':amount,'anchor':anchor,'trip':trip,'v':v,
                'dlo':dlo,'dhi':dhi,'valid':[vl,vu],'E':E,'S':S})
            mv+=amount*v;msl+=amount*((trip>>32)&((1<<32)-1));mw+=amount
            cp+=amount*max(0,(trip>>64)-2*D)*(anchor-L0)
            cn+=amount*max(0,2*D-(trip>>64))*(anchor-L0)
        delta=msl-2*D*mw;sigma=F(delta,D*R)
        beta=F(mv,V*R)+F(cp-cn,Q*D*R)-sigma*F(L0,Q)
        meanE=F(lc*Q*R*low,R)+sum(F(t['amount']*t['E'],R) for t in anchors)
        meanS=sum(F(t['amount']*t['S'],R) for t in anchors)
        assert meanE==KAPPA*beta and meanS==F(KAPPA,20*Q)*sigma
        cstar+=a*(Q*mv+10*(cp-cn-delta*L0))
        for rr in range(i,j):jcoef[rr]+=a*delta
        terms.append({'i':i,'j':j,'a':a,'ti':ti,'L':L,'U':U,'L0':L0,'FS':list(fields),
            'masses':[lc,*amounts],'lb':low,'anchors':anchors,'meanE':meanE,'meanS':meanS,
            'beta':beta,'sigma':sigma})
    P,S,Cp,Cm,consumed=runner.flow(state,word,at)
    assert consumed==used
    semantic={'FS':fs,'P':P,'S':S,'Cp':Cp,'Cm':Cm,'consumed_bits':used}
    payload={'bits':used,'value':str(word&((1<<used)-1))}
    assert sha256(canon(semantic)).hexdigest()==row['witness']['decoded_semantic_sha256']
    assert sha256(canon(payload)).hexdigest()==row['witness']['packed_payload_sha256']
    penalty=sum((state[1][r]-state[0][r])*max(P[r]-S[r]-jcoef[r],0) for r in range(8))
    certified=cstar+sum(10*jcoef[r]*state[0][r] for r in range(8))+10*(Cm-Cp-penalty)
    assert certified-KAPPA*CN==margin
    return terms,cstar,jcoef

def rebuild(cells,m,own,events):
    rows=[];term_records=[];pressure=[0]*10;mixed=[0]*10;mixconst=F(0);original_gamma=[0]*9;stars=[]
    def add(pos,tidx,tc,bound,kind,metadata):
        assert len(pos)==10 and sum(pos)==0 and all(type(x) is int for x in pos)
        rows.append({'row_id':len(rows),'position10':pos,'epigraph_index':tidx,
            'epigraph_coefficient':tc,'bound':bound,'kind':kind,**metadata});return len(rows)-1
    for wi,(cid,off,rev) in enumerate(((0,0,False),(604,1,True))):
        s=cells[cid]['state'];lo=s['L']+s['A'];hi=s['U']+s['B']
        for k,(i,j) in enumerate(m['ALL']):
            u,v=span(i,j,off,rev);a=inc(u,v)
            add(a,None,0,20*hi[k],'original_span_upper',{'window':wi,'original_span_slot':k})
            add([-x for x in a],None,0,-20*lo[k],'original_span_lower',{'window':wi,'original_span_slot':k})
    for r in range(9):add(inc(r+1,r),None,0,-17*Q,'original_separation',{'gap':r})
    for wi,(off,sign) in enumerate(((0,1),(1,-1))):
        a=[0]*10
        for i,v in ((off,-1),(off+1,1),(off+7,1),(off+8,-1)):a[i]+=sign*v
        add(a,None,0,0,'true_ordered_four_point',{'window':wi,'reverse':sign==-1})
    for wi,(cid,off,rev) in enumerate(((0,0,False),(604,1,True))):
        terms,cstar,jcoef=original_terms(cells[cid],m,own,events);stars.append(cstar)
        for r,bs in enumerate(m['BS']):
            normal=inc(gap(r,off,rev),gap(r,off,rev)+1)
            for v in range(10):pressure[v]+=D*R*bs*normal[v]
            original_gamma[gap(r,off,rev)]+=jcoef[r]
        for t in terms:
            e=len(term_records);u,v=span(t['i'],t['j'],off,rev);normal=inc(u,v);constant=Q*R*t['lb']
            comps=[{'kind':'constant','E':constant,'S':0,'row_id':add([0]*10,e,-1,-constant,
                'constant_component',{'term':e,'window':wi,'original_term':t['ti']})}]
            for x in t['anchors']:
                rid=add([x['S']*a for a in normal],e,-1,-x['E'],'active_anchor_component',
                    {'term':e,'window':wi,'original_term':t['ti'],'original_slot':x['slot'],'anchor':x['anchor']})
                comps.append({'kind':'active_anchor','original_slot':x['slot'],'original_mass':x['amount'],
                    'anchor':x['anchor'],'trip':str(x['trip']),'value_lower_numerator':x['v'],
                    'derivative_lower_numerator':x['dlo'],'derivative_upper_numerator':x['dhi'],
                    'original_valid_interval':x['valid'],'E':x['E'],'S':x['S'],'row_id':rid})
            mixconst+=2*t['a']*t['meanE']
            for k in range(10):
                z=2*t['a']*t['meanS']*normal[k];assert z.denominator==1;mixed[k]+=z.numerator
            term_records.append({'term':e,'window':wi,'original_cell':cid,'original_term':t['ti'],
                'original_span':[t['i'],t['j']],'physical_span':[u,v],'weight_numerator':t['a'],
                'original_L0':t['L0'],'original_bounds':[t['L'],t['U']],'original_FS':t['FS'],
                'original_masses':t['masses'],'component_rows':[c['row_id'] for c in comps],'components':comps,
                'original_mixture_intercept':str(t['meanE']),'original_mixture_slope':str(t['meanS']),
                'component_convex_combination_equals_original_FS':True})
    expected_b=[-original_gamma[0]]+[original_gamma[r-1]-original_gamma[r] for r in range(1,9)]+[original_gamma[-1]]
    assert [a+b for a,b in zip(pressure,mixed)]==expected_b and mixconst==2*sum(stars)
    assert len(term_records)==68 and 223<=len(rows)<=359
    return {'rows':rows,'terms':term_records,'objective_position10':pressure,
        'objective_epigraph68':[2*t['weight_numerator'] for t in term_records],
        'columns':['X'+str(i) for i in range(1,10)]+['T'+str(i) for i in range(68)],
        'columns_count':77,'geometry_rows':155,'objective_constant':0,'target':TARGET,
        'fixed_cells':[0,604],'chart':'id/rev','gauge_X0':0,'all_variable_bounds_free':True,
        'original_mixture_identity_checked':True}

def full(row):
    t=[0]*68
    if row['epigraph_index'] is not None:t[row['epigraph_index']]=row['epigraph_coefficient']
    return row['position10']+t
def primal(model,values):
    assert len(values)==77;x=list(map(F,values));z=[F(0)]+x
    violated=[r['row_id'] for r in model['rows'] if dot(full(r),z)>r['bound']]
    objective=dot(model['objective_position10']+model['objective_epigraph68'],z)
    return {'valid':not violated,'violated_row_ids':violated,'raw_objective':str(objective)}
def dual(model,weights):
    assert len(weights)==len(model['rows']);mu=list(map(F,weights))
    balance=list(map(F,model['objective_position10']+model['objective_epigraph68']))
    for w,row in zip(mu,model['rows']):
        for j,a in enumerate(full(row)):balance[j]+=w*a
    bound=-sum(w*r['bound'] for w,r in zip(mu,model['rows']))
    neg=[i for i,w in enumerate(mu) if w<0]
    return {'valid':not neg and balance==[0]*78,'negative_row_ids':neg,'full78_balance':list(map(str,balance)),
        'raw_lower_bound':str(bound),'raw_minus_target':str(bound-TARGET)}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--audit-authorized-fixed-M',action='store_true')
    ap.add_argument('--gate');ap.add_argument('--gate-sha256');a=ap.parse_args()
    if not a.audit_authorized_fixed_M:print(json.dumps({'prepared_only':True,'mathematical_executions':0}));return
    assert a.gate and a.gate_sha256
    assert not (HERE/'independent-review.json').exists() and not (HERE/'failure.json').exists()
    start=time.monotonic();refs={}
    def bind(path,h=None):
        path=path.resolve();assert path.is_relative_to(ROOT);actual=pin(path)
        if h is not None:assert actual==h
        name=path.relative_to(ROOT).as_posix()
        if name in refs:assert refs[name]==actual
        refs[name]=actual;return path
    def package(path,h):
        obj=load(bind(path,h))
        for key in ('files','package_files','read_only_dependencies','dependencies','read_only_existing_references'):
            for row in obj.get(key,[]):bind(local(row['path']),row['sha256'])
    try:
        gate=load(bind(local(a.gate),a.gate_sha256));assert gate['independent_component_audits_authorized']==1
        assert gate['audit_script_path']==Path(__file__).relative_to(ROOT).as_posix()
        bind(Path(__file__),gate['audit_script_sha256'])
        for name,h in PINS.items():
            if name.endswith(('/files.json','/audit-files.json','/prepared-files.json')):package(local(name),h)
            else:bind(local(name),h)
        package(local(gate['producer_manifest_path']),gate['producer_manifest_sha256'])
        assert local(gate['producer_manifest_path']).parent==PROD
        spec=importlib.util.spec_from_file_location('own_independent_A_for_M',OWN_A)
        own=importlib.util.module_from_spec(spec);spec.loader.exec_module(own);source=own.load_source()
        cells={}
        with gzip.open(B/'exception-cells.jsonl.gz','rt',encoding='ascii') as f:
            for line in f:
                row=json.loads(line)
                if row['exception_id'] in (0,604):cells[row['exception_id']]=row
        assert set(cells)=={0,604};events={};wanted={r['root'] for r in cells.values()}
        with gzip.open(BASE/'baseline-events.jsonl.gz','rt',encoding='ascii') as f:
            for line in f:
                event=json.loads(line)
                if event['root'] in wanted:events[event['root'],event['pos']]=event
        model=rebuild(cells,source,own,events);stored=load(bind(PROD/'model.json'));subset(model,stored)
        scaling=load(bind(PROD/'scaling.json'))
        subset({'variable_raw_equals_scale_times_native':list(map(str,[20*Q]*9+[KAPPA]*68)),
            'row_divisors':list(map(str,[20*Q]*155+[KAPPA]*(len(model['rows'])-155))),
            'objective_divisor':str(O),'native_target':str(F(TARGET,O)),'columns':77,'rows':len(model['rows'])},scaling)
        # Validate, never reconstruct or optimize, every supplied exact object.
        exact=load(bind(PROD/'exact-reconstruction.json'));dc=pc=None
        if exact.get('exact_dual'):
            item=exact['exact_dual'];dc=dual(model,item['raw_row_weights']);subset(dc,item['checks'])
        if exact.get('exact_primal'):
            item=exact['exact_primal'];pc=primal(model,item['raw77']);subset(pc,item['checks'])
        lower=bool(dc and dc['valid'] and F(dc['raw_lower_bound'])>=TARGET)
        below=bool(pc and pc['valid'] and F(pc['raw_objective'])<TARGET);assert not (lower and below)
        equal=None
        if dc and dc['valid'] and pc and pc['valid']:
            assert F(dc['raw_lower_bound'])<=F(pc['raw_objective'])
            equal=F(dc['raw_lower_bound'])==F(pc['raw_objective'])
        result=load(bind(PROD/'result.json'))
        assert result['inputs_sha256_start']==result['inputs_sha256_end']
        for name,h in result['inputs_sha256_start'].items():bind(local(name),h)
        assert result['linprog_calls']==1 and result['auxiliary_optimization_calls']==0
        assert result['exact_dual_valid']==bool(dc and dc['valid']) and result['exact_primal_valid']==bool(pc and pc['valid'])
        assert result['component_model_lower_proven_by_exact_certificate'] is lower
        assert result['below_refutes_only_fixed_component_polyhedral_lower_model'] is below
        assert result['passed'] is (lower or below) and result['model_sha256']==pin(PROD/'model.json')
        if lower or below:
            certificate=load(bind(PROD/'certificate.json'));assert certificate['model_sha256']==pin(PROD/'model.json')
            assert int(certificate['target'])==TARGET
            if lower:
                assert certificate['kind']=='Lower';cc=dual(model,certificate['raw_row_weights'])
                subset(dc,cc);subset(cc,certificate['checks'])
            else:
                assert certificate['kind']=='Below' and certificate['actual_F_counterexample'] is False
                checks=primal(model,certificate['raw77']);assert checks['valid'] and F(checks['raw_objective'])<TARGET
                subset(checks,certificate['checks'])
            assert result['certificate_sha256']==pin(PROD/'certificate.json')
        external=load(PROD/'external-runtime.json');runtime={}
        for item in external['files']:
            p=Path(item['path']);assert p.is_absolute() and p.stat().st_size==item['bytes'] and pin(p)==item['sha256']
            runtime[str(p)]=item['sha256']
        assert result['external_runtime_sha256_start']==result['external_runtime_sha256_end']==runtime
        after={name:pin(local(name)) for name in refs};assert refs==after
        record={'schema':'M-independent-original-component-raw-certificate-review-v1','passed':True,'pid':os.getpid(),
            'seconds':time.monotonic()-start,'independent_audit_calls':1,'inputs_sha256_start':refs,'inputs_sha256_end':after,
            'rows':len(model['rows']),'variables':77,'full_dual_coordinates':78,'original_FS_terms_reconstructed':68,
            'all_components_original_anchors_and_guards_verified':True,'original_state_cursor_semantic_payload_verified':True,
            'component_convex_mixture_equals_original_affine_verified':True,'dual_checks':dc,'primal_checks':pc,
            'exact_primal_dual_objectives_equal_if_both_valid':equal,
            'valid_local_Lower':lower,'valid_fixed_model_Below':below,'producer_M_I_J_modules_imported':0,
            'independent_A_parser_only_imported':True,'RREF_solver_new_FS_anchor_kernel_point_or_Lean_runs':0,
            'external_discovery_runtime_sha256':runtime,'new_global_floor_or_unconditional_kappa_proven':False,
            'scope':'Only this fixed component lower model. Actual function validity uses the original LBSound/TVal/mokI and reflection premises; no new Lean consumer or global cover is supplied.'}
        write_new('independent-review.json',record)
        print(json.dumps({'passed':True,'rows':len(model['rows']),'valid_local_Lower':lower,'valid_fixed_model_Below':below,'seconds':record['seconds']}))
    except BaseException as exc:
        write_new('failure.json',{'passed':False,'error':repr(exc),'traceback':traceback.format_exc(),
            'seconds':time.monotonic()-start,'automatic_retry_allowed':False});raise

if __name__=='__main__':main()
