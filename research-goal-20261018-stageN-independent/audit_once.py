"""Prepared independent N committed-prefix audit; no mathematics at import.

Only our frozen A parser is imported after a separate root gate. No N/M/I/J
Python imports, RREF, optimizer, new points, kernel evaluation or Lean. Every
published record receives full mathematics; an optional retained next record
is separately audited and never silently promoted into the published history.
"""
import argparse
from collections import Counter
from fractions import Fraction as F
import gzip
from hashlib import sha256
import importlib.util
import json
import os
from pathlib import Path
import struct
import sys
import time
import traceback
import zlib

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
PROD=ROOT/'research-goal-20261018-stageN-complete-component-preparation'
OWN=ROOT/'research-goal-20261018-record-baseline-independent/replay_independent.py'
B=ROOT/'research-goal-20261018-stageB-classification'
H=ROOT/'research-goal-20261018-stageH-ordered-transport'
Q,R,D,V,SA,N=32768,1024,10**9,10**10,10**20,1187
K=Q*R*V
CN,C=893616123055294719,893766123055294719
TARGET=4*K*C
CHARTS=['id/id','id/rev','rev/id','rev/rev']
DEDUCTIONS={2417:'verified_M_unpooled_Lower_implies_pooled_Lower',5331088:'verified_J_Lower'}
SCOPE='complete_published_N_prefix_with_separate_optional_retained_next_record'

def canonical(x):
    return (json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False)+'\n').encode('ascii')
def read(p):return json.loads(p.read_text(encoding='utf8'))
def digest(p):
    h=sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''):h.update(block)
    return h.hexdigest()
def checked(name):
    p=(ROOT/name).resolve();assert p.is_relative_to(ROOT);return p
def save(name,x):
    with (HERE/name).open('xb') as f:f.write(canonical(x));f.flush();os.fsync(f.fileno())
def scalar(text):
    assert type(text) is str
    value=F(text);assert str(value)==text
    return value
def pin(refs,row):
    p=checked(row['path']);assert digest(p)==row['sha256']
    if 'bytes' in row:assert p.stat().st_size==row['bytes']
    if row['path'] in refs:assert refs[row['path']]==row['sha256']
    refs[row['path']]=row['sha256']
def inventory(refs,row):
    pin(refs,row);m=read(checked(row['path']))
    for field in ['files','package_files','read_only_dependencies','dependencies','read_only_existing_references']:
        for dep in m.get(field,[]):pin(refs,dep)
    return m

def identity(args):
    refs={};pin(refs,{'path':args.gate,'sha256':args.gate_sha256})
    g=read(checked(args.gate))
    assert type(g['independent_N_published_prefix_audits_authorized']) is int and g['independent_N_published_prefix_audits_authorized']==1
    assert g['scope']==SCOPE and g['automatic_retry_allowed'] is False
    assert type(g['new_solver_RREF_points_kernel_or_Lean_authorized']) is int and g['new_solver_RREF_points_kernel_or_Lean_authorized']==0
    assert g['expected_H_remaining']==15378 and g['expected_published_records']==675
    assert g['all_published_records_mathematically_audited'] is True
    assert type(g['audit_retained_next_record']) is bool
    if g['audit_retained_next_record']:assert g['expected_retained_records']==676
    prep_row={'path':HERE.relative_to(ROOT).as_posix()+'/prepared-files.json','sha256':g['prepared_manifest_sha256']}
    prep=inventory(refs,prep_row)
    rt=prep['runtime'];assert Path(sys.executable).resolve()==Path(rt['executable']).resolve()
    assert digest(Path(sys.executable))==rt['sha256'] and sys.version==rt['version'] and sys.flags.optimize==0
    for f in rt['additional_files']:assert digest(Path(f['path']))==f['sha256']
    assert g['producer_manifest']['path']==PROD.relative_to(ROOT).as_posix()+'/files.json'
    inventory(refs,g['producer_manifest'])
    for row in g['producer_endpoints']:pin(refs,row)
    return g,refs

def journal(desc,required_full_file):
    """One bounded gzip member at a time; prove hashes, CRC and exact EOF."""
    p=checked(desc['path']);limit=desc['bytes']
    assert type(limit) is int and limit>=0
    if required_full_file:assert p.stat().st_size==limit
    else:assert p.stat().st_size>=limit
    left=limit;buffer=b'';totalhash=sha256();offset=0;count=0
    with p.open('rb') as f:
        while offset<limit:
            z=zlib.decompressobj(31);parts=[];memberhash=sha256();length=0
            while not z.eof:
                if not buffer:
                    block=f.read(min(65536,left));assert block
                    left-=len(block);buffer=block;totalhash.update(block)
                out=z.decompress(buffer);parts.append(out)
                used=len(buffer)-len(z.unused_data)
                assert used>0 or z.eof
                memberhash.update(buffer[:used]);length+=used;buffer=z.unused_data
            data=b''.join(parts);value=json.loads(data)
            assert data==canonical(value)
            ref={'offset':offset,'bytes':length,'decoded_sha256':sha256(data).hexdigest(),
                 'compressed_member_sha256':memberhash.hexdigest()}
            yield value,ref
            offset+=length;count+=1
        assert offset==limit and left==0 and not buffer
        if required_full_file:assert not f.read(1)
    assert count==desc['records'] and totalhash.hexdigest()==desc['sha256']

def prefix_metadata(path,expected):
    prefix=read(path)
    assert prefix['expected_records']==15378 and prefix['unprocessed_suffix_is_not_classified'] is True
    data=(H/'remaining-indices.u32.bin').read_bytes()
    indices=[v[0] for v in struct.iter_unpack('<I',data)]
    assert len(indices)==15378 and indices==sorted(set(indices))
    committed=prefix['committed_records'];assert committed==expected and 0<committed<=len(indices)
    assert prefix['input_index_sequence_sha256']==sha256(data).hexdigest()
    assert prefix['committed_index_sequence_sha256']==sha256(data[:4*committed]).hexdigest()
    assert prefix['last_G_index']==indices[committed-1]
    streams=prefix['streams']
    native={};originals={};native_ids=[]
    for rec,ref in journal(streams['original-components.jsonl.gz'],False):
        cid=rec['cell_id'];assert type(cid) is int and 0<=cid<N and cid not in originals
        originals[cid]=(rec,ref)
    for rec,ref in journal(streams['native-results.jsonl.gz'],False):
        ix=rec['G_index'];assert ix not in native
        assert rec['call_number']==len(native)+1
        native[ix]=(ref,rec['native_row_ids']);native_ids.append(ix)
    counts=Counter();records=[];expected_native=[];seen_records=0
    for rec,ref in journal(streams['case-records.jsonl.gz'],False):
        assert seen_records<committed
        ix=indices[seen_records];assert rec['G_index']==ix
        kind=rec['outcome'];assert kind in ['deduction_Lower','Lower','Below','unresolved']
        if ix in DEDUCTIONS:
            assert kind=='deduction_Lower' and rec['dependency']==DEDUCTIONS[ix]
            assert rec['no_new_FS_model_or_solver_for_this_case'] is True
        else:
            assert kind!='deduction_Lower';pair,chart=divmod(ix,4);i,j=divmod(pair,N)
            assert rec['pair']==[i,j] and rec['chart']==CHARTS[chart]
            assert rec['group_count']==42 and rec['raw_column_count']==51 and rec['full_balance_coordinates']==52
            assert rec['native_record']==native[ix][0]
            assert sorted(set(native[ix][1]))==native[ix][1]
            assert all(type(r) is int and 0<=r<rec['row_count'] for r in native[ix][1])
            for cid in [i,j]:assert rec['original_components'][str(cid)]==originals[cid][1]
            assert rec['Below_is_not_actual_F_counterexample'] is True
            expected_native.append(ix)
        records.append(rec);counts[kind]+=1;seen_records+=1
    assert seen_records==committed and dict(counts)==prefix['counts']
    assert native_ids==expected_native and len(native_ids)==prefix['linprog_calls_started']
    assert len(native_ids)<=15376 and prefix['streams']['case-records.jsonl.gz']['records']==committed
    intents=[]
    with (PROD/'call-intents.jsonl').open('rb') as f:
        for line in f:
            rec=json.loads(line);assert line==canonical(rec);intents.append(rec)
    assert [r['G_index'] for r in intents[:len(native_ids)]]==native_ids
    assert [r['linprog_call_number'] for r in intents]==list(range(1,len(intents)+1))
    tails={}
    for name,desc in streams.items():
        with checked(desc['path']).open('rb') as f:
            f.seek(desc['bytes']);h=sha256();length=0
            for block in iter(lambda:f.read(65536),b''):h.update(block);length+=len(block)
        tails[name]={'bytes':length,'sha256':h.hexdigest(),'included_in_this_prefix':False}
    return records,originals,{'committed_records':committed,'expected_records':15378,'counts':dict(counts),
        'all_prefix_index_membership_order_stream_hashes_and_EOF_checked':True,
        'EOF_scope':'Strict EOF inside every published descriptor byte range; full-file tails are explicitly separate.',
        'retained_stream_tails':tails,'uncommitted_call_intents':len(intents)-len(native_ids),'native_calls':len(native_ids)}

def load_cells():
    out=[]
    with gzip.open(B/'exception-cells.jsonl.gz','rb') as f:
        for line in f:
            r=json.loads(line);assert line==canonical(r) and r['exception_id']==len(out);out.append(r)
    assert len(out)==N;return out

def load_history(roots):
    out={}
    with gzip.open(ROOT/'research-goal-20261018-record-baseline-replay/baseline-events.jsonl.gz','rb') as f:
        for line in f:
            r=json.loads(line)
            if r['root'] in roots:
                assert line==canonical(r) and (r['root'],r['pos']) not in out;out[r['root'],r['pos']]=r
    return out

def locate(runner,m,row,hist):
    root=row['root'];at=1;state=runner.root(m['roots'][root]['indices'])
    assert row['path'].startswith('r') and set(row['path'][1:])<={'0','1'}
    def word(p):return (m['dispatch_value']('WL'+str(root),p//Q)>>(p%Q))&((1<<480)-1)
    for direction in row['path'][1:]:
        old=hist[root,at];w=word(at)
        assert old['kind']=='branch' and old['state_sha256']==runner.hashstate(state) and w&1
        axis,mode=(w>>1)&63,(w>>7)&1
        assert (axis,mode)==(old['axis'],old['mode']) and old['left']==at+8
        low,high=state[0][axis],state[1][axis];cut=(low+high)//2
        if mode:
            valid=[(abs(2*b-low-high),k,b) for k,b in enumerate(m['BND']) if low+64<=b and b+64<=high]
            if valid:cut=min(valid)[2]
        assert cut==old['cut'];a,b=m['ALL'][axis]
        state=runner.split(state,a,b,cut,direction=='0');at=old['left'] if direction=='0' else old['right']
    end=hist[root,at]
    assert end['kind']=='numeric' and end['end']==row['end'] and at==row['position']
    assert runner.hashstate(state)==row['state_sha256']==end['state_sha256']
    assert state==(row['state']['L']+row['state']['A'],row['state']['U']+row['state']['B'])
    w=word(at);assert w&3==0 and state[1][7]>=state[0][0]
    return state,w>>2

def original(own,m,row,hist,saved):
    runner=own.Replay(m);state,word=locate(runner,m,row,hist)
    consumed,ast=runner.numeric(state,word)
    assert row['position']+2+consumed==row['end'] and ast==int(row['original_margin'])>=0
    at=0;FS=[];terms=[];cstar=0;coef=[D*R*b for b in m['BS']]
    for tid,(i,j,a,_slot) in enumerate(m['TS']):
        low,high=runner.bounds(state,i,j);l0=sum(state[0][i:j]);assert l0<=low<=high
        fields,at=runner.decode_term(word,at,low,high);kind,mass,p,r=fields;FS.append(list(fields))
        one,two=runner.weights(kind,mass);lc=R-one-two;assert min(one,two,lc)>=0 and lc+one+two==R
        packed=[m['point_value'](x)&((1<<96)-1) for x in [p,r]];guards=[];lines=[]
        table=runner.lower_bound(low,max(high,low+1));lines.append((Q*R*table,0))
        for amount,x,trip in zip([one,two],[p,r],packed):
            if amount:
                assert x in m['pts'];full=m['point_value'](x);lo=(full>>96)&((1<<24)-1);hi=full>>120
                assert 1<=hi and lo<=low<=x<=high<=hi
                guards.append({'mass':amount,'original_anchor':x,'valid_lower':lo,'valid_upper':hi,'guard_passed':True})
                dl=((trip>>32)&((1<<32)-1))-2*D;du=2*D-(trip>>64);v=trip&((1<<32)-1)
                lines.append((Q*R*v-10*R*(dl*l0+du*(x-l0)),512*dl))
        vals=[x&((1<<32)-1) for x in packed];sl=[(x>>32)&((1<<32)-1) for x in packed];up=[x>>64 for x in packed]
        cp=sum(t*max(u-2*D,0)*max(x-l0,0) for t,u,x in zip([one,two],up,[p,r]))
        cn=sum(t*max(2*D-u,0)*max(x-l0,0) for t,u,x in zip([one,two],up,[p,r]))
        mv=lc*table+one*vals[0]+two*vals[1];msl=one*sl[0]+two*sl[1];mw=one+two;delta=msl-2*D*mw
        beta=F(mv,V*R)+F(cp-cn-delta*l0,Q*D*R);sigma=F(delta,D*R)
        term={'term_id':tid,'edge':[i,j],'external_weight_numerator':a,'external_weight_denominator':SA,
            'original_term_bounds':[low,high],'uc_upper':max(high,low+1),'original_L0':l0,'FS':list(fields),
            'mass_constant':lc,'mass_first':one,'mass_second':two,'original_lb_table_value':table,
            'active_mokI_guards':guards,'mvT':mv,'mslT':msl,'mwT':mw,'mcpT':cp,'mcnT':cn,
            'signed_delta':delta,'beta':str(beta),'sigma':str(sigma)}
        terms.append((term,lines));cstar+=a*K*beta
        for gap in range(i,j):coef[gap]+=a*delta
    P,S,Cp,Cm,end=runner.flow(state,word,at);assert end==consumed
    semantic={'FS':FS,'P':P,'S':S,'Cp':Cp,'Cm':Cm,'consumed_bits':end}
    payload={'bits':end,'value':str(word&((1<<end)-1))}
    witness={'WD':row['root'],'original_leaf_position':row['position'],'payload_bit_position':row['position']+2,
        'consumed_payload_bits':end,'original_rdw_block':row['position']//Q,'original_rdw_shift':row['position']%Q,
        'packed_payload_sha256':sha256(canonical(payload)).hexdigest(),'decoded_semantic_sha256':sha256(canonical(semantic)).hexdigest()}
    assert witness==row['witness']==saved['witness']
    assert [t for t,_ in terms]==saved['terms']
    assert cstar.denominator==1 and str(cstar)==saved['canonical_Cstar'] and list(map(str,coef))==saved['canonical_J']
    assert saved['state_sha256']==row['state_sha256'] and int(saved['original_compact_margin'])==ast
    return terms

def incidence(i,j):
    out=[0]*10;out[i]-=1;out[j]+=1;return out
def placed(i,j,off,rev):return (off+8-j,off+8-i) if rev else (off+i,off+j)

def model_from_source(m,cells,windows,chart):
    rows=[];lookup={};groups=[];members=[];pressure=[0]*10
    def add(pos,t,rhs):rows.append((pos,t,rhs))
    for wi,(cell,rev) in enumerate(zip(cells,[chart//2,chart%2])):
        state=cell['state'];lo=state['L']+state['A'];hi=state['U']+state['B']
        for (a,b),l,u in zip(m['ALL'],lo,hi):
            a,b=placed(a,b,wi,rev);n=incidence(a,b);add(n,None,20*u);add([-x for x in n],None,-20*l)
    for r in range(9):add(incidence(r+1,r),None,-17*Q)
    for off,rev in [(0,chart//2),(1,chart%2)]:
        n=[0]*10
        for k,v in [(off,-1),(off+1,1),(off+7,1),(off+8,-1)]:n[k]+=(-1 if rev else 1)*v
        add(n,None,0)
    assert len(rows)==155
    for wi,(window,rev) in enumerate(zip(windows,[chart//2,chart%2])):
        for r,b in enumerate(m['BS']):
            k=wi+(7-r if rev else r);n=incidence(k,k+1)
            for v in range(10):pressure[v]+=D*R*b*n[v]
        for term,lines in window:
            a,b=placed(*term['edge'],wi,rev);key=(a,b)
            if key not in lookup:lookup[key]=len(groups);groups.append(0)
            group=lookup[key];groups[group]+=2*term['external_weight_numerator'];members.append((wi,group,term['external_weight_numerator']))
            n=incidence(a,b)
            for E,S in lines:add([S*x for x in n],group,-E)
    assert len(groups)==42 and len(rows)>=155 and sum(pressure)==0
    return rows,pressure,groups,members

def certificates(target,rows,pressure,weights,members,cells,source,chart):
    exact=target['normalized_exact_reconstruction'];reported=target['separate_raw_verification']
    primal=exact.get('exact_primal');primalsummary=None;below=False;lower=False
    if primal:
        x=list(map(scalar,primal['raw_primal']));assert len(x)==51;X=[F(0)]+x[:9];bad=[]
        for rid,(pos,g,rhs) in enumerate(rows):
            lhs=sum(a*p for a,p in zip(pos,X))-(x[9+g] if g is not None else 0)
            if lhs>rhs:bad.append(rid)
        value=sum(a*p for a,p in zip(pressure,X))+sum(a*x[9+g] for g,a in enumerate(weights))
        valid=not bad;below=valid and value<TARGET
        assert primal['checks']['valid']==valid and primal['checks']['violated_row_ids']==bad
        assert scalar(primal['checks']['raw_objective'])==value and reported['primal_valid']==valid
        assert scalar(reported['raw_objective'])==value
        floors=[]
        if valid:
            for wi,(cell,rev) in enumerate(zip(cells,[chart//2,chart%2])):
                p=F(0)
                for r,b in enumerate(source['BS']):
                    k=wi+(7-r if rev else r);p+=D*R*b*(X[k+1]-X[k])
                p+=sum(2*a*x[9+g] for w,g,a in members if w==wi)
                floor=2*K*CN+2*int(cell['original_margin']);assert p>=floor;floors.append(str(p-floor))
        primalsummary={'valid':valid,'violated_row_ids':bad,'raw_objective':str(value),
            'raw_minus_target':str(value-TARGET),'perwindow_original_floor_surpluses':floors}
    dual=exact.get('exact_dual');dualsummary=None
    if dual:
        mu=list(map(scalar,dual['raw_row_weights']));assert len(mu)==len(rows)
        balance=list(map(F,pressure+weights));cost=F(0)
        for w,(pos,g,rhs) in zip(mu,rows):
            for k,a in enumerate(pos):balance[k]+=w*a
            if g is not None:balance[10+g]-=w
            cost-=w*rhs
        valid=all(w>=0 for w in mu) and all(b==0 for b in balance)
        assert dual['checks']['valid']==valid
        assert list(map(str,balance))==dual['checks']['full_balance'] and scalar(dual['checks']['raw_lower_bound'])==cost
        assert reported['dual_valid']==valid and scalar(reported['raw_lower_bound'])==cost
        lower=valid and cost>=TARGET
        dualsummary={'valid':valid,'cost':str(cost),'minus_target':str(cost-TARGET)}
    assert reported['Lower']==lower and reported['Below']==below and not(lower and below)
    outcome='Lower' if lower else 'Below' if below else 'unresolved';assert outcome==target['outcome']
    semantic={'rows':rows,'objective_position10':pressure,'objective_T42':weights,'target':TARGET}
    return {'all_original_rows':len(rows),'full_balance_coordinates':52,'raw_columns':51,'outcome':outcome,
        'independent_raw_semantic_sha256':sha256(canonical(semantic)).hexdigest(),
        'primal_rechecked':primalsummary,'original_dual_rechecked':dualsummary,
        'model_sha256_metadata_not_used_as_proof':target['model_sha256']}

def deductions():
    m=read(ROOT/'research-goal-20261018-stageM-independent/independent-review.json')
    j=read(ROOT/'research-goal-20261018-stageJ-independent/independent-review.json')
    mm=read(ROOT/'research-goal-20261018-stageM-component-envelope-preparation/model.json')
    assert m['passed'] is True and m['valid_local_Lower'] is True
    assert mm['fixed_cells']==[0,604] and mm['chart']=='id/rev' and mm['target']==TARGET
    assert ((0*N+604)*4+1)==2417 and j['passed'] is True
    old=(H/'remaining-indices.u32.bin').read_bytes()
    new=(ROOT/'research-goal-20261018-stageJ-fixed-basis-preparation/remaining-indices.u32.bin').read_bytes()
    a={v[0] for v in struct.iter_unpack('<I',old)};b={v[0] for v in struct.iter_unpack('<I',new)}
    assert a-b=={5331088} and b<=a
    return {'M2417_prior_independent_Lower_dependency_verified':True,
            'J5331088_prior_independent_Lower_dependency_verified':True,'prior_certificates_not_reexecuted':True}

def execute(args):
    for n in ['started.json','independent-review.json','failure.json']:assert not (HERE/n).exists()
    start=time.monotonic();stage='identity';refs={}
    try:
        g,refs=identity(args);save('started.json',{'pid':os.getpid(),'scope':SCOPE,'inputs_sha256':refs})
        stage='all_committed_prefix_metadata';records,originals,meta=prefix_metadata(PROD/'prefix.json',675)
        assert meta['counts']=={'Lower':674,'deduction_Lower':1}
        retained=None;retained_originals=None;retained_meta=None
        if g['audit_retained_next_record']:
            all_retained,retained_originals,retained_meta=prefix_metadata(PROD/'prefix.json.tmp',676)
            assert all_retained[:675]==records
            retained=all_retained[675]
            assert retained['G_index']==g['retained_next_G_index']
        assert time.monotonic()-start<g['resource_limits']['elapsed_seconds']
        stage='prior_deductions';ded=deductions()
        stage='source_FS_and_component_rebuild'
        spec=importlib.util.spec_from_file_location('N_audit_own_frozen_A_only',OWN)
        own=importlib.util.module_from_spec(spec);spec.loader.exec_module(own);m=own.load_source()
        cells_all=load_cells();needed=set()
        for rec in records+([retained] if retained else []):
            if rec['outcome']!='deduction_Lower':
                pair,_=divmod(rec['G_index'],4);i,j=divmod(pair,N);needed.update([i,j])
        hist=load_history({cells_all[cid]['root'] for cid in needed});cache={};trace=sha256();counts=Counter()
        def audit_case(rec,cache_records):
            pair,chart=divmod(rec['G_index'],4);i,j=divmod(pair,N);cells=[cells_all[i],cells_all[j]];windows=[]
            for cell in cells:
                cid=cell['exception_id']
                if cid not in cache:cache[cid]=original(own,m,cell,hist,cache_records[cid][0])
                else:assert [t for t,_ in cache[cid]]==cache_records[cid][0]['terms']
                windows.append(cache[cid])
            rows,pressure,weights,members=model_from_source(m,cells,windows,chart)
            assert len(rows)==rec['row_count'] and [r['state_sha256'] for r in cells]==rec['original_cell_state_sha256']
            checked=certificates(rec,rows,pressure,weights,members,cells,m,chart)
            return {'G_index':rec['G_index'],**checked}
        stage='all_published_raw_certificates'
        for rec in records:
            assert time.monotonic()-start<g['resource_limits']['elapsed_seconds']
            checked={'G_index':rec['G_index'],'outcome':'deduction_Lower'} if rec['outcome']=='deduction_Lower' else audit_case(rec,originals)
            counts[checked['outcome']]+=1;trace.update(canonical(checked))
        assert dict(counts)==meta['counts']
        recovered=audit_case(retained,retained_originals) if retained else None
        after={p:digest(checked(p)) for p in refs};assert refs==after
        assert time.monotonic()-start<g['resource_limits']['elapsed_seconds']
        save('independent-review.json',{'schema':'N-independent-complete-published-prefix-review-v1','passed':True,
            'pid':os.getpid(),'seconds':time.monotonic()-start,'scope':SCOPE,
            'inputs_sha256_start':refs,'inputs_sha256_end':after,'prefix_metadata':meta,'deductions':ded,
            'all_675_published_records_mathematically_audited':True,'mathematical_counts':dict(counts),
            'mathematical_trace_sha256':trace.hexdigest(),'original_source_FS_cells_rebuilt':len(cache),
            'separate_retained_candidate':recovered,'retained_metadata':retained_meta,
            'retained_candidate_promoted_into_published_history':False,'all_domain_floor_proven':False,
            'actual_F_counterexample_claimed':False,'producer_N_M_I_J_modules_imported':False,
            'own_A_source_parser_only_imported':True,'RREF_solver_new_FS_points_kernel_Lean_runs':0})
        print(json.dumps({'passed':True,'published':675,'retained_candidate_audited':bool(retained),'scope':SCOPE}),flush=True)
    except BaseException as exc:
        save('failure.json',{'stage':stage,'error':repr(exc),'traceback':traceback.format_exc(),
            'seconds':time.monotonic()-start,'scope':SCOPE,'automatic_retry':False});raise

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--execute-authorized-audit-once',action='store_true')
    p.add_argument('--gate');p.add_argument('--gate-sha256');a=p.parse_args()
    assert a.execute_authorized_audit_once and a.gate and a.gate_sha256;execute(a)
if __name__=='__main__':main()
