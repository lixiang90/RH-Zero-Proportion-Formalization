"""One gated fixed O replay. No mathematics or external imports at import.

Uses our own frozen A/v1 source helpers and independent SZ-pair evaluator.
Never imports O/N/N2 producer code; does not solve a linear system.
"""
import argparse
from collections import defaultdict
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
import os
from pathlib import Path
import sys
import time
import traceback
import zlib

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
PROD=ROOT/'research-goal-20261018-stageO-fixed-curvature-preparation'
N2=ROOT/'research-goal-20261018-stageN2-pooled-component-resumption'
OWN=ROOT/'research-goal-20261018-stageN-independent-v1/audit_once.py'
OWN_A=ROOT/'research-goal-20261018-record-baseline-independent/replay_independent.py'
SCOPE='fixed_O_1322606_23_original_CellA_49_anchor_rows_42_spans_saved_stationarity'
PRODUCER_SHA='9eeb39270ad6853ee7ad3472c0446237ad21b64be0db442815e2566bfe97191b'
PACKET_SHA='a952a8bd239bddaa0c8d1f24b45a5096cb3a3b6ff19f067baaba46686eb11cbf'
Q=32768
K=Q*1024*10**10
TARGET=4*K*893766123055294719

def canonical(x):return (json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False)+'\n').encode('ascii')
def load(p):return json.loads(p.read_text(encoding='utf8'))
def digest(p):
    h=sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def path_checked(name):
    p=(ROOT/name).resolve();assert p.is_relative_to(ROOT);return p
def save(n,x):
    with (HERE/n).open('xb') as f:f.write(canonical(x));f.flush();os.fsync(f.fileno())
def add_pin(refs,r):
    p=path_checked(r['path']);assert digest(p)==r['sha256']
    if 'bytes' in r:assert p.stat().st_size==r['bytes']
    if r['path'] in refs:assert refs[r['path']]==r['sha256']
    refs[r['path']]=r['sha256']
def inventory(refs,r):
    add_pin(refs,r);doc=load(path_checked(r['path']))
    for field in ['files','package_files','read_only_dependencies','dependencies']:
        for dep in doc.get(field,[]):add_pin(refs,dep)
    return doc
def own_import(p,name):
    spec=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
def scalar(s):
    assert type(s) is str;v=F(s);assert str(v)==s;return v
def member(desc):
    """Exactly the one fixed, hash-bound gzip member, with no trailing bytes."""
    p=path_checked(desc['path'])
    with p.open('rb') as f:f.seek(desc['offset']);data=f.read(desc['bytes'])
    assert len(data)==desc['bytes'] and sha256(data).hexdigest()==desc['compressed_member_sha256']
    dec=zlib.decompressobj(16+zlib.MAX_WBITS);raw=dec.decompress(data)+dec.flush()
    assert dec.eof and not dec.unused_data and not dec.unconsumed_tail
    assert sha256(raw).hexdigest()==desc['decoded_sha256']
    value=json.loads(raw);assert raw==canonical(value);return value
def identity(args):
    refs={};add_pin(refs,{'path':args.gate,'sha256':args.gate_sha256});g=load(path_checked(args.gate))
    assert type(g['independent_fixed_O_audits_authorized']) is int and g['independent_fixed_O_audits_authorized']==1
    assert g['scope']==SCOPE and g['fixed_G_index']==1322606
    assert g['fixed_pair']==[278,665] and g['fixed_chart']=='rev/id'
    assert g['maximum_original_CellA_evaluations']==23 and g['positive_anchor_rows']==49 and g['physical_spans']==42
    assert g['new_linear_solve_LP_RREF_FS_anchor_kernel_Lean_authorized']==0 and g['automatic_retry_allowed'] is False
    assert g['other_case_mathematical_replay_authorized'] is False
    assert g['resource_limits']['elapsed_seconds']>0 and g['resource_limits']['closed_output_bytes']>0
    prep=inventory(refs,{'path':HERE.relative_to(ROOT).as_posix()+'/prepared-files.json','sha256':g['prepared_manifest_sha256']})
    rt=prep['runtime'];assert Path(sys.executable).resolve()==Path(rt['executable']).resolve()
    assert digest(Path(sys.executable))==rt['sha256'] and sys.version==rt['version'] and sys.flags.optimize==0
    for r in rt['additional_files']:assert digest(Path(r['path']))==r['sha256']
    assert g['producer_manifest']=={'path':PROD.relative_to(ROOT).as_posix()+'/files.json','sha256':PRODUCER_SHA}
    inventory(refs,g['producer_manifest'])
    assert g['producer_packet']=={'path':PROD.relative_to(ROOT).as_posix()+'/curvature-packet.json','sha256':PACKET_SHA}
    add_pin(refs,g['producer_packet'])
    for r in g['producer_endpoints']:add_pin(refs,r)
    return g,refs

def raw_dual(record,rows,pressure,weights,prior):
    dual=record['normalized_exact_reconstruction']['exact_dual']
    mu=[scalar(s) for s in dual['raw_row_weights']];assert len(mu)==305 and all(w>=0 for w in mu)
    balance=list(map(F,pressure+weights));cost=F(0)
    for w,(pos,group,rhs) in zip(mu,rows):
        for k,a in enumerate(pos):balance[k]+=w*a
        if group is not None:balance[10+group]-=w
        cost-=w*rhs
    assert len(balance)==52 and all(v==0 for v in balance)
    assert dual['checks']['valid'] is True and list(map(str,balance))==dual['checks']['full_balance']
    assert scalar(dual['checks']['raw_lower_bound'])==cost
    assert prior['passed'] is True and prior['fixed_G_index']==1322606
    expected=prior['fixed_case_math']['original_dual_rechecked']
    assert expected['valid'] is True and expected['cost']==str(cost) and expected['minus_target']==str(cost-TARGET)
    semantic={'rows':rows,'objective_position10':pressure,'objective_T42':weights,'target':TARGET}
    assert sha256(canonical(semantic)).hexdigest()==prior['fixed_case_math']['independent_raw_semantic_sha256']
    assert cost<TARGET;return mu,cost

def source_rows(source,cells,windows,saved,mu):
    components=[];intervals={};rid=155;all_guards=0
    for wi,(cell,window,rev) in enumerate(zip(cells,windows,[True,False])):
        cid=cell['exception_id'];cached=saved[cid]
        assert cached['cell_id']==cid and cached['state_sha256']==cell['state_sha256']
        for term,lines in window:
            ti=term['term_id'];i,j=term['edge'];L,U=term['original_term_bounds'];L0=term['original_L0']
            assert tuple(source['TS'][ti][:3])==(i,j,term['external_weight_numerator'])
            edge=(wi+8-j,wi+8-i) if rev else (wi+i,wi+j)
            lo=max(F(L,Q),F(17*(edge[1]-edge[0]),20));hi=F(U,Q)
            if edge in intervals:lo=max(lo,intervals[edge][0]);hi=min(hi,intervals[edge][1])
            assert lo<=hi;intervals[edge]=(lo,hi)
            components.append({'row_id':rid,'kind':'constant','physical_span':list(edge),'source_window':wi,'source_term':ti,'raw_dual_weight':str(mu[rid])});rid+=1
            present=[]
            for slot,(mass,p) in enumerate(zip([term['mass_first'],term['mass_second']],term['FS'][2:])):
                if not mass:continue
                assert mass>0 and p in source['pts'];word=source['pts'][p]
                vl=max(0,p-((word>>96)&1048575));vu=p+(word>>116)
                assert vu>0 and vl<=L<=p<=U<=vu and L0<=L
                present.append((p,vl,vu));all_guards+=1
                components.append({'row_id':rid,'kind':'anchor','physical_span':list(edge),'source_window':wi,
                    'cell_id':cid,'source_term':ti,'source_slot':slot,'source_original_positive_mass':mass,
                    'q_integer':p,'q_physical':str(F(p,Q)),'original_L0':L0,'original_guard':[vl,L,p,U,vu],
                    'original_state_sha256':cell['state_sha256'],'original_witness':cached['witness'],
                    'raw_dual_weight':str(mu[rid])});rid+=1
            assert len(lines)==1+len(present) and len(term['active_mokI_guards'])==len(present)
            for (p,vl,vu),guard in zip(present,term['active_mokI_guards']):
                assert guard['original_anchor']==p and guard['valid_lower']==vl and guard['valid_upper']==vu and guard['guard_passed'] is True
    assert rid==305 and len(components)==150 and len(intervals)==42 and all_guards==82
    active=[r for r in components if r['kind']=='anchor' and scalar(r['raw_dual_weight'])>0]
    assert len(active)==49;return components,active,intervals

def cover(params,lo,hi):
    assert lo<=hi;reg=params['REG']
    for k,chain in enumerate(reg['chains']):
        if not chain:continue
        a=(reg['A']>>(20*k))&1048575;b=(reg['B']>>(20*k))&1048575
        if a<=lo<=hi<=b:
            selected=[c for c in reg['cells'] if c['chain']==k and c['U']>=lo and c['L']<=hi]
            assert selected and selected[0]['L']<=lo and hi<=selected[-1]['U']
            assert all(x['U']==y['L'] for x,y in zip(selected,selected[1:]));return selected
    return None

def curvature(independent,params,active,intervals,packet):
    cache={};weighted=[];cell_reviews=[]
    reported_cells={(c['L'],c['U']):c for c in packet['selected_original_CellA_cells']}
    assert len(reported_cells)==len(packet['selected_original_CellA_cells'])==23
    for row in active:
        edge=tuple(row['physical_span']);lo,hi=intervals[edge];q=row['q_integer']
        hlo=min(F(q),Q*lo);hhi=max(F(q),Q*hi);selected=cover(params,hlo,hhi)
        assert selected is not None
        entries=[]
        for c in selected:
            key=(c['L'],c['U'])
            if key not in cache:
                assert len(cache)<23
                value=independent.evaluate(params,*key);assert key in reported_cells
                for name,datum in value.items():assert reported_cells[key][name]==datum,(key,name)
                cache[key]=value;cell_reviews.append(value)
            entries.append(cache[key])
        m=min(scalar(v['m_quantitative']) for v in entries);assert m>=0
        coefficient=scalar(row['raw_dual_weight'])*K*m/2
        weighted.append({**row,'joint_direct_span_interval':list(map(str,[lo,hi])),
            'required_hull_in_Q_units':list(map(str,[hlo,hhi])),
            'coverage':'complete_original_REG_chain','original_cells':selected,'m':str(m),'c_raw':str(coefficient)})
    assert set(cache)==set(reported_cells) and len(cache)==packet['original_REG_cell_queries']==23
    assert weighted==packet['weighted_anchor_rows']
    return weighted,sorted(cell_reviews,key=lambda r:(r['L'],r['U']))

def payments(weighted,intervals,packet):
    totals=defaultdict(lambda:[F(0),F(0),F(0)])
    for r in weighted:
        c=scalar(r['c_raw']);q=scalar(r['q_physical']);assert c>=0
        t=totals[tuple(r['physical_span'])];t[0]+=c;t[1]+=c*q;t[2]+=c*q*q
    variance=F(0);vproof=[]
    for edge,(C,B,A) in sorted(totals.items()):
        if not C:continue
        qbar=B/C;V=A-B*B/C;assert V>=0;lo,hi=intervals[edge]
        clamp=lo if qbar<lo else hi if qbar>hi else qbar
        value=V+C*(clamp-qbar)**2;variance+=value
        vproof.append({'physical_span':list(edge),'C':str(C),'qbar':str(qbar),'variance':str(V),
            'closed_interval':list(map(str,[lo,hi])),'clamp':str(clamp),'uniform_payment':str(value)})
    assert vproof==packet['variance_proof'] and str(variance)==packet['variance_clamp_payment']
    lp=packet['laplace_proof'];point=list(map(scalar,lp['p_star']));assert len(point)==10
    residual=[F(0)]*10;value=F(0)
    for r in weighted:
        i,j=r['physical_span'];c=scalar(r['c_raw']);q=scalar(r['q_physical'])
        delta=point[j]-point[i]-q;residual[i]-=c*delta;residual[j]+=c*delta;value+=c*delta*delta
    assert all(v==0 for v in residual) and list(map(str,residual))==lp['full10_stationarity_residual']
    assert value>=0 and str(value)==lp['Q_p_star']==packet['laplace_payment']
    # Full stationarity is sufficient for the global square-completion identity.
    # The supplied gauge partition and linear solve are not used as proof.
    assert lp['linear_solve_calls']==1
    return variance,value,{'saved_point_only':True,'full10_stationarity_residual':list(map(str,residual)),
        'Q_p_star':str(value),'new_linear_system_solves':0,
        'uniform_identity':'Q(p)=Q(p_star)+sum c_r*(B_r*(p-p_star))^2'}

def execute(args):
    for n in ['started.json','independent-review.json','failure.json','cell-replay.json']:assert not (HERE/n).exists()
    start=time.monotonic();stage='identity';refs={}
    try:
        g,refs=identity(args);save('started.json',{'pid':os.getpid(),'scope':SCOPE,'inputs_sha256':refs})
        packet=load(PROD/'curvature-packet.json')
        assert packet['G_index']==1322606 and packet['pair']==[278,665] and packet['chart']=='rev/id'
        assert packet['raw_target']==str(TARGET)
        own=own_import(OWN,'O_own_frozen_v1');a=own_import(OWN_A,'O_own_frozen_A')
        independent=own_import(HERE/'source_cell.py','O_independent_SZ_pair_operators')
        stage='two_original_source_FS_and_fixed_raw_dual'
        readout=load(N2/'first-Below-readout.json');record=member(readout['proof_record'])
        assert record['G_index']==1322606 and record['pair']==[278,665] and record['chart']=='rev/id' and record['outcome']=='Below'
        saved={cid:member(record['original_components'][str(cid)]) for cid in record['pair']}
        source=a.load_source();allcells=own.load_cells();cells=[allcells[cid] for cid in [278,665]]
        history=own.load_history({r['root'] for r in cells})
        windows=[own.original(a,source,row,history,saved[row['exception_id']]) for row in cells]
        rows,pressure,weights,members=own.model_from_source(source,cells,windows,2)
        assert len(rows)==305 and len(weights)==42
        prior=load(ROOT/'research-goal-20261018-stageN2-independent-below/independent-review.json')
        mu,cost=raw_dual(record,rows,pressure,weights,prior)
        components,active,intervals=source_rows(source,cells,windows,saved,mu)
        assert components==packet['all_original_component_rows']
        assert packet['physical_span_intervals']==[{'edge':list(e),'interval':list(map(str,v))} for e,v in sorted(intervals.items())]
        assert packet['frozen_raw_dual_cost']==str(cost) and packet['raw_dual_deficit']==str(TARGET-cost)
        stage='independent_23_original_SZ_CellA_replays'
        params=independent.read_parameters(source['text'])
        weighted,cell_reviews=curvature(independent,params,active,intervals,packet)
        stage='variance_saved_point_stationarity_and_uniform_payment'
        variance,network,network_review=payments(weighted,intervals,packet)
        payment=max(variance,network);margin=cost+payment-TARGET
        assert str(payment)==packet['chosen_uniform_payment']
        assert str(cost+payment)==packet['uniform_raw_lower_bound'] and str(margin)==packet['minus_target']
        assert margin>0 and packet['conditional_fixed_pair_floor_closes'] is True
        assert packet['all_source_curvature_cells_preexisting_REG'] is True
        assert packet['new_subdivision_kernel_anchors_FS_LP_or_Lean_runs']==0
        save('cell-replay.json',{'schema':'O-independent-SZ-pair-23-cell-replay-v1','cells':cell_reviews})
        after={name:digest(path_checked(name)) for name in refs};assert after==refs
        assert time.monotonic()-start<g['resource_limits']['elapsed_seconds']
        save('independent-review.json',{'schema':'O-independent-fixed-curvature-review-v1','passed':True,
            'pid':os.getpid(),'seconds':time.monotonic()-start,'scope':SCOPE,'fixed_G_index':1322606,
            'pair':[278,665],'chart':'rev/id','inputs_sha256_start':refs,'inputs_sha256_end':after,
            'source_original_FS_cells_rebuilt':2,'original_positive_mass_anchor_guards_checked':82,
            'raw_dual_rows':305,'full_raw_balance_coordinates':52,'raw_dual_cost':str(cost),
            'independent_SZ_pair_CellA_cells':23,'positive_anchor_rows':49,'physical_spans':42,
            'all_selected_integer_intermediates_match':True,'variance_clamp_payment':str(variance),
            'network_payment':str(network),'network_review':network_review,'chosen_uniform_payment':str(payment),
            'raw_margin':str(margin),'conditional_fixed_pair_floor_closes':True,
            'new_linear_solve_LP_RREF_FS_anchor_kernel_Lean_runs':0,'producer_code_imports':0,
            'all_2375_commit_metadata_replayed_again':False,'other_case_math_replayed':False,
            'quantitative_CellA_and_strong_tangent_Lean_bridge_pending':True,
            'global_floor_or_new_kappa_proven':False,'source_runtime_submission_budget':'unknown'})
        print(json.dumps({'passed':True,'fixed_G_index':1322606,'original_CellA_cells':23,
            'positive_anchor_rows':49,'conditional_fixed_pair_closes':True}),flush=True)
    except BaseException as exc:
        save('failure.json',{'stage':stage,'error':repr(exc),'traceback':traceback.format_exc(),
            'seconds':time.monotonic()-start,'scope':SCOPE,'automatic_retry':False});raise

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--execute-authorized-audit-once',action='store_true')
    p.add_argument('--gate');p.add_argument('--gate-sha256');a=p.parse_args()
    assert a.execute_authorized_audit_once and a.gate and a.gate_sha256;execute(a)
if __name__=='__main__':main()
