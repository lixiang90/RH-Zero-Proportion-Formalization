"""Independent stdlib read-only audit of fixed-cell coverage relevance.

Verify immutable database bytes, exported records/frontier, target subtree
topology and absence from the new journal. No historical math replay,
search, solver, oracle or Lean. --write-receipt creates an absent receipt.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse,hashlib,json,sqlite3,time
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent;OUT=HERE/'independent-replay.json'
SRC=ROOT/'research-goal-20261017-global-relevance-audit/global-relevance.json'
EXPECTED='0053de28579a0bd8646df4dedb14d10735e5324756f415b58f523bc08377ad85'
def sha(p):
    h=hashlib.sha256()
    with p.open('rb')as f:
        for b in iter(lambda:f.read(4*1024*1024),b''):h.update(b)
    return h.hexdigest()
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write-receipt',action='store_true');args=ap.parse_args()
    if args.write_receipt:assert not OUT.exists()
    began=time.monotonic();assert sha(SRC)==EXPECTED;p=json.loads(SRC.read_bytes());assert p['passed']
    pins={**p['source_sha256'],SRC.relative_to(ROOT).as_posix():EXPECTED,Path(__file__).relative_to(ROOT).as_posix():sha(Path(__file__))}
    for n,h in pins.items():assert sha(ROOT/n)==h
    target=p['target'];assert target=='r001000001000100110011001'and p['floor']=='11/1250'
    dbpath=ROOT/p['database_path'];size=dbpath.stat().st_size;before=sha(dbpath)
    assert size==p['database_bytes']==1215361024 and before==p['database_sha256_before']==p['database_sha256_after']=='ceb41e0e34b79e92bff8bf658b91510be8c6bc2da4fe527d5bbc1200f5866296'
    progress=json.loads((ROOT/'research-goal-20261016/sqlite-bounded143004/progress.json').read_bytes());assert progress['database_sha256']==before and progress['database_bytes']==size
    con=sqlite3.connect(dbpath.resolve().as_uri()+'?mode=ro',uri=True);con.execute('PRAGMA query_only=1');assert con.execute('PRAGMA query_only').fetchone()==(1,)
    front=[]
    for pos,path,payload,dig in con.execute('SELECT position,path,payload,digest FROM frontier ORDER BY position'):
        assert hashlib.sha256(payload).hexdigest()==dig;value=json.loads(payload);assert value['path']==path
        front.append({'position':pos,'path':path,'payload_sha256':dig,'payload':value,'payload_bytes':len(payload)})
    assert front==p['current_frontier']and len(front)==progress['final_state']['unresolved_count']==17
    fpaths=[r['path']for r in front];assert len(set(fpaths))==17
    assert all(not(a.startswith(b)or b.startswith(a))for i,a in enumerate(fpaths)for b in fpaths[i+1:])
    related=[s for s in fpaths if s.startswith(target)or target.startswith(s)];assert related==p['related_frontier']==[]
    records=[]
    for section,pos,path,payload,dig in con.execute('SELECT section,position,item_key,payload,digest FROM entries WHERE substr(item_key,1,?)=? ORDER BY section,position',(len(target),target)):
        assert path.startswith(target)and hashlib.sha256(payload).hexdigest()==dig
        records.append({'section':section,'position':pos,'path':path,'payload_sha256':dig,'payload_bytes':len(payload),'payload':json.loads(payload)})
    assert records==p['target_records']and len(records)==17
    leaves={r['path']for r in records if r['section']=='accepted'};branches={r['path']for r in records if r['section']=='branches'}
    assert len(leaves)==5 and len(branches)==4 and sorted(leaves)==p['binary_subtree_leaves']and sorted(branches)==p['binary_subtree_branches']and leaves.isdisjoint(branches)
    stack=[target];seen=set()
    while stack:
        s=stack.pop();assert s not in seen;seen.add(s)
        if s in branches:stack.extend([s+'1',s+'0'])
        else:assert s in leaves
    assert seen==leaves|branches
    kraft=sum(F(1,2**(len(s)-len(target)))for s in leaves);assert kraft==1 and p['kraft_sum']=='1'
    summary={s:{'records':sum(r['section']==s for r in records),'payload_bytes':sum(r['payload_bytes']for r in records if r['section']==s)}for s in sorted({r['section']for r in records})}
    assert summary==p['target_record_summary']
    journal=con.execute('SELECT sequence,path FROM node_log WHERE substr(path,1,?)=? ORDER BY sequence',(len(target),target)).fetchall();assert journal==p['matching_new_journal_nodes']==[]
    assert sorted(r['position']for r in records if r['section']=='accepted')==list(range(23790,23795))
    # Inventory frontier projections are checked, not the baseline's global
    # ancestor byte/count totals, which are not needed for this conclusion.
    assert len(p['ancestor_record_inventory'])==len(target)
    for i,r in enumerate(p['ancestor_record_inventory']):
        assert r['path']==target[:i+1]and r['frontier_descendants']==[s for s in fpaths if s.startswith(r['path'])]
    assert p['ancestor_record_inventory'][-1]['record_counts_and_JSON_bytes']=={k:[v['records'],v['payload_bytes']]for k,v in summary.items()}
    assert not p['exact_sextic_result_closes_new_frontier']and not p['historical_baseline_mathematics_replayed']and not p['source_compression_benefit_from_replacing_this_subtree_proved']
    con.close();assert sha(dbpath)==before and dbpath.stat().st_size==size
    for n,h in pins.items():assert sha(ROOT/n)==h
    out={'scope':__doc__,'passed':True,'source_sha256_start':pins,'source_sha256_end':pins,'all_inputs_unchanged':True,
        'database_path':p['database_path'],'database_bytes':size,'database_sha256_before':before,'database_sha256_after':before,'database_readonly_and_queryonly':True,
        'target':target,'floor':p['floor'],'exported_target_records_checked_against_DB':17,'frontier_records_checked_against_DB':17,'frontier_prefix_antichain':True,'related_frontier_count':0,
        'binary_subtree_branches':4,'binary_subtree_leaves':5,'complete_binary_prefix_tree':True,'kraft_sum':'1','accepted_positions':list(range(23790,23795)),'target_record_summary':summary,
        'matching_new_journal_nodes':0,'ancestor_frontier_projections_checked':True,'full_ancestor_record_counts_recomputed':False,'fixed_cell_already_closed_in_imported_baseline':True,
        'historical_baseline_mathematics_replayed':False,'baseline_closure_soundness_reproved':False,'new_frontier_closure':False,'source_compression_benefit_proved':False,
        'producer_imports':0,'solver_calls':0,'eigh_calls':0,'Lean_invocations':0,'new_points':0,'global_cover_completed':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-began}
    if args.write_receipt:OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'passed':True,'target_records':17,'branches':4,'leaves':5,'frontier':17,'related_frontier':0,'seconds':out['seconds']}),flush=True)
if __name__=='__main__':
    assert __debug__
    main()
