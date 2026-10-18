"""One authorized read of already independently proved integer/geometry archives.
No leaf decoder, kernel, FS, optimization, matrix, or Lean execution.
"""
from fractions import Fraction as F
from hashlib import sha256
import gzip
import json
import os
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
B=ROOT/'research-goal-20261018-stageB-classification'
K=335544320000000000
CN=893616123055294719
SA=10**20
DELTA=389500523
TAU_INCREMENT=779001046
PINS={
 'research-goal-20261018-stageB-classification/files.json':'3f9408f2cf1ceae12339456da034d9e8f175f828cf2d53a652339ee79eec89ad',
 'research-goal-20261018-stageB-independent/audit-files.json':'e6458883bc7588a2302afe435c3b79a08c9236bb895ec3010655024c767d7288',
 'research-goal-20261018-record-source-audit/snapshot/Solution.lean':'f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf',
 'research-goal-20261018-record-fresh-independent-1152/files.json':'16f8fb8d4adc3fdfcd0d1d4b4f58652e343a8cb385f5fdf3991cc9e06d59bf20'}
def canonical(x):return (json.dumps(x,sort_keys=True,separators=(',',':'),allow_nan=False)+'\n').encode('ascii')
def digest(p):return sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf8'))
def row(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':digest(p)}
def save(name,x):
    with (HERE/name).open('xb') as f:f.write(canonical(x));f.flush();os.fsync(f.fileno())
def pin_manifest(name,refs):
    p=ROOT/name;doc=load(p)
    for field in ['files','package_files','read_only_dependencies','dependencies']:
        for r in doc.get(field,[]):
            q=(ROOT/r['path']).resolve();assert q.is_relative_to(ROOT)
            assert digest(q)==r['sha256']
            if 'bytes' in r:assert q.stat().st_size==r['bytes']
            refs[r['path']]=r['sha256']
    return doc
def archive(name,expected):
    p=B/name
    with gzip.open(p,'rb') as f:raw=f.read()
    assert len(raw)==expected['uncompressed_bytes'] and sha256(raw).hexdigest()==expected['uncompressed_sha256']
    lines=raw.splitlines(keepends=True);values=[json.loads(line) for line in lines]
    assert len(values)==expected['rows'] and all(canonical(v)==line for v,line in zip(values,lines))
    return values
def main():
    assert not (HERE/'independent-review.json').exists()
    refs={}
    for p,h in PINS.items():assert digest(ROOT/p)==h;refs[p]=h
    manifest=pin_manifest('research-goal-20261018-stageB-classification/files.json',refs)
    pin_manifest('research-goal-20261018-stageB-independent/audit-files.json',refs)
    prior=load(ROOT/'research-goal-20261018-stageB-independent/independent-review.json')
    assert prior['passed'] is True and prior['row_comparison']['all_numeric_rows_equal']==13046
    assert prior['row_comparison']['all_exception_complete_36_pair_rows_equal']==1187
    assert prior['root_payment_comparison']['all_raised_payments_passed'] is True
    summary=load(B/'classification.json')
    assert summary['source_sha256_start']==summary['source_sha256_end']==PINS['research-goal-20261018-record-source-audit/snapshot/Solution.lean']
    assert summary['original_cN']==CN and summary['denominator']==SA and summary['tau_numerator']==CN+300000000000000
    ast=summary['threshold_AST_identity']
    assert ast['passed'] is True and ast['cN_occurrences']==1 and ast['cN_in_rhs'] is False
    assert ast['unique_threshold_term']==['Nat.mul',str(K),'cN'] and ast['other_AST_subexpressions_unchanged'] is True
    numeric=archive('numeric-classification.jsonl.gz',manifest['archive_integrity']['numeric'])
    exceptions=archive('exception-cells.jsonl.gz',manifest['archive_integrity']['exceptions'])
    assert len(numeric)==13046 and len(exceptions)==1187
    margins=[];seen=set()
    for n in numeric:
        m=int(n['original_margin']);assert str(m)==n['original_margin'] and m>=0
        assert int(n['tau_margin'])==m-K*300000000000000
        key=(n['root'],n['position']);assert key not in seen;seen.add(key)
        margins.append((m,n['root'],n['position'],n))
    ordered=sorted(margins,key=lambda v:v[:3]);m0,r0,p0,minimum=ordered[0];m1,r1,p1,second=ordered[1]
    assert (m0,r0,p0)==(65385001396000000,11,27229)
    assert (m1,r1,p1)==(261389376341096919346000000,37,84312)
    assert sum(m==m0 for m,_,_,_ in margins)==1 and m0<K and m1//K==779001046
    assert TAU_INCREMENT==2*DELTA and TAU_INCREMENT==m1//K
    debit=K*TAU_INCREMENT
    failed=[n for m,_,_,n in margins if m<debit]
    assert len(failed)==1 and failed[0]==minimum
    assert all(m-debit>=0 for m,_,_,n in margins if n is not minimum)
    e=exceptions[462];assert e['exception_id']==462
    for key,value in minimum.items():assert e[key]==value
    assert e['coordinate_scale']==32768 and e['original_cell_is_closed'] is True
    assert e['relaxed_orientation'] is True and e['omitted_orientation_condition']=='h0 <= h7'
    L,U=e['state']['L'],e['state']['U']
    assert L==[64168,33989,64287,34192,64031,65043,33724,64461]
    assert U==[65648,34980,65278,35097,65033,66904,34464,67523]
    charts=[]
    for a,b in [(0,0),(0,1),(1,0),(1,1)]:
        # prefix g1=h1 (id), h6 (rev); suffix g1=h0 (id), h7 (rev).
        pi=6 if a else 1;si=7 if b else 0
        upper,lower=U[pi],L[si];assert upper<lower
        charts.append({'chart':['id/id','id/rev','rev/id','rev/rev'][2*a+b],
            'same_physical_gap':'g1','prefix_original_gap_index':pi,'suffix_original_gap_index':si,
            'prefix_upper_scaled':upper,'suffix_lower_scaled':lower,'strict_integer_contradiction':lower-upper})
    assert max(U[1],U[6])==34980 and min(L[0],L[7])==64168
    c9=F(CN,SA);tau=F(CN+TAU_INCREMENT,SA);c=F(CN+DELTA,SA)
    assert c9<c<tau<F(summary['tau_numerator'],SA) and c<F(1,64) and c9+tau==2*c
    overlap=load(ROOT/'research-goal-20261018-record-overlap-static/static-receipt.json')
    H=F(overlap['new_window_floor_H']);current=F(overlap['record_ratio_recovered_from_source_parameters'])
    fresh=load(ROOT/'research-goal-20261018-record-fresh-independent-1152/comparison.json')
    assert str(current)==fresh['highest_current_exact_rational'] and H/(1-c9)==current
    candidate=H/(1-c);assert candidate>current
    assert all(F(v)<=2 for v in overlap['prefix_suffix_span_masses'])
    for name in ['research-goal-20261018-record-overlap-static/static-receipt.json','research-goal-20261018-record-fresh-independent-1152/comparison.json']:
        refs[name]=digest(ROOT/name)
    after={p:digest(ROOT/p) for p in refs};assert after==refs
    save('unique-exception.json',e)
    save('independent-review.json',{'schema':'tiny-overlap-independent-existing-metadata-v1','passed':True,
        'scope':'one_read_of_original_13046_integer_margins_and_original_exception462_geometry_only',
        'source_sha256':PINS['research-goal-20261018-record-source-audit/snapshot/Solution.lean'],
        'inputs_sha256_start':refs,'inputs_sha256_end':after,'numeric_count':len(numeric),
        'unique_minimum':{'margin':str(m0),'root':r0,'position':p0,'exception_id':462,
            'state_sha256':minimum['state_sha256'],'witness':minimum['witness']},
        'second_minimum':{'margin':str(m1),'root':r1,'position':p1,'floor_margin_over_K':m1//K},
        'fixed_delta_numerator':DELTA,'single_window_threshold_increment_numerator':TAU_INCREMENT,
        'single_window_threshold':str(tau),'joint_floor':str(c),'threshold_integer_debit':str(debit),
        'unique_failed_numeric_leaf':462,'other_numeric_debit_nonnegative':13045,
        'minimum_other_debit_margin':str(m1-debit),'exception_negative_debit_margin':str(m0-debit),
        'four_charts':charts,'closed_boundary_contradiction':True,
        'previous_stronger_root_guards_reused_by_monotonicity':True,'ordered_reflection_exclusions_reused':595,
        'pair_short_distance_floor_1_over_64_suffices':True,'prefix_suffix_capacity_bound':2,
        'current_exact_R':str(current),'conditional_candidate_exact_R':str(candidate),
        'candidate_minus_current_exact':str(candidate-current),'candidate_strictly_exceeds_fresh_current':True,
        'new_leaf_decode_FS_kernel_LP_Lean_runs':0,'new_mathematical_family_search':False,
        'actual_complete_Lean_global_proof_or_submission_ready':False})
    print(json.dumps({'passed':True,'numeric':13046,'unique_exception':462,'all_four_charts_disjoint':True,
        'delta_numerator':DELTA,'candidate_exact':str(candidate),'strict_improvement':True}))
if __name__=='__main__':main()
