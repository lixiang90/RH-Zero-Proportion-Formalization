"""One fixed read-only integer size audit on B1187 original margins.

Sorted/bisect counts are cross-checked by a separate full integer double loop.
No geometry, FS, point, kernel, LP, Lean or per-pair table is evaluated.
"""
from pathlib import Path
from hashlib import sha256
from collections import Counter
from bisect import bisect_left,bisect_right
import gzip
import json
import os
import sys
import time
import traceback

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
B=ROOT/'research-goal-20261018-stageB-classification'
BI=ROOT/'research-goal-20261018-stageB-independent/audit-files.json'
B_PIN='3f9408f2cf1ceae12339456da034d9e8f175f828cf2d53a652339ee79eec89ad'
BI_PIN='e6458883bc7588a2302afe435c3b79a08c9236bb895ec3010655024c767d7288'
N=1187
Q=32768
V=10**10
R=1024
KAPPA=Q*V*R
MAX_SECONDS=60
MAX_BYTES=2000000

def pin(p):
    h=sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''):h.update(block)
    return h.hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def rel(p):return p.relative_to(ROOT).as_posix()
def write_new(p,x):
    with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(x,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())

def inputs():
    refs={rel(Path(__file__)):pin(Path(__file__)),rel(HERE/'run_once.py'):pin(HERE/'run_once.py')}
    for manifest,expected in [(B/'files.json',B_PIN),(BI,BI_PIN)]:
        assert pin(manifest)==expected;refs[rel(manifest)]=expected
        obj=load(manifest)
        for field in ['files','package_files','read_only_dependencies','dependency_files','dependencies']:
            for row in obj.get(field,[]):
                p=ROOT/row['path'];assert p.is_relative_to(ROOT) and pin(p)==row['sha256']
                if 'bytes' in row:assert p.stat().st_size==row['bytes']
                if row['path'] in refs:assert refs[row['path']]==row['sha256']
                refs[row['path']]=row['sha256']
    a=load(B/'classification.json')
    assert a['passed'] and a['classification_counts']['exception']==N
    assert a['original_cN']==893616123055294719 and a['tau_numerator']==893916123055294719
    delta=a['tau_numerator']-a['original_cN'];threshold=KAPPA*delta
    assert delta==3*10**14 and threshold==int(a['integer_debit'])
    p=ROOT/a['outputs']['exceptions']['path'];assert pin(p)==a['outputs']['exceptions']['sha256']
    margins=[]
    with gzip.open(p,'rt',encoding='ascii') as f:
        for line in f:
            row=json.loads(line)
            assert row['exception_id']==len(margins)
            m=int(row['original_margin'])
            assert 0<=m<threshold and int(row['tau_margin'])==m-threshold
            margins.append(m)
    assert len(margins)==N
    return refs,threshold,delta,margins

def main():
    assert __debug__ and sys.argv[1:]==['--execute-fixed-size-audit']
    assert not any((HERE/n).exists() for n in ['started.json','audit.json','failure.json'])
    t=time.monotonic();stage='input_pins';refs={}
    try:
        refs,threshold,delta,margins=inputs()
        write_new(HERE/'started.json',{'schema':'fixed-B1187-margin-size-start-v1','pid':os.getpid(),
            'time_unix':time.time(),'audit_attempt':1,'inputs_sha256':refs,'geometry_or_solver_calls':0})
        print(json.dumps({'stage':'integer_size_audit_live','pid':os.getpid()}),flush=True)
        stage='sorted_bisect_count';sort_start=time.monotonic();ordered=sorted(margins)
        under=[bisect_left(ordered,threshold-m) for m in margins]
        equal=[bisect_right(ordered,threshold-m)-bisect_left(ordered,threshold-m) for m in margins]
        paid=[N-u for u in under];npairs=N*N
        under_count=sum(under);paid_count=sum(paid);equal_count=sum(equal)
        assert under_count+paid_count==npairs and paid_count>=equal_count
        sorted_seconds=time.monotonic()-sort_start
        # Deliberately independent O(n^2) counting, no bisect or sorted lists.
        stage='independent_integer_double_loop';quad_start=time.monotonic()
        row_under=[0]*N;col_under=[0]*N;quad_paid=quad_under=quad_equal=0
        diag_under=diag_paid=0
        for i,mi in enumerate(margins):
            if time.monotonic()-t>MAX_SECONDS:raise TimeoutError('60_second_limit')
            for j,mj in enumerate(margins):
                s=mi+mj
                if s<threshold:
                    quad_under+=1;row_under[i]+=1;col_under[j]+=1
                    if i==j:diag_under+=1
                else:
                    quad_paid+=1
                    if s==threshold:quad_equal+=1
                    if i==j:diag_paid+=1
        quad_seconds=time.monotonic()-quad_start
        assert under_count==quad_under and paid_count==quad_paid and equal_count==quad_equal
        assert row_under==col_under==under and diag_under+diag_paid==N
        assert 4*(paid_count+under_count)==4*N*N==5635876
        hist=Counter(under);freq=Counter(margins)
        after={name:pin(ROOT/name) for name in refs};assert refs==after
        result={'schema':'fixed-B1187-exact-margin-size-audit-v1','passed':True,'pid':os.getpid(),
            'seconds':time.monotonic()-t,'audit_executions':1,'inputs_sha256_start':refs,'inputs_sha256_end':after,
            'N':N,'KAPPA':KAPPA,'delta_numerator':delta,'payment_threshold':str(threshold),
            'threshold_formula':'(32768*10^10*1024)*(tauNum-c9Num)',
            'comparison':'underpaid iff Mi+Mj<T, paid iff Mi+Mj>=T; equality pays',
            'ordered_pairs_include_diagonal':True,'ordered_pairs_per_orientation':npairs,
            'scalar_paid_ordered_pairs_per_orientation':paid_count,
            'underpaid_ordered_pairs_per_orientation':under_count,
            'equal_threshold_ordered_pairs_per_orientation':equal_count,
            'paid_strictly_above_threshold_per_orientation':paid_count-equal_count,
            'four_independent_orientations':4,'all_oriented_cases':4*npairs,
            'scalar_paid_oriented_cases':4*paid_count,'underpaid_oriented_cases':4*under_count,
            'diagonal_underpaid_per_orientation':diag_under,'diagonal_paid_per_orientation':diag_paid,
            'margin_min':str(min(margins)),'margin_max':str(max(margins)),
            'unique_margin_count':len(freq),
            'underpaid_count_histogram_per_left_cell':{str(k):v for k,v in sorted(hist.items())},
            'underpaid_count_histogram_per_right_cell':{str(k):v for k,v in sorted(Counter(col_under).items())},
            'underpaid_per_left_cell':under,'underpaid_per_right_cell':col_under,
            'per_left_and_right_distributions_equal_by_direct_check':True,
            'minimum_underpaid_partners_per_cell':min(under),
            'maximum_underpaid_partners_per_cell':max(under),
            'cells_with_zero_underpaid_partners':hist[0],
            'worst_case_unresolved_geometry_cases_without_any_geometric_reduction':4*under_count,
            'worst_case_cases_involving_one_fixed_left_cell_across4orientations':4*max(under),
            'worst_case_is_a_combinatorial_upper_bound_not_a_runtime_prediction':True,
            'algorithms':{'sort_and_bisect_seconds':sorted_seconds,'independent_O_n_squared_seconds':quad_seconds,
                'integer_pair_comparisons_in_crosscheck':npairs,'all_counts_and_each_left_right_count_equal':True},
            'geometry_queries':0,'FS_queries':0,'kernel_queries':0,'new_points':0,'optimizer_calls':0,'Lean_runs':0,
            'new_energy_or_joint_floor_claim':False,'new_unconditional_zero_proportion_proven':False,
            'full_source_and_runtime_budget':'unknown','website_submission_ready':False,
            'scope':'Read-only size audit of one frozen margin multiset. No per-pair geometry/FS/energy computation or certificate table; no conclusion that underpaid cases need LP or are actually feasible.'}
        assert time.monotonic()-t<=MAX_SECONDS
        write_new(HERE/'audit.json',result)
        assert sum(p.stat().st_size for p in HERE.iterdir() if p.is_file())<=MAX_BYTES
        print(json.dumps({k:result[k] for k in ['passed','pid','seconds','scalar_paid_ordered_pairs_per_orientation',
            'underpaid_ordered_pairs_per_orientation','scalar_paid_oriented_cases','underpaid_oriented_cases',
            'unique_margin_count','minimum_underpaid_partners_per_cell','maximum_underpaid_partners_per_cell']}),flush=True)
    except BaseException as exc:
        write_new(HERE/'failure.json',{'passed':False,'stage':stage,'pid':os.getpid(),
            'seconds':time.monotonic()-t,'error':repr(exc),'traceback':traceback.format_exc(),
            'inputs_sha256_start':refs,'automatic_retry_allowed':False})
        raise

if __name__=='__main__':main()
