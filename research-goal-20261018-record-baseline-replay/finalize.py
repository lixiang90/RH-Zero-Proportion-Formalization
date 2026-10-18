"""Join closed Stage-A receipts and freeze files; no walk/kernel execution."""
from pathlib import Path
from hashlib import sha256
import ast
import json
import re

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent


def h(p):return sha256(p.read_bytes()).hexdigest()


def main():
    dest=HERE/'stage-a-summary.json';manifest=HERE/'files.json'
    assert not dest.exists() and not manifest.exists()
    def load(name):return json.loads((HERE/name).read_bytes())
    packing=load('packing-parser-v3.json');cross=load('packing-crosscheck.json')
    baseline=load('baseline-replay.json');wz=load('root-wz-replay.json');trace=load('trace-integrity.json')
    assert all(d['passed'] for d in [packing,cross,baseline,wz,trace])
    source=ROOT/'research-goal-20261018-record-source-audit/snapshot/Solution.lean'
    sourcehash='f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf'
    assert h(source)==sourcehash==packing['source_sha256_start']==packing['source_sha256_end']
    assert baseline['source_sha256_start']==baseline['source_sha256_end']==sourcehash
    for keys,d in [('script_input_sha256',baseline),('source_and_scripts_sha256',wz)]:
        assert d[keys+'_start']==d[keys+'_end']
        for name,value in d[keys+'_start'].items():assert h(ROOT/name)==value,name
    assert h(HERE/'baseline-events.jsonl.gz')==trace['gzip_sha256']==baseline['trace']['gzip_sha256']
    assert cross['producer_receipt_sha256']==h(HERE/'packing-parser-v3.json')
    source_text=source.read_text(encoding='utf-8')
    wd={int(a):int(b) for a,b in re.findall(r'\bdef WD(\d+) : ℕ → ℕ := rdw WL(\d+)\s*$',source_text,re.M)}
    assert wd=={i:i for i in range(48)}
    # Extra literal schema checks only, no leaf traversal.
    cert=source_text[source_text.index('namespace AMW.Cert.PC9QB6M\n'):source_text.index('end AMW.Cert.PC9QB6MData')]
    def lit(name):
        rows=re.findall(r'\bdef '+name+r'\s*:[^\n]*:= (\[[^\n]*\])',cert)
        assert len(rows)==1,name
        return ast.literal_eval(rows[0])
    TS,PR,SL,ADJ=[lit(name) for name in ['TS','PR','SL','ADJ']]
    spans=[(r,r+1) for r in range(8)]+PR
    assert len(PR)==28 and len(set(PR))==28 and all(0<=i and i+2<=j<=8 for i,j in PR)
    assert all(0<=i<j<=8 and (j==i+1 or (k<len(PR) and PR[k]==(i,j))) for i,j,a,k in TS)
    assert len(SL)==81 and all(SL[9*i+j]==spans.index((i,j)) for i in range(9) for j in range(i+1,9))
    assert len(ADJ)==8 and all(tuple(TS[k][:2])==(r,r+1) for r,k in enumerate(ADJ))
    counts={key:baseline['derived_counts'].get(key,0) for key in
            ['nodes','branches','terminal_leaves','numeric_leaves','reflection_leaves','farkas_leaves','direct_AST_comparisons','active_mokI_checks','term_decode_checks']}
    assert counts['nodes']==counts['branches']+counts['terminal_leaves']==27234
    assert counts['numeric_leaves']==counts['direct_AST_comparisons']==13046
    assert counts['reflection_leaves']==595 and counts['farkas_leaves']==0
    assert wz['all_original_true_COV_WZ_integer_guards_passed']
    assert wz['existing_COV_true_guard_count']==sum(1 for r in baseline['root_outside_contract']['rows'] if r['kind']=='cover' and r['truth'])
    assert baseline['root_outside_contract']['topology_and_tail_small_arithmetic_passed']
    assert baseline['ready_contract_counts']['nested_cursor_checks']==70
    assert baseline['ready_contract_counts']['parent_cursor_checks']==48
    summary={'schema':'new-record-original-floor-StageA-production-summary-v1','producer_stage_A_complete':True,
             'independent_full_mathematical_review_pending':True,'source_sha256':sourcehash,
             'unchanged_original_cN':893616123055294719,'objective_scale':10**20,
             'packing_count':137,'all137_canonical_inverses_and_independent_decoder_match':True,
             'complete_root_count':48,'all_original_root_end_cursors_equal':True,'derived_counts':counts,
             'minimum_original_integer_margin':baseline['minimum_original_integer_margin'],
             'minimum_root':baseline['minimum_root'],'minimum_position':baseline['minimum_position'],
             'all_active_mokI_checks_passed':True,'all_numeric_compact_vs_printed_AST_equal':True,
             'ready_contract_counts':baseline['ready_contract_counts'],
             'root_outside_guards':{'COV_true_WZ_guards':wz['existing_COV_true_guard_count'],
                                    'total_guard_and_topology_rows':len(baseline['root_outside_contract']['rows']),
                                    'pressure_tails':8,'small_gap_payments':8,
                                    'minimum_WZ_guard_integer_margin':wz['minimum_guard_margin'],
                                    'previous_baseline_receipt_WZ_gap_discharged_by':'root-wz-replay.json'},
             'metadata_correction':{'unchanged_v3_WD_identity_count':packing['WD_identity_count'],
                                    'correct_original_WD_dict_identity_count':48,
                                    'reason':'Later cursor loop reused local wd name as a string. Original48-dict assertion passed before local shadowing; current summary independently rechecks raw WD declarations. No numerical model change or walk rerun.'},
             'extra_source_schema_checks':{'TSok':True,'PRok':True,'SLok':True,'ADJ':True},
             'real_executions':{'packing_parser_attempts':3,'packing_attempts1_2_failures_preserved':True,
                                'preparation_stdout_encoding_failure_preserved':True,
                                'whole_math_passes':1,'math_pid':baseline['pid'],'math_seconds':baseline['seconds'],
                                'math_peak_working_set_bytes':baseline['rss']['peak_bytes'],
                                'WZ_existing_queries_passes':1,'WZ_pid':wz['pid'],'WZ_seconds':wz['seconds'],
                                'all_producer_processes_terminal':True},
             'fixed_receipts':{name:h(HERE/name) for name in ['packing-parser-v3.json','packing-crosscheck.json','baseline-replay.json','root-wz-replay.json','trace-integrity.json']},
             'analytic_scope':'Existing source proofs supply actual LB/PT/WZ analytic soundness; Python replays original finite arguments and active guards only. No Lean/Comparator/nanoda execution by this package.',
             'new_threshold_classification':False,'exception_pair_scan':False,'new_kernel_queries':0,'solver_calls':0,'Lean_runs':0,
             'new_floor_proven':False,'new_unconditional_zero_proportion_proven':False,'website_submission_ready':False,
             'StageB_authorized_by_this_receipt':False,'mutable_governance_dependency':False}
    dest.write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
    files=[]
    for p in sorted(HERE.iterdir()):
        if not p.is_file() or p.name=='files.json':continue
        files.append({'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':h(p)})
    refs=[source,ROOT/'scripts/finite_margin_20261015.py',ROOT/'scripts/review_finite_margin_20261015.py',
          ROOT/'research-goal-20261018-record-packing-independent/packing-replay.json',
          ROOT/'research-goal-20261018-record-wz-static-addendum/comparison.json',
          ROOT/'research-goal-20261018-record-wz-static-addendum/addendum-files.json']
    out={'schema':'new-record-original-floor-StageA-files-v1','scope':'Closed original-floor production Stage A. Independent full arithmetic review pending; not a new floor or kernel acceptance.',
         'files':files,'total_bytes':sum(f['bytes'] for f in files),
         'read_only_existing_references':[{'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':h(p)} for p in refs],
         'failed_parser_versions_and_attempt_receipts_preserved':True,'mutable_governance_dependency':False,
         'producer_stage_A_complete':True,'independent_full_mathematical_review_pending':True,
         'new_global_floor_proven':False,'new_unconditional_zero_proportion_proven':False,'website_submission_ready':False}
    manifest.write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'manifest':manifest.relative_to(ROOT).as_posix(),'sha256':h(manifest),'files':len(files),'bytes':out['total_bytes'],'summary_sha256':h(dest),'producer_stage_A_complete':True}))


if __name__=='__main__':main()
