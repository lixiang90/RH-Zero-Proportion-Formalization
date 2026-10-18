"""Freeze actual Phase2--4 receipts, without rerunning any mathematics or Lean."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent
def row(p):
    b=p.read_bytes()
    return dict(path=p.relative_to(ROOT).as_posix(),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def dump(p,o):
    with p.open('x',encoding='utf-8',newline='\n') as f:json.dump(o,f,indent=2);f.write('\n')
files=[Path(__file__)]; phases=[]
for n,session in [(2,3699),(3,62021),(4,95032)]:
    prep=ROOT/f'research-goal-20261018-tiny-runtime-preparation/phase{n}-prepared.json'
    gate=ROOT/f'research-goal-20261016/gates/tiny-phase{n}-ordinary-20261018.json'
    p=json.loads(prep.read_bytes())
    for r in p['files']+p['dependencies']:
        actual=row(ROOT/r['path'])
        assert actual['sha256']==r['sha256'] and actual['bytes']==r['bytes'],r['path']
    job=ROOT/f'tmp/current-s1r-tiny-20261018/phase{n}-v0'
    terminal=json.loads((job/'terminal.json').read_bytes())
    assert terminal['passed']==(n==4)
    files.extend([prep,gate]+[x for x in sorted(job.iterdir()) if x.is_file()])
    phases.append(dict(phase=n,actual_exec_session=session,exit_code=0 if n==4 else 1,terminal=terminal))
final=json.loads((ROOT/'tmp/current-s1r-tiny-20261018/phase4-v0/Final.receipt.json').read_bytes())
assert final['ordinary_compile_passed'] and final['axiom_audit_passed'] and final['source_unchanged']
assert len(final['printed_roots'])==6
assert all(set(x['axioms'])<={'propext','Quot.sound','Classical.choice'} for x in final['printed_roots'])
out=dict(schema='tiny-full-unconditional-ordinary-proof-result-v1',phases=phases,
    final_receipt=final,full_actual_root_counting_dyadic_and_cumulative_bound_proved=True,
    hypotheses_remaining_in_final_bound=False,all_six_transitive_roots_only_standard_three_axioms=True,
    mathematical_constants_or_models_changed_by_API_repairs=False,
    previous_failed_sources_and_logs_preserved=True,
    cold_single_file_verified=False,Comparator_passed=False,nanoda_passed=False,
    website_submission_ready=False,official_website_acceptance=False)
dump(HERE/'ordinary-proof.json',out);files.append(HERE/'ordinary-proof.json')
dump(HERE/'files.json',dict(schema='tiny-ordinary-result-files-v1',files=[row(x) for x in dict.fromkeys(files)],runtime_oleans_excluded_from_delivery=True))
print(json.dumps(row(HERE/'files.json')))
