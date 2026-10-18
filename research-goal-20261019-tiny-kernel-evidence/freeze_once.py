"""Freeze separately completed checks honestly; retain the failed total deadline."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent
OLD=Path('/var/tmp/rh-zero-20261015/tiny-production-v0')
DIAG=Path('/var/tmp/rh-zero-20261015/tiny-nanoda-diagnostic-v0')
SOURCE=ROOT/'research-goal-20261018-tiny-flatten-preparation-v3/draft/Solution.lean'
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def row(p):return dict(path=p.relative_to(ROOT).as_posix(),bytes=p.stat().st_size,sha256=sha(p))
def dump(p,o):
    with p.open('x',encoding='utf-8') as f:json.dump(o,f,indent=2);f.write('\n')
def main():
    f=json.loads((OLD/'failure.json').read_bytes())
    d=json.loads((DIAG/'terminal.json').read_bytes())
    assert f['failed'] and f['stage']=='nanoda' and not f['local_single_file_verified']
    assert f['statement_equality_proved'] and f['permitted_axioms_checked'] and f['default_kernel_replay_passed']
    assert d['diagnostic_only'] and d['independent_complete_nanoda_passed'] and d['exit_code']==0
    assert d['inputs_unchanged'] and set(d['observed_axioms'])=={'propext','Quot.sound','Classical.choice'}
    assert d['source_export_sha256']==f['exports']['solution']['output_sha256']==sha(OLD/'solution.ndjson')
    assert d['log_sha256']==sha(DIAG/'nanoda.log')
    assert sha(SOURCE)=='024902a7ef01ccba2a6c71e54682a31712417e5d3c0b4ead5f6f80ad25fd1a81'
    assert sha(SOURCE)==sha(OLD/'source/Solution/Candidate.lean')
    assert f['compiled_modules'][-1]['source_sha256']==sha(SOURCE)
    assert all(s['exit_code']==0 for s in f['stages'][:-1])
    dest=HERE/'snapshots';dest.mkdir()
    copied=[]
    for base,label in [(OLD,'cold-v0'),(DIAG,'nanoda-diagnostic')]:
        paths=[x for x in base.iterdir() if x.is_file() and x.suffix=='.json']
        logs=base/'logs'
        paths+=list(logs.iterdir()) if logs.is_dir() else [base/'nanoda.log',base/'resources.txt']
        for p in sorted(set(paths)):
            assert p.is_file() and p.stat().st_size<=20_000_000
            assert p.suffix in {'.json','.log','.txt'}
            target=dest/label/p.relative_to(base);target.parent.mkdir(parents=True,exist_ok=True)
            with target.open('xb') as out:out.write(p.read_bytes())
            assert sha(target)==sha(p);copied.append(target)
    actual=dict(schema='tiny-separately-completed-checks-v1',source=row(SOURCE),
        ordinary_Lean_passed=True,Comparator_exact_statement_dependency_primitive_passed=True,
        transitive_axiom_check_passed=True,Lean_default_kernel_passed=True,
        independent_complete_nanoda_passed=True,nanoda_declarations=d['checked_declarations'],
        nanoda_seconds=d['elapsed_seconds'],nanoda_threads=d['num_threads'],
        allowed_axioms=d['observed_axioms'],diagnostic_source_export_sha256=d['source_export_sha256'],
        full_cold3200s_passed=False,previous_full_cold_timeout_seconds=f['total_elapsed_seconds_at_failure'],
        previous_full_cold_nanoda_remaining_seconds=f['stages'][-1]['timeout_seconds_remaining_from_total'],
        no_failure_hidden_or_relabelled=True,official_website_acceptance=False,
        website_result_pending=True,source_immutable_for_human_parallel_upload=True,
        proof_file_upload_ready_not_asserted=True)
    dump(HERE/'checks.json',actual)
    copied += [HERE/'checks.json',Path(__file__),SOURCE]
    dump(HERE/'files.json',dict(schema='tiny-check-evidence-files-v1',files=[row(p) for p in copied],
        large_exports_and_oleans_not_copied=True,full_cold3200s_passed=False,
        official_website_acceptance=False))
    print(json.dumps(row(HERE/'files.json')))
if __name__=='__main__':main()
