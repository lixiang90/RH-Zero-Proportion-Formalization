"""Static metadata freezing only; no live job or producer execution."""
import ast
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
TARGET=ROOT/'research-goal-20261019-native-materials-preparation'
PIN='4c9239ec89cbef146a71c18d44e341eca38bda9592a7c92febd2ce1720fef349'
SOURCE_PIN='a22f6dd7d690e9714349262672c5b7ecc14ad7728611bc29dc0b41c8a3a7cda0'

def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()

def row(p):
    return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)}

def write(name,x):
    with (HERE/name).open('x',encoding='utf-8',newline='\n') as f:
        json.dump(x,f,ensure_ascii=False,indent=2);f.write('\n')

def main():
    assert not (HERE/'review.json').exists() and not (HERE/'files.json').exists()
    prep=TARGET/'prepared-files.json'
    assert sha(prep)==PIN and sha(TARGET/'collect_once.py')==SOURCE_PIN
    m=json.loads(prep.read_text(encoding='utf-8'))
    bound={prep.relative_to(ROOT).as_posix():PIN}
    for r in m['files']+m['dependencies']:
        p=ROOT/r['path'];assert p.stat().st_size==r['bytes'] and sha(p)==r['sha256']
        bound[r['path']]=r['sha256']
    for name in ['collect_once.py','freeze_static.py']:
        ast.parse((TARGET/name).read_text(encoding='utf-8'),filename=name)
    source=(TARGET/'collect_once.py').read_text(encoding='utf-8')
    for fragment in ["confirmation['production_session_id'] == 84529", "confirmation['production_session_exit_code'] == 0",
      "assert len(finals) == 1", "assert original_pins[path] == bound[path]", "stable()",
      "assert deadline ==", "'num_threads': 0", "assert not DEST.exists()",
      "assert all(stage[key] == value for key, value in end_record.items())", "'official_website_acceptance': False"]:
        assert fragment in source,fragment
    assert all(sha(ROOT/p)==expected for p,expected in bound.items())
    write('review.json',{'schema':'post-pass-collector-independent-static-review-v1',
      'reviewed_prepared_sha256':PIN,'collector_sha256':SOURCE_PIN,
      'static_review_passed':True,'definite_success_blocker_or_scope_omission_found':False,
      'root_real_terminal_confirmation_and_original_outputs_required':True,
      'all_three_receipts_and_full_ten_stage_checks_present':True,
      'live_job_reads_in_this_collector_source_review':0,'collector_executions':0,
      'compiler_generator_kernel_network_or_math_runs':0,
      'review_does_not_assert_actual_session_terminal':True,
      'frozen_sources_unchanged':True,'website_acceptance_claimed':False})
    write('files.json',{'schema':'post-pass-collector-static-review-files-v1',
      'files':[row(HERE/'REVIEW.zh.md'),row(HERE/'freeze_review.py'),row(HERE/'review.json')],
      'read_dependencies':[row(ROOT/p) for p in sorted(bound)],
      'scope':'Independent static source review only; no collection or live proof result'})
    print(json.dumps({'static_review_passed':True,'manifest_sha256':sha(HERE/'files.json')}))

if __name__=='__main__':main()
