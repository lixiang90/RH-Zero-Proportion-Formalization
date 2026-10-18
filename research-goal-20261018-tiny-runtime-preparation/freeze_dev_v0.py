"""Byte-only freeze of the first terminated Tiny four-module compile attempt."""
import hashlib
import json
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent
JOB=ROOT/'tmp/current-s1r-tiny-20261018/dev-v0'


def item(p):
    b=p.read_bytes()
    return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}


def main():
    terminal=json.loads((JOB/'terminal.json').read_text())
    assert terminal['passed'] is False and terminal['completed_modules']==2
    core=json.loads((JOB/'Core.receipt.json').read_text())
    loc=json.loads((JOB/'Localization.receipt.json').read_text())
    assert core['ordinary_compile_passed'] and core['exit_code']==0
    assert not loc['ordinary_compile_passed'] and loc['exit_code']==1
    assert not (JOB/'Counting.receipt.json').exists() and not (JOB/'Final.receipt.json').exists()
    prep=HERE/'compiler-prepared.json'
    prepared=json.loads(prep.read_text())
    for r in prepared['files']+prepared['dependencies']:
        assert item(ROOT/r['path'])['sha256']==r['sha256'],r['path']
    for t in prepared['targets']:
        source=ROOT/(t['module']+'.lean')
        assert source.read_bytes()==(JOB/(source.name)).read_bytes()
    oleans=[]
    for p in [JOB/'lib/StructuralS1RTiny20261018/Dev/Core.olean',
              JOB/'lib/StructuralS1RM20261018/CurrentPrefix.olean']:
        oleans.append(item(p))
    assert oleans[0]['sha256']==core['olean_sha256']
    assert oleans[1]['sha256']=='8a67fa6cd8dbf293b802471bf39fb2cc160130a263191ce1c854d16fc35db692'
    rss={}
    for name in ['Core','Localization']:
        m=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',(JOB/(name+'.resources.log')).read_text())
        assert m
        rss[name]=int(m.group(1))
    out={'schema':'tiny-dev-v0-ordinary-execution-v1','actual_exec_session':36511,
        'exec_terminal_exit':1,'files':[item(p) for p in sorted(JOB.iterdir()) if p.is_file()]+[item(Path(__file__))],
        'dependencies':[item(prep),item(ROOT/'research-goal-20261016/gates/tiny-dev-ordinary-v0-20261018.json')],
        'compiled_and_reused_oleans_metadata_only':oleans,
        'ordinary_passed_but_axioms_pending_module':core,'failed_module':loc,
        'unrun_modules':['StructuralS1RTiny20261018/Dev/Counting','StructuralS1RTiny20261018/Dev/Final'],
        'max_RSS_KiB':rss,'prefix_recompiled':False,'automatic_repairs_or_retries':0,
        'all_four_modules_passed':False,'all_transitive_axiom_roots_audited':False,
        'tiny_pair_floor_proved':False,'tiny_dyadic_or_cumulative_proved':False,
        'Nano_or_Comparator_passed':False,'website_submission_ready':False,
        'failure_scope':'Four Localization API/simplification goals; original source unchanged, no automatic repair.'}
    target=HERE/'dev-v0-execution-files.json'
    with target.open('x',encoding='utf-8',newline='\n') as f:json.dump(out,f,indent=2);f.write('\n')
    print(json.dumps(item(target)))
    print(json.dumps({'max_RSS_KiB':rss,'Core_ordinary_seconds':core['elapsed_seconds'],
        'Localization_failed_seconds':loc['elapsed_seconds']}))


if __name__=='__main__':main()
