"""Byte-only freeze of the terminated LocV1/Counting/FinalV1 attempt."""
import hashlib
import json
from pathlib import Path
import re

ROOT=Path(__file__).resolve().parents[1]
HERE=Path(__file__).resolve().parent
JOB=ROOT/'tmp/current-s1r-tiny-20261018/phase1-v0'


def item(p):
    b=p.read_bytes()
    return {'path':p.relative_to(ROOT).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}


def main():
    terminal=json.loads((JOB/'terminal.json').read_text())
    loc=json.loads((JOB/'Localization.receipt.json').read_text())
    count=json.loads((JOB/'Counting.receipt.json').read_text())
    assert terminal['passed'] is False and terminal['completed_modules']==2
    assert loc['ordinary_compile_passed'] and loc['exit_code']==0
    assert not count['ordinary_compile_passed'] and count['exit_code']==1
    assert not (JOB/'Final.receipt.json').exists()
    prep=HERE/'phase1-prepared.json';p=json.loads(prep.read_text())
    for r in p['files']+p['dependencies']:
        assert item(ROOT/r['path'])['sha256']==r['sha256'],r['path']
    for t in p['targets']:
        source=ROOT/(t['module']+'.lean')
        assert source.read_bytes()==(JOB/source.name).read_bytes()
    os=[item(JOB/('lib/'+r['relative_module_path'])) for r in p['reused_oleans']]
    os.append(item(JOB/'lib/StructuralS1RTiny20261018/Phase1/Localization.olean'))
    assert os[-1]['sha256']==loc['olean_sha256']
    rss={}
    for n in ['Localization','Counting']:
        m=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',(JOB/(n+'.resources.log')).read_text())
        assert m;rss[n]=int(m.group(1))
    out={'schema':'tiny-phase1-ordinary-execution-v1','actual_exec_session':31405,'exec_terminal_exit':1,
        'files':[item(x) for x in sorted(JOB.iterdir()) if x.is_file()]+[item(Path(__file__))],
        'dependencies':[item(prep),item(ROOT/'research-goal-20261016/gates/tiny-phase1-ordinary-20261018.json')],
        'compiled_and_reused_oleans_metadata_only':os,'ordinary_passed_but_axioms_pending_module':loc,
        'failed_unverified_module':count,'Final_unrun':True,'max_RSS_KiB':rss,
        'prefix_or_Core_recompiled':False,'automatic_repairs_or_retries':0,
        'all_transitive_axiom_roots_audited':False,'tiny_dyadic_or_cumulative_proved':False,
        'Nano_or_Comparator_passed':False,'website_submission_ready':False,
        'failure_scope':'Only summed_of_pair final let/Nat.cast normalization failed; sorryAx roots are unverified.'}
    target=HERE/'phase1-execution-files.json'
    with target.open('x',encoding='utf-8',newline='\n') as f:json.dump(out,f,indent=2);f.write('\n')
    print(json.dumps(item(target)));print(json.dumps(rss))


if __name__=='__main__':main()
