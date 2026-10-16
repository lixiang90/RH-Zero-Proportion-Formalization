"""Stage proved conditional results and explicitly unverified full data source.

The website upload remains blocked by source size and the unexecuted full
finite Lean instance. Large discovery checkpoints stay local; exact reduced
evidence is archived in byte-bound parts.
"""
from pathlib import Path
import hashlib,json,re,subprocess
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).resolve().parent
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    if not __debug__:raise RuntimeError('Snapshot assertions must remain enabled')
    p=json.loads((HERE/'progress.json').read_bytes())
    assert p['complete_independent_integer_audit'] and not p['complete_global_floor_proven'] and not p['upload_ready']
    files={'.gitattributes','.gitignore','README.md','research-20261016-w10-cert/progress.json'}
    for name,digest in {**p['bound_source_and_receipt_sha256'],**p['generated_unverified_sources']}.items():
        assert sha(ROOT/name)==digest,('Changed checkpoint input',name)
        files.add(name)
    files.update(str(x.relative_to(ROOT)).replace('\\','/') for x in HERE.glob('*.py'))
    for x in HERE.glob('*.json'):
        if x.stat().st_size>150000:continue
        if re.match(r'^(?:error|old-format|parallel|seed|prototype|native-|tailfix-pooled|ordered-(?:[0-9]|native-seed|seed|master|hints)|relative-|tree-flow|thin-)',x.name):continue
        files.add(str(x.relative_to(ROOT)).replace('\\','/'))
    for name in ['REPRODUCE-CERTIFICATE.txt','submission-notes.draft.md',
                 'core-dependencies.json','relative-codec-scale-report.json',
                 'flow-primal-probe.json','hessian-subtree-probe.json',
                 'SourceBlocksSmoke.lean','source-blocks-smoke.log',
                 'compressed-preflight.log','compressed-preflight-resources.log']:
        if (HERE/name).exists():files.add('research-20261016-w10-cert/'+name)
    for name in ['CompressedCommands','CompressedCommandsSmoke']:
        files.add('StructuralW10Cert20261016/'+name+'.lean')
    for directory in [HERE/'evidence-parts',ROOT/'submission/w10-20261016',ROOT/'verification/w10-20261016/conditional']:
        for x in directory.rglob('*'):
            if x.is_file():files.add(str(x.relative_to(ROOT)).replace('\\','/'))
    git('add','--force','--',*sorted(files))
    changed=git('diff','--cached','--name-only','-z').decode().split('\0')[:-1]
    entries=[]
    for name in changed:
        raw=git('show',':'+name)
        try:raw.decode('utf8');binary=b'\0' in raw
        except UnicodeDecodeError:binary=True
        blob=git('rev-parse',':'+name).decode().strip()
        entries.append({'path':name,'sha':blob,'bytes':len(raw),'binary':binary})
    result={'scope':__doc__,'parent':git('rev-parse','HEAD').decode().strip(),
            'tree':git('write-tree').decode().strip(),'files':changed,'entries':entries}
    out=ROOT/'tmp/w10-final-sync';out.mkdir(parents=True,exist_ok=True)
    (out/'staged.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'parent':result['parent'],'tree':result['tree'],'files':len(changed),
                      'bytes':sum(e['bytes'] for e in entries),'binary_files':sum(e['binary'] for e in entries)}))

if __name__=='__main__':main()
