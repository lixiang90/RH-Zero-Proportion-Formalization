"""Stage only the reviewable W10 checkpoint, never live large search dumps."""
from pathlib import Path
import hashlib,json,re,subprocess
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).parent
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
def main():
  p=json.loads((HERE/'progress.json').read_text())
  assert not p['complete_global_floor_proven'] and not p['upload_ready']
  files={'.gitattributes','.gitignore','README.md','research-20261016-w10-cert/progress.json'}
  for name,digest in p['bound_source_and_receipt_sha256'].items():
    path=ROOT/name;assert hashlib.sha256(path.read_bytes()).hexdigest()==digest,('Changed verified snapshot input',name)
    files.add(name)
  files.update(str(x.relative_to(ROOT)).replace('\\','/') for x in HERE.glob('*.py'))
  for x in HERE.glob('*.json'):
    if x.stat().st_size>150000:continue
    if re.match(r'^(?:error|old-format|parallel|seed|ordered-(?:native-seed|seed|master|hints)|native-ordered|relative-|tree-flow|thin-)',x.name):continue
    files.add(str(x.relative_to(ROOT)).replace('\\','/'))
  for x in HERE.rglob('*'):
    if x.is_file() and x.is_relative_to(HERE/'website-snapshot'):files.add(str(x.relative_to(ROOT)).replace('\\','/'))
  for name in ['current-record-source.txt','submission-notes.draft.md','RootAudit.lean',
    'root-axioms.log','root-Coercivity.log','root-TreeCoverage.log','root-RootBounds.log','closed-tree-smoke-lean.log']:
    if (HERE/name).exists():files.add('research-20261016-w10-cert/'+name)
  git('add','--force','--',*sorted(files))
  tree=git('write-tree').decode().strip();names=git('diff','--cached','--name-only','-z').decode().split('\0')[:-1]
  result={'scope':'Staged WIP checkpoint only; complete W10 floor remains unproved',
    'parent':git('rev-parse','HEAD').decode().strip(),'tree':tree,'files':names}
  out=ROOT/'tmp/w10-sync';out.mkdir(parents=True,exist_ok=True)
  (out/'staged.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf8')
  print(json.dumps({'parent':result['parent'],'tree':tree,'changed_files':len(names)}))
if __name__=='__main__':main()
