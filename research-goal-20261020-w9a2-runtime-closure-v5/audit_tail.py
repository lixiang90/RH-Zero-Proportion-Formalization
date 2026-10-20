"""Read-only checks of every previously unrun tail input premise; no SDK/API/main."""
import ast
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
from cache_binding import git_tree, canonical_git_blob

HERE=Path(__file__).resolve().parent;ROOT=HERE.parent
BASE=ROOT/'research-goal-20261020-w9a2-runtime-closure-preparation'
SDK=Path('C:/Users/A/.elan/toolchains/leanprover--lean4---v4.33.0-rc2')
SYSTEM=Path('C:/Windows/System32')
files={}
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def pin(p):
    p=p.absolute();row=dict(path=str(p),resolved_path=str(p.resolve()),bytes=p.stat().st_size,sha256=sha(p))
    if str(p) in files:assert files[str(p)]==row
    files[str(p)]=row;return row
def load(p):pin(p);return json.loads(p.read_text(encoding='utf-8'))
base=load(BASE/'runtime-closure-CANDIDATE-INCOMPLETE.json')
c=load(ROOT/'verification/comparator-core-public-driver-check.json')
gate=load(HERE/'gate-template.json')
assert c['compiler']==gate['lean_version'] and c['exit_code']==0 and c['local_comparator_core_passed'] and c['source_unchanged_during_check']
assert c['comparator_commit']==base['tool_commits']['Comparator'] and c['exporter_commit']==base['tool_commits']['lean4export']
five=['Comparator','Comparator.Axioms','Comparator.Compare','Comparator.Util','Export.Parse']
for name in five:
    p=ROOT/('tmp/Comparator/.lake/packages/lean4export/.lake/build/lib/lean' if name=='Export.Parse' else 'tmp/Comparator/.lake/build/lib/lean')/Path(*name.split('.')).with_suffix('.olean')
    assert pin(p)['sha256']==c['input_sha256'][p.relative_to(ROOT).as_posix()]
native=load(ROOT/'verification/three-website-declarations-modular-nanoda.json')
assert native['compiler']==gate['lean_version'] and native['export_process_ran'] and native['export_exit_code']==0 and native['inputs_unchanged']
for key,path in [('exporter_binary',ROOT/'tmp/lean4export/.lake/build/bin/lean4export.exe'),('nanoda_binary',ROOT/'tmp/kernel-tools/nanoda-target/release/nanoda_bin')]:
    assert pin(path)['sha256']==native['sha256_before'][key]==native['sha256_after'][key]
runner=ROOT/'research-goal-20261020-w9a2-verification-preparation-v1/run_verification.py';pin(runner)
expected=next(ast.literal_eval(n.value) for n in ast.parse(runner.read_bytes()).body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='TOOL_SOURCE_LF_SHA' for t in n.targets))
trees={name:git_tree(ROOT/'tmp'/name,base['tool_commits'][name]) for name in ['Comparator','lean4export','nanoda']}
for row in base['trusted_tool_sources']:
    p=Path(row['path']);name,rel=row['logical_name'].split('/',1)
    raw=canonical_git_blob(p,rel,trees[name]);assert hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest()==expected[row['logical_name']]
    oldpath=ROOT/'tmp/Comparator/.lake/packages/lean4export'/rel if name=='lean4export' else p
    assert pin(p)['sha256']==pin(oldpath)['sha256']==c['input_sha256'][oldpath.relative_to(ROOT).as_posix()]
nested=ROOT/'tmp/Comparator/.lake/packages/lean4export';nt=git_tree(nested,base['tool_commits']['lean4export'])
raw=canonical_git_blob(nested/'Export/Parse.lean','Export/Parse.lean',nt)
assert hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest()==expected['lean4export/Export/Parse.lean']
old=load(ROOT/'verification/gram-defect-single-20261014/independent-kernel.json');nano=old['tool_provenance']['nanoda_binary']
assert nano['pin']==base['tool_commits']['nanoda'] and nano['sha256']==sha(ROOT/'tmp/kernel-tools/nanoda-target/release/nanoda_bin')
cargo=ROOT/'tmp/nanoda/Cargo.toml';raw=canonical_git_blob(cargo,'Cargo.toml',trees['nanoda'])
assert hashlib.sha256(raw).hexdigest()==nano['cargo_git_blob_content_sha256']
pin(ROOT/'tmp/nanoda/Cargo.lock')
for rel,(mode,kind,oid) in trees['nanoda'].items():
    if kind=='blob' and (rel.endswith('.rs') or rel in ['Cargo.toml','Cargo.lock']):
        p=ROOT/'tmp/nanoda'/rel;canonical_git_blob(p,rel,trees['nanoda']);pin(p)
for rel in ['tmp/lean4export/.lake/build/bin/lean4export.exe.trace','tmp/lean4export/.lake/build/bin/lean4export.exe.rsp','tmp/kernel-tools/build-nanoda.sh','tmp/kernel-tools/build-nanoda.log']:
    pin(ROOT/rel)
cap=load(HERE/'controller-stdlib-loaded-modules.json')
assert cap['sys_version']==sys.version and Path(cap['python']).resolve()==Path(sys.executable).resolve()
for row in cap['all_actual_loaded_modules_with_instrumentation']:
    actual=pin(Path(row['path']));assert all(actual[k]==row[k] for k in ['bytes','sha256'])
    assert actual['resolved_path'].casefold()==row['resolved_path'].casefold()
spec=importlib.util.spec_from_file_location('static_file_PE_parser',BASE/'inspect_runtime.py')
pe=importlib.util.module_from_spec(spec);spec.loader.exec_module(pe);pin(BASE/'inspect_runtime.py')
known={Path(r['path']).name.casefold():Path(r['path']) for r in cap['all_actual_loaded_modules_with_instrumentation']}
comp=load(BASE/'evidence/compiler19056-loaded-modules.json')
todo=[SDK/'bin/lean.exe',ROOT/'tmp/lean4export/.lake/build/bin/lean4export.exe',Path(sys.executable),SYSTEM/'wsl.exe',SYSTEM/'taskkill.exe']
todo += list(known.values())+[Path(r['Path']) for r in comp['Modules']]
seen=set();edges=[]
while todo:
    p=todo.pop();key=str(p.absolute()).casefold()
    if key in seen:continue
    seen.add(key);pin(p)
    if p.resolve().is_relative_to(SYSTEM.resolve()):continue
    for edge in pe.PE(p).imports():
        name=edge['name']
        if name.casefold().startswith(('api-ms-','ext-ms-')):continue
        choices=[p.parent/name,SYSTEM/name,SDK/'bin'/name,Path(sys.executable).parent/name,Path(sys.executable).parent/'DLLs'/name]
        target=known.get(name.casefold()) or next((x for x in choices if x.is_file()),None)
        assert target is not None,(p,edge)
        edges.append(dict(importer=str(p),**edge,resolved=str(target)));todo.append(target)
elf=load(BASE/'evidence/WSL-ELF-loader-resolution.json')
for row in elf['files']:
    if row['path'].startswith('/mnt/e/'):continue
    actual=pin(Path(row['Windows_read_path']));assert actual['bytes']==row['bytes'] and actual['sha256']==row['sha256']
core=pin(ROOT/'tools/ComparatorCoreAudit.lean');assert core['sha256']==base['coreaudit_source_sha256']
for row in files.values():
    p=Path(row['path']);assert sha(p)==row['sha256'] and str(p.resolve())==row['resolved_path']
result=dict(scope='Actual read-only tail premise checks of fixed sources/old receipts/5 tool oleans/native binaries/installed Python/ordinary application PE dependencies/WSL current file hashes; no overlay copy or setup/closure seal executed',
  result='PASS',SDK_hash_API_calls=0,DLL_loads=0,compiler_runs=0,proof_runs=0,
  exact_tool_olean_count=5,PE_boundary='Stop recursive traversal at installed Windows System32 boundary; no OS delay-import closure claim',
  nonOS_PE_edges=edges,files=list(files.values()),source=pin(Path(__file__)))
with (HERE/'tail-static-check.json').open('x',encoding='utf-8',newline='\n') as f:
    json.dump(result,f,indent=2);f.write('\n')
print(json.dumps(dict(result='PASS',files=len(files),nonOS_PE_edges=len(edges),SDK_hash_API_calls=0,DLL_loads=0)))
