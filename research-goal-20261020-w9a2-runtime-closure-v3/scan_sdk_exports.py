"""Read PE exports from files only. Never loads or executes a DLL/tool main."""
import hashlib
import importlib.util
import json
from pathlib import Path
import struct

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
SDK=Path('C:/Users/A/.elan/toolchains/leanprover--lean4---v4.33.0-rc2')
CHECK=ROOT/'tmp/w9a2-20261020/trusted-runtime-closure-v2/official-sdk-check.json'
PARSER=ROOT/'research-goal-20261020-w9a2-runtime-closure-preparation/inspect_runtime.py'
TARGETS=['lean_byte_array_hash','lean_string_hash']

def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def pin(p):
    return dict(path=str(p.absolute()),resolved_path=str(p.resolve()),bytes=p.stat().st_size,sha256=sha(p))

spec=importlib.util.spec_from_file_location('static_PE_file_parser',PARSER)
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
receipt=json.loads(CHECK.read_text());assert receipt['all_selected_members_identical'] is True
assert receipt['archive_sha256']=='022576004ed8a4fc81ee8d375419064b54d4475931429d989519fd847ee053f6'
verified={str(Path(r['path']).resolve()).casefold():r for r in receipt['selected_members']}
rows=[]
for path in sorted((SDK/'bin').glob('*.dll')):
    row=pin(path);prior=verified[str(path.resolve()).casefold()]
    assert row['bytes']==prior['bytes'] and row['sha256']==prior['sha256']
    pe=module.PE(path);rva,size=struct.unpack_from('<II',pe.data,pe.dd)
    exports=[];names=[]
    if rva:
        p=pe.offset(rva)
        fields=struct.unpack_from('<IIHHIIIIIII',pe.data,p)
        _,_,_,_,_,base,count,named,functions,names_rva,ordinals=fields
        foff=pe.offset(functions);noff=pe.offset(names_rva);ooff=pe.offset(ordinals)
        for i in range(named):
            name=pe.cstring(struct.unpack_from('<I',pe.data,noff+4*i)[0]);names.append(name)
            if name in TARGETS:
                index=struct.unpack_from('<H',pe.data,ooff+2*i)[0];assert index<count
                target=struct.unpack_from('<I',pe.data,foff+4*index)[0]
                exports.append(dict(name=name,ordinal=base+index,function_RVA=target,
                  forwarder=pe.cstring(target) if rva<=target<rva+size else None))
    rows.append(dict(**row,PE_machine=pe.machine,named_export_count=len(names),
      sorted_export_names_sha256=hashlib.sha256('\n'.join(sorted(names)).encode()).hexdigest(),
      selected_exact_exports=exports))
result=dict(scope='Actual pure file PE export-table scan of every officially byte-verified SDK bin DLL',
  SDK_archive_check=pin(CHECK),PE_parser=pin(PARSER),scan_source=pin(Path(__file__)),
  target_symbols=TARGETS,DLLs=rows,DLL_loads=0,SDK_hash_API_calls=0,compiler_runs=0,proof_runs=0)
with (HERE/'sdk-export-scan.json').open('x',encoding='utf-8',newline='\n') as f:
    json.dump(result,f,indent=2);f.write('\n')
print(json.dumps(dict(output=pin(HERE/'sdk-export-scan.json'),exports=[dict(DLL=r['path'],exports=r['selected_exact_exports']) for r in rows if r['selected_exact_exports']],DLL_loads=0)))
