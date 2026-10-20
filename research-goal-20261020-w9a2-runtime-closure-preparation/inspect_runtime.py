"""Pure file inspection; no compiler/export/kernel/install/subprocess/network.

This builds an INCOMPLETE review packet. It never sets the v1 verification
runtime-closure approval fields true. Loaded-process evidence is input captured
read-only by PowerShell; PE imports/API-set hosts are inspected as file bytes.
Large package-cache enumeration/hashing is opt-in so it need not compete with
the root's one active compiler. An approved setup/closure still needs root audit.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import struct
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
SDK=Path('C:/Users/A/.elan/toolchains/leanprover--lean4---v4.33.0-rc2')
SYSTEM=Path(os.environ.get('SYSTEMROOT','C:/Windows'))/'System32'
TOOL_COMMITS={'Comparator':'273294467ce06429e6667ece7f5699f8678c9f4e',
              'lean4export':'b18d673bd29b476466a51a3be1012df2ed322b10',
              'nanoda':'418320295890faed83a96fd97907b12a3b6728c2'}


def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda:stream.read(1048576),b''):
            h.update(block)
    return h.hexdigest()


def pin(path,role):
    path=Path(path).absolute()
    return {'path':str(path),'resolved_path':str(path.resolve()),'bytes':path.stat().st_size,
            'sha256':sha(path),'role':role}


def new(path,obj):
    with Path(path).open('x',encoding='utf-8',newline='\n') as stream:
        json.dump(obj,stream,ensure_ascii=False,indent=2);stream.write('\n')


class PE:
    def __init__(self,path):
        self.path=Path(path);self.data=self.path.read_bytes();d=self.data
        if d[:2]!=b'MZ':raise ValueError('Not PE: '+str(path))
        p=struct.unpack_from('<I',d,0x3c)[0]
        if d[p:p+4]!=b'PE\0\0':raise ValueError('Invalid PE header')
        self.machine,self.count=struct.unpack_from('<HH',d,p+4)
        self.opt=p+24;size=struct.unpack_from('<H',d,p+20)[0]
        self.magic=struct.unpack_from('<H',d,self.opt)[0]
        if self.magic not in [0x10b,0x20b]:raise ValueError('Unsupported PE optional header')
        self.imagebase=struct.unpack_from('<Q' if self.magic==0x20b else '<I',d,
                                        self.opt+(24 if self.magic==0x20b else 28))[0]
        self.dd=self.opt+(112 if self.magic==0x20b else 96)
        self.sections=[]
        for i in range(self.count):
            s=self.opt+size+40*i
            name=d[s:s+8].rstrip(b'\0').decode('ascii')
            virtual_size,va,rawsize,raw=struct.unpack_from('<IIII',d,s+8)
            self.sections.append({'name':name,'va':va,'size':max(virtual_size,rawsize),
                                  'raw':raw,'rawsize':rawsize})

    def offset(self,va):
        for s in self.sections:
            if s['va']<=va<s['va']+s['size']:
                result=s['raw']+va-s['va']
                if result>=len(self.data):raise ValueError('PE RVA outside file bytes')
                return result
        if va<len(self.data) and va<self.sections[0]['raw']:return va
        raise ValueError('Unmapped PE RVA '+hex(va))

    def cstring(self,va):
        off=self.offset(va);end=self.data.index(b'\0',off)
        return self.data[off:end].decode('ascii')

    def imports(self):
        result=[]
        for index,stride,kind in [(1,20,'ordinary'),(13,32,'delay')]:
            rva,size=struct.unpack_from('<II',self.data,self.dd+8*index)
            if not rva:continue
            off=self.offset(rva)
            for n in range(max(1,size//stride)+1):
                fields=struct.unpack_from('<'+('I'*(stride//4)),self.data,off+n*stride)
                if not any(fields):break
                name=fields[3] if kind=='ordinary' else fields[1]
                if kind=='delay' and not (fields[0]&1):name-=self.imagebase
                result.append({'name':self.cstring(name),'kind':kind})
        return result


def api_sets(path):
    pe=PE(path)
    section=next(s for s in pe.sections if s['name']=='.apiset')
    d=pe.data[section['raw']:section['raw']+section['rawsize']]
    version,size,flags,count,entries,hash_offset,hash_factor=struct.unpack_from('<7I',d,0)
    if version!=6 or size>len(d):raise ValueError('Unsupported API-set schema/version')
    text=lambda offset,length:d[offset:offset+length].decode('utf-16-le')
    result={};prefixes={}
    for i in range(count):
        ef,no,nl,hashed_len,vo,vc=struct.unpack_from('<6I',d,entries+24*i)
        name=text(no,nl).casefold()
        prefix=text(no,hashed_len).casefold()
        values=[]
        for j in range(vc):
            vf,ao,al,ho,hl=struct.unpack_from('<5I',d,vo+20*j)
            values.append({'alias':text(ao,al),'host':text(ho,hl)})
        result[name]=values
        prefixes.setdefault(prefix,[]).append({'contract':name,'values':values})
    return {'version':version,'count':count,'contracts':result,'hashed_prefixes':prefixes}


def git_head(repo):
    meta=Path(repo)/'.git'
    if meta.is_file():meta=(Path(repo)/meta.read_text().strip().removeprefix('gitdir: ')).resolve()
    value=(meta/'HEAD').read_text().strip()
    if value.startswith('ref: '):
        ref=value[5:];target=meta/ref
        if target.is_file():return target.read_text().strip()
        for line in (meta/'packed-refs').read_text().splitlines():
            if line.endswith(' '+ref):return line.split()[0]
        raise ValueError('Missing git ref '+ref)
    return value


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--inspect-files-once',required=True,action='store_true')
    ap.add_argument('--output-name',required=True)
    ap.add_argument('--include-all-package-cache-files',action='store_true')
    args=ap.parse_args()
    if Path(args.output_name).name!=args.output_name:raise ValueError('Output must be one directory name')
    dest=HERE/args.output_name
    if dest.exists():raise ValueError('Exclusive output already exists')
    snapshot=json.loads((HERE/'evidence/compiler19056-loaded-modules.json').read_text())
    observed={m['Name'].casefold():Path(m['Path']) for m in snapshot['Modules']}
    schema=api_sets(SYSTEM/'apisetschema.dll')
    seeds=[Path(snapshot['Executable']),ROOT/'tmp/lean4export/.lake/build/bin/lean4export.exe',
           Path(sys.executable),SYSTEM/'wsl.exe',SYSTEM/'taskkill.exe',*observed.values()]
    allfiles={};images={};unresolved=[];ambiguous=[];queue=list(seeds)
    # API-set contracts select hosts; no DLL is loaded or executed by this parser.
    while queue:
        path=queue.pop(0).absolute();key=str(path).casefold()
        if key in images:continue
        pe=PE(path);dependencies=[]
        for imp in pe.imports():
            name=imp['name'];contract=name.casefold().removesuffix('.dll')
            hosts=schema['contracts'].get(contract)
            api_resolution='exact-contract' if hosts is not None else None
            prefix_candidates=[]
            if hosts is None and contract.startswith(('api-ms-','ext-ms-')):
                prefix_candidates=schema['hashed_prefixes'].get(contract.rsplit('-',1)[0],[])
                if len(prefix_candidates)==1:
                    entry=prefix_candidates[0]
                    # Actual namespace HashedLength is retained as evidence; this static
                    # compatibility inference is not a loader execution or approval.
                    try:
                        compatible=int(entry['contract'].rsplit('-',1)[1])>=int(contract.rsplit('-',1)[1])
                    except ValueError:
                        compatible=False
                    if compatible:
                        hosts=entry['values'];api_resolution='namespace-HashedLength-compatible-revision-inference'
            names=[name]
            if hosts is not None:
                default=[v['host'] for v in hosts if not v['alias']]
                specific=[v['host'] for v in hosts if v['alias'].casefold()==path.name.casefold()]
                names=specific or default
                if not names:names=[v['host'] for v in hosts]
            resolutions=[]
            for host in names:
                # Observed loaded module is authoritative for the captured compiler.
                known=observed.get(host.casefold())
                candidates=[]
                for folder in [path.parent,SYSTEM,SYSTEM.parent,SDK/'bin',Path(sys.executable).parent]:
                    candidate=folder/host
                    if candidate.is_file() and str(candidate.resolve()).casefold() not in {
                            str(p.resolve()).casefold() for p in candidates}:candidates.append(candidate)
                if known and known.is_file():selected=known
                elif len(candidates)==1:selected=candidates[0]
                elif candidates:selected=candidates[0]
                else:selected=None
                if len(candidates)>1:ambiguous.append({'importer':str(path),'name':host,'candidates':list(map(str,candidates))})
                resolutions.append({'host':host,'selected':str(selected) if selected else None,
                    'candidates':list(map(str,candidates)),'observed_loaded_module':bool(known)})
                if selected:queue.append(selected)
                else:unresolved.append({'importer':str(path),'import':name,'host':host})
            dependencies.append({**imp,'api_set_values':hosts,'api_set_resolution_method':api_resolution,
                'api_set_hashed_prefix_candidates':prefix_candidates,'resolutions':resolutions})
        images[key]={'path':str(path),'machine':pe.machine,'imports':dependencies}
        allfiles[key]=pin(path,'PE-runtime-file-observed-or-static-candidate')
    allfiles[str((SYSTEM/'apisetschema.dll').absolute()).casefold()]=pin(SYSTEM/'apisetschema.dll','Windows-API-set-schema')
    package_gate=json.loads((ROOT/'research-goal-20261020-w9a2-runtime/trusted-setup-gate.json').read_text())
    packages=[]
    for row in package_gate['packages']:
        repo=ROOT/row['path'];actual=git_head(repo)
        packages.append({'path':str(repo),'expected_commit':row['commit'],'actual_HEAD':actual,
                         'HEAD_matches':actual==row['commit'],'whole_source_tree_and_cache_bound':False})
    cache_count=0
    if args.include_all_package_cache_files:
        for relative in [*package_gate['package_libs'],'tmp/Comparator/.lake/build/lib/lean',
                         'tmp/lean4export/.lake/build/lib/lean']:
            for p in (ROOT/relative).rglob('*'):
                if p.is_file():
                    allfiles[str(p.absolute()).casefold()]=pin(p,'trusted-cache-byte-inventory-not-source-provenance')
                    cache_count+=1
    evidence_paths=['verification/gram-defect-single-20261014/independent-kernel.json',
                    'verification/gram-defect-single-20261014/full-local-verification.json',
                    'verification/analytic-independent-nanoda-driver.json',
                    'verification/three-website-declarations-modular-nanoda.json',
                    'tmp/kernel-tools/build-nanoda.sh','tmp/kernel-tools/build-nanoda.log',
                    'tmp/lean4export/.lake/build/bin/lean4export.exe.trace',
                    'tmp/lean4export/.lake/build/bin/lean4export.exe.rsp']
    evidence=[pin(ROOT/p,'historical-provenance-or-build-trace') for p in evidence_paths]
    dest.mkdir()
    new(dest/'PE-import-review.json',{'scope':'Static PE import/delay-import and API-set file parser; no executable started',
        'captured_compiler':snapshot,'api_set_schema_version':schema['version'],
        'api_set_contract_count':schema['count'],'images':list(images.values()),
        'unresolved':unresolved,'ambiguous_candidates':ambiguous,
        'complete_runtime_closure_verified':False})
    new(dest/'runtime-file-inventory.json',{'scope':'File identity inventory only; never an approved runtime closure',
        'generated_at_utc':datetime.now(timezone.utc).isoformat(),'files':list(allfiles.values()),
        'package_git_identity_only':packages,'all_package_cache_files_hashed':args.include_all_package_cache_files,
        'cache_files_hashed':cache_count,'historical_provenance_files':evidence,
        'tool_commits':TOOL_COMMITS,'complete_source_bound_runtime_closure_verified':False,
        'compiler_export_kernel_install_runs':0})
    print(json.dumps({'output':str(dest),'PE_images':len(images),'unresolved_imports':len(unresolved),
                      'ambiguous':len(ambiguous),'runtime_complete':False,'proof_runs':0}))


if __name__=='__main__':main()
