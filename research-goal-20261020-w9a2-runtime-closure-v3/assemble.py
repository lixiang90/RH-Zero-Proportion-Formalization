"""Source-bound trusted runtime preparation. No Lean/lake/export/kernel main.

Only authorized SDK DLL operations: borrowed lean_string_hash and
lean_byte_array_hash on caller-owned buffers, after official archive comparison.
All outputs are fresh. Failure preserves diagnostic files and never emits PASS.
"""
import argparse
import ast
import ctypes
from datetime import datetime, timezone
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import struct
import sys
import tarfile
import traceback
import zstandard
from fractions import Fraction
import re
import signal
import subprocess
import time

from cache_binding import (SDKHash, CacheSourceHash, canonical_git_blob, git_tree,
                           imports, header, mix, flatten_values, verify_outputs)

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SDK = Path('C:/Users/A/.elan/toolchains/leanprover--lean4---v4.33.0-rc2')
ARCHIVE = ROOT / 'tmp/toolchain-download/lean-4.33.0-rc2-windows.tar.zst'
ARCHIVE_SHA = '022576004ed8a4fc81ee8d375419064b54d4475931429d989519fd847ee053f6'
SDK_COMMIT = 'd8b18978322de05a8f3dba51ef03cf5461676c17'
BASE = ROOT / 'research-goal-20261020-w9a2-runtime-closure-preparation'
RUNNER = ROOT / 'research-goal-20261020-w9a2-verification-preparation-v1/run_verification.py'
RUNNER_SHA = '92cc8dcf3e3c46e76490ba7bfe8d93bc10e331131eaab3b4c3ae500f80ac66a8'
FORBIDDEN = ['ChallengeDeps.olean','ChallengeDeps/CandidateSpec.olean',
             'Challenge/Candidate.olean','Solution/Candidate.olean']
TOOL_MODULES={'Comparator','Comparator.Axioms','Comparator.Compare','Comparator.Util',
              'Export','Export.Parse','Main'}


def utc(): return datetime.now(timezone.utc).isoformat()
def note(phase,**data):print(json.dumps(dict(phase=phase,at_utc=utc(),**data)),flush=True)
def load(path): return json.loads(Path(path).read_text(encoding='utf-8'))
def digest(raw): return hashlib.sha256(raw).hexdigest()
def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def absolute(path):
    p=Path(path)
    return Path(os.path.abspath(p if p.is_absolute() else ROOT/p))
def write(path, data):
    with Path(path).open('x',encoding='utf-8',newline='\n') as f:
        json.dump(data,f,ensure_ascii=False,indent=2);f.write('\n')
def identity(path, role):
    p=absolute(path)
    return dict(path=str(p),resolved_path=str(p.resolve()),bytes=p.stat().st_size,
                sha256=sha(p),role=role)
def check(row):
    p=absolute(row['path']); assert p.is_file(), str(p)
    assert sha(p)==row['sha256'], 'SHA changed: '+str(p)
    if 'bytes' in row:assert p.stat().st_size==row['bytes']
    if 'resolved_path' in row:assert str(p.resolve()).casefold()==row['resolved_path'].casefold()
    return p
def constants(path):
    result={}
    for n in ast.parse(path.read_bytes()).body:
        if isinstance(n,(ast.Assign,ast.AnnAssign)):
            target=n.targets[0] if isinstance(n,ast.Assign) else n.target
            if isinstance(target,ast.Name):
                try:result[target.id]=ast.literal_eval(n.value)
                except (ValueError,TypeError):pass
    return result


class Assembler:
    def __init__(self, gate, output):
        self.gate=gate;self.output=output;self.files={};self.nodes={};self.active=set()
        self.packages={};self.trees={};self.sources={};self.sdk_members=set()
        self.cache_rows=[];self.sdk_verified=False
    def pin(self,path,role):
        row=identity(path,role);key=row['path'].casefold()
        if key in self.files:assert self.files[key]['sha256']==row['sha256']
        else:self.files[key]=row
        return row
    def bind(self,row,role):
        return self.pin(check(row),role)
    def find(self,module):
        rel=Path(*module.split('.')).with_suffix('.lean'); found=[]
        for owner,package in self.packages.items():
            p=package/rel
            if p.is_file():found.append((p,owner))
        # Official archive keeps Lake sources below src/lean/lake even though
        # their modules/data are Lake.* / lib/lean/Lake.* respectively.
        for source_root in [SDK/'src/lean',SDK/'src/lean/lake']:
            p=source_root/rel
            if p.is_file():found.append((p,'SDK'))
        assert len(found)==1, 'Ambiguous/missing source '+module+': '+str(found)
        return found[0]
    def canonical(self,path,owner):
        key=str(path)
        if key in self.sources:return self.sources[key]
        if owner=='SDK':
            value=path.read_bytes();self.sdk_members.add(path.relative_to(SDK).as_posix())
        else:
            value=canonical_git_blob(path,path.relative_to(self.packages[owner]).as_posix(),self.trees[owner])
        self.pin(path,'pinned-source-'+owner);self.sources[key]=value
        return value
    def visit(self,module):
        if module in self.nodes:return
        assert module not in self.active, 'Import cycle '+module
        self.active.add(module)
        source,owner=self.find(module);raw=self.canonical(source,owner)
        is_module,deps,prelude=header(raw)
        # ParseImportsFast inserts both ordinary and meta Init when not prelude.
        # One physical Init closure is sufficient; source import duplicates are
        # retained for Lake hashes, where SDK modules are ignored by findModules.
        closure_deps=([] if prelude else ['Init'])+deps
        for dep in closure_deps:self.visit(dep)
        if owner=='SDK':base=SDK/'lib/lean'/Path(*module.split('.'))
        else:base=self.packages[owner]/'.lake/build/lib/lean'/Path(*module.split('.'))
        assert base.with_suffix('.olean').is_file(), 'Missing cached '+module
        self.nodes[module]=dict(source=source,owner=owner,base=base,raw=raw,
                                imports=deps,is_module=is_module)
        if len(self.nodes)%500==0:note('source-import-closure',modules=len(self.nodes))
        if owner=='SDK':
            suffixes=['olean','olean.server','olean.private','ir','ir.sig']
            for suffix in suffixes:
                p=base.with_suffix('.'+suffix)
                if p.is_file():self.sdk_members.add(p.relative_to(SDK).as_posix())
        self.active.remove(module)
    def archive_verify(self):
        note('official-sdk-archive-verify',selected_members=len(self.sdk_members))
        assert sha(ARCHIVE)==ARCHIVE_SHA, 'Official SDK archive SHA'
        self.pin(ARCHIVE,'official-SDK-archive')
        self.sdk_members.update(['include/lean/lean.h','bin/lean.exe'])
        for p in (SDK/'bin').glob('*.dll'):self.sdk_members.add(p.relative_to(SDK).as_posix())
        for rel in ['Init/Prelude.lean','Init/Data/Hashable.lean','Lean/Elab/ParseImportsFast.lean',
                    'lake/Lake/Build/Trace.lean','lake/Lake/Build/Module.lean']:
            self.sdk_members.add('src/lean/'+rel)
        wanted=set(self.sdk_members);seen=set();rows=[]
        previous=self.gate.get('reuse_previous_sdk_archive_check')
        if previous is not None:
            assert self.gate['previous_sdk_archive_component_accepted'] is True
            prior_path=check(previous);prior=load(prior_path)
            self.pin(prior_path,'actual-prior-complete-SDK-archive-member-check')
            assert prior['archive_sha256']==ARCHIVE_SHA and prior['all_selected_members_identical'] is True
            for row in prior['selected_members']:
                p=absolute(row['path']);rel=p.relative_to(SDK).as_posix()
                assert rel not in seen and rel in wanted
                check(row);seen.add(rel)
                # Current bytes/resolved paths were just rechecked against the
                # exact actual archive PASS receipt. Avoid a redundant read.
                key=str(p).casefold()
                if key in self.files:assert self.files[key]['sha256']==row['sha256']
                else:self.files[key]={**row,'role':'revalidated-official-SDK-identical-archive-member'}
                rows.append(self.files[key])
            assert seen==wanted, 'Current SDK member selection differs from prior actual check'
            write(self.output/'official-sdk-check.json',dict(archive_sha256=ARCHIVE_SHA,
              selected_members=rows,all_selected_members_identical=True,compiler_main_runs=0,
              reuse_method='Actual prior archive-member equality receipt plus current SHA/size/resolved-path revalidation of every selected member and archive',
              previous_actual_archive_check=identity(prior_path,'prior-actual-SDK-archive-PASS')))
            self.pin(self.output/'official-sdk-check.json','actual-SDK-byte-check')
            self.sdk_verified=True;note('official-sdk-revalidation-PASS',selected_members=len(rows))
            return
        with ARCHIVE.open('rb') as compressed:
            with zstandard.ZstdDecompressor().stream_reader(compressed) as stream:
                with tarfile.open(fileobj=stream,mode='r|') as tar:
                    for member in tar:
                        prefix='lean-4.33.0-rc2-windows/'
                        assert member.name==prefix[:-1] or member.name.startswith(prefix)
                        rel=member.name.removeprefix(prefix)
                        if rel not in wanted:continue
                        assert member.isfile() and rel not in seen, rel
                        f=tar.extractfile(member);h=hashlib.sha256()
                        for b in iter(lambda:f.read(1048576),b''):h.update(b)
                        p=SDK/rel;assert p.stat().st_size==member.size and sha(p)==h.hexdigest(), rel
                        rows.append(self.pin(p,'official-SDK-identical-archive-member'))
                        seen.add(rel)
        assert seen==wanted, 'SDK archive absent members: '+str(wanted-seen)
        write(self.output/'official-sdk-check.json',dict(archive_sha256=ARCHIVE_SHA,
              selected_members=rows,all_selected_members_identical=True,compiler_main_runs=0))
        self.pin(self.output/'official-sdk-check.json','actual-SDK-byte-check')
        self.sdk_verified=True
        note('official-sdk-archive-PASS',selected_members=len(rows))
    def legacy_all_art_hash(self,module):
        n=self.nodes[module];h=1723
        if 'all_art_hash' in n:return n['all_art_hash']
        order=['olean','olean.server','olean.private','ir.sig','ir'] if n['is_module'] else ['olean']
        for suffix in order:
            p=n['base'].with_suffix('.'+suffix)
            h=mix(h,int(self.sdk_hash.lake_bytes(p.read_bytes()),16))
        n['all_art_hash']=h
        return h
    def legacy_trans_hash(self,module):
        n=self.nodes[module]
        if 'legacy_trans' in n:return n['legacy_trans']
        h=1723
        for dep in n['imports']:
            if self.nodes[dep]['owner']=='SDK':continue
            h=mix(h,self.legacy_trans_hash(dep));h=mix(h,self.legacy_all_art_hash(dep))
        n['legacy_trans']=h;return h
    def legacy_trace(self,module,trace):
        n=self.nodes[module];assert n['owner']=='Zeta23' and not n['is_module']
        inputs=trace['inputs'];assert len(inputs)==9
        # Full fixed package configuration, rather than accepting arbitrary
        # trace captions. Source, all imports, SDK/options/name leaves checked.
        deps=inputs[0];assert deps[0]=='deps'
        extra,imps=deps[1]
        assert extra==['Zeta23/Zeta23:extraDep',[['@Zeta23:extraDep','00000000000006bb']]]
        expected=[]
        for dep in n['imports']:
            if self.nodes[dep]['owner']=='SDK':continue
            expected += [[dep+' transitive imports (legacy)',f'{self.legacy_trans_hash(dep):016x}'],
                         [dep+':importAllArts',f'{self.legacy_all_art_hash(dep):016x}']]
        assert imps==['imports',expected], 'Legacy import trace mismatch: '+module
        assert inputs[1]==['libs',[[s,'00000000000006bb'] for s in
          ['import dynlibs','package external libraries','module dynlibs','module plugins']]]
        assert inputs[2]==['Lean 4.33.0, commit '+SDK_COMMIT,'3eca9d16ab6c877d']
        assert Path(inputs[3][0]).resolve()==n['source'].resolve()
        assert inputs[3][1]==self.sdk_hash.lake_text(n['source'].read_bytes())
        opts=['-DrelaxedAutoImplicit=false','-Dpp.unicode.fun=true']
        assert inputs[4]==['options',[[s,f'{mix(1723,self.sdk_hash.string(s)):016x}'] for s in opts]]
        assert inputs[5]==['isModule: false',f'{mix(1723,13):016x}']
        def name_hash(name):
            h=1723
            for part in name.split('.'):h=mix(h,self.sdk_hash.string(part))
            return h
        assert inputs[6]==['Module.name: '+module,f'{mix(1723,name_hash(module)):016x}']
        assert inputs[7]==['Package.id?: (some Zeta23)',f'{mix(1723,mix(name_hash("Zeta23"),13)):016x}']
        assert inputs[8]==['Module.leanArgs: #[]','00000000000006bb']
        def node_hash(node):
            assert isinstance(node,list) and len(node)==2 and isinstance(node[0],str)
            if isinstance(node[1],str):return int(node[1],16)
            assert isinstance(node[1],list)
            h=1723
            for child in node[1]:h=mix(h,node_hash(child))
            return h
        dep_hash=1723
        for node in inputs:dep_hash=mix(dep_hash,node_hash(node))
        assert trace['depHash']==f'{dep_hash:016x}', 'Legacy complete depHash '+module
    def outputs(self,module):
        n=self.nodes[module]
        if n['owner']=='SDK':return
        base=n['base'];trace=load(base.with_suffix('.trace'))
        assert trace['outputs'].get('m',False)==n['is_module'], module
        data=verify_outputs(trace,base,self.sdk_hash,self.pin)
        if n['owner']=='Zeta23':
            # Exact inputs are validated separately below with list length 9.
            self.legacy_trace(module,trace)
        else:
            source_hash=self.cache.module(module)
            ltar=Path(self.gate['mathlib_cache_directory'])/(f'{source_hash:016x}.ltar')
            with ltar.open('rb') as f:head=f.read(12)
            assert head[:4] in [b'LTAR',b'LTR2',b'LTR3']
            assert int.from_bytes(head[4:12],'little')==int(trace['depHash'],16), 'Source cache depHash '+module
            self.pin(ltar,'source-addressed-Mathlib-cache-archive')
            self.cache_rows.append(dict(module=module,source_cache_hash=f'{source_hash:016x}',
              ltar=str(ltar),depHash=trace['depHash'],output_files=[str(p) for p in data]))
        n['data']=data
    def tool_provenance(self,base):
        cp=ROOT/'verification/comparator-core-public-driver-check.json';c=load(cp)
        self.pin(cp,'historical-actual-core-audit-cache-provenance')
        assert c['compiler']==self.gate['lean_version'] and c['exit_code']==0
        assert c['local_comparator_core_passed'] and c['source_unchanged_during_check']
        assert c['comparator_commit']==base['tool_commits']['Comparator']
        assert c['exporter_commit']==base['tool_commits']['lean4export']
        overlay=self.output/'tool-overlay';overlay.mkdir()
        five=['Comparator','Comparator.Axioms','Comparator.Compare','Comparator.Util','Export.Parse']
        rows=[]
        for module in five:
            root=ROOT/('tmp/Comparator/.lake/packages/lean4export/.lake/build/lib/lean' if module=='Export.Parse'
                       else 'tmp/Comparator/.lake/build/lib/lean')
            p=root/Path(*module.split('.')).with_suffix('.olean');rel=p.relative_to(ROOT).as_posix()
            assert sha(p)==c['input_sha256'][rel], 'Historical tool olean mismatch '+module
            self.pin(p,'exact-historical-tool-olean')
            target=overlay/Path(*module.split('.')).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(p,target);row=self.pin(target,'source-bound-interpreted-tool-cache')
            assert row['sha256']==c['input_sha256'][rel];rows.append(row)
        r=load(ROOT/'verification/three-website-declarations-modular-nanoda.json')
        self.pin(ROOT/'verification/three-website-declarations-modular-nanoda.json','actual-old-exporter-Nano-receipt')
        assert r['compiler']==self.gate['lean_version'] and r['export_process_ran'] and r['export_exit_code']==0
        assert r['inputs_unchanged']
        paths={'exporter_binary':ROOT/'tmp/lean4export/.lake/build/bin/lean4export.exe',
               'nanoda_binary':ROOT/'tmp/kernel-tools/nanoda-target/release/nanoda_bin'}
        for key,p in paths.items():
            assert r['sha256_before'][key]==r['sha256_after'][key]==sha(p)
            self.pin(p,'exact-source-bound-historical-native-tool')
        sources=[];tooltrees={}
        for owner in ['Comparator','lean4export']:
            tooltrees[owner]=git_tree(ROOT/'tmp'/owner,base['tool_commits'][owner])
        expected=constants(RUNNER)['TOOL_SOURCE_LF_SHA']
        for row in base['trusted_tool_sources']:
            p=Path(row['path']);owner,rel=row['logical_name'].split('/',1)
            raw=canonical_git_blob(p,rel,tooltrees[owner])
            assert digest(raw.replace(b'\r\n',b'\n'))==expected[row['logical_name']]
            # Historical CoreAudit pinned its nested exporter checkout. Its
            # bytes equal this top-level native exporter source at the same
            # fixed commit; preserve that actual receipt path in the bridge.
            receipt_path=(ROOT/'tmp/Comparator/.lake/packages/lean4export'/rel
                          if owner=='lean4export' else p)
            receipt_rel=receipt_path.relative_to(ROOT).as_posix()
            assert sha(p)==sha(receipt_path)==c['input_sha256'][receipt_rel]
            self.pin(receipt_path,'actual-historical-tool-source-path')
            out=self.pin(p,'pinned-trusted-tool-source');out={**out,'logical_name':row['logical_name']};sources.append(out)
        # Nested Parse is source-identical to fixed exporter source, not merely
        # a same-named arbitrary olean selected through search-path accident.
        nested=ROOT/'tmp/Comparator/.lake/packages/lean4export'
        assert git_tree(nested,base['tool_commits']['lean4export'])
        p=nested/'Export/Parse.lean';raw=canonical_git_blob(p,'Export/Parse.lean',git_tree(nested,base['tool_commits']['lean4export']))
        assert digest(raw.replace(b'\r\n',b'\n'))==expected['lean4export/Export/Parse.lean']
        self.pin(p,'nested-Parse-source')
        old=ROOT/'verification/gram-defect-single-20261014/independent-kernel.json';oldr=load(old)
        self.pin(old,'source-to-identical-Nano-and-exporter-provenance')
        nano=oldr['tool_provenance']['nanoda_binary'];assert nano['sha256']==sha(paths['nanoda_binary'])
        assert nano['pin']==base['tool_commits']['nanoda']
        tree=git_tree(ROOT/'tmp/nanoda',base['tool_commits']['nanoda'])
        cargo=ROOT/'tmp/nanoda/Cargo.toml';raw=canonical_git_blob(cargo,'Cargo.toml',tree)
        assert digest(raw)==nano['cargo_git_blob_content_sha256'];self.pin(cargo,'Nano-pinned-Cargo-source')
        self.pin(ROOT/'tmp/nanoda/Cargo.lock','Nano-dependency-lock')
        for rel,(mode,kind,oid) in tree.items():
            if kind=='blob' and (rel.endswith('.rs') or rel in ['Cargo.toml','Cargo.lock']):
                p=ROOT/'tmp/nanoda'/rel;canonical_git_blob(p,rel,tree)
                self.pin(p,'Nano-fixed-commit-source')
        for rel in ['tmp/lean4export/.lake/build/bin/lean4export.exe.trace',
                    'tmp/lean4export/.lake/build/bin/lean4export.exe.rsp',
                    'tmp/kernel-tools/build-nanoda.sh','tmp/kernel-tools/build-nanoda.log']:
            self.pin(ROOT/rel,'retained-native-build-provenance')
        return overlay,sources
    def pe_runtime(self):
        # Stop recursive traversal at the explicitly reviewed Windows System32
        # OS boundary. Its delay-import graph is not an application requirement.
        spec=importlib.util.spec_from_file_location('file_pe_inspector',BASE/'inspect_runtime.py')
        mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
        self.pin(BASE/'inspect_runtime.py','PE-static-parser-source')
        system=Path('C:/Windows/System32');self.pin(system/'apisetschema.dll','OS-API-set-boundary')
        pycap=load(HERE/'controller-stdlib-loaded-modules.json');self.pin(HERE/'controller-stdlib-loaded-modules.json','actual-Python-extension-loader-observation')
        assert pycap['runner_sha256']==RUNNER_SHA and pycap['python'].casefold()==sys.executable.casefold()
        assert pycap['sys_version']==sys.version
        for row in pycap['all_actual_loaded_modules_with_instrumentation']:
            self.bind(row,'current-matching-actual-Python-loaded-module')
        # Exact imported Python library files (including actual bytecode cache
        # when present) are installed-controller trusted data, pinned here.
        for module in tuple(sys.modules.values()):
            for name in ['__file__','__cached__']:
                value=getattr(module,name,None)
                if value and Path(value).is_file() and Path(value).absolute().is_relative_to(Path(sys.executable).parent):
                    self.pin(Path(value),'installed-Python-controller-library-file')
        known={Path(r['path']).name.casefold():Path(r['path']) for r in pycap['all_actual_loaded_modules_with_instrumentation']}
        roots=[SDK/'bin/lean.exe',ROOT/'tmp/lean4export/.lake/build/bin/lean4export.exe',Path(sys.executable),
               system/'wsl.exe',system/'taskkill.exe']
        roots += [Path(r['path']) for r in pycap['all_actual_loaded_modules_with_instrumentation']]
        comp=load(BASE/'evidence/compiler19056-loaded-modules.json')
        self.pin(BASE/'evidence/compiler19056-loaded-modules.json','historical-actual-Lean-loaded-paths')
        roots += [Path(r['Path']) for r in comp['Modules']]
        todo=list(roots);seen=set();edges=[]
        while todo:
            p=todo.pop();key=str(p.absolute()).casefold()
            if key in seen:continue
            seen.add(key);self.pin(p,'actual-or-ordinary-import-runtime-file')
            if p.resolve().is_relative_to(system.resolve()):continue
            for edge in mod.PE(p).imports():
                name=edge['name'];record=dict(importer=str(p),**edge)
                if name.casefold().startswith(('api-ms-','ext-ms-')):
                    record['resolution']='root-reviewed-OS-API-set-boundary'
                else:
                    candidates=[p.parent/name,system/name,SDK/'bin'/name,Path(sys.executable).parent/name,
                                Path(sys.executable).parent/'DLLs'/name]
                    target=known.get(name.casefold()) or next((x for x in candidates if x.is_file()),None)
                    assert target is not None, 'Unresolved non-OS PE dependency '+str(record)
                    record['resolved']=str(target);todo.append(target)
                edges.append(record)
        write(self.output/'application-pe-closure.json',dict(edges=edges,
              system32_recursive_delay_imports_outside_application_scope=True,
              root_reviewed_boundary=self.gate['reviewed_scope']['windows_os_boundary']))
        self.pin(self.output/'application-pe-closure.json','actual-application-PE-closure')
        elf=load(BASE/'evidence/WSL-ELF-loader-resolution.json');self.pin(BASE/'evidence/WSL-ELF-loader-resolution.json','actual-WSL-loader-metadata')
        for row in elf['files']:
            if row['path'].startswith('/mnt/e/'):continue
            self.bind(dict(path=row['Windows_read_path'],bytes=row['bytes'],sha256=row['sha256']),
                      'ELF-loader-or-launcher-runtime')
    def run(self):
        for row in self.gate['metadata_inputs']:self.bind(row,'gate-pinned-metadata-input')
        base=load(BASE/'runtime-closure-CANDIDATE-INCOMPLETE.json')
        self.pin(BASE/'runtime-closure-CANDIDATE-INCOMPLETE.json','preparation-scope-input')
        assert sha(RUNNER)==RUNNER_SHA;self.pin(RUNNER,'frozen-fullchain-runner')
        for owner,rev in base['package_source_revisions'].items():
            package=ROOT/'.lake/packages'/owner;self.packages[owner]=package
            self.trees[owner]=git_tree(package,rev)
            # Bind the selected fixed package configuration as well as source
            # leaves. In particular Zeta's legacy trace options correspond to
            # this exact lakefile.toml, not a mutable same-HEAD config.
            for rel in ['lakefile.toml','lakefile.lean','lean-toolchain','lake-manifest.json']:
                if rel in self.trees[owner]:self.canonical(package/rel,owner)
        for rootrow in self.gate['candidate_import_source_files']:
            p=check(rootrow);self.pin(p,'candidate-source-imports-only-never-compiled')
            for module in imports(p.read_bytes()):
                if module not in TOOL_MODULES and module.split('.')[0] not in ['ChallengeDeps','Challenge','Solution','StructuralW9A220261020']:
                    self.visit(module)
        for row in base['trusted_tool_sources']:
            for module in imports(Path(row['path']).read_bytes()):
                if module not in TOOL_MODULES:self.visit(module)
        # Trusted imported library closure only. No cached user module added.
        self.archive_verify()
        assert self.sdk_verified
        self.sdk_hash=SDKHash(SDK)
        self.pin(self.sdk_hash.loaded_path,'actual-borrowed-hash-DLL-loaded-path')
        self.cache=CacheSourceHash(self.sdk_hash,self.packages['mathlib'],self.find,self.canonical)
        for rel in ['lakefile.lean','lean-toolchain','lake-manifest.json','Cache/Hashing.lean','Cache/IO.lean']:
            p=self.packages['mathlib']/rel;self.canonical(p,'mathlib')
        for index,module in enumerate(list(self.nodes)):
            self.outputs(module)
            if (index+1)%500==0:note('source-cache-check',modules=index+1)
        note('source-cache-check-PASS',modules=len(self.nodes))
        package_root=self.output/'package-overlay';package_root.mkdir()
        libs=[]
        for owner in self.packages:
            lib=package_root/owner/'.lake/build/lib/lean';lib.mkdir(parents=True);libs.append(str(lib))
        for module,n in self.nodes.items():
            if n['owner']=='SDK':continue
            for src in n['data']:
                relative=src.relative_to(self.packages[n['owner']]/'.lake/build/lib/lean')
                dst=package_root/n['owner']/'.lake/build/lib/lean'/relative
                dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
                assert sha(src)==sha(dst);self.pin(dst,'source-bound-clean-trusted-library-overlay')
        for lib in libs:
            for rel in FORBIDDEN:assert not (Path(lib)/rel).exists()
            assert not (Path(lib)/'StructuralW9A220261020').exists()
        tool_lib,sources=self.tool_provenance(base);self.pe_runtime()
        core=self.pin(ROOT/'tools/ComparatorCoreAudit.lean','locked-CoreAudit-source')
        assert core['sha256']==base['coreaudit_source_sha256']
        write(self.output/'cache-source-check.json',dict(module_count=len(self.nodes),
             package_modules=sum(n['owner']!='SDK' for n in self.nodes.values()),
             cache_source_hashes=self.cache_rows,SDKHash_exports_called=['lean_string_hash','lean_byte_array_hash'],
             compiler_main_runs=0,proof_runs=0))
        self.pin(self.output/'cache-source-check.json','actual-source-cache-verification')
        # Rehash every selected source/data dependency and overlay before seal.
        for row in list(self.files.values()):check(row)
        receipt=self.output/'read-only-setup-receipt.json'
        write(receipt,dict(schema='w9a2-read-only-runtime-setup-v1',assembler_pid=os.getpid(),
             assembler_argv=sys.argv,assembler_sha256=sha(HERE/'assemble.py'),
             started=identity(self.output/'started.json','actual-assembler-start'),
             gate=identity(self.gate_path,'root-reviewed-metadata-only-setup-gate'),
             proof_runs=0,user_proofs_compiled_or_reused_in_setup=False,
             source_and_data_checks_passed=True,completed_at_utc=utc()))
        py=load(HERE/'controller-stdlib-loaded-modules.json')
        fragment=load(ROOT/'research-goal-20261020-w9a2-verification-preparation-v1/gate-template.json')['runtime']
        fragment.update(root_confirmed_setup_terminal_exit_code=None,
          root_reviewed_complete_runtime_closure=False,
          python_controller={**identity(sys.executable,'Python-controller'),'version':py['sys_version']},
          package_root=str(package_root),package_libs=libs,interpreted_tool_libs=[str(tool_lib)])
        for key,p in [('wsl_executable','C:/Windows/System32/wsl.exe'),('taskkill_executable','C:/Windows/System32/taskkill.exe')]:
            fragment[key]=identity(p,key)
        elf=load(BASE/'evidence/WSL-ELF-loader-resolution.json')
        nano_row=next(r for r in elf['files'] if r['path']==fragment['nanoda']['execution_path'])
        assert nano_row['sha256']==fragment['nanoda']['host_binary']['sha256']
        fragment['nanoda']['resolved_execution_path']=nano_row['resolved_path']
        closure=dict(schema='w9a2-trusted-runtime-closure-v1',
          complete_source_bound_runtime_closure_verified=True,
          user_proofs_compiled_or_reused_in_setup=False,official_runtime_equivalence_claimed=False,
          tool_commits=base['tool_commits'],package_source_revisions=base['package_source_revisions'],
          coreaudit_source_sha256=base['coreaudit_source_sha256'],trusted_tool_sources=sources,
          trusted_setup_receipt=identity(receipt,'actual-read-only-setup-receipt'),
          candidate_package_libs=libs,interpreted_tool_libs=[str(tool_lib)],package_root=str(package_root),
          runtime_gate_fragment=fragment,reviewed_scope=self.gate['reviewed_scope'],
          root_confirmed_setup_exit0=False,candidate_pipeline_runs=0,
          files=list(self.files.values()),missing_evidence=[])
        write(self.output/'closure.json',closure)


def main():
    if not __debug__:raise RuntimeError('Python optimization disables validation assertions; refusing setup')
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--gate',required=True)
    args=ap.parse_args();gate_path=absolute(args.gate);gate=load(gate_path)
    assert os.name=='nt' and gate['schema']=='w9a2-metadata-runtime-closure-gate-v1'
    assert gate['authorized'] is True and gate['allow_compiler_main'] is False
    assert gate['allow_export_or_kernel_main'] is False
    assert gate['allow_two_borrowed_sdk_hash_apis'] is True
    for name in ['assemble.py','cache_binding.py']:
        assert sha(HERE/name)==gate['script_sha256'][name]
    assert gate['reviewed_scope']['windows_os_boundary']=='Windows System32, OS loader and API-set resolution trusted as installed; no recursive OS delay-import closure claim'
    assert gate['reviewed_scope']['mathlib_cache_source_binding']=='Pinned Git source -> Cache.Hashing generation5 source hash -> local ltar header depHash -> matching trace outputs -> actual data LakeHash; not an official cache signature or independent proof check'
    out=absolute(gate['output_directory']);assert out.is_relative_to(ROOT/'tmp/w9a2-20261020')
    out.mkdir(parents=True,exist_ok=False)
    write(out/'started.json',dict(schema='w9a2-runtime-closure-started-v1',pid=os.getpid(),argv=sys.argv,
          script=identity(HERE/'assemble.py','assembler'),gate=identity(gate_path,'setup-gate'),at_utc=utc()))
    try:
        a=Assembler(gate,out);a.gate_path=gate_path;a.run()
        write(out/'terminal.json',dict(exit_code=0,assembler_pid=os.getpid(),proof_runs=0,at_utc=utc(),
              closure=identity(out/'closure.json','actual-runtime-closure')))
        print(json.dumps(dict(exit_code=0,output=str(out),closure=identity(out/'closure.json','actual-runtime-closure'))))
    except BaseException as error:
        write(out/'terminal.json',dict(exit_code=1,assembler_pid=os.getpid(),proof_runs=0,at_utc=utc(),
              error=str(error),traceback=traceback.format_exc()))
        raise


if __name__=='__main__':main()
