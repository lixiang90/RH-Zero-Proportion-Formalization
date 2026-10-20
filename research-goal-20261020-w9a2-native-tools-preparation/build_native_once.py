"""Gated Windows trusted-tools setup. PREPARED ONLY; no preparation execution.

Only the fixed nine trusted sources and SDK are built, in a new empty project.
No Mathlib/Zeta23/user proof imports, cache fetch, exporter main or kernel replay.
Loader-only child probes stop at the Windows automatic initial breakpoint.
"""
from datetime import datetime,timezone
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time
import traceback

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
CORE_SHA='7e88e84d1d35d5f3115c97a574cc64dd089ef713ef6f9bccb2303fbd41e07ff2'
MODULES={'Export','Export.Parse','ExporterMain','Comparator','Comparator.Util',
         'Comparator.Compare','Comparator.Axioms','ComparatorMain','CoreAudit'}
SDK_IMPORTS={'Lean','Lean.Declaration','Lean.Environment','Lean.Data.Json.Parser',
             'Std.Data.HashMap','Std.Data.HashMap.Basic','Std.Internal.Parsec.String'}


def load(path):return json.loads(Path(path).read_text(encoding='utf-8'))


class Setup:
    def __init__(self,args):
        self.args=args;self.t0=time.monotonic();self.deadline=None
        self.work=None;self.active=None;self.lock=None;self.lock_raw=None
        self.bound={};self.commands=[]
        self.receipt={'schema':'w9a2-windows-trusted-tool-installation-v1',
            'scope':'Trusted SDK-only setup, no candidate compilation/export/replay',
            'proof_runs':0,'user_proofs_compiled_or_reused':False,'automatic_retries':0,
            'passed':False,'official_website_acceptance':False}

    def remaining(self):
        if self.deadline is None:return 60
        left=self.deadline-time.monotonic()
        if left<=0:raise TimeoutError('Trusted-tools setup deadline expired')
        return left

    def sha(self,path):
        h=hashlib.sha256()
        with Path(path).open('rb') as stream:
            for block in iter(lambda:stream.read(1048576),b''):
                self.remaining();h.update(block)
        return h.hexdigest()

    def path(self,path):
        p=Path(path);return p.absolute() if p.is_absolute() else (ROOT/p).absolute()

    def bind(self,path,expected=None):
        p=self.path(path);row={'path':str(p),'resolved_path':str(p.resolve()),
                              'bytes':p.stat().st_size,'sha256':self.sha(p)}
        if expected and row['sha256']!=expected:raise RuntimeError('Pinned SHA changed: '+str(p))
        self.bound[str(p)]=row;return row

    def unchanged(self):
        for row in list(self.bound.values()):
            p=Path(row['path'])
            if str(p.resolve())!=row['resolved_path'] or p.stat().st_size!=row['bytes'] or self.sha(p)!=row['sha256']:
                raise RuntimeError('Bound setup input/artifact changed: '+str(p))

    def write(self,path,data,bind=True):
        self.remaining();p=Path(path);p.parent.mkdir(parents=True,exist_ok=True)
        raw=data if isinstance(data,bytes) else (json.dumps(data,ensure_ascii=False,indent=2)+'\n').encode()
        with p.open('xb') as stream:stream.write(raw);stream.flush();os.fsync(stream.fileno())
        if bind:self.bind(p,hashlib.sha256(raw).hexdigest())

    def no_other_compiler(self):
        cmd=[self.powershell,'-NoLogo','-NoProfile','-NonInteractive','-Command',
             "@(Get-Process lean,lake,clang,lld -ErrorAction SilentlyContinue).Count"]
        result=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=15,check=True)
        if result.stdout.decode().strip()!='0':raise RuntimeError('Another Windows compiler/tool build is live')
        result=subprocess.run([self.wsl,'--distribution',self.gate['wsl_distribution'],'--exec',
             '/usr/bin/pgrep','-a','-x','lean|lake|clang|ld.lld|lld-link'],
             stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=15,check=False)
        if result.returncode!=1:raise RuntimeError('Linux compiler live or exclusivity observation failed')

    def command(self,label,argv):
        log=self.work/'logs'/(label+'.log');start=time.monotonic();p=None
        record={'label':label,'argv':argv,'started_monotonic':start}
        self.commands.append(record)
        try:
            with log.open('xb') as stream:
                p=subprocess.Popen(argv,cwd=self.work,env=self.env,stdout=stream,
                    stderr=subprocess.STDOUT,creationflags=subprocess.CREATE_NEW_PROCESS_GROUP)
                self.active=p;record['pid']=p.pid
                self.write(self.work/'logs'/(label+'.child.json'),record)
                print(json.dumps({'stage':label,'pid':p.pid,'remaining_seconds':self.remaining()}),flush=True)
                record['exit_code']=p.wait(timeout=self.remaining())
                stream.flush();os.fsync(stream.fileno())
        except BaseException:
            if p is not None and p.poll() is None:
                subprocess.run([self.taskkill,'/PID',str(p.pid),'/T','/F'],stdout=subprocess.DEVNULL,
                               stderr=subprocess.DEVNULL,timeout=15,check=False)
                p.wait(timeout=5)
            raise
        finally:
            self.active=None;record['elapsed_seconds']=time.monotonic()-start
        record['log']=self.bind(log)
        self.write(self.work/'logs'/(label+'.terminal.json'),record)
        if record['exit_code']!=0:raise RuntimeError('Trusted stage failed; no retry: '+label)

    def execute(self):
        if os.name!='nt':raise RuntimeError('This backup setup is Windows-only')
        gate_path=self.path(self.args.gate);self.bind(gate_path,self.args.gate_sha256)
        self.gate=gate=load(gate_path)
        if gate['allow_trusted_native_tools_setup'] is not True or gate['all_previous_compiler_handles_terminal_by_root'] is not True:
            raise RuntimeError('No affirmative root setup/exclusivity gate')
        if not gate['sole_owner'] or gate['automatic_retries']!=0:raise RuntimeError('Wrong owner/retry scope')
        self.deadline=self.t0+gate['setup_timeout_seconds']
        if not 1<=gate['setup_timeout_seconds']<=7200:raise RuntimeError('Invalid setup deadline')
        self.bind(__file__,gate['runner_sha256'])
        prepared_path=HERE/'prepared-files.json';self.bind(prepared_path,gate['prepared_sha256'])
        for row in load(prepared_path)['files']:self.bind(HERE/row['path'],row['sha256'])
        self.bind(gate['root_terminal_evidence']['path'],gate['root_terminal_evidence']['sha256'])
        self.sdk=self.path(gate['SDK_root'])
        self.bind(self.sdk/'bin/lean.exe','bc137e6662c48eedf2cdf167fb176080e18a15f57e248d214df0cb3939248683')
        self.powershell=str(self.path(gate['powershell']));self.wsl=str(self.path(gate['wsl']))
        self.taskkill=str(self.path(gate['taskkill']))
        self.no_other_compiler()
        self.work=self.path(gate['work_directory']).resolve()
        if not self.work.is_relative_to(ROOT/'tmp') or self.work.exists():raise RuntimeError('Fresh workspace/tmp setup directory required')
        self.lock=ROOT/'tmp/w9a2-20261020/trusted-native-active.lock'
        self.lock_raw=(json.dumps({'pid':os.getpid(),'gate_sha256':self.args.gate_sha256})+'\n').encode()
        self.write(self.lock,self.lock_raw,bind=False)
        self.no_other_compiler()
        self.work.mkdir(parents=True,exist_ok=False)
        for name in ['source','logs','home','temporary']:(self.work/name).mkdir()
        self.env={'PATH':str(self.sdk/'bin')+';'+os.environ['SYSTEMROOT']+'\\System32;'+os.environ['SYSTEMROOT'],
                  'SYSTEMROOT':os.environ['SYSTEMROOT'],'WINDIR':os.environ['WINDIR'],
                  'HOME':str(self.work/'home'),'USERPROFILE':str(self.work/'home'),
                  'TEMP':str(self.work/'temporary'),'TMP':str(self.work/'temporary'),
                  'LEAN_SYSROOT':str(self.sdk),'LEAN_ABORT_ON_PANIC':'1'}
        sdk_inputs=[]
        for top in ['bin','include','lib']:
            for p in (self.sdk/top).rglob('*'):
                if p.is_file():sdk_inputs.append(self.bind(p))
        source_spec=load(HERE/'source-pins.json')
        actual=set()
        for row in source_spec['sources']:
            source=HERE/row['prepared_path'];self.bind(source,row['sha256'])
            data=source.read_bytes();module=row['module'];actual.add(module)
            imported=set(re.findall(rb'^import\s+(\S+)',data,re.M))
            if not {v.decode() for v in imported}<=MODULES|SDK_IMPORTS:raise RuntimeError('Non-SDK/non-tool import')
            if module=='CoreAudit' and hashlib.sha256(data).hexdigest()!=CORE_SHA:raise RuntimeError('Locked CoreAudit changed')
            self.write(self.work/'source'/row['destination'],data)
        if actual!=MODULES:raise RuntimeError('The exact nine trusted source modules are required')
        self.write(self.work/'lakefile.toml',(HERE/'lakefile.toml.in').read_bytes())
        self.write(self.work/'lean-toolchain',b'leanprover/lean4:v4.33.0-rc2\n')
        self.write(self.work/'lake-manifest.json',{'version':'1.2.0','packagesDir':'.lake/packages',
            'packages':[],'name':'W9A2TrustedNativeTools','lakeDir':'.lake'})
        self.receipt.update({'started_at_utc':datetime.now(timezone.utc).isoformat(),
            'gate_sha256':self.args.gate_sha256,'SDK_input_pins':sdk_inputs,'source_provenance':source_spec})
        self.write(self.work/'started.json',self.receipt)
        self.command('lake-version',[str(self.sdk/'bin/lake.exe'),'--version'])
        self.command('clang-version',[str(self.sdk/'bin/clang.exe'),'--version'])
        self.command('trusted-nine-source-native-build',[str(self.sdk/'bin/lake.exe'),
                     '--no-cache','-v','build','lean4export','coreaudit','comparator'])
        if load(self.work/'lake-manifest.json')['packages']:raise RuntimeError('External package appeared')
        package_dir=self.work/'.lake/packages'
        if package_dir.exists() and any(package_dir.iterdir()):raise RuntimeError('External dependency/cache appeared')
        artifact_rows=[self.bind(p) for p in (self.work/'.lake/build').rglob('*') if p.is_file()]
        if not any(p['path'].endswith('.c') for p in artifact_rows) or not any('.o.' in p['path'] or p['path'].endswith('.o') for p in artifact_rows):
            raise RuntimeError('Missing actual C/object compilation chain')
        for module in MODULES:
            relative=Path(*module.split('.'))
            if not (self.work/'.lake/build/lib/lean'/relative).with_suffix('.olean').is_file():
                raise RuntimeError('Missing compiled trusted module '+module)
        outputs={name:self.work/'.lake/build/bin'/(name+'.exe') for name in ['lean4export','coreaudit','comparator']}
        from probe_before_main import probe
        probes=[];runtime_rows={}
        for name,p in outputs.items():
            if p.read_bytes()[:2]!=b'MZ':raise RuntimeError('Expected native Windows PE output')
            result=probe(p,self.env,self.work,timeout=min(30,self.remaining()))
            probes.append(result)
            for path in result['loaded_PE_paths']:runtime_rows[path.casefold()]=self.bind(path)
        for p in (self.sdk/'bin').glob('*.dll'):runtime_rows[str(p).casefold()]=self.bind(p)
        # Existing running-Lean snapshot supplies actually observed late SDK/OS loads;
        # this is pinned evidence, not a request to enumerate all optional Windows DLLs.
        observed_path=self.path(gate['observed_Lean_modules']['path'])
        self.bind(observed_path,gate['observed_Lean_modules']['sha256'])
        for row in load(observed_path)['Modules']:
            p=Path(row['Path']);runtime_rows[str(p).casefold()]=self.bind(p)
        self.no_other_compiler();self.unchanged()
        self.receipt.update({'passed':True,'commands':self.commands,
            'native_executables':{name:self.bind(p) for name,p in outputs.items()},
            'all_generated_olean_IR_C_object_trace_rsp_executable_pins':artifact_rows,
            'actual_before_main_loader_protocol':probes,'runtime_file_pins':list(runtime_rows.values()),
            'runtime_scope':'Actual mandatory PE loader files plus all SDK DLLs and pinned observed late Lean loads; OS optional delay components not required',
            'complete_source_and_SDK_input_bytes_unchanged':True,'no_external_packages_or_cache_fetch':True,
            'elapsed_setup_seconds':time.monotonic()-self.t0,
            'actual_setup_parent_exit0_requires_outer_handle_observation':True})
        self.write(self.work/'installation.json',self.receipt,bind=False)
        installation_sha=self.sha(self.work/'installation.json')
        self.write(self.work/'terminal.json',{'installation_sha256':installation_sha,
            'return_code':0,'actual_parent_exit0_must_be_observed_by_root':True,'proof_runs':0},bind=False)
        self.remaining()
        print(json.dumps({'installation':str(self.work/'installation.json'),'installation_sha256':installation_sha,
                         'proof_runs':0,'root_must_observe_actual_parent_exit_code':0}),flush=True)
        self.remaining()

    def failure(self,error):
        if self.work and self.work.is_dir():
            value={'passed':False,'proof_runs':0,'error_type':type(error).__name__,
                   'message':str(error),'traceback':traceback.format_exc(),'commands':self.commands}
            with (self.work/'failure.json').open('x',encoding='utf-8') as stream:
                json.dump(value,stream,indent=2);stream.write('\n');stream.flush();os.fsync(stream.fileno())

    def release_lock(self):
        if self.lock and self.lock.exists() and self.lock.read_bytes()==self.lock_raw:self.lock.unlink()


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--gate',required=True);ap.add_argument('--gate-sha256',required=True)
    setup=Setup(ap.parse_args())
    def interrupted(signum,frame):raise InterruptedError('Received signal '+str(signum))
    signal.signal(signal.SIGTERM,interrupted)
    try:setup.execute()
    except BaseException as error:setup.failure(error);raise
    finally:setup.release_lock()
    return 0


if __name__=='__main__':raise SystemExit(main())
