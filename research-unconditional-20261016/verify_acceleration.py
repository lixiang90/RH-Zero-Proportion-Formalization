"""Serial, synchronous pinned-kernel checks for the new geometry experiments."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('modules', nargs='+')
    parser.add_argument('--receipt', default='acceleration-verification.json')
    args = parser.parse_args()
    runtime = json.loads((ROOT/'tmp/setup-20261015/runtime.json').read_text())
    lib = '/var/tmp/rh-zero-20261015/w10-cert/lib'
    linux = '/mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization'
    lp = ':'.join([lib, '/var/tmp/rh-zero-20261015/research-20261016/lib',
                   '/var/tmp/rh-zero-20261015/record-verification/modular/lib', runtime['lean_path']])
    check = subprocess.run(['wsl.exe','--distribution','Ubuntu','--exec','/usr/bin/sha256sum',runtime['lean']],capture_output=True,check=True)
    compiler_sha = check.stdout.decode().split()[0]
    assert compiler_sha == runtime['lean_sha256']
    record = {'scope':'Pinned Lean default-kernel proof and synchronous subtree timings. No global floor is asserted by timing smokes.',
              'compiler_sha256':compiler_sha,'modules':[],'passed':False}
    for module in args.modules:
        assert re.fullmatch(r'[A-Za-z0-9_]+(\.[A-Za-z0-9_]+)+',module)
        relative=module.replace('.','/')
        source=ROOT/(relative+'.lean')
        sha=hashlib.sha256(source.read_bytes()).hexdigest()
        subprocess.run(['wsl.exe','--distribution','Ubuntu','--exec','/bin/mkdir','-p',lib+'/'+relative.rsplit('/',1)[0]],check=True)
        argv=['wsl.exe','--distribution','Ubuntu','--exec','/usr/bin/prlimit','--stack=268435456:268435456','--','env','LEAN_PATH='+lp,runtime['lean'],'-j1','--tstack=262144',
              '-DrelaxedAutoImplicit=false','-R',linux,'-o',lib+'/'+relative+'.olean',linux+'/'+relative+'.lean']
        start=time.monotonic()
        result=subprocess.run(argv,capture_output=True)
        elapsed=time.monotonic()-start
        output=result.stdout.decode('utf8',errors='replace')
        log=result.stdout+result.stderr
        logname=module.rsplit('.',1)[-1]+'.log'
        (HERE/logname).write_bytes(log)
        marks={key:int(value) for key,value in re.findall(r'W10_TIMING\s+(\w+)\s+(\d+)',output)}
        item={'module':module,'source_sha256':sha,'source_unchanged':hashlib.sha256(source.read_bytes()).hexdigest()==sha,
              'command':argv,'exit_code':result.returncode,'whole_process_seconds':elapsed,'log':logname,
              'log_sha256':hashlib.sha256(log).hexdigest(),'marks_milliseconds':marks,
              'synchronous_elaboration':'set_option Elab.async false' in source.read_text(encoding='utf8'),
              'passed':result.returncode==0 and 'sorryAx' not in output}
        if 'certificate_begin' in marks and 'certificate_end' in marks:
            item['certificate_seconds']=(marks['certificate_end']-marks['certificate_begin'])/1000
        record['modules'].append(item)
        record['passed']=len(record['modules'])==len(args.modules) and all(x['passed'] for x in record['modules'])
        (HERE/args.receipt).write_text(json.dumps(record,indent=2)+'\n',encoding='utf8')
        print(json.dumps(item),flush=True)
        if result.returncode:
            print(output,flush=True)
            raise SystemExit(result.returncode)


if __name__=='__main__':
    main()
