"""Compile new W10 modules in the pinned runtime; never certify a new score by itself."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,time
ROOT=Path(__file__).resolve().parents[1];HERE=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    assert __debug__
    ap=argparse.ArgumentParser();ap.add_argument('modules',nargs='+')
    ap.add_argument('--receipt',type=Path,default=HERE/'ordinary-verification.json');args=ap.parse_args()
    runtime=json.loads((ROOT/'tmp/setup-20261015/runtime.json').read_bytes())
    lean=runtime['lean'];lib='/var/tmp/rh-zero-20261015/w10-unconditional/lib'
    linux='/mnt/d/codex-build/Riemann-Zero/RH-Zero-Proportion-Formalization'
    prefix=['wsl.exe','--distribution','Ubuntu','--exec']
    compiler=subprocess.check_output(prefix+['sha256sum',lean]).decode().split()[0]
    assert compiler=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
    lp=':'.join([lib,'/var/tmp/rh-zero-20261015/w10-cert/lib',
        '/var/tmp/rh-zero-20261015/research-20261016/lib',
        '/var/tmp/rh-zero-20261015/record-verification/modular/lib',runtime['lean_path']])
    subprocess.run(prefix+['mkdir','-p',lib+'/StructuralW10Unconditional20261016'],check=True)
    receipt={'scope':__doc__,'compiler_sha256':compiler,'driver_sha256':sha(Path(__file__)),
             'passed':False,'complete_floor_proven':False,'modules':[]}
    for name in args.modules:
        assert re.fullmatch('[A-Za-z][A-Za-z0-9_]*',name)
        module='StructuralW10Unconditional20261016.'+name
        relative=module.replace('.','/')+'.lean';source=ROOT/relative
        digest=sha(source)
        command=prefix+['env','LEAN_PATH='+lp,lean,'-j1','--tstack=32768',
            '-DrelaxedAutoImplicit=false','-DmaxHeartbeats=0','-R',linux,
            '-o',lib+'/'+module.replace('.','/')+'.olean',linux+'/'+relative]
        start=time.monotonic();result=subprocess.run(command,capture_output=True,timeout=14400)
        log=HERE/(name+'.log');log.write_bytes(result.stdout+result.stderr)
        output=result.stdout.decode('utf8',errors='replace')
        item={'module':module,'command':command,'exit_code':result.returncode,
              'seconds':time.monotonic()-start,'source_sha256':digest,
              'source_unchanged':sha(source)==digest,'log_sha256':sha(log),
              'passed':result.returncode==0 and 'sorryAx' not in output}
        receipt['modules'].append(item);receipt['passed']=all(x['passed'] and x['source_unchanged'] for x in receipt['modules'])
        args.receipt.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8')
        print(json.dumps(item),flush=True)
        if not item['passed']:print(output,flush=True);raise SystemExit(1)

if __name__=='__main__':main()
