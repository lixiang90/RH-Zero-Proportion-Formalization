"""Compile the actual re-encoded finite-data snapshot and record real results."""
from pathlib import Path
import hashlib,json,subprocess,sys,time
import bundle_solution as bundler
root=Path(__file__).resolve().parents[1]
lean=Path(r'C:\Users\A\.elan\bin\lean.exe')
version=subprocess.run([str(lean),'--version'],cwd=root,capture_output=True,text=True,encoding='utf-8',check=True).stdout.strip()
assert 'version 4.33.0-rc2' in version, version
source=(root/'RecordProportion/FiniteCertificateData.lean').read_text(encoding='utf-8')
body,number_count,saved=bundler.compact_hex(source)
body='import Lean\n'+bundler.MACRO+'\n'+'\n'.join(line for line in body.splitlines() if not line.startswith('import '))+'\n'
for name in ['orbit_coverage','reflectionLabel_involution','fixed_representatives_count','cells_size','catalog_size','representative_size']:
 body += '#print axioms RHWeil.RecordSubmission.FiniteCertificateData.'+name+'\n'
path=root/'tmp/verification/data-encoding-audit.lean';path.parent.mkdir(parents=True,exist_ok=True)
path.write_text(body,encoding='utf-8',newline='\n')
source_hash=hashlib.sha256(source.encode()).hexdigest()
body_hash=hashlib.sha256(body.encode()).hexdigest()
command=[str(lean),'--tstack=32768','-j1',str(path)]
print('Compiling finite-data snapshot',source_hash,flush=True)
start=time.monotonic()
result=subprocess.run(command,cwd=root,capture_output=True,text=True,encoding='utf-8')
print(result.stdout,flush=True);print(result.stderr,file=sys.stderr,flush=True)
assert hashlib.sha256(path.read_bytes()).hexdigest()==body_hash,'Compiler input changed during run'
record={'compiler':version,'source_sha256':source_hash,'compiled_input_sha256':body_hash,'compiled_input_bytes':len(body.encode()),'command':command,'compile_exit_code':result.returncode,'compiled':result.returncode==0,'elapsed_seconds':round(time.monotonic()-start,2),'recoded_numerals':number_count,'source_bytes_saved':saved,'axiom_output':result.stdout,'scope':'Data snapshot, orbit coverage, size and fixed-point lemmas; not a continuous certificate or zero-count headline theorem.','whole_submission_compiled':False,'submitted':False}
(root/'verification/data-encoding-check.json').write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
raise SystemExit(result.returncode)
