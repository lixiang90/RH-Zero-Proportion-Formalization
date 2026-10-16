"""Check that the small seed reproduces all current 478-leaf Lean bytes.

This is a source-generation audit, not a substitute for the Lean proofs.
"""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
sha=lambda raw:hashlib.sha256(raw).hexdigest()
plan=json.loads((HERE/'lean_aux478_generated.json').read_bytes())
before={r['source']:(sha((ROOT/r['source']).read_bytes()),(ROOT/r['source']).stat().st_mtime_ns)
        for r in plan['modules']}
run=subprocess.run([sys.executable,'-B','-X','utf8',str(HERE/'lean_generate_aux478.py')],
                   cwd=ROOT,capture_output=True,check=True)
after={p:(sha((ROOT/p).read_bytes()),(ROOT/p).stat().st_mtime_ns)for p in before}
assert before==after, 'Source bytes or timestamps changed during no-op regeneration'
out={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),
     'generator_sha256':sha((HERE/'lean_generate_aux478.py').read_bytes()),
     'seed_sha256':sha((HERE/'lean_aux478_seed.json.gz').read_bytes()),
     'modules':len(before),'all_source_bytes_and_mtimes_unchanged':True,
     'large_original_inputs_needed_by_generator':False,
     'unpassed_monolithic_Lean_source_needed_by_generator':False,
     'source_sha256s':{p:v[0]for p,v in before.items()},
     'generator_stdout':run.stdout.decode('utf8'),'mathematical_verification':False}
p=HERE/'lean_aux478_reproduction.json'
p.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
print(json.dumps({'reproduction_sha256':sha(p.read_bytes()),'modules':len(before),'unchanged':True}))
