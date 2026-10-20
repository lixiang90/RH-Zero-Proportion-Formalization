"""Pure Python parser/trace arithmetic fixtures; never creates SDKHash."""
import ast
import hashlib
import json
from pathlib import Path
from cache_binding import imports, flatten_values, mix

here=Path(__file__).resolve().parent
for p in here.glob('*.py'):ast.parse(p.read_bytes())
assert imports(b'/- x -/\nmodule\nprelude\npublic import\n Mathlib.X\nmeta import Init.X\ndef x:=1')==['Mathlib.X','Init.X']
assert imports(b'import A\nimport A\n/-!body-/\nimport B')==['A','A']
assert list(flatten_values({'o':['x.olean']}))==['x.olean']
def node_hash(node):
    if isinstance(node[1],str):return int(node[1],16)
    return fold(node[1])
def fold(nodes):
    h=1723
    for node in nodes:h=mix(h,node_hash(node))
    return h
t=json.loads((here.parent/'.lake/packages/Zeta23/.lake/build/lib/lean/Zeta23/Statement.trace').read_text())
assert format(fold(t['inputs']),'016x')==t['depHash']
out=dict(scope='Pure parser fixtures and actual legacy trace structural arithmetic only',
         sdk_hash_DLL_loaded=False,compiler_runs=0,proof_runs=0,result='PASS',
         source_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in
                        [here/'assemble.py',here/'cache_binding.py',here/'static_fixtures.py']})
with (here/'static-fixtures-result.json').open('x',encoding='utf-8',newline='\n') as f:
    json.dump(out,f,indent=2);f.write('\n')
print(json.dumps(out))
