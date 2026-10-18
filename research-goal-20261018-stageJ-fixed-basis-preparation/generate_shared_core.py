"""Static source-text adaptation only; no producer import, FS or matrix work."""
from pathlib import Path
from hashlib import sha256
import ast
import json
import os

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
SOURCE=ROOT/'research-goal-20261018-stageI-original-affine-point/evaluate_once.py'
SOURCE_SHA='9170d9f229a0e8c4c659812467abdac163008ef89049123d58254bbb8e47e724'
def main():
    raw=SOURCE.read_bytes();assert sha256(raw).hexdigest()==SOURCE_SHA
    text=raw.decode('utf-8');body=text[text.index('def extract_original_affine('):text.index('def embed_and_evaluate(')]
    old="FIXED_CELLS[cid]['payload_bits']";new="cell['witness']['consumed_payload_bits']"
    assert body.count(old)==1;body=body.replace(old,new)
    prefix='''"""General original-cell affine extraction, text-adapted from frozen I.
Only the terminal expected-payload-length lookup is generalized to the same
original B witness; formulas/guards/semantics remain the I point-free body.
No functions run at import. Original locator is supplied only after gate.
"""
from fractions import Fraction as F
from hashlib import sha256
import json
Q=32768
R=1024
D=10**9
V=10**10
SA=10**20
KAPPA=Q*V*R
K=KAPPA*SA
CN=893616123055294719
TAU_N=893916123055294719
ORIGINAL_LOCATOR=None
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode('ascii')+b'\\n'
def locate_original_payload(cell,model,math,traces):
    assert ORIGINAL_LOCATOR is not None
    return ORIGINAL_LOCATOR(cell,model,math,traces)

'''
    output=prefix+body;ast.parse(output)
    target=HERE/'original_affine_core.py'
    with target.open('x',encoding='utf-8',newline='\n') as f:f.write(output);f.flush();os.fsync(f.fileno())
    print(json.dumps({'static_source_adaptation_only':True,'source_sha256':SOURCE_SHA,
        'output_sha256':sha256(target.read_bytes()).hexdigest(),'modified_lookup_count':1,
        'producer_imports':0,'FS_or_matrix_executions':0}))

if __name__=='__main__':main()
