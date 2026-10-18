"""Exact source-byte prefix copy only. No Lean or mathematical evaluation."""
from pathlib import Path
from hashlib import sha256
import json
import os
ROOT=Path(__file__).resolve().parent.parent
SOURCE=ROOT/'research-goal-20261018-record-source-audit/snapshot/Solution.lean'
SOURCE_SHA='f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf'
PREFIX_SHA='18714f049ddcc2c105d28ec442049e759d118dad5a9fede097ebc3bc6ba90135'
def main():
    raw=SOURCE.read_bytes();assert sha256(raw).hexdigest()==SOURCE_SHA
    lines=raw.splitlines(keepends=True);prefix=b''.join(lines[:12407])
    assert len(prefix)==934974 and sha256(prefix).hexdigest()==PREFIX_SHA
    rev=b''.join(lines[14292:14294])
    assert rev.startswith(b'theorem PC9QB6M_G_rev ') and b'unfold PC9QB6M.G; ring_nf' in rev
    out=prefix+b'\nend AMW.Cert.PC9QB6MData\nend\n\nnoncomputable section\nnamespace AMW.Cert\n'+rev+b'\nend AMW.Cert\nend\n'
    target=ROOT/'StructuralS1RM20261018/CurrentPrefix.lean'
    with target.open('xb') as f:f.write(out);f.flush();os.fsync(f.fileno())
    print(json.dumps({'exact_current_prefix':True,'path':target.relative_to(ROOT).as_posix(),
        'bytes':len(out),'sha256':sha256(out).hexdigest(),'prefix_sha256':PREFIX_SHA,
        'source_sha256':SOURCE_SHA,'new_kernel_or_FS_or_Lean_runs':0}))
if __name__=='__main__':main()
