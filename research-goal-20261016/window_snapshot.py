"""Freeze and archive an evolving numerical checkpoint without stopping it."""
from pathlib import Path
import argparse,gzip,hashlib,json
ROOT=Path(__file__).resolve().parents[1]
def sha(raw):return hashlib.sha256(raw).hexdigest()
def main():
    ap=argparse.ArgumentParser();ap.add_argument('input',type=Path);ap.add_argument('--label',required=True);args=ap.parse_args()
    assert args.label and all(c.isalnum() or c in '-_' for c in args.label)
    raw=args.input.read_bytes();data=json.loads(raw)
    archive=ROOT/'research-goal-20261016/snapshots';archive.mkdir(exist_ok=True)
    label=args.label+'-'+str(data['checked'])
    local=ROOT/'tmp/goal-20261016';local.mkdir(parents=True,exist_ok=True)
    frozen=local/(label+'.json');frozen.write_bytes(raw)
    zipped=gzip.compress(raw,compresslevel=6,mtime=0);parts=[];chunk=4*1024*1024
    for n,start in enumerate(range(0,len(zipped),chunk)):
        path=archive/(label+'.json.gz.part'+str(n).zfill(2));part=zipped[start:start+chunk]
        path.write_bytes(part);parts.append({'path':str(path.relative_to(ROOT)),'bytes':len(part),'sha256':sha(part)})
    out={'scope':__doc__,'label':label,'input_sha256':sha(raw),'uncompressed_bytes':len(raw),
         'gzip_sha256':sha(zipped),'gzip_bytes':len(zipped),'parts':parts,
         'frozen_local_path':str(frozen),'checked':data['checked'],'unresolved_count':data['unresolved_count'],
         'target':data['target'],'complete_numerical_cover':not data['unresolved_count'],
         'global_floor_Lean_proven':False,'new_zero_proportion_proven':False}
    receipt=archive/(label+'.json');receipt.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps(out),flush=True)
if __name__=='__main__':main()
