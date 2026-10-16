"""Archive the fifteen new global-competitor chains with minimal ancestors."""
from pathlib import Path
import gzip,hashlib,json
import cover_compact_codec as codec
HERE=Path(__file__).parent;ROOT=HERE.parent
sha=lambda raw:hashlib.sha256(raw).hexdigest()

def main():
    proofpath=HERE/'cover-integer-move-concave.json';proofraw=proofpath.read_bytes();proof=json.loads(proofraw)
    receiptpath=HERE/'cover-integer-move-concave-replay.json';receipt=json.loads(receiptpath.read_bytes());assert receipt['all_passed'] and receipt['checked_integer_move_chains']==15
    assert receipt['input_sha256']==sha(proofraw)
    source=(HERE/'cover-sublevel-obbt.json').read_bytes();original=json.loads(source);assert sha(source)==proof['receipt']['input_sha256'];lookup={r['path']:r for r in original['contractions']}
    prefixraw=gzip.decompress((HERE/'cover-correlated-direction.input.json.gz').read_bytes());prefix=json.loads(prefixraw)
    branches={r['path']:r for r in prefix['branches']};paths={r['path'] for r in proof['exclusions']}
    needed={p[:k] for p in paths for k in range(1,len(p)+1)}
    ancestors=[branches[p] for p in sorted(needed-paths)];descendants=[r for r in prefix['branches'] if any(r['path'].startswith(p) for p in paths)]
    assert len(descendants)==141 and not any(p!=q and p.startswith(q) for p in paths for q in paths)
    cases=[]
    for row in proof['exclusions']:
        old=lookup[row['path']];assert old['result'] is None
        step={k:old[k] for k in ['old_cell','new_cell','certificates']}
        cases.append({'path':row['path'],'obbt':codec.pack_obbt(step),'newton':[codec.pack_newton(s) for s in row['newton_steps']],
          'cell_sha256':codec.digest(row['cell']),'move':row['result']})
    jointpath=HERE/'cover-joint-after-obbt.json';jointpaths={r['path'] for r in json.loads(jointpath.read_bytes())['exclusions']};assert not(paths&jointpaths)
    out={'scope':__doc__,'target_numerator':proof['receipt']['target_numerator'],'source_OBBT_sha256':sha(source),
      'source_move_proof_sha256':sha(proofraw),'source_old_prefix_sha256':sha(prefixraw),'source_old_root_target':prefix['target'],
      'source_root':prefix['root'],'ancestors':ancestors,'old_descendant_branches':descendants,'cases':cases,
      'prior_joint_paths':sorted(jointpaths),'complete_global_cover':False,'new_zero_proportion_proven':False}
    packed=(json.dumps(out,separators=(',',':'))+'\n').encode();zipped=gzip.compress(packed,compresslevel=9,mtime=0)
    assert len(zipped)<4*1024*1024;folder=HERE/'cover-global-move-evidence';folder.mkdir(exist_ok=True);(folder/'proof.json.gz').write_bytes(zipped)
    oldmanifest=json.loads((HERE/'cover-obbt-archive/manifest.json').read_bytes());pins={k.replace('\\','/'):v for k,v in oldmanifest['sources'].items()}
    files=['cover_compact_codec.py','cover_flow_basis.py','cover_newwindow_gram_replay.py','cover_integer_move_verify.py',
      'cover_integer_move_concave_verify.py','cover_global_move_archive_replay.py','cover-integer-move-concave.json',
      'cover-integer-move-concave-replay.json','cover-joint-after-obbt.json']
    for name in files:
        p=HERE/name;pins[str(p.relative_to(ROOT)).replace('\\','/')]=sha(p.read_bytes())
    for p,digest in pins.items():assert sha((ROOT/p).read_bytes())==digest,p
    header={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'sources':pins,'file':'proof.json.gz',
      'bytes':len(zipped),'sha256':sha(zipped),'uncompressed_bytes':len(packed),'uncompressed_sha256':sha(packed),
      'global_move_chains':15,'ancestor_branches':len(ancestors),'old_descendant_branches_covered':141,'joint7_overlap':0,
      'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,'new_zero_proportion_proven':False,
      'final_website_submission_ready':False}
    (folder/'manifest.json').write_text(json.dumps(header,indent=2)+'\n',encoding='utf8');print(json.dumps({k:v for k,v in header.items() if k!='sources'}),flush=True)
if __name__=='__main__':main()
