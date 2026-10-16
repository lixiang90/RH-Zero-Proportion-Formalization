"""Archive nine additional sublevel-conditioned finite global moves."""
from pathlib import Path
import gzip,hashlib,json
import cover_compact_codec as codec
HERE=Path(__file__).parent;ROOT=HERE.parent
sha=lambda b:hashlib.sha256(b).hexdigest()

def main():
    proofraw=(HERE/'cover-global-move-epigraph.json').read_bytes();proof=json.loads(proofraw)
    replay=json.loads((HERE/'cover-global-move-epigraph-replay.json').read_bytes())
    assert replay['all_passed'] and replay['checked_global_move_chains']==9 and replay['input_sha256']==sha(proofraw)
    sourceraw=(HERE/'cover-sublevel-obbt.json').read_bytes();source=json.loads(sourceraw);assert sha(sourceraw)==proof['receipt']['input_sha256']
    lookup={r['path']:r for r in source['contractions']};prefixraw=gzip.decompress((HERE/'cover-correlated-direction.input.json.gz').read_bytes());prefix=json.loads(prefixraw)
    branches={r['path']:r for r in prefix['branches']};paths={r['path'] for r in proof['exclusions']}
    signed={r['path'] for r in json.loads((HERE/'cover-integer-move-concave.json').read_bytes())['exclusions']}
    joint={r['path'] for r in json.loads((HERE/'cover-joint-after-obbt.json').read_bytes())['exclusions']}
    assert len(paths)==9 and not(paths&joint) and not any(p.startswith(q) or q.startswith(p) for p in paths for q in signed)
    assert not any(p!=q and p.startswith(q) for p in paths for q in paths)
    needed={p[:k] for p in paths for k in range(1,len(p)+1)};ancestors=[branches[p] for p in sorted(needed-paths)]
    descendants=[r for r in prefix['branches'] if any(r['path'].startswith(p) for p in paths)];assert len(descendants)==110
    cases=[]
    for row in proof['exclusions']:
        original=lookup[row['path']];assert original['result'] is None;result=row['result'].copy();energy=result.pop('energy_minorant')
        cases.append({'path':row['path'],'obbt':codec.pack_obbt({k:original[k] for k in ['old_cell','new_cell','certificates']}),
          'newton':[codec.pack_newton(s) for s in row['newton_steps']],'cell_sha256':codec.digest(row['cell']),
          'move':result,'energy_minorant':codec.pack_minorant(energy) if energy else None,'move_sha256':codec.digest(row['result'])})
    data={'scope':__doc__,'target_numerator':proof['receipt']['target_numerator'],'source_OBBT_sha256':sha(sourceraw),
      'source_proof_sha256':sha(proofraw),'source_old_prefix_sha256':sha(prefixraw),'source_old_root_target':prefix['target'],'source_root':prefix['root'],
      'ancestors':ancestors,'old_descendant_branches':descendants,'cases':cases,'previous_signed_paths':sorted(signed),'previous_joint_paths':sorted(joint),
      'complete_global_cover':False,'new_zero_proportion_proven':False}
    raw=(json.dumps(data,separators=(',',':'))+'\n').encode();zipped=gzip.compress(raw,compresslevel=9,mtime=0)
    folder=HERE/'cover-global-move-epigraph-evidence';folder.mkdir(exist_ok=True);(folder/'proof.json.gz').write_bytes(zipped)
    pins={k.replace('\\','/'):v for k,v in json.loads((HERE/'cover-obbt-archive/manifest.json').read_bytes())['sources'].items()}
    files=['cover_compact_codec.py','cover_flow_basis.py','cover_newwindow_gram_replay.py','cover_integer_move_verify.py',
      'cover_integer_move_concave_verify.py','cover_global_move_epigraph_verify.py','cover_global_move_epigraph_archive_replay.py',
      'cover-global-move-epigraph.json','cover-global-move-epigraph-replay.json','cover-integer-move-concave.json','cover-joint-after-obbt.json',
      'cover-global-move-evidence/manifest.json','cover-global-move-evidence/proof.json.gz']
    for name in files:
        p=HERE/name;pins[str(p.relative_to(ROOT)).replace('\\','/')]=sha(p.read_bytes())
    for p,digest in pins.items():assert sha((ROOT/p).read_bytes())==digest,p
    header={'scope':__doc__,'script_sha256':sha(Path(__file__).read_bytes()),'sources':pins,'file':'proof.json.gz','bytes':len(zipped),
      'sha256':sha(zipped),'uncompressed_bytes':len(raw),'uncompressed_sha256':sha(raw),'new_global_move_chains':9,
      'new_old_branches_covered':110,'previous_signed_chains':15,'previous_old_branches_covered':141,'combined_topmost_chains':24,
      'combined_old_branches_covered':251,'joint7_overlap':0,'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,'new_zero_proportion_proven':False}
    (folder/'manifest.json').write_text(json.dumps(header,indent=2)+'\n',encoding='utf8');print(json.dumps({k:v for k,v in header.items() if k!='sources'}),flush=True)
if __name__=='__main__':main()
