"""Make a small replay archive containing only needed ancestor branches.

The projection is a subset-of-witness replay artifact, not a full cover.
The original complete discovery snapshot remains hash-identified but is not
needed to rebuild the cells or check the projected witnesses.
"""
from pathlib import Path
import argparse, gzip, hashlib, json
HERE=Path(__file__).parent
sha=lambda b:hashlib.sha256(b).hexdigest()

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--witness',type=Path,default=HERE/'cover-correlated-direction.json')
    ap.add_argument('--snapshot',type=Path,default=HERE/'cover-correlated-direction.input.json.gz')
    ap.add_argument('--contractions',type=Path,default=HERE/'cover-newton-contractor.json')
    ap.add_argument('--output-dir',type=Path,default=HERE/'cover-compact-archive')
    args=ap.parse_args();args.output_dir.mkdir(exist_ok=True)
    witness_raw=args.witness.read_bytes();witness=json.loads(witness_raw);snapshot_raw=args.snapshot.read_bytes()
    original_raw=gzip.decompress(snapshot_raw);original=json.loads(original_raw);original_sha=sha(original_raw)
    assert original_sha==witness['receipt']['input_sha256']
    contraction_raw=args.contractions.read_bytes();contractions=json.loads(contraction_raw)
    assert contractions['receipt']['input_sha256']==original_sha
    paths={r['path'] for r in witness['exclusions']}|{r['path'] for r in contractions['contractions']}
    ancestors={p[:k] for p in paths for k in range(1,len(p))}
    original_branches={r['path']:r for r in original['branches']}
    projected=[original_branches[p] for p in sorted(ancestors)]
    projection={'receipt':{'scope':__doc__,'original_input_sha256':original_sha,'original_snapshot_sha256':sha(snapshot_raw),
        'original_branches':len(original_branches),'projected_ancestor_branches':len(projected),
        'correlated_witness_sha256':sha(witness_raw),'contraction_witness_sha256':sha(contraction_raw),
        'correlated_cells':len(witness['exclusions']),'contraction_chains':len(contractions['contractions']),
        'source_script_sha256':sha(Path(__file__).read_bytes()),'full_global_cover_asserted':False},
      'root':original['root'],'target':original['target'],'separation':original['separation'],'SC':original['SC'],
      'denominator':original['denominator'],'branches':projected}
    projected_raw=(json.dumps(projection,separators=(',',':'))+'\n').encode('utf8')
    files={'projection.json.gz':gzip.compress(projected_raw,mtime=0),
      'correlated-witness.json.gz':gzip.compress(witness_raw,mtime=0),
      'contraction-witness.json.gz':gzip.compress(contraction_raw,mtime=0)}
    for name,raw in files.items():(args.output_dir/name).write_bytes(raw)
    manifest={'scope':__doc__,'original_input_sha256':original_sha,'projection_uncompressed_sha256':sha(projected_raw),
      'files':{name:{'sha256':sha(raw),'bytes':len(raw)} for name,raw in files.items()},
      'total_archive_bytes':sum(map(len,files.values())),'original_snapshot_bytes':len(snapshot_raw),
      'complete_global_cover_asserted':False}
    (args.output_dir/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf8');print(json.dumps(manifest))
if __name__=='__main__':main()
