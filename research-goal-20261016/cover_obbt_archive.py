"""Package all 806 independently replayed OBBT witnesses in <=4 MiB gzip shards.

Includes only the required ancestor branches, the original receipt and its
source/parameter/target hashes. This is a finite witness projection, not a
complete global cover and not an unconditional zero-proportion theorem.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,time
HERE=Path(__file__).parent;ROOT=HERE.parent;LIMIT=4*1024*1024

def sha(raw):return hashlib.sha256(raw).hexdigest()
def encode(doc):return json.dumps(doc,separators=(',',':')).encode('utf8')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--proof',type=Path,default=HERE/'cover-sublevel-obbt.json')
    ap.add_argument('--source',type=Path,default=HERE/'cover-correlated-direction.input.json.gz')
    ap.add_argument('--output',type=Path,default=HERE/'cover-obbt-archive');args=ap.parse_args();start=time.monotonic()
    raw=args.proof.read_bytes();doc=json.loads(raw);source=gzip.decompress(args.source.read_bytes());original=json.loads(source)
    assert sha(source)==doc['receipt']['input_sha256'];rows=doc['contractions'];assert len(rows)==806
    paths={row['path'] for row in rows};assert len(paths)==len(rows)
    needed={p[:k] for p in paths for k in range(1,len(p))}
    branches=[b for b in original['branches'] if b['path'] in needed];assert {b['path'] for b in branches}==needed
    projection={'source_input_sha256':sha(source),'source_root':original['root'],'source_target':original['target'],
      'SC':original['SC'],'energy_denominator':original['denominator'],'branches':branches,'witness_paths':sorted(paths),
      'complete_global_cover':False,'scope':'Only the ancestors of all 806 exact OBBT witness cells.'}
    args.output.mkdir(parents=True,exist_ok=True);encoded=encode(projection);packed=gzip.compress(encoded,compresslevel=9,mtime=0)
    assert len(packed)<=LIMIT;projection_path=args.output/'projection.json.gz';projection_path.write_bytes(packed)
    pieces=[]
    def emit(batch,first):
        encoded=encode({'first':first,'rows':batch});packed=gzip.compress(encoded,compresslevel=9,mtime=0)
        if len(packed)>LIMIT:
            assert len(batch)>1;half=len(batch)//2;emit(batch[:half],first);emit(batch[half:],first+half);return
        path=args.output/f'witness-{len(pieces):03}.json.gz';path.write_bytes(packed)
        pieces.append({'file':path.name,'first':first,'rows':len(batch),'bounds':sum(len(r['certificates']) for r in batch),
          'bytes':len(packed),'sha256':sha(packed),'uncompressed_sha256':sha(encoded)})
    for first in range(0,len(rows),128):emit(rows[first:first+128],first)
    source_paths=['cover_sublevel_obbt.py','cover_sublevel_obbt_api.py','cover_sublevel_obbt_verify.py','cover_sublevel_obbt_verify_api.py',
      'cover_sublevel_contractor.py','cover_sublevel_verify.py','cover_correlated_api.py','cover_correlated_direction.py',
      'cover_correlated_verify.py','cover_correlated_replay.py','cover_contractor_verify.py','cover_obbt_archive.py','cover_obbt_archive_replay.py',
      'window_global_cover.py','window_interval_kernel.py','cover_newjet.json','window_interval_kernel.json']
    sources={str((HERE/p).relative_to(ROOT)).replace('\\','/'):sha((HERE/p).read_bytes()) for p in source_paths}
    geometry=ROOT/'research-20261016-w10-unconditional/audit_exact.py'
    # The independently imported geometry helper's exact path is recorded below.
    import cover_correlated_replay as helper
    geometry=Path(helper.a.__file__);sources[str(geometry.relative_to(ROOT)).replace('\\','/')]=sha(geometry.read_bytes())
    import cover_sublevel_obbt_verify as verifier
    dependencies=[ROOT/'research-20261016-followup/global_periodic_upper_bound.py',
      ROOT/'research-20261016-w10-cert/generate.py',ROOT/'scripts/finite_margin_20261015.py',
      ROOT/'research-20261016/spectral-w10-refined-rational.json',Path(verifier.g.f.SRC)]
    for dependency in dependencies:
        sources[str(dependency.relative_to(ROOT)).replace('\\','/')]=sha(dependency.read_bytes())
    parameter=ROOT/'research-20261016-followup/window_reweight_rational.json';sources[str(parameter.relative_to(ROOT)).replace('\\','/')]=sha(parameter.read_bytes())
    receipt_path=HERE/'cover-sublevel-obbt-replay.json';receipt_raw=receipt_path.read_bytes();receipt=json.loads(receipt_raw)
    assert receipt['input_sha256']==sha(raw) and receipt['all_passed']
    newline='\n';rebuilt=encode(doc)+newline.encode()
    if rebuilt!=raw:newline='\r\n';rebuilt=encode(doc)+newline.encode()
    assert rebuilt==raw,'Archive must reconstruct the exact source witness bytes'
    manifest={'format':'OBBT-finite-witness-projection-v1','scope':__doc__,'source_proof_sha256':sha(raw),
      'source_proof_final_newline':newline,'source_input_sha256':sha(source),'source_receipt':doc['receipt'],
      'independent_receipt':receipt,'independent_receipt_sha256':sha(receipt_raw),'sources':sources,
      'projection':{'file':projection_path.name,'bytes':len(packed),'sha256':sha(packed),'uncompressed_sha256':sha(encoded),
        'ancestor_branches':len(branches)},'witness_shards':pieces,'total_witness_paths':len(rows),
      'total_bounds':sum(len(r['certificates']) for r in rows),'maximum_gzip_shard_bytes':LIMIT,
      'total_archive_gzip_bytes':projection_path.stat().st_size+sum(p['bytes'] for p in pieces),
      'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,'new_zero_proportion_proven':False,
      'seconds':time.monotonic()-start}
    # `packed` / `encoded` above are the projection variables; emit has a local scope.
    manifest_path=args.output/'manifest.json';manifest_path.write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:manifest[k] for k in ['total_witness_paths','total_bounds','total_archive_gzip_bytes','complete_global_cover','seconds']}))
if __name__=='__main__':main()
