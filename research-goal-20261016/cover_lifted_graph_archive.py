"""Project completed lifted-graph witnesses and paired controls to ancestors only."""
from pathlib import Path
import argparse,gzip,hashlib,json
HERE=Path(__file__).parent
sha=lambda b:hashlib.sha256(b).hexdigest()

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--proof',type=Path,default=HERE/'cover-lifted-graph8.json');ap.add_argument('--output',type=Path,default=HERE/'cover-lifted-graph8-evidence');args=ap.parse_args()
    raw=args.proof.read_bytes();proof=json.loads(raw);packed=(HERE/'cover-curvature-parent64.input.json.gz').read_bytes();source=json.loads(gzip.decompress(packed));assert sha(packed)==proof['receipt']['input_sha256']
    controlraw=(HERE/'cover-curvature-parent64.json').read_bytes();controls=json.loads(controlraw);assert controls['receipt']['input_sha256']==sha(packed)
    selected={r['path']:r for r in proof['rows'] if r['graph']};needed={p[:k] for p in selected for k in range(1,len(p))}
    projection={k:source[k] for k in ['target','root','input_sha256']};projection['branches']={p:r for p,r in source['branches'].items() if p in needed}
    projection['OBBT']={p:r for p,r in source['OBBT'].items() if p in needed};projection['Newton']={p:r for p,r in source['Newton'].items() if p in needed}
    projection['cases']=[r for r in source['cases'] if r['path'] in selected]
    projected_controls=[{'path':r['path'],'control':r['control']} for r in controls['rows'] if r['path'] in selected]
    assert all(r['control']['outcome'] is None for r in projected_controls)
    out={'schema':'lifted-graph-ancestor-projection-v1','target':source['target'],'source':projection,
      'records':[r for r in proof['rows'] if r['path'] in selected],'paired_controls':projected_controls,
      'source_recorded_descendant_branches':[r for r in source['source_descendant_branches'] if any(r['path'].startswith(p) for p in selected)],
      'provenance':{'full_proof_sha256':sha(raw),'full_parent_input_gzip_sha256':sha(packed),'full_control_sha256':sha(controlraw),
        'original_source_checkpoint_sha256':source.get('source_checkpoint_sha256'),'original_source_checked':source.get('source_checkpoint_checked',source.get('source_checked'))},
      'complete_global_cover':False,'new_zero_proportion_proven':False}
    data=(json.dumps(out,separators=(',',':'))+'\n').encode();compressed=gzip.compress(data,mtime=0);args.output.mkdir(exist_ok=True)
    (args.output/'proof.json.gz').write_bytes(compressed)
    manifest={'schema':out['schema'],'exporter_sha256':sha(Path(__file__).read_bytes()),'source_proof_sha256':sha(raw),
      'proof_gzip_sha256':sha(compressed),'proof_gzip_bytes':len(compressed),'uncompressed_sha256':sha(data),'uncompressed_bytes':len(data),
      'witnesses':len(selected),'ancestor_branches':len(needed),'old_controls_nonclosed':len(projected_controls),
      'complete_global_cover':False,'new_zero_proportion_proven':False}
    (args.output/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf8');print(json.dumps(manifest),flush=True)
if __name__=='__main__':main()
