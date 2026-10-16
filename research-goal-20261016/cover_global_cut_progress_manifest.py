"""Freeze the verified 17-path global-competitor cut pilot and its paired control."""
from pathlib import Path
import gzip, hashlib, json
HERE=Path(__file__).parent

def sha(data): return hashlib.sha256(data).hexdigest()

def main():
    proof=HERE/'cover-global-cut-contractor.json'
    control=HERE/'cover-global-cut-control.json'
    replay=json.loads((HERE/'cover-global-cut-contractor-replay.json').read_bytes())
    assert replay['all_passed'] and replay['global_cut_paths']==17 and replay['closed']==8
    assert sha(proof.read_bytes())==replay['input_sha256']
    dest=HERE/'cover-global-cut-evidence';dest.mkdir(exist_ok=True)
    payloads={}
    for name,source in [('proof.json.gz',proof),('paired-control.json.gz',control)]:
        raw=source.read_bytes();packed=gzip.compress(raw,compresslevel=9,mtime=0)
        assert gzip.decompress(packed)==raw
        (dest/name).write_bytes(packed)
        payloads[name]={'source_name':source.name,'source_bytes':len(raw),'source_sha256':sha(raw),
                        'gzip_bytes':len(packed),'gzip_sha256':sha(packed)}
    c=json.loads(control.read_bytes())
    receipt={'scope':__doc__,'payloads':payloads,'global_cut_independent_replay':replay,
      'paired_control_receipt':c['receipt'],
      'control_classifications_are_diagnostic':True,
      'control_terminal_leaf_witnesses_independently_replayed':False,
      'archive_roundtrip_checked':True,'standalone_geometry_archive':False,
      'required_prior_obbt_input_sha256':'869122355b263bba85408cf3269ad3172d9f42914bec5077a7e44f28abe01197',
      'preserves_original_global_minima_below_target':True,'preserves_all_KKT_points':False,
      'complete_global_cover':False,'actual_analytic_Lean_bridges_complete':False,
      'new_zero_proportion_proven':False,'final_website_submission_ready':False}
    (dest/'manifest.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8')
    names=['cover_global_cut_contractor.py','cover_global_cut_verify.py','cover_global_cut_control.py',
      'cover-global-cut-contractor-replay.json','cover_global_cut_progress_note.md',Path(__file__).name]
    names.extend('cover-global-cut-evidence/'+p.name for p in sorted(dest.iterdir()) if p.is_file())
    files={name:{'bytes':(HERE/name).stat().st_size,'sha256':sha((HERE/name).read_bytes())} for name in names}
    out={'scope':__doc__,'files':files,'file_count':len(files),'total_bytes':sum(r['bytes'] for r in files.values()),
      'independently_verified_paths':17,'independently_verified_coordinate_bounds':149,
      'independently_verified_new_closed_regions':8,'control_diagnostic_closed_regions':3,
      'diagnostic_global_only_closed_regions':7,'full_gamma_zero_variant_excluded':True,
      'all_live_main_checkpoints_excluded':True,'complete_global_cover':False,
      'actual_analytic_Lean_bridges_complete':False,'new_zero_proportion_proven':False,
      'final_website_submission_ready':False}
    target=HERE/'cover-global-cut-progress-files.json';target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'manifest':target.name,'file_count':len(files),'total_bytes':out['total_bytes'],
      'sha256':sha(target.read_bytes()),'payloads':payloads}))
if __name__=='__main__':main()
