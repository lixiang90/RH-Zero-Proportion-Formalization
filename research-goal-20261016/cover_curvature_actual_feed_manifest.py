"""Freeze the selected actual derivative feed and independent exact audit."""
from pathlib import Path
import gzip,hashlib,json
HERE=Path(__file__).parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
    raw=(HERE/'cover-curvature-actual-feed.json').read_bytes();receipt=json.loads((HERE/'cover-curvature-actual-feed-replay.json').read_bytes())
    assert receipt['all_passed'] and receipt['input_sha256']==sha(raw) and receipt['scalar_rows_checked']==123
    zipped=gzip.compress(raw,compresslevel=9,mtime=0);assert gzip.decompress(zipped)==raw
    (HERE/'cover-curvature-actual-feed.json.gz').write_bytes(zipped)
    names=['cover_curvature_actual_feed.py','cover_curvature_actual_active.py','cover_curvature_actual_feed_replay.py',
      'cover-curvature-actual-feed.json.gz','cover-curvature-actual-active.json','cover-curvature-actual-feed-replay.json',
      'cover_curvature_actual_feed_note.md',Path(__file__).name]
    files={name:{'bytes':(HERE/name).stat().st_size,'sha256':sha((HERE/name).read_bytes())} for name in names}
    out={'scope':__doc__,'files':files,'file_count':len(files),'total_bytes':sum(v['bytes'] for v in files.values()),
      'uncompressed_complete_audit_bytes':len(raw),'uncompressed_complete_audit_sha256':sha(raw),'scalar_rows_preserved':123,
      'active_scalar_rows':51,'active_grid_union':331,'active_point_locations':31,'ordinary_Lean_proven':False,
      'complete_global_cover':False,'new_zero_proportion_proven':False,'all_live_checkpoints_excluded':True}
    target=HERE/'cover-curvature-actual-feed-files.json';target.write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'manifest':target.name,'bytes':target.stat().st_size,'sha256':sha(target.read_bytes()),'file_count':len(files),'total_bytes':out['total_bytes']}))
if __name__=='__main__':main()
