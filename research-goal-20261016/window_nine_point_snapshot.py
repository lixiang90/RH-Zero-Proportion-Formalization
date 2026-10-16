"""Freeze a replayable partial nine-point checkpoint before resuming discovery."""
from pathlib import Path
import gzip,hashlib,json
HERE=Path(__file__).parent
def main():
    src=HERE/'window-nine-point-cover.json';raw=src.read_bytes();doc=json.loads(raw)
    receipt=json.loads((HERE/'window-nine-point-cover-replay.json').read_bytes())
    assert receipt['all_passed'] and receipt['input_sha256']==hashlib.sha256(raw).hexdigest()
    folder=HERE/'nine-point-pilot';folder.mkdir(exist_ok=True)
    arc=gzip.compress(raw,compresslevel=9,mtime=0);(folder/'checkpoint.json.gz').write_bytes(arc)
    (folder/'raw-replay.json').write_bytes((HERE/'window-nine-point-cover-replay.json').read_bytes())
    manifest={'scope':__doc__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'raw_sha256':hashlib.sha256(raw).hexdigest(),'archive_sha256':hashlib.sha256(arc).hexdigest(),
      'raw_bytes':len(raw),'archive_bytes':len(arc),'checked':doc['checked'],
      'unresolved_count':doc['unresolved_count'],'input_sha256':doc['input_sha256'],
      'complete_global_cover':False,'new_zero_proportion_proven':False,'submission_ready':False}
    (folder/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:manifest[k] for k in ['raw_bytes','archive_bytes','checked','unresolved_count']}))
if __name__=='__main__':main()
