"""Pack an existing pilot, reconstruct every original field, then replay it."""
from pathlib import Path
import argparse,gzip,hashlib,json,time
import cover_compact_codec as codec
import window_lower_global_cover as low
import window_global_cover as high
import window_compact_obbt_replay as verifier
HERE=Path(__file__).parent

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--input',type=Path,default=HERE/'window-obbt-newton-pilot.json')
    ap.add_argument('--output',type=Path,default=HERE/'window-compact-obbt-pilot.json');args=ap.parse_args();start=time.monotonic()
    raw=args.input.read_bytes();old=json.loads(raw);packed=codec.pack_document(old)
    encoded=(json.dumps(packed,separators=(',',':'))+'\n').encode();args.output.write_bytes(encoded)
    w=low if old['target']=='11/1250' else high
    decoded=codec.unpack_document(json.loads(args.output.read_bytes()),w)
    assert decoded==old,'lossless document roundtrip failed'
    replay=verifier.replay(packed)
    receipt={'scope':__doc__,'input_sha256':hashlib.sha256(raw).hexdigest(),'packed_sha256':hashlib.sha256(encoded).hexdigest(),
      'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'codec_sha256':hashlib.sha256(Path(codec.__file__).read_bytes()).hexdigest(),
      'original_bytes':len(raw),'compact_JSON_bytes':len(encoded),'compact_gzip_bytes':len(gzip.compress(encoded,mtime=0)),
      'all_original_fields_reconstructed':True,'independent_full_replay':replay,'complete_global_cover':False,'new_zero_proportion_proven':False,
      'seconds':time.monotonic()-start}
    args.output.with_suffix('.replay.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
