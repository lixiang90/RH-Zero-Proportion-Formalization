"""Split or restore exact finite evidence for reproducible GitHub archival.

These files are supporting integer data, not a website proof. Splitting does
not change the compressed byte stream or reduce the upload proof size.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,shutil
HERE=Path(__file__).resolve().parent
CHUNK=4*1024*1024
digest=lambda b:hashlib.sha256(b).hexdigest()

def build():
    records=[];dest=HERE/'evidence-parts';dest.mkdir(exist_ok=True)
    for name in ['ordered-proof-input.json','ordered-compact.json']:
        source=HERE/name;archive=source.with_suffix(source.suffix+'.gz')
        raw=archive.read_bytes();parts=[]
        for index,start in enumerate(range(0,len(raw),CHUNK)):
            data=raw[start:start+CHUNK];target=dest/(name+'.gz.part'+str(index).zfill(3))
            if target.exists():assert target.read_bytes()==data
            else:target.write_bytes(data)
            parts.append({'path':str(target.relative_to(HERE)).replace('\\','/'),
                          'bytes':len(data),'sha256':digest(data)})
        assert b''.join((HERE/p['path']).read_bytes() for p in parts)==raw
        records.append({'restored':name,'restored_bytes':source.stat().st_size,
            'restored_sha256':digest(source.read_bytes()),'archive_bytes':len(raw),
            'archive_sha256':digest(raw),'parts':parts})
    manifest={'scope':__doc__,'part_bytes':CHUNK,'archives':records,
              'complete_tree_lean_verified':False,'website_upload_ready':False}
    (dest/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'archives':len(records),'parts':sum(len(r['parts']) for r in records),
                      'bytes':sum(r['archive_bytes'] for r in records)}))

def restore():
    manifest=json.loads((HERE/'evidence-parts/manifest.json').read_bytes())
    for row in manifest['archives']:
        target=HERE/row['restored']
        if target.exists():
            assert digest(target.read_bytes())==row['restored_sha256']
            continue
        archive=bytearray()
        for part in row['parts']:
            data=(HERE/part['path']).read_bytes()
            assert len(data)==part['bytes'] and digest(data)==part['sha256']
            archive.extend(data)
        assert len(archive)==row['archive_bytes'] and digest(archive)==row['archive_sha256']
        raw=gzip.decompress(archive)
        assert len(raw)==row['restored_bytes'] and digest(raw)==row['restored_sha256']
        target.write_bytes(raw)
    print(json.dumps({'restored_or_checked':[r['restored'] for r in manifest['archives']]}))

if __name__=='__main__':
    if not __debug__:raise RuntimeError('Archive assertions must remain enabled')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--restore',action='store_true');args=parser.parse_args()
    restore() if args.restore else build()
