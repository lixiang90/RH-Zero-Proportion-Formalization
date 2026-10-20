"""Only insert reviewed modifiers into a fresh source version; never run Lean."""
from pathlib import Path
import hashlib
import json
import sys

ROOT=Path(__file__).resolve().parent.parent
SOURCE=ROOT/'research-goal-20261020-w9a2-delivery/draft-v8/Solution.lean'
TARGETS=ROOT/'research-goal-20261021-w9a2-runtime-closure-formal/candidate-keyword-offsets.json'
OUT=ROOT/'research-goal-20261021-w9a2-delivery/draft-v9'
SHA=lambda b:hashlib.sha256(b).hexdigest()

def main():
    if sys.flags.optimize:
        raise RuntimeError('Optimized Python is forbidden')
    if sys.argv[1:]!=['--prepare-once']:
        raise RuntimeError('Explicit one-time preparation required')
    raw=SOURCE.read_bytes(); targets_raw=TARGETS.read_bytes()
    assert len(raw)==1829382 and SHA(raw)=='5424212b6d2cf70b9eeaa632d6bf429dea4e1aadb13b0fedd948d38f94f8ac6b'
    assert SHA(targets_raw)=='d25c727a385cdd758fa8027c0530cabbf870f6aee6039be72af4daabcd5464f2'
    targets=json.loads(targets_raw)['candidates']
    assert len(targets)==2267
    positions=[x['UTF8_keyword_byte_offset_0based'] for x in targets]
    assert positions==sorted(set(positions))
    insertion=b'noncomputable '
    parts=[]; last=0; edits=[]
    for i,(target,pos) in enumerate(zip(targets,positions)):
        kind=target['kind'].encode()
        assert target['kind'] in {'def','abbrev','instance'}
        assert target['line_1based']>125 and target['name_as_written'] not in {'digit64','decode64'}
        assert 'noncomputable' not in target['original_modifiers']
        assert raw[pos:pos+len(kind)]==kind
        assert raw[pos+len(kind):pos+len(kind)+1].isspace()
        parts.extend((raw[last:pos],insertion)); last=pos
        edits.append(dict(original_byte_offset=pos,new_byte_offset=pos+i*len(insertion),kind=target['kind'],line=target['line_1based'],name_as_written=target['name_as_written']))
    parts.append(raw[last:]); modified=b''.join(parts)
    assert len(modified)==1861120 and len(modified)<2000000
    projection=bytearray(modified)
    for edit in reversed(edits):
        p=edit['new_byte_offset'];assert projection[p:p+len(insertion)]==insertion
        del projection[p:p+len(insertion)]
    assert bytes(projection)==raw
    assert raw.count(b'\r\n')==modified.count(b'\r\n')
    assert raw.endswith(b'\n') and modified.endswith(b'\n')
    # Preserve the entire macro/decoder prefix and create an exclusive new version.
    assert modified[:positions[0]]==raw[:positions[0]]
    OUT.mkdir(parents=True,exist_ok=False)
    (OUT/'Solution.lean').write_bytes(modified)
    report=dict(schema='w9a2-v9-explicit-kernel-only-codegen-source-projection-v1',
                input=dict(path=SOURCE.relative_to(ROOT).as_posix(),bytes=len(raw),sha256=SHA(raw)),
                targets=dict(path=TARGETS.relative_to(ROOT).as_posix(),sha256=SHA(targets_raw)),
                output=dict(path=(OUT/'Solution.lean').relative_to(ROOT).as_posix(),bytes=len(modified),sha256=SHA(modified)),
                insertion_count=len(edits),inserted_bytes=len(modified)-len(raw),insertion_text=insertion.decode(),
                exact_reverse_projection_equal=True,CRLF_count=modified.count(b'\r\n'),
                original_v8_unchanged=(SOURCE.read_bytes()==raw),compiler_or_kernel_run=False,
                resource_pass=False,official_acceptance=False,goal_complete=False,edits=edits)
    (OUT/'projection.json').write_bytes((json.dumps(report,ensure_ascii=False,indent=2)+'\n').encode())
    members=[]
    for p in sorted(OUT.iterdir(),key=lambda p:p.name):
        b=p.read_bytes();members.append(dict(path=p.name,bytes=len(b),sha256=SHA(b)))
    manifest=(json.dumps(dict(schema='w9a2-v9-source-files-v1',files=members),ensure_ascii=False,indent=2)+'\n').encode()
    (OUT/'files.json').write_bytes(manifest)
    print(json.dumps(dict(source_bytes=len(modified),source_sha256=SHA(modified),manifest_sha256=SHA(manifest),insertions=len(edits),reverse_projection_equal=True,compiler_run=False)))

if __name__=='__main__':
    raise SystemExit(main())
