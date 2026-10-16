"""Batch the same eight accepted pilot leaves into independent declarations.

The two import-only controls separate a cold start from a warm import. No
additional numerical leaves or complete-cover claims are introduced.
"""
from pathlib import Path
import hashlib
import json
from window_moment_frozen_write import write_lean

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
receipt=json.loads((HERE/'lean_verification.json').read_bytes())
known={r['module']:r for r in receipt['modules']}
sha=lambda raw:hashlib.sha256(raw).hexdigest()
prefix='StructuralGoal20261016.W10LeafPilot'
sources=[]
for i in range(8):
    module=prefix+f'Leaf{i:02d}'
    path=ROOT/(module.replace('.','/')+'.lean')
    raw=path.read_bytes()
    assert known[module]['passed'] and sha(raw)==known[module]['source_sha256']
    sources.append(raw.decode('utf8'))
head=sources[0].split('namespace '+prefix+'\n')[0]
records=[]
for suffix in ['ColdImport','WarmImport','Batch']:
    module=prefix+suffix
    body=''
    if suffix=='Batch':
        for source in sources:
            body+=source.split('namespace '+prefix+'\n',1)[1].rsplit('end '+prefix+'\n',1)[0]+'\n'
    else:
        body='theorem import_control : True := True.intro\n'
    source=head+'namespace '+module+'\nopen '+prefix+'\n'+body+'end '+module+'\nend\n'
    path=ROOT/(module.replace('.','/')+'.lean')
    write_lean(path,source)
    records.append({'module':module,'source':path.relative_to(ROOT).as_posix(),
                    'source_sha256':sha(path.read_bytes()),'source_bytes':path.stat().st_size,
                    'numeric_leaves':8 if suffix=='Batch' else 0})
out={'scope':__doc__,'generator_sha256':sha(Path(__file__).read_bytes()),
     'pilot_manifest_sha256':sha((HERE/'lean_leaf_pilot_generated.json').read_bytes()),
     'modules':records,'distinct_numerical_leaves':8,'complete_W10_cover':False,
     'ordinary_Lean_verified':False,'new_zero_proportion_proven':False}
(HERE/'lean_leaf_batch_generated.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf8')
print(json.dumps({'modules':len(records),'distinct_numerical_leaves':8}))
