from pathlib import Path
import ast, json, re, hashlib

project=Path('E:/codex-build/RH-Weil')
formal=Path('E:/codex-build/RH-Zero-Proportion-Formalization')
text=(formal/'RecordProportion/ImportedAM.lean').read_text(encoding='utf8')
full={}
for line in text.splitlines():
    m=re.fullmatch(r'def PTL_(\d+) \(x : ℕ\) : ℕ := ptl (.+) x',line)
    if m:
        for p,pack in ast.literal_eval(m[2]):
            assert p not in full
            full[p]=(pack,int(m[1]))
data=json.loads((project/'output/am-ninth-span-point-catalog.json').read_text(encoding='utf8'))
assert len(full)==2196
assert len(data['point_catalog'])==541
assert all(full[p]==(pack,bucket) for p,pack,bucket in data['point_catalog'])
assert all(0 <= pack < 2**96 for p,pack,bucket in data['point_catalog'])
module=(formal/'RecordProportion/NinthSpanPoints.lean').read_text(encoding='utf8')
section=re.search(r'def catalog : Array \(Nat × Nat\) := #\[(.*?)\]\ndef catalogPoint',module,re.S)
assert section
module_rows=ast.literal_eval('['+section[1]+']')
assert module_rows==[(p,pack) for p,pack,bucket in data['point_catalog']]
receipt={'original_points':len(full), 'new_catalog_points':541,
         'all_imported_pack_identities':True,'all_pack_96bit_bounds':True,
         'final_lean_catalog_matches_json_in_original_order':True,
         'catalog_sha256':hashlib.sha256((project/'output/am-ninth-span-point-catalog.json').read_bytes()).hexdigest(),
         'proof_module_sha256':hashlib.sha256((formal/'RecordProportion/NinthSpanPoints.lean').read_bytes()).hexdigest(),
         'scope':'source/data crosscheck only; Lean kernel certification is recorded separately'}
(project/'tmp/ninth-span-points-source-audit.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8')
print(json.dumps(receipt,indent=2))
