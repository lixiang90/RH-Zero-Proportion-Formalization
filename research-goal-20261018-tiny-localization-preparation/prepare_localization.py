"""Only source-byte mapping, lexical checks and hashes. Never imports Lean/math."""
from pathlib import Path
from hashlib import sha256
import ast
import difflib
import json
import os
import re

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
CANONICAL=ROOT/'StructuralS1RTiny20261018/Localization.lean'
DEV=ROOT/'StructuralS1RTiny20261018/Dev/Localization.lean'
PINS={
 'StructuralS1RTiny20261018/Core.lean':'9fbdf3f2dc62333b636d3b25dfb3bf2b15e3b8c628ece73d6ba1bc768fc5f1a6',
 'research-goal-20261018-tiny-core-preparation/prepared-files.json':'fda610f6156cb81b3582c5b919d7d2841422f24d8067d3f1097b5a197e54b3e9',
 'research-goal-20261018-tiny-counting-preparation/prepared-files.json':'36d9ac75c35009cdf0a4280dddabb408a9dfa3ebd4f8de75e9850d256a2aa67b',
 'research-goal-20261018-tiny-counting-preparation/INTERFACE.zh.md':'87f71992c90a89f2eb5527265a5448fd6d2286aaccaa30ed4af561eb2aa5a72d',
 'StructuralS1RTiny20261018/Dev/Core.lean':'1e144c848b39c85277af45c590cb0e54e93b2f098d44f5eb40bcb2e1b8d216ac',
}
def row(path):
    data=path.read_bytes();return {'path':path.relative_to(ROOT).as_posix(),'bytes':len(data),'sha256':sha256(data).hexdigest()}
def write_bytes(path,data):
    with path.open('xb') as handle:handle.write(data);handle.flush();os.fsync(handle.fileno())
def write(path,value):write_bytes(path,(json.dumps(value,indent=2)+'\n').encode('utf-8'))
def main():
    for path in [DEV,HERE/'mapping.diff',HERE/'preparation.json',HERE/'prepared-files.json']:
        assert not path.exists(),('exclusive_preparation_outputs',str(path))
    dependencies=[]
    for name,expected in PINS.items():
        item=row(ROOT/name);assert item['sha256']==expected;dependencies.append(item)
    source=CANONICAL.read_text(encoding='utf-8')
    assert source.count('import StructuralS1RTiny20261018.Core')==1
    assert 'import StructuralS1RTiny20261018.Counting' not in source
    assert not re.search(r'\b(?:sorry|admit|native_decide)\b',source)
    assert not re.search(r'^\s*axiom\s',source,re.M)
    assert 'theorem pair_floor (g : Fin 9 → ℝ)' in source
    assert 'theorem base_floor (g : Fin 8 → ℝ)' in source
    mappings=[('import StructuralS1RTiny20261018.Core','import StructuralS1RTiny20261018.Dev.Core'),
        ('StructuralS1RTiny20261018.Localization','StructuralS1RTiny20261018.Dev.Localization'),
        ('PC9QB6M','PC9Tiny')]
    dev=source
    for before,after in mappings:
        assert before in dev;dev=dev.replace(before,after)
    inverse=dev
    for before,after in reversed(mappings):inverse=inverse.replace(after,before)
    assert inverse==source
    DEV.parent.mkdir(exist_ok=True)
    write_bytes(DEV,dev.encode('utf-8'))
    diff=''.join(difflib.unified_diff(source.splitlines(keepends=True),dev.splitlines(keepends=True),
        fromfile=CANONICAL.relative_to(ROOT).as_posix(),tofile=DEV.relative_to(ROOT).as_posix()))
    write_bytes(HERE/'mapping.diff',diff.encode('utf-8'))
    ast.parse(Path(__file__).read_text(encoding='utf-8'))
    report={'schema':'tiny-localization-source-only-preparation-v1','canonical':row(CANONICAL),'development':row(DEV),
        'mapping_diff':row(HERE/'mapping.diff'),'mappings':mappings,'inverse_mapping_byte_text_identity':True,
        'no_Counting_import_or_cycle':True,'original_Core_or_Counting_modified':False,
        'original_c9_guards_have_actual_proof_source_not_assumed_from_floor':True,
        'no_raised_coverChk_or_new_WZ_queries':True,'proof_bodies_present_no_placeholders':True,
        'Lean_parser_elaborator_kernel_or_numerical_runs':0,
        'development_Core_source_pinned_owner_final_package_pending':True,
        'actual_pair_floor_typechecks_or_new_record_proven':False,
        'still_unchecked':['finite pressure bounds','old hS/hcov proofs in new context','root_TinyGoal root geometry',
            'Core new E fullwalk','actual Fw/G/reversal transfer','four-orientation endpoint contradiction','Counting final instance']}
    write(HERE/'preparation.json',report)
    owned=[row(CANONICAL),row(DEV)]+[row(HERE/name) for name in ['prepare_localization.py','INTERFACE.zh.md','mapping.diff','preparation.json']]
    manifest={'schema':'tiny-localization-canonical-and-dev-prepared-only-v1','files':owned,'read_only_dependencies':dependencies,
        'mathematical_or_Lean_executions':0,'no_new_FS_kernel_LP_or_P_runs':True,
        'whole_unconditional_record_source_runtime_or_submission_gate_passed':False}
    write(HERE/'prepared-files.json',manifest)
    print(json.dumps({'prepared_manifest':row(HERE/'prepared-files.json'),'canonical':row(CANONICAL),
        'development':row(DEV),'owned_rows':len(owned),'mathematical_or_Lean_runs':0}))
if __name__=='__main__':main()
