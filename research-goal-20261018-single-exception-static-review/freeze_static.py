"""Freeze source-only single-exception review. No leaf/table decoding."""
from pathlib import Path
from hashlib import sha256
import json
import os

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
PINS = {
 'research-goal-20261018-record-source-audit/snapshot/Solution.lean':'f82a4914100fb0a39dfff98ed17ed6647a9a36bb8138d0b922b9cb4a10a736cf',
 'research-goal-20261018-stageB-classification/files.json':'3f9408f2cf1ceae12339456da034d9e8f175f828cf2d53a652339ee79eec89ad',
 'research-goal-20261018-stageB-independent/audit-files.json':'e6458883bc7588a2302afe435c3b79a08c9236bb895ec3010655024c767d7288',
}
def row(path):
    data=path.read_bytes()
    return {'path':path.relative_to(ROOT).as_posix(),'bytes':len(data),'sha256':sha256(data).hexdigest()}
def write(path, value):
    with path.open('x',encoding='utf-8',newline='\n') as handle:
        json.dump(value,handle,ensure_ascii=False,indent=2);handle.write('\n');handle.flush();os.fsync(handle.fileno())
def main():
    assert not (HERE/'files.json').exists() and not (HERE/'static-review.json').exists()
    dependencies=[]
    for name, expected in PINS.items():
        item=row(ROOT/name);assert item['sha256']==expected;dependencies.append(item)
    lines=(ROOT/next(iter(PINS))).read_text(encoding='utf-8').splitlines()
    needles=['theorem mcheckGX_sound','abbrev Covered :','noncomputable def CovK','noncomputable def WalkOK',
        'theorem leafStep_ok','theorem walkC_ok','theorem walk_ok','noncomputable def CutsOk',
        'theorem walkCut_ok','theorem ready_cover_cursor','theorem root_cover','theorem cert_AM :']
    anchors=[]
    for needle in needles:
        found=[(i+1,line) for i,line in enumerate(lines) if line.startswith(needle)]
        assert len(found)==1,(needle,len(found))
        number,text=found[0];anchors.append({'declaration_prefix':needle,'line':number,
            'declaration_first_line_utf8_sha256':sha256(text.encode('utf-8')).hexdigest()})
    result={'schema':'single-exception-overlap-independent-static-review-v1','source_anchors':anchors,
        'proposed_numbers_from_root_not_independently_reclassified_here':{
            'unique_original_exception':462,'root':11,'position':27229,'original_margin':'65385001396000000',
            'next_margin':'261389376341096919346000000','delta_N':'389500523','raised_single_window_delta_N':'779001046',
            'L':[64168,33989,64287,34192,64031,65043,33724,64461],
            'U':[65648,34980,65278,35097,65033,66904,34464,67523]},
        'static_logic_review':'Complete arbitrary-separated-sublevel dichotomy plus four-orientation shared-gap contradiction implies conditional averaged floor.',
        'new_leaf_classification_or_mathematical_execution':False,'Lean_runs':0,'P_executed':False,
        'source_runtime_counting_or_unconditional_record_gate_passed':False}
    write(HERE/'static-review.json',result)
    manifest={'schema':'single-exception-static-review-files-v1',
        'files':[row(HERE/name) for name in ['NOTE.zh.md','freeze_static.py','static-review.json']],
        'read_only_dependencies':dependencies,'mathematical_executions':0,'scope':'Static conditional proof-path review only; no new threshold classification or Lean run.'}
    write(HERE/'files.json',manifest)
    print(json.dumps({'manifest':row(HERE/'files.json'),'mathematical_executions':0,'P_executions':0}))
if __name__=='__main__':main()
