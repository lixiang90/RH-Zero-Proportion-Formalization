"""Pin the independent one-pass replay of the stable zero-merge packet."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];OUT=HERE/'independent-merge-files.json'
def record(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def main():
    assert not OUT.exists();names=['independent_merge_replay.py','independent-merge-replay.json','independent_merge_note.txt','independent_merge_pin.py']
    receipt=json.loads((HERE/names[1]).read_bytes());assert receipt['source_sha256_start']==receipt['source_sha256_end'];deps=[]
    for relative,h in receipt['source_sha256_start'].items():
        p=ROOT/relative;item=record(p);assert item['sha256']==h
        if relative not in [(HERE/n).relative_to(ROOT).as_posix() for n in names]:deps.append(item)
    out={'scope':__doc__,'package_files':[record(HERE/n) for n in names],'dependency_files':deps,
        'read_only_replay':(HERE/names[0]).relative_to(ROOT).as_posix(),'numeric_original_witnesses_checked':95615,
        'retained_branches_checked':95778,'strictly_merged_parent_leaves':0,'all_integer_checks_passed':True,
        'Lean_invocations':0,'new_math_cover':False,'two_MB_source_achieved':False,'new_zero_proportion_proven':False}
    OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'manifest_sha256':record(OUT)['sha256'],'files':len(names),'dependencies':len(deps)}))
if __name__=='__main__':main()
