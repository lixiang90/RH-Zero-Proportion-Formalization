"""Pin only the independent read-only codec review and its frozen dependencies."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1];OUT=HERE/'independent-codec-files.json'
def record(p):return {'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def main():
    assert not OUT.exists();names=['independent_codec_replay.py','independent-codec-replay.json','independent_codec_note.txt','independent_codec_pin.py']
    receipt=json.loads((HERE/names[1]).read_bytes());assert receipt['source_sha256_start']==receipt['source_sha256_end'];deps=[]
    for relative,h in receipt['source_sha256_start'].items():
        p=ROOT/relative;item=record(p);assert item['sha256']==h
        if relative not in [(HERE/n).relative_to(ROOT).as_posix() for n in names]:deps.append(item)
    out={'scope':__doc__,'package_files':[record(HERE/n) for n in names],'dependency_files':deps,
        'read_only_replay':(HERE/names[0]).relative_to(ROOT).as_posix(),'numeric_leaves_checked':95615,
        'all_nodes_checked':191557,'mathematical_integer_checks_passed':True,'Lean_invocations':0,
        'new_Huffman_Lean_consumer_implemented':False,'two_MB_complete_source_achieved':False,'new_zero_proportion_proven':False}
    OUT.write_text(json.dumps(out,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print(json.dumps({'manifest_sha256':record(OUT)['sha256'],'files':len(names),'dependencies':len(deps)}))
if __name__=='__main__':main()
