"""Independent global-box wrapper around the unchanged factor replay.

Override only box construction with physical gap limits, unit moment boxes
and +/-7 for every u/q variable. Canonical RLT decomposition, old actual
graph/facet checking, unmerged multiplier equality and independent outward
rounding remain in the frozen replay. No tight scalar-box query is used.
"""
from pathlib import Path
from fractions import Fraction as F
import gzip,hashlib,json,sys,time
import cover_cross_moment_factor_replay as frozen
HERE=Path(__file__).parent;sha=lambda b:hashlib.sha256(b).hexdigest()
POLICY='cell-g/unit-H/global7-u-q-v1';CALLS=0


def global_boxes(state,params,checker):
    global CALLS
    CALLS+=1;box=[];mid=[];rad=[]
    for k in range(9):
        a,b=F(state[0][k],32768),F(state[1][k],32768);assert a<b
        box.append((a,b));mid.append((a+b)/2);rad.append((b-a)/2)
    box.extend([(F(-7),F(7))]*41)
    for i in range(9):
        for j in range(i,9):box.append((F(0),F(1)) if i==j else (F(-1),F(1)))
    box.extend([(F(-7),F(7))]*369)
    assert len(box)==464 and all(pair==(F(-7),F(7)) for pair in box[9:50]+box[95:])
    return box,mid,rad


def main():
    start=time.monotonic()
    if '--folder' not in sys.argv:sys.argv.extend(['--folder',str(HERE/'cover-cross-moment-global-box-evidence')])
    index=sys.argv.index('--folder');folder=Path(sys.argv[index+1]);proof_raw=(folder/'proof.json.gz').read_bytes();doc=json.loads(gzip.decompress(proof_raw))
    assert doc['schema']=='quadratic-energy-affine-factor-global-box-v1' and doc['box_policy']==POLICY
    assert all(c['box_policy']==POLICY and c['global_derivative_bound']=='7' for c in doc['records'])
    frozen.boxes=global_boxes;frozen.main();assert CALLS==2
    receipt_path=folder/'independent-replay.json';receipt=json.loads(receipt_path.read_bytes())
    assert receipt['all_checks_passed'] and receipt['strict_local_integer_systems']==2
    receipt['frozen_factor_replay_script_sha256']=receipt['script_sha256'];receipt['script_sha256']=sha(Path(__file__).read_bytes())
    receipt.update({'scope':__doc__,'box_policy':POLICY,'global_box_constructions':CALLS,'tight_derivative_box_queries_required':0,
      'old_graph_atoms_and_facets_still_checked':True,'seconds':time.monotonic()-start})
    receipt_path.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf8')
    print(json.dumps({'global_box_replay_passed':True,'seconds':receipt['seconds'],'receipt_sha256':sha(receipt_path.read_bytes())}),flush=True)
if __name__=='__main__':main()
