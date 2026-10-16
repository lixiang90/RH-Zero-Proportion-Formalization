"""Merge the completed tailfix search with the unchanged closed low/high trees."""
from pathlib import Path
import hashlib,json,sys
import ordered_merge

INPUTS=['ordered-master.json','ordered-0.json','ordered-2.json',
    'native-tailfix-mid-master.json','native-tailfix-mid-1.json',
    'native-tailfix-mid-0-master.json','native-tailfix-mid-0-0.json','native-tailfix-mid-0-1.json',
    'native-tailfix-mid-2-master.json','native-tailfix-mid-2-0-master.json','native-tailfix-mid-2-0-1.json',
    'native-tailfix-mid-2-0-0-master.json','native-tailfix-mid-2-0-0-0.json',
    'native-tailfix-mid-2-0-0-1-master.json','native-tailfix-mid-2-1-master.json',
    'native-tailfix-mid-2-1-0.json','native-tailfix-mid-2-1-1-master.json','tailfix-pooled.json']

def main():
    here=Path(__file__).parent
    assert json.loads((here/'tailfix-pooled.json').read_text())['unresolved_count']==0,'Shared queue not complete'
    hashes={name:hashlib.sha256((here/name).read_bytes()).hexdigest() for name in INPUTS}
    destination=here/'ordered-complete.json';assert not destination.exists(),'Final immutable output already exists'
    sys.argv=['ordered_merge.py','--output',str(destination),'--inputs']+[str(here/name) for name in INPUTS]
    result=ordered_merge.main()
    assert hashes=={name:hashlib.sha256((here/name).read_bytes()).hexdigest() for name in INPUTS},'Merge inputs changed'
    assert result['complete_finite_partition'] and result['unresolved_count']==0
    report={'scope':'Immutable final merge of independently replayable exact-integer search data; Lean and independent audit remain separate.',
        'inputs':[{'path':name,'sha256':hashes[name]} for name in INPUTS],
        'output':{'path':destination.name,'sha256':hashlib.sha256(destination.read_bytes()).hexdigest()},
        'gzip':{'path':destination.with_suffix('.json.gz').name,'sha256':hashlib.sha256(destination.with_suffix('.json.gz').read_bytes()).hexdigest()},
        'numeric_leaves':result['numeric_leaves'],'empty_leaves':result['empty_leaves'],
        'branches':result['branches'],'unresolved_count':0,'all_inputs_unchanged':True}
    (here/'tailfix-final-merge-manifest.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report),flush=True)
if __name__=='__main__':main()
