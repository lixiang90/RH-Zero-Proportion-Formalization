"""Test a pressure halfspace dual on previously failed parent cells.

Only the frozen original mcheckGX integer inequality can accept a cell.
The floating LP multiplier merely chooses new support mixtures.
"""
from pathlib import Path
import argparse,json,time
import numpy as np
import ordered_generate as o
g=o.g

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int,default=100);args=ap.parse_args()
    here=Path(__file__).parent;x=json.loads((here/'native-tailfix-mid-master.json').read_text())
    branches={z['path']:z for z in x['branches']};seed=json.loads((here/'ordered-seed-1.json').read_text())['unresolved'][0]
    picked={list(sorted(branches))[i] for i in np.linspace(0,len(branches)-1,args.limit,dtype=int)}
    states={};todo=[(seed['path'],seed['state'])]
    while todo:
        path,state=todo.pop()
        if path not in branches:continue
        state,cuts=o.normalize(state)
        if path in picked:states[path]=state
        r=branches[path];a=r['axis'];q=r['cut']
        todo.extend([(path+'1',o.rawsplit(state,a,q,False)),(path+'0',o.rawsplit(state,a,q,True))])
    out=[];started=time.monotonic()
    for path,state in sorted(states.items()):
        old=g.certify(state,True);rec=g.certify(state,True,pressure=True)
        assert int(old['mcheck_numerator'])<g.TARGET,('not a failed parent',path)
        out.append({'path':path,'old_floor':old['floor'],'pressure_lp_floor':rec.get('lp_floor'),
            'new_floor':rec['floor'],'pressure_multiplier':rec.get('pressure_multiplier',0),
            'accepted_by_original_integer_checker':int(rec['mcheck_numerator'])>=g.TARGET})
    stats={'scope':__doc__,'processed':len(out),'old_failures_confirmed':len(out),
        'newly_closed':sum(z['accepted_by_original_integer_checker'] for z in out),
        'positive_pressure_multiplier':sum(z['pressure_multiplier']>0 for z in out),
        'max_multiplier':max(z['pressure_multiplier'] for z in out),'seconds':time.monotonic()-started}
    (here/'pressure-probe.json').write_text(json.dumps({'stats':stats,'rows':out},indent=2)+'\n')
    print(json.dumps(stats),flush=True)
if __name__=='__main__':main()
