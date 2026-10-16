"""Paired energy-only OBBT control from the identical seventeen refined cells."""
from pathlib import Path
import hashlib,json,math,time
import numpy as np
import cover_integer_move_concave as context
import cover_sublevel_obbt_api as obbt
HERE=Path(__file__).parent;w=context.base.w;g=context.g

def main():
    start=time.monotonic();raw=(HERE/'cover-global-cut-contractor.json').read_bytes();source=json.loads(raw);target=int(source['receipt']['target_numerator'])
    oracle=context.base.api.make_correlated_oracle();engine=obbt.make_engine(w);rows=[];counts={'paths':0,'control_contracted':0,'control_closed':0,'global_cut_closed':0,'only_global_cut_closed':0};ratios=[]
    for record in source['contractions']:
        state=record['steps'][0]['old_cell'];state=(state[0],state[1]);initial=state;control=None;steps=[];counts['paths']+=1
        for k in range(2):
            rec=w.certify(state);axis,_=g.cut(state,rec);refined,bounds=obbt.contract(state,target,sorted(set(list(range(9))+[axis])),engine)
            if not bounds:break
            steps.append({'old_cell':state,'new_cell':refined,'certificates':bounds});state=refined
            if state is None:control='empty';break
            if context.base.api.correlated_exclusion(state,oracle):control='stationary';break
            rec=w.certify(state)
            if int(rec.get('floor_numerator','-1'))>=target:control='value';break
        if steps:counts['control_contracted']+=1
        if control:counts['control_closed']+=1
        cutclosed=record['result'] is not None;counts['global_cut_closed']+=cutclosed
        if cutclosed and not control:counts['only_global_cut_closed']+=1
        ratio=None if state is None else math.prod((state[1][k]-state[0][k]+1)/(initial[1][k]-initial[0][k]+1) for k in range(9))
        if ratio is not None:ratios.append(ratio)
        rows.append({'path':record['path'],'control_result':control,'global_cut_result':record['result']['kind'] if cutclosed else None,
          'control_volume_ratio_hint':ratio,'global_cut_volume_ratio_hint':record['volume_ratio_hint'],'control_steps':steps})
    receipt={'scope':__doc__,'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'input_sha256':hashlib.sha256(raw).hexdigest(),
      'counts':counts,'control_median_volume_ratio_hint':float(np.median(ratios)) if ratios else None,'complete_global_cover':False,
      'new_zero_proportion_proven':False,'seconds':time.monotonic()-start}
    (HERE/'cover-global-cut-control.json').write_text(json.dumps({'receipt':receipt,'rows':rows},separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(receipt),flush=True)
if __name__=='__main__':main()
