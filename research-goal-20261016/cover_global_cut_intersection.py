"""Intersect separately valid global-minimum hulls, then apply KKT Newton."""
from pathlib import Path
import hashlib,json,math,time
import cover_global_cut_hypograph as h
HERE=Path(__file__).parent

def main():
    start=time.monotonic();files=['cover-global-cut-full-contractor.json','cover-global-cut-hypograph.json']
    raws=[(HERE/name).read_bytes() for name in files];docs=[json.loads(raw) for raw in raws];full,hypo=docs
    lookup={r['path']:r for r in hypo['rows']};target=int(full['receipt']['target_numerator']);assert target==int(hypo['receipt']['target_numerator'])
    oracle=h.base.api.make_correlated_oracle();rows=[];counts={'remaining_both':0,'intersection_contracts':0,'Newton_paths':0,'Newton_steps':0,'closed':0}
    for original in full['contractions']:
        other=lookup[original['path']]
        if original['result'] or other['result']:continue
        initial=original['steps'][0]['old_cell'];assert initial==other['cell']
        s=original['steps'][-1]['new_cell'];t=other['steps'][-1]['new_cell'] if other['steps'] else other['cell']
        raw_intersection=[[max(x,y) for x,y in zip(s[0],t[0])],[min(x,y) for x,y in zip(s[1],t[1])]]
        cl=h.g.close(*raw_intersection);state=None if cl is None else cl[:2];steps=[];result=None;counts['remaining_both']+=1
        if state is None:result={'kind':'empty_intersection'}
        else:
            counts['intersection_contracts']+=state!=s and state!=t
            state,steps,ex=h.base.newton.contract(state,8,oracle)
            counts['Newton_paths']+=bool(steps);counts['Newton_steps']+=len(steps)
            if state is None:result={'kind':'empty_Newton'}
            elif ex:result={'kind':'stationary','result':ex}
            else:
                ex=h.base.api.correlated_exclusion(state,oracle)
                if ex:result={'kind':'stationary','result':ex}
                else:
                    rec=h.w.certify(state)
                    if int(rec.get('floor_numerator','-1'))>=target:result={'kind':'value','result':rec}
        counts['closed']+=bool(result);rows.append({'path':original['path'],'intersection_raw':raw_intersection,'Newton_steps':steps,'result':result})
    out={'receipt':{'scope':__doc__,'inputs':{name:hashlib.sha256(raw).hexdigest() for name,raw in zip(files,raws)},
      'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'target_numerator':str(target),'counts':counts,
      'complete_global_cover':False,'new_zero_proportion_proven':False,'seconds':time.monotonic()-start},'rows':rows}
    (HERE/'cover-global-cut-intersection.json').write_text(json.dumps(out,separators=(',',':'))+'\n',encoding='utf8');print(json.dumps(out['receipt']),flush=True)
if __name__=='__main__':main()
